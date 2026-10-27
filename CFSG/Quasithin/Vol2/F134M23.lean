module

public import CFSG.Quasithin.Vol2.F134M23Check
public import CFSG.Quasithin.Vol2.F134M23Cover
public import CFSG.Quasithin.Vol2.F134M23Basic
public import CFSG.Quasithin.Vol2.F134J2

public section

namespace CFSG.Quasithin.F134

open Equiv CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem permCode_m23Word (w : List ℕ) : permCode (m23Word w) = m23WordC w := by
  induction w with
  | nil => exact m23_code_one
  | cons c w ih =>
    by_cases hc : c = 0
    · simp only [m23Word, m23WordC, hc, ite_true, permCode_mul23, ih, m23_code_a]
    · simp only [m23Word, m23WordC, hc, ite_false, permCode_mul23, ih, m23_code_b]

theorem m23Word_mem (w : List ℕ) : m23Word w ∈ NativeSporadic.M23 := by
  induction w with
  | nil => exact one_mem _
  | cons c w ih =>
    refine mul_mem ?_ ih
    rw [m23_eq_closure]
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m23TGen (k : ℕ) : Perm (Fin 23) := m23Word (m23TGenW.getD k [])

@[expose] def m23T : Subgroup (Perm (Fin 23)) := Subgroup.closure {x | ∃ k < 3, m23TGen k = x}

theorem permCode_m23TGen {k : ℕ} (hk : k < 3) : permCode (m23TGen k) = m23TG k := by
  rw [m23TGen, permCode_m23Word]
  exact m23_tgen_check k hk

theorem m23T_le : m23T ≤ NativeSporadic.M23 := by
  rw [m23T, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact m23Word_mem _

theorem m23T_sub {x : Perm (Fin 23)} (hx : x ∈ m23T) : ∃ i < 128, permCode x = m23Tel i := by
  refine closure_subset_of_right_closed (S := {x | ∃ k < 3, m23TGen k = x})
    (P := {x | ∃ i < 128, permCode x = m23Tel i})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, by rw [m23_code_one, m23_tel_zero]⟩ ?_ hx
  rintro p ⟨i, hi, hp⟩ s ⟨k, hk, rfl⟩
  obtain ⟨h1, h2⟩ := m23_nxt_check i hi k hk
  exact ⟨_, h1, by rw [permCode_mul23, hp, permCode_m23TGen hk, h2]⟩

theorem m23T_sup : ∀ i < 128, ∃ x ∈ m23T, permCode x = m23Tel i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [m23_code_one, m23_tel_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := m23_par_check i hi hpos
      obtain ⟨y, hy, hyc⟩ := ih _ h1 (h1.trans hi)
      refine ⟨y * m23TGen (m23Par i % 4), mul_mem hy (Subgroup.subset_closure ⟨_, h2, rfl⟩), ?_⟩
      rw [permCode_mul23, hyc, permCode_m23TGen h2, h3]

theorem m23T_isPGroup : IsPGroup 2 m23T := by
  intro x
  obtain ⟨i, hi, hx⟩ := m23T_sub x.2
  refine ⟨3, Subtype.ext (eq_of_permCode23 ?_)⟩
  rw [Subgroup.coe_pow, permCode_pow_two_pow23, hx, Subgroup.coe_one, m23_code_one]
  exact m23_pow_check i hi

@[expose] noncomputable def m23TelE (i : ℕ) : Perm (Fin 23) :=
  if h : i < 128 then Classical.choose (m23T_sup i h) else 1

theorem m23TelE_mem (i : ℕ) : m23TelE i ∈ m23T := by
  unfold m23TelE
  split_ifs with h
  · exact (Classical.choose_spec (m23T_sup i h)).1
  · exact one_mem _

theorem permCode_m23TelE {i : ℕ} (hi : i < 128) : permCode (m23TelE i) = m23Tel i := by
  unfold m23TelE
  rw [dite_eq_left hi]
  exact (Classical.choose_spec (m23T_sup i hi)).2

theorem m23TelE_zero : m23TelE 0 = 1 :=
  eq_of_permCode23 (by rw [permCode_m23TelE (by norm_num), m23_tel_zero, m23_code_one])

theorem card_m23T : Nat.card m23T = 128 := by
  let f : Fin 128 → m23T := fun i => ⟨m23TelE i, m23TelE_mem i⟩
  have hinj : Function.Injective f := by
    intro i j h
    have hc := congrArg permCode (congrArg Subtype.val h : m23TelE i = m23TelE j)
    rw [permCode_m23TelE i.2, permCode_m23TelE j.2] at hc
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact m23_tel_ne j j.2 i hlt hc.symm
    · exact m23_tel_ne i i.2 j hlt hc
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, hc⟩ := m23T_sub hx
    exact ⟨⟨i, hi⟩, Subtype.ext (eq_of_permCode23 ((permCode_m23TelE hi).trans hc.symm))⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_fin]

@[expose] def m23GP (c : ℕ) : Perm (Fin 23) := m23Word (m23GW.getD c [])

theorem permCode_m23GP {c : ℕ} (hc : c < 2) : permCode (m23GP c) = m23G c := by
  rw [m23GP, permCode_m23Word]
  exact m23_g_check c hc

@[expose] noncomputable def m23LetE (l : ℕ) : Perm (Fin 23) :=
  if l < 128 then m23TelE l else m23GP (l - 128)

theorem permCode_m23LetE {l : ℕ} (hl : l < 130) : permCode (m23LetE l) = m23Let l := by
  unfold m23LetE m23Let
  split_ifs with h
  · exact permCode_m23TelE h
  · exact permCode_m23GP (by omega)

@[expose] noncomputable def m23LWord : List ℕ → Perm (Fin 23)
  | [] => 1
  | l :: w => m23LetE l * m23LWord w

theorem permCode_m23LWord : ∀ w : List ℕ, (∀ l ∈ w, l < 130) →
    permCode (m23LWord w) = m23LWordC w
  | [], _ => m23_code_one
  | l :: w, hw => by
    rw [m23LWord, m23LWordC, permCode_mul23, permCode_m23LetE (hw l List.mem_cons_self),
      permCode_m23LWord w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]

@[expose] noncomputable def m23DP (j : ℕ) : Perm (Fin 23) := m23LWord (m23DW.getD j [])

theorem permCode_m23DP {j : ℕ} (hj : j < 835) : permCode (m23DP j) = m23D j := by
  obtain ⟨h1, h2⟩ := m23_d_check j hj
  rw [m23DP, permCode_m23LWord _ h2]
  exact h1

theorem m23DP_zero : m23DP 0 = 1 := by
  rw [m23DP, m23_dw_zero]
  rfl

@[expose] def m23U : Set (Perm (Fin 23)) :=
  {x | ∃ j < 835, ∃ t ∈ m23T, ∃ t' ∈ m23T, x = t * m23DP j * t'}

theorem one_mem_m23U : (1 : Perm (Fin 23)) ∈ m23U :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [m23DP_zero]; group⟩

theorem m23U_mul_T {x s : Perm (Fin 23)} (hx : x ∈ m23U) (hs : s ∈ m23T) : x * s ∈ m23U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem m23U_mul_g {c : ℕ} (hc : c < 2) {x : Perm (Fin 23)} (hx : x ∈ m23U) :
    x * m23GP c ∈ m23U := by
  have hE : ∀ p < 32, ∃ v ∈ m23T, m23TelE (m23GEAt c p) * m23GP c = m23GP c * v := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      obtain ⟨hE0, htree⟩ := m23_gtree_check c hc
      rcases Nat.eq_zero_or_pos p with rfl | hpos
      · exact ⟨1, one_mem _, by rw [hE0, m23TelE_zero, one_mul, mul_one]⟩
      · obtain ⟨hEp, hrest⟩ := htree p hp
        obtain ⟨hq, hl, hprod⟩ := hrest hpos
        obtain ⟨v, hv, hve⟩ := ih _ hq (hq.trans hp)
        obtain ⟨hEq, -⟩ := htree _ (hq.trans hp)
        obtain ⟨hu, hcl, hconj'⟩ := m23_gconj_check c hc _ hl
        have hug : m23TelE ((m23GUL.getD c []).getD (m23GPAt c p % 8) 0) * m23GP c =
            m23GP c * m23TelE ((m23GCL.getD c []).getD (m23GPAt c p % 8) 0) :=
          eq_of_permCode23 (by
            rw [permCode_mul23, permCode_mul23, permCode_m23TelE hu, permCode_m23GP hc,
              permCode_m23TelE hcl]
            exact hconj')
        have hsplit : m23TelE (m23GEAt c p) = m23TelE (m23GEAt c (m23GPAt c p / 8)) *
            m23TelE ((m23GUL.getD c []).getD (m23GPAt c p % 8) 0) := eq_of_permCode23 (by
          rw [permCode_mul23, permCode_m23TelE hEp, permCode_m23TelE hEq, permCode_m23TelE hu]
          exact hprod.symm)
        exact ⟨v * m23TelE ((m23GCL.getD c []).getD (m23GPAt c p % 8) 0),
          mul_mem hv (m23TelE_mem _), by rw [hsplit]; exact mul_conj_step hug hve⟩
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨i, hi, hci⟩ := m23T_sub ht'
  obtain ⟨hs, hp, hr, htr⟩ := m23_gtrans_check c hc i hi
  obtain ⟨hEp, -⟩ := (m23_gtree_check c hc).2 _ hp
  have ht'eq : t' = m23TelE ((m23GRL.getD c []).getD (m23GQAt c i / 128) 0) *
      m23TelE (m23GEAt c (m23GQAt c i % 128)) :=
    eq_of_permCode23 (by
      rw [hci, permCode_mul23, permCode_m23TelE hr, permCode_m23TelE hEp]
      exact htr)
  obtain ⟨v, hv, hve⟩ := hE _ hp
  obtain ⟨hk, hdeq⟩ := m23_gdec_spec hc hj hs
  generalize m23GDecAt c (4 * j + m23GQAt c i / 128) = e at hk hdeq
  have hd : m23DP j * m23TelE ((m23GRL.getD c []).getD (m23GQAt c i / 128) 0) * m23GP c =
      m23TelE (e / 128 % 128) * m23DP (e / 16384) * m23TelE (e % 128) := eq_of_permCode23 (by
    rw [permCode_mul23, permCode_mul23, permCode_mul23, permCode_mul23, permCode_m23DP hj,
      permCode_m23TelE hr, permCode_m23GP hc, permCode_m23TelE (Nat.mod_lt _ (by norm_num)),
      permCode_m23DP hk, permCode_m23TelE (Nat.mod_lt _ (by norm_num))]
    exact hdeq)
  refine ⟨e / 16384, hk, t * m23TelE (e / 128 % 128), mul_mem ht (m23TelE_mem _),
    m23TelE (e % 128) * v, mul_mem (m23TelE_mem _) hv, ?_⟩
  rw [ht'eq]
  exact mul_rearrange hve hd

theorem m23U_mul_LetE {x : Perm (Fin 23)} (hx : x ∈ m23U) {l : ℕ} (hl : l < 130) :
    x * m23LetE l ∈ m23U := by
  unfold m23LetE
  split_ifs with h
  · exact m23U_mul_T hx (m23TelE_mem l)
  · exact m23U_mul_g (by omega) hx

theorem m23U_mul_LWord : ∀ (w : List ℕ), (∀ l ∈ w, l < 130) → ∀ {x : Perm (Fin 23)},
    x ∈ m23U → x * m23LWord w ∈ m23U
  | [], _, x, hx => by rw [m23LWord, mul_one]; exact hx
  | l :: w, hw, x, hx => by
    rw [m23LWord, ← mul_assoc]
    exact m23U_mul_LWord w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (m23U_mul_LetE hx (hw l List.mem_cons_self))

theorem m23U_mul_ab {x : Perm (Fin 23)} (hx : x ∈ m23U) :
    x * m23PermA ∈ m23U ∧ x * m23PermB ∈ m23U := by
  obtain ⟨h1, h2, h3, h4⟩ := m23_ab_check
  have ha : m23PermA = m23LWord m23AW :=
    eq_of_permCode23 (by rw [m23_code_a, permCode_m23LWord _ h2, h1])
  have hb : m23PermB = m23LWord m23BW :=
    eq_of_permCode23 (by rw [m23_code_b, permCode_m23LWord _ h4, h3])
  rw [ha, hb]
  exact ⟨m23U_mul_LWord _ h2 hx, m23U_mul_LWord _ h4 hx⟩

theorem m23_subset_U : (NativeSporadic.M23 : Set (Perm (Fin 23))) ⊆ m23U := by
  rw [m23_eq_closure]
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_m23U ?_
  rintro p hp s (rfl | rfl)
  · exact (m23U_mul_ab hp).1
  · exact (m23U_mul_ab hp).2

theorem m23_not_mem_of_bad {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {j : ℕ} (hj : j < 835) (hj6 : 6 ≤ j)
    (hD : m23DP j ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := m23_bad_check j hj hj6
  set p := m23Bad j % 16 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(m23DP j * m23TelE (m23Bad j / 256)) ^ (m23Bad j / 16 % 16),
    pow_mem (mul_mem hD (hTH (m23TelE_mem _))) _⟩
  have hcode : permCode (x : Perm (Fin 23)) = powC23 m23oneC (m23Bad j / 16 % 16)
      (mul23 (m23D j) (m23Tel (m23Bad j / 256))) := by
    show permCode ((m23DP j * m23TelE (m23Bad j / 256)) ^ (m23Bad j / 16 % 16)) = _
    rw [permCode_pow23, permCode_mul23, permCode_m23DP hj, permCode_m23TelE hi, m23_code_one]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_permCode23
    rw [Subgroup.coe_pow, permCode_pow23, hcode, Subgroup.coe_one, m23_code_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, m23_code_one]
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  rcases hp' with h | h
  · rw [h] at hdvd
    exact h5 hdvd
  · rw [h] at hdvd
    exact h7 hdvd

theorem m23_not_mem_of_excl {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {k : ℕ} (hk0 : 0 < k) (hk : k < 5)
    (hD5 : m23DP 5 ∈ H) (hDk : m23DP k ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := m23_excl_check k hk hk0
  set p := m23Excl k % 16 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(m23DP 5 * m23TelE (m23Excl k / 256) * m23DP k) ^ (m23Excl k / 16 % 16),
    pow_mem (mul_mem (mul_mem hD5 (hTH (m23TelE_mem _))) hDk) _⟩
  have hcode : permCode (x : Perm (Fin 23)) = powC23 m23oneC (m23Excl k / 16 % 16)
      (mul23 (mul23 (m23D 5) (m23Tel (m23Excl k / 256))) (m23D k)) := by
    show permCode ((m23DP 5 * m23TelE (m23Excl k / 256) * m23DP k) ^ (m23Excl k / 16 % 16)) = _
    rw [permCode_pow23, permCode_mul23, permCode_mul23, permCode_m23DP (by norm_num),
      permCode_m23TelE hi, permCode_m23DP (by omega), m23_code_one]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_permCode23
    rw [Subgroup.coe_pow, permCode_pow23, hcode, Subgroup.coe_one, m23_code_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, m23_code_one]
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  rcases hp' with h | h
  · rw [h] at hdvd
    exact h5 hdvd
  · rw [h] at hdvd
    exact h7 hdvd

theorem m23_cos {j : ℕ} (hj0 : 0 < j) (hj : j < 6) {t t' : Perm (Fin 23)} (ht : t ∈ m23T) :
    ∃ b < 2, ∃ w ∈ m23T,
      t * m23DP j * t' = m23TelE (if b = 0 then 0 else 1) * m23DP j * (w * t') := by
  obtain ⟨i, hi, htc⟩ := m23T_sub ht
  obtain ⟨hs, hcos⟩ := m23_cos_check j hj hj0 i hi
  have hr : (if m23Cos j i / 128 = 0 then 0 else 1) < 128 := by split_ifs <;> norm_num
  refine ⟨m23Cos j i / 128, hs, m23TelE (m23Cos j i % 128), m23TelE_mem _, ?_⟩
  have key : t * m23DP j = m23TelE (if m23Cos j i / 128 = 0 then 0 else 1) * m23DP j *
      m23TelE (m23Cos j i % 128) := by
    apply eq_of_permCode23
    rw [permCode_mul23, permCode_mul23, permCode_mul23, htc, permCode_m23TelE hr,
      permCode_m23TelE (Nat.mod_lt _ (by norm_num)), permCode_m23DP (by omega)]
    exact hcos
  rw [key]
  group

theorem m23_mem_U_good {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H)
    (hH : H ≤ NativeSporadic.M23) (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) :
    ∀ h ∈ H, ∃ j < 6, m23DP j ∈ H ∧ ∃ t ∈ m23T, ∃ t' ∈ m23T, h = t * m23DP j * t' := by
  intro h hh
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := m23_subset_U (hH hh)
  have hD : m23DP j ∈ H := by
    have e : m23DP j = t⁻¹ * (t * m23DP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · exact ⟨j, hj6, hD, t, ht, t', ht', rfl⟩
  · exact (m23_not_mem_of_bad hTH h5 h7 hj hj6 hD).elim

theorem m23_card_le_of_five {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H)
    (hH : H ≤ NativeSporadic.M23) (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H)
    (hD5 : m23DP 5 ∈ H) : Nat.card H ≤ 3 * Nat.card m23T := by
  have : Finite m23T := Nat.finite_of_card_ne_zero (by rw [card_m23T]; norm_num)
  refine card_le_of_cover ![1, m23DP 5, m23TelE 1 * m23DP 5] fun h hh => ?_
  obtain ⟨j, hj, hD, t, ht, t', ht', rfl⟩ := m23_mem_U_good hTH hH h5 h7 h hh
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨0, t * t', mul_mem ht ht', by rw [m23DP_zero]; simp⟩
  rcases Nat.lt_or_ge j 5 with hj5 | hj5
  · exact (m23_not_mem_of_excl hTH h5 h7 hj0 hj5 hD5 hD).elim
  have hj' : j = 5 := by omega
  subst hj'
  obtain ⟨b, hb, w, hw, e⟩ := m23_cos hj0 hj ht (t' := t')
  interval_cases b
  · exact ⟨1, w * t', mul_mem hw ht', by rw [e]; simp [m23TelE_zero]⟩
  · exact ⟨2, w * t', mul_mem hw ht', by rw [e]; simp⟩

@[expose] noncomputable def m23CP (s : ℕ) : Perm (Fin 23) :=
  if s = 0 then 1 else m23TelE (if s % 2 = 0 then 1 else 0) * m23DP ((s + 1) / 2)

theorem permCode_m23CP {s : ℕ} (hs : s < 9) : permCode (m23CP s) = m23CC s := by
  unfold m23CP m23CC
  split_ifs
  · exact m23_code_one
  · rw [permCode_mul23, permCode_m23TelE (by norm_num), permCode_m23DP (by omega)]
  · rw [permCode_mul23, permCode_m23TelE (by norm_num), permCode_m23DP (by omega)]

theorem m23_cover {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H) (hH : H ≤ NativeSporadic.M23)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) (hD5 : m23DP 5 ∉ H) :
    ∀ h ∈ H, ∃ s < 9, ∃ t ∈ m23T, h = m23CP s * t := by
  intro h hh
  obtain ⟨j, hj, hD, t, ht, t', ht', rfl⟩ := m23_mem_U_good hTH hH h5 h7 h hh
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨0, by norm_num, t * t', mul_mem ht ht', by rw [m23DP_zero]; simp [m23CP]⟩
  have hj5 : j < 5 := by
    rcases Nat.lt_or_ge j 5 with h | h
    · exact h
    · exact absurd (show j = 5 by omega ▸ hD) hD5
  obtain ⟨b, hb, w, hw, e⟩ := m23_cos hj0 (by omega) ht (t' := t')
  refine ⟨2 * j - 1 + b, by omega, w * t', mul_mem hw ht', ?_⟩
  rw [e]
  have hs0 : 2 * j - 1 + b ≠ 0 := by omega
  have hsj : (2 * j - 1 + b + 1) / 2 = j := by omega
  have hsb : (if (2 * j - 1 + b) % 2 = 0 then 1 else 0) = (if b = 0 then 0 else 1) := by
    interval_cases b <;> simp <;> omega
  simp only [m23CP, hs0, ite_false, hsj, hsb, mul_assoc]

@[expose] def m23H0 : Set (Perm (Fin 23)) := {x | ∃ s < 9, ∃ t ∈ m23T, x = m23CP s * t}

theorem m23H0_eq_range :
    m23H0 = Set.range fun q : Fin 9 × Fin 128 => m23CP q.1 * m23TelE q.2 := by
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    obtain ⟨i, hi, hc⟩ := m23T_sub ht
    refine ⟨(⟨s, hs⟩, ⟨i, hi⟩), ?_⟩
    show m23CP s * m23TelE i = m23CP s * t
    rw [eq_of_permCode23 ((permCode_m23TelE hi).trans hc.symm)]
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.1.2, m23TelE q.2, m23TelE_mem _, rfl⟩

theorem ncard_m23H0_le : m23H0.ncard ≤ 1152 := by
  rw [m23H0_eq_range, ← Set.image_univ]
  calc _ ≤ (Set.univ : Set (Fin 9 × Fin 128)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 1152 := by rw [Set.ncard_univ]; simp

theorem m23_eq_H0 {H : Subgroup (Perm (Fin 23))} (hTH : m23T ≤ H) (hH : H ≤ NativeSporadic.M23)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) (hcard : Nat.card H = 1152) :
    (H : Set (Perm (Fin 23))) = m23H0 := by
  have hD5 : m23DP 5 ∉ H := by
    intro hD5
    have := m23_card_le_of_five hTH hH h5 h7 hD5
    rw [hcard, card_m23T] at this
    norm_num at this
  have hH' : (H : Set (Perm (Fin 23))).ncard = 1152 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  refine Set.eq_of_subset_of_ncard_le (fun h hh => m23_cover hTH hH h5 h7 hD5 h hh) ?_
    (Set.toFinite _)
  rw [hH']
  exact ncard_m23H0_le

@[expose] noncomputable def m23Cnt (K : Subgroup (Perm (Fin 23))) (z : Perm (Fin 23)) : ℕ :=
  Nat.card ↥(K ⊓ Subgroup.centralizer ({z} : Set (Perm (Fin 23))))

theorem m23_card_cent {K : Subgroup (Perm (Fin 23))}
    (hK : (K : Set (Perm (Fin 23))) = m23H0) (hcard : Nat.card K = 1152) (z : Perm (Fin 23)) :
    m23Cnt K z = m23CentCount (permCode z) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin 9 × Fin 128 → Perm (Fin 23),
      Φ = fun q => m23CP q.1 * m23TelE q.2 := ⟨_, rfl⟩
  have hrange : Set.range Φ = (K : Set (Perm (Fin 23))) := by rw [hK, m23H0_eq_range, hΦ]
  have hinj : Function.Injective Φ := by
    have e1 : (K : Set (Perm (Fin 23))).ncard = 1152 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    have h1 : (Φ '' Set.univ).ncard = (Set.univ : Set (Fin 9 × Fin 128)).ncard := by
      rw [Set.image_univ, hrange, Set.ncard_univ, e1]
      simp
    exact Set.injOn_univ.mp (Set.injOn_of_ncard_image_eq h1)
  have hcode : ∀ q : Fin 9 × Fin 128, permCode (Φ q) = mul23 (m23CC q.1) (m23Tel q.2) := by
    intro q
    rw [hΦ]
    show permCode (m23CP q.1 * m23TelE q.2) = _
    rw [permCode_mul23, permCode_m23CP q.1.2, permCode_m23TelE q.2.2]
  set S : Finset (Fin 9 × Fin 128) := (Finset.univ : Finset (Fin 9 × Fin 128)).filter fun q =>
    mul23 (mul23 (m23CC q.1) (m23Tel q.2)) (permCode z) =
      mul23 (permCode z) (mul23 (m23CC q.1) (m23Tel q.2)) with hS
  have hP : ∀ q, q ∈ S ↔ Φ q * z = z * Φ q := by
    intro q
    rw [hS, Finset.mem_filter, ← hcode q]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      apply eq_of_permCode23
      rw [permCode_mul23 (Φ q) z, permCode_mul23 z (Φ q)]
      exact h
    · intro h
      have := congrArg permCode h
      rw [permCode_mul23 (Φ q) z, permCode_mul23 z (Φ q)] at this
      exact this
  let f : ↥S → ↥(K ⊓ Subgroup.centralizer ({z} : Set (Perm (Fin 23)))) :=
    fun q => ⟨Φ q.1, Subgroup.mem_inf.mpr ⟨by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨q.1, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ((hP q.1).mp q.2)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ Set.range Φ := by rw [hrange]; exact hxK
      obtain ⟨q, rfl⟩ := hx'
      exact ⟨⟨q, (hP q).mpr (Subgroup.mem_centralizer_singleton_iff.mp hxC)⟩, rfl⟩
  rw [m23Cnt, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard]
  rfl

theorem m23_P0 {K : Subgroup (Perm (Fin 23))}
    (hK : (K : Set (Perm (Fin 23))) = m23H0) (hcard : Nat.card K = 1152) :
    ∃ x1 x2 : Perm (Fin 23), x1 ∈ K ∧ x2 ∈ K ∧ orderOf x1 = 3 ∧ orderOf x2 = 3 ∧
      x1 * x2 = x2 * x1 ∧ (∀ a < 3, ∀ b < 3, 0 < b → x2 ^ b ≠ x1 ^ a) ∧
      m23Cnt K x1 = 9 ∧ ∀ a < 3, ∀ b < 3, 0 < b → m23Cnt K (x1 ^ a * x2 ^ b) ≠ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x1, hx1def⟩ : ∃ x : Perm (Fin 23), x = m23DP 1 * m23TelE 1 := ⟨_, rfl⟩
  obtain ⟨x2, hx2def⟩ : ∃ x : Perm (Fin 23), x = m23DP 2 * m23TelE 115 := ⟨_, rfl⟩
  have hc1 : permCode x1 = m23X1 := by
    rw [hx1def, permCode_mul23, permCode_m23DP (by norm_num), permCode_m23TelE (by norm_num)]
    rfl
  have hc2 : permCode x2 = m23X2 := by
    rw [hx2def, permCode_mul23, permCode_m23DP (by norm_num), permCode_m23TelE (by norm_num)]
    rfl
  obtain ⟨h13, h1ne, h23, hcomm, hdis⟩ := m23_x_check
  have hmemK : ∀ {s i : ℕ}, s < 9 → i < 128 → m23CP s * m23TelE i ∈ K := by
    intro s i hs hi
    rw [← SetLike.mem_coe, hK]
    exact ⟨s, hs, m23TelE i, m23TelE_mem i, rfl⟩
  have hx1K : x1 ∈ K := by
    have h := hmemK (s := 1) (i := 1) (by norm_num) (by norm_num)
    simpa [m23CP, m23TelE_zero, ← hx1def] using h
  have hx2K : x2 ∈ K := by
    have h := hmemK (s := 3) (i := 115) (by norm_num) (by norm_num)
    simpa [m23CP, m23TelE_zero, ← hx2def] using h
  have hcodePow : ∀ (u : Perm (Fin 23)) (n : ℕ),
      permCode (u ^ n) = powC23 m23oneC n (permCode u) := fun u n => by
    rw [permCode_pow23, m23_code_one]
  have hpow1 : x1 ^ 3 = 1 := eq_of_permCode23 (by rw [hcodePow, hc1, m23_code_one]; exact h13)
  have hne1 : x1 ≠ 1 := fun h => h1ne (by rw [← hc1, h, m23_code_one])
  have ho1 : orderOf x1 = 3 := orderOf_eq_prime hpow1 hne1
  have hd : ∀ a < 3, ∀ b < 3, 0 < b → x2 ^ b ≠ x1 ^ a := by
    intro a ha b hb hb0 h
    exact hdis a ha b hb hb0 (by rw [← hc1, ← hc2, ← hcodePow, ← hcodePow, h])
  have hpow2 : x2 ^ 3 = 1 := eq_of_permCode23 (by rw [hcodePow, hc2, m23_code_one]; exact h23)
  have hne2 : x2 ≠ 1 := by
    intro h
    apply hd 0 (by norm_num) 1 (by norm_num) (by norm_num)
    rw [h, pow_zero, one_pow]
  have ho2 : orderOf x2 = 3 := orderOf_eq_prime hpow2 hne2
  have hc12 : x1 * x2 = x2 * x1 := eq_of_permCode23 (by
    have h := hcomm 1 (by norm_num)
    rw [← hc1, ← hc2, ← hcodePow, pow_one] at h
    rw [permCode_mul23, permCode_mul23]
    exact h)
  have hcntinv : ∀ z, m23Cnt K z⁻¹ = m23Cnt K z := fun z => by
    simp only [m23Cnt, centralizer_inv_singleton]
  have hcx1 : m23Cnt K x1 = 9 := by rw [m23_card_cent hK hcard, hc1]; exact m23_cent_check₁
  have hcx2 : m23Cnt K x2 = 36 := by rw [m23_card_cent hK hcard, hc2]; exact m23_cent_check₂
  have hcx3 : m23Cnt K (x1 * x2) = 36 := by
    rw [m23_card_cent hK hcard, permCode_mul23 x1 x2, hc1, hc2]; exact m23_cent_check₃
  have hcx4 : m23Cnt K (x1 * (x2 * x2)) = 36 := by
    rw [m23_card_cent hK hcard, permCode_mul23 x1 (x2 * x2), permCode_mul23 x2 x2, hc1, hc2]
    exact m23_cent_check₄
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := m23_rel_check
  have hzc : ∀ a b : ℕ, permCode (x1 ^ a * x2 ^ b) = m23ZC a b := fun a b => by
    rw [permCode_mul23, hcodePow, hcodePow, hc1, hc2]
    rfl
  refine ⟨x1, x2, hx1K, hx2K, ho1, ho2, hc12, hd, hcx1, fun a ha b hb hb0 => ?_⟩
  have hinv : ∀ w, permCode (x1 ^ a * x2 ^ b) = permCode w →
      m23Cnt K (x1 ^ a * x2 ^ b) = m23Cnt K w := fun w h => by rw [eq_of_permCode23 h]
  have hinv' : ∀ w, mul23 (m23ZC a b) (permCode w) = m23oneC →
      m23Cnt K (x1 ^ a * x2 ^ b) = m23Cnt K w := fun w h => by
    have e : x1 ^ a * x2 ^ b * w = 1 :=
      eq_of_permCode23 (by rw [permCode_mul23 (x1 ^ a * x2 ^ b) w, hzc, m23_code_one]; exact h)
    have e' : x1 ^ a * x2 ^ b = w⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [e', hcntinv]
  interval_cases b
  · interval_cases a
    · rw [hinv x2 (by rw [hzc, hc2]; exact r1), hcx2]
      omega
    · rw [hinv (x1 * x2) (by rw [hzc, permCode_mul23 x1 x2, hc1, hc2]; exact r3), hcx3]
      omega
    · rw [hinv' (x1 * (x2 * x2))
        (by rw [permCode_mul23 x1 (x2 * x2), permCode_mul23 x2 x2, hc1, hc2]; exact r6), hcx4]
      omega
  · interval_cases a
    · rw [hinv' x2 (by rw [hc2]; exact r2), hcx2]
      omega
    · rw [hinv (x1 * (x2 * x2))
        (by rw [hzc, permCode_mul23 x1 (x2 * x2), permCode_mul23 x2 x2, hc1, hc2]; exact r5),
        hcx4]
      omega
    · rw [hinv' (x1 * x2) (by rw [permCode_mul23 x1 x2, hc1, hc2]; exact r4), hcx3]
      omega

theorem m23_model_key {K : Subgroup (Perm (Fin 23))}
    (hK : (K : Set (Perm (Fin 23))) = m23H0) (hcard : Nat.card K = 1152)
    {Q : Subgroup (Perm (Fin 23))} (hQK : Q ≤ K) (hQ : Nat.card Q = 9) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ m23Cnt K y₀ = 9 ∧
      ∀ y ∈ Q, m23Cnt K y = 9 → y ∈ Subgroup.zpowers y₀ := by
  obtain ⟨x1, x2, hx1K, hx2K, ho1, ho2, hc12, hd, hcx1, hbad⟩ := m23_P0 hK hcard
  obtain ⟨hP0, hP0el⟩ := card_sup_zpowers_of_comm ho1 ho2 hc12 hd
  have hP0K : Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hx1K) (Subgroup.zpowers_le.mpr hx2K)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine exists_inv_of_sylow (m := 128) (fun z => m23Cnt K z = 9) (fun k hk z hz => ?_) hP0K hQK
    hP0 hQ (by rw [hcard]) (by norm_num) (Subgroup.mem_sup_left (Subgroup.mem_zpowers x1)) ho1
    hcx1 (fun z hz hcz => ?_)
  · rw [m23Cnt, card_inf_centralizer_conj hk z]
    exact hz
  · obtain ⟨a, ha, b, hb, rfl⟩ := hP0el z hz
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · exact absurd hcz (hbad a ha b hb hb0)

@[expose] def carrierM23Equiv : NativeSporadic.Carrier .M23 ≃* ↥NativeSporadic.M23 :=
  MulEquiv.refl _

theorem noE9Config_m23 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ₀, hφ₀def⟩ : ∃ φ₀ : ↥L →* Perm (Fin 23),
      φ₀ = (Subgroup.subtype _).comp ((e.trans carrierM23Equiv) : ↥L →* ↥NativeSporadic.M23) :=
    ⟨_, rfl⟩
  have hφ₀ : Function.Injective φ₀ := by
    rw [hφ₀def]
    exact (Subgroup.subtype_injective _).comp (e.trans carrierM23Equiv).injective
  have hφ₀G : ∀ x, φ₀ x ∈ NativeSporadic.M23 := fun x => by rw [hφ₀def]; exact (Subtype.prop _)
  have hφ₀s : ∀ y ∈ NativeSporadic.M23, ∃ x, φ₀ x = y := by
    intro y hy
    obtain ⟨x, hx⟩ := (e.trans carrierM23Equiv).surjective ⟨y, hy⟩
    exact ⟨x, by rw [hφ₀def]; exact congrArg Subtype.val hx⟩
  obtain ⟨φ, hφ, hφG, -, hTφ⟩ :=
    E9Config.exists_model_conj hcfg hφ₀ hφ₀G hφ₀s m23T_le m23T_isPGroup
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (Perm (Fin 23)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : m23T ≤ K := by
    rw [hKdef]
    exact hTφ.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right))
  have hKM : K ≤ NativeSporadic.M23 := by
    rw [hKdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφG _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inl rfl)
  have h7 : ¬ 7 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inr (Or.inl rfl))
  have hTU : 128 ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv,
      Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ hφ).toEquiv, ← card_m23T]
    have : Finite (((T ⊓ L).subgroupOf L).map φ) := Subgroup.instFiniteSubtypeMem _
    exact Subgroup.card_le_of_le hTφ
  have hD5 : m23DP 5 ∉ K := by
    intro hD5
    have := m23_card_le_of_five hTK hKM h5 h7 hD5
    rw [card_m23T, hKc, hHc] at this
    omega
  have hle : Nat.card K ≤ 9 * 128 := by
    have : Finite m23T := Nat.finite_of_card_ne_zero (by rw [card_m23T]; norm_num)
    have h := card_le_of_cover (fun s : Fin 9 => m23CP s) fun h hh => by
      obtain ⟨s, hs, t, ht, rfl⟩ := m23_cover hTK hKM h5 h7 hD5 h hh
      exact ⟨⟨s, hs⟩, t, ht, rfl⟩
    rwa [card_m23T] at h
  have hK1152 : Nat.card K = 1152 := by
    rw [hKc, hHc] at hle ⊢
    omega
  have hKset := m23_eq_H0 hTK hKM h5 h7 hK1152
  obtain ⟨PK, hPKdef⟩ : ∃ R : Subgroup (Perm (Fin 23)), R = (P.subgroupOf L).map φ := ⟨_, rfl⟩
  have hPKK : PK ≤ K := by
    rw [hPKdef, hKdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left)
  have hPKc : Nat.card PK = 9 := by
    rw [hPKdef, ← Nat.card_congr ((P.subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  obtain ⟨y₀', hy₀'P, hy₀'o, hy₀'c, hy₀'max⟩ := m23_model_key hKset hK1152 hPKK hPKc
  rw [hPKdef] at hy₀'P
  obtain ⟨x₀, hx₀P, rfl⟩ := hy₀'P
  have hx₀P' : (x₀ : A) ∈ P := Subgroup.mem_subgroupOf.mp hx₀P
  have hcA : ∀ y : ↥L, Nat.card ↥((P ⊔ (T ⊓ L)) ⊓ Subgroup.centralizer ({(y : A)} : Set A)) =
      m23Cnt K (φ y) := by
    intro y
    have h1 := card_inf_centralizer_map L.subtype L.subtype_injective
      ((P ⊔ (T ⊓ L)).subgroupOf L) y
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHL] at h1
    rw [show (y : A) = L.subtype y from rfl, h1, m23Cnt, hKdef,
      card_inf_centralizer_map φ hφ]
  have hL := hcfg.normal
  have htH : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P ⊔ (T ⊓ L),
      t * x * t⁻¹ ∈ P ⊔ (T ⊓ L) := by
    intro t ht
    refine conj_mem_sup (fun p hp => Subgroup.mem_sup_left ?_)
      (fun s hs => Subgroup.mem_sup_right ?_)
    · exact (Subgroup.mem_normalizer_iff.mp ht.2 p).1 hp
    · exact ⟨T.mul_mem (T.mul_mem ht.1 hs.1) (T.inv_mem ht.1), hL.conj_mem s hs.2 t⟩
  have hinvT : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t⁻¹ ∈ T ⊓ Subgroup.normalizer (P : Set A) :=
    fun t ht => (T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht
  refine E9Config.false_of_inv hcfg
    (fun y => Nat.card ↥((P ⊔ (T ⊓ L)) ⊓ Subgroup.centralizer ({y} : Set A)) = 9)
    (fun t ht y _ hy => ?_) hx₀P' (fun h => ?_) ?_ (fun y hyP hy => ?_)
  · rw [card_inf_centralizer_conj' (H := P ⊔ (T ⊓ L)) (htH t ht)
      (fun x hx => by simpa using htH t⁻¹ (hinvT t ht) x hx) y]
    exact hy
  · have h1 : orderOf x₀ = 3 := by rw [← orderOf_injective φ hφ x₀]; exact hy₀'o
    have hx1 : x₀ = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at h1
    omega
  · show Nat.card ↥((P ⊔ (T ⊓ L)) ⊓ Subgroup.centralizer ({(x₀ : A)} : Set A)) = 9
    rw [hcA]
    exact hy₀'c
  · have hyL : y ∈ L := hcfg.le hyP
    have hc : m23Cnt K (φ ⟨y, hyL⟩) = 9 := by rw [← hcA]; exact hy
    have hmem : φ ⟨y, hyL⟩ ∈ PK := by
      rw [hPKdef]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩
    have hz := hy₀'max _ hmem hc
    rw [← MonoidHom.map_zpowers] at hz
    obtain ⟨z, hz, hzφ⟩ := hz
    have hz' : (z : A) = y := by rw [hφ hzφ]
    rw [← hz']
    have := Subgroup.mem_map_of_mem L.subtype hz
    rwa [MonoidHom.map_zpowers] at this

theorem orderThree_m23 :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥NativeSporadic.M23 := ⟨m23Word m23ThreeW, m23Word_mem _⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply eq_of_permCode23
    rw [Subgroup.coe_pow, permCode_pow23, Subgroup.coe_one, m23_code_one]
    show powC23 m23oneC 3 (permCode (m23Word m23ThreeW)) = m23oneC
    rw [permCode_m23Word]
    exact m23_three_check.1
  have hx1 : x ≠ 1 := by
    intro h
    apply m23_three_check.2
    have := congrArg (fun y : ↥NativeSporadic.M23 => permCode (y : Perm (Fin 23))) h
    simp only [x, Subgroup.coe_one, m23_code_one, permCode_m23Word] at this
    exact this
  rw [Nat.card_congr (e.trans carrierM23Equiv).toEquiv, ← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
