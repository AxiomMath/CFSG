module

public import CFSG.Quasithin.Vol2.F134M24Check
public import CFSG.Quasithin.Vol2.F134M24Cover
public import CFSG.Quasithin.Vol2.F134M24Basic
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Vol2.F134M23Basic

public section

namespace CFSG.Quasithin.F134

open Equiv CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem permCode_m24Word (w : List ℕ) : permCode (m24Word w) = m24WordC w := by
  induction w with
  | nil => exact m24_code_one
  | cons c w ih =>
    by_cases hc : c = 0
    · simp only [m24Word, m24WordC, hc, ite_true, permCode_mul24, ih, m24_code_a]
    · simp only [m24Word, m24WordC, hc, ite_false, permCode_mul24, ih, m24_code_b]

theorem m24Word_mem (w : List ℕ) : m24Word w ∈ NativeSporadic.M24 := by
  induction w with
  | nil => exact one_mem _
  | cons c w ih =>
    refine mul_mem ?_ ih
    rw [m24_eq_closure]
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m24TGen (k : ℕ) : Perm (Fin 24) := m24Word (m24TGenW.getD k [])

@[expose] def m24T : Subgroup (Perm (Fin 24)) := Subgroup.closure {x | ∃ k < 4, m24TGen k = x}

theorem permCode_m24TGen {k : ℕ} (hk : k < 4) : permCode (m24TGen k) = m24TG k := by
  rw [m24TGen, permCode_m24Word]
  exact m24_tgen_check k hk

theorem m24T_le : m24T ≤ NativeSporadic.M24 := by
  rw [m24T, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact m24Word_mem _

theorem m24T_sub {x : Perm (Fin 24)} (hx : x ∈ m24T) : ∃ i < 1024, permCode x = m24Tel i := by
  refine closure_subset_of_right_closed (S := {x | ∃ k < 4, m24TGen k = x})
    (P := {x | ∃ i < 1024, permCode x = m24Tel i})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, by rw [m24_code_one, m24_tel_zero]⟩ ?_ hx
  rintro p ⟨i, hi, hp⟩ s ⟨k, hk, rfl⟩
  obtain ⟨h1, h2⟩ := m24_nxt_check i hi k hk
  exact ⟨_, h1, by rw [permCode_mul24, hp, permCode_m24TGen hk, h2]⟩

theorem m24T_sup : ∀ i < 1024, ∃ x ∈ m24T, permCode x = m24Tel i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [m24_code_one, m24_tel_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := m24_par_check i hi hpos
      obtain ⟨y, hy, hyc⟩ := ih _ h1 (h1.trans hi)
      refine ⟨y * m24TGen (m24Par i % 8), mul_mem hy (Subgroup.subset_closure ⟨_, h2, rfl⟩), ?_⟩
      rw [permCode_mul24, hyc, permCode_m24TGen h2, h3]

theorem m24T_isPGroup : IsPGroup 2 m24T := by
  intro x
  obtain ⟨i, hi, hx⟩ := m24T_sub x.2
  refine ⟨3, Subtype.ext (eq_of_permCode24 ?_)⟩
  rw [Subgroup.coe_pow, permCode_pow_two_pow24, hx, Subgroup.coe_one, m24_code_one]
  exact m24_pow_check i hi

instance : Finite m24T := Subgroup.instFiniteSubtypeMem _

theorem m24T_not_three_dvd : ¬ 3 ∣ Nat.card m24T := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 m24T_isPGroup
  rw [hk]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

@[expose] noncomputable def m24TelE (i : ℕ) : Perm (Fin 24) :=
  if h : i < 1024 then Classical.choose (m24T_sup i h) else 1

theorem m24TelE_mem (i : ℕ) : m24TelE i ∈ m24T := by
  unfold m24TelE
  split_ifs with h
  · exact (Classical.choose_spec (m24T_sup i h)).1
  · exact one_mem _

theorem permCode_m24TelE {i : ℕ} (hi : i < 1024) : permCode (m24TelE i) = m24Tel i := by
  unfold m24TelE
  rw [dite_eq_left hi]
  exact (Classical.choose_spec (m24T_sup i hi)).2

theorem m24TelE_zero : m24TelE 0 = 1 :=
  eq_of_permCode24 (by rw [permCode_m24TelE (by norm_num), m24_tel_zero, m24_code_one])

@[expose] noncomputable def m24Z0E : Perm (Fin 24) := m24TelE m24Z0

theorem m24Z0E_comm {t : Perm (Fin 24)} (ht : t ∈ m24T) : t * m24Z0E = m24Z0E * t := by
  have hgen : ∀ k < 4, m24TGen k * m24Z0E = m24Z0E * m24TGen k := fun k hk =>
    eq_of_permCode24 (by
      rw [permCode_mul24, permCode_mul24, permCode_m24TGen hk, m24Z0E,
        permCode_m24TelE (by norm_num [m24Z0])]
      exact (m24_center_check.1 k hk).symm)
  have hC : m24T ≤ Subgroup.centralizer ({m24Z0E} : Set (Perm (Fin 24))) := by
    rw [m24T, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hgen k hk)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hC ht)

theorem m24_center {t : Perm (Fin 24)} (ht : t ∈ m24T) (hc : ∀ s ∈ m24T, t * s = s * t) :
    t = 1 ∨ t = m24Z0E := by
  obtain ⟨i, hi, htc⟩ := m24T_sub ht
  have h := m24_center_check.2 i hi fun k hk => by
    have := hc _ (Subgroup.subset_closure ⟨k, hk, rfl⟩)
    have hcode := congrArg permCode this
    rw [permCode_mul24, permCode_mul24, htc, permCode_m24TGen hk] at hcode
    exact hcode
  rcases h with rfl | rfl
  · exact Or.inl (eq_of_permCode24 (by rw [htc, m24_tel_zero, m24_code_one]))
  · exact Or.inr (eq_of_permCode24 (by
      rw [htc, m24Z0E, permCode_m24TelE (by norm_num [m24Z0])]))

@[expose] def m24GP (c : ℕ) : Perm (Fin 24) := m24Word (m24GW.getD c [])

theorem permCode_m24GP {c : ℕ} (hc : c < 3) : permCode (m24GP c) = m24G c := by
  rw [m24GP, permCode_m24Word]
  exact m24_g_check c hc

@[expose] noncomputable def m24LetE (l : ℕ) : Perm (Fin 24) :=
  if l < 1024 then m24TelE l else m24GP (l - 1024)

theorem permCode_m24LetE {l : ℕ} (hl : l < 1027) : permCode (m24LetE l) = m24Let l := by
  unfold m24LetE m24Let
  split_ifs with h
  · exact permCode_m24TelE h
  · exact permCode_m24GP (by omega)

theorem m24LetE_mem (l : ℕ) : m24LetE l ∈ NativeSporadic.M24 := by
  unfold m24LetE
  split_ifs
  · exact m24T_le (m24TelE_mem l)
  · exact m24Word_mem _

@[expose] noncomputable def m24LWord : List ℕ → Perm (Fin 24)
  | [] => 1
  | l :: w => m24LetE l * m24LWord w

theorem permCode_m24LWord : ∀ w : List ℕ, (∀ l ∈ w, l < 1027) →
    permCode (m24LWord w) = m24LWordC w
  | [], _ => m24_code_one
  | l :: w, hw => by
    rw [m24LWord, m24LWordC, permCode_mul24, permCode_m24LetE (hw l List.mem_cons_self),
      permCode_m24LWord w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]

theorem m24LWord_mem : ∀ w : List ℕ, m24LWord w ∈ NativeSporadic.M24
  | [] => one_mem _
  | l :: w => mul_mem (m24LetE_mem l) (m24LWord_mem w)

@[expose] noncomputable def m24DP (j : ℕ) : Perm (Fin 24) := m24LWord (m24DW.getD j [])

theorem permCode_m24DP {j : ℕ} (hj : j < 510) : permCode (m24DP j) = m24D j := by
  obtain ⟨h1, h2⟩ := m24_d_check j hj
  rw [m24DP, permCode_m24LWord _ h2]
  exact h1

theorem m24DP_zero : m24DP 0 = 1 := by
  rw [m24DP, m24_dw_zero]
  rfl

@[expose] def m24U : Set (Perm (Fin 24)) :=
  {x | ∃ j < 510, ∃ t ∈ m24T, ∃ t' ∈ m24T, x = t * m24DP j * t'}

theorem one_mem_m24U : (1 : Perm (Fin 24)) ∈ m24U :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [m24DP_zero]; group⟩

theorem m24U_mul_T {x s : Perm (Fin 24)} (hx : x ∈ m24U) (hs : s ∈ m24T) : x * s ∈ m24U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem m24U_mul_g {c : ℕ} (hc : c < 3) {x : Perm (Fin 24)} (hx : x ∈ m24U) :
    x * m24GP c ∈ m24U := by
  have hE : ∀ p < 512, ∃ v ∈ m24T, m24TelE (m24GEAt c p) * m24GP c = m24GP c * v := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      obtain ⟨hE0, htree⟩ := m24_gtree_check c hc
      rcases Nat.eq_zero_or_pos p with rfl | hpos
      · exact ⟨1, one_mem _, by rw [hE0, m24TelE_zero, one_mul, mul_one]⟩
      · obtain ⟨hEp, hrest⟩ := htree p hp
        obtain ⟨hq, hl, hprod⟩ := hrest hpos
        obtain ⟨v, hv, hve⟩ := ih _ hq (hq.trans hp)
        obtain ⟨hEq, -⟩ := htree _ (hq.trans hp)
        obtain ⟨hu, hcl, hconj'⟩ := m24_gconj_check c hc _ hl
        have hug : m24TelE ((m24GUL.getD c []).getD (m24GPAt c p % 8) 0) * m24GP c =
            m24GP c * m24TelE ((m24GCL.getD c []).getD (m24GPAt c p % 8) 0) :=
          eq_of_permCode24 (by
            rw [permCode_mul24, permCode_mul24, permCode_m24TelE hu, permCode_m24GP hc,
              permCode_m24TelE hcl]
            exact hconj')
        have hsplit : m24TelE (m24GEAt c p) = m24TelE (m24GEAt c (m24GPAt c p / 8)) *
            m24TelE ((m24GUL.getD c []).getD (m24GPAt c p % 8) 0) := eq_of_permCode24 (by
          rw [permCode_mul24, permCode_m24TelE hEp, permCode_m24TelE hEq, permCode_m24TelE hu]
          exact hprod.symm)
        exact ⟨v * m24TelE ((m24GCL.getD c []).getD (m24GPAt c p % 8) 0),
          mul_mem hv (m24TelE_mem _), by rw [hsplit]; exact mul_conj_step hug hve⟩
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨i, hi, hci⟩ := m24T_sub ht'
  obtain ⟨hs, hp, hr, htr⟩ := m24_gtrans_check c hc i hi
  obtain ⟨hEp, -⟩ := (m24_gtree_check c hc).2 _ hp
  have ht'eq : t' = m24TelE ((m24GRL.getD c []).getD (m24GQAt c i / 512) 0) *
      m24TelE (m24GEAt c (m24GQAt c i % 512)) :=
    eq_of_permCode24 (by
      rw [hci, permCode_mul24, permCode_m24TelE hr, permCode_m24TelE hEp]
      exact htr)
  obtain ⟨v, hv, hve⟩ := hE _ hp
  obtain ⟨hk, hdeq⟩ := m24_gdec_spec hc hj hs
  generalize m24GDecAt c (2 * j + m24GQAt c i / 512) = e at hk hdeq
  have hd : m24DP j * m24TelE ((m24GRL.getD c []).getD (m24GQAt c i / 512) 0) * m24GP c =
      m24TelE (e / 1024 % 1024) * m24DP (e / 1048576) * m24TelE (e % 1024) :=
    eq_of_permCode24 (by
      rw [permCode_mul24, permCode_mul24, permCode_mul24, permCode_mul24, permCode_m24DP hj,
        permCode_m24TelE hr, permCode_m24GP hc, permCode_m24TelE (Nat.mod_lt _ (by norm_num)),
        permCode_m24DP hk, permCode_m24TelE (Nat.mod_lt _ (by norm_num))]
      exact hdeq)
  refine ⟨e / 1048576, hk, t * m24TelE (e / 1024 % 1024), mul_mem ht (m24TelE_mem _),
    m24TelE (e % 1024) * v, mul_mem (m24TelE_mem _) hv, ?_⟩
  rw [ht'eq]
  exact mul_rearrange hve hd

theorem m24U_mul_LetE {x : Perm (Fin 24)} (hx : x ∈ m24U) {l : ℕ} (hl : l < 1027) :
    x * m24LetE l ∈ m24U := by
  unfold m24LetE
  split_ifs with h
  · exact m24U_mul_T hx (m24TelE_mem l)
  · exact m24U_mul_g (by omega) hx

theorem m24U_mul_LWord : ∀ (w : List ℕ), (∀ l ∈ w, l < 1027) → ∀ {x : Perm (Fin 24)},
    x ∈ m24U → x * m24LWord w ∈ m24U
  | [], _, x, hx => by rw [m24LWord, mul_one]; exact hx
  | l :: w, hw, x, hx => by
    rw [m24LWord, ← mul_assoc]
    exact m24U_mul_LWord w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (m24U_mul_LetE hx (hw l List.mem_cons_self))

theorem m24U_mul_ab {x : Perm (Fin 24)} (hx : x ∈ m24U) :
    x * m24PermA ∈ m24U ∧ x * m24PermB ∈ m24U := by
  obtain ⟨h1, h2, h3, h4⟩ := m24_ab_check
  have ha : m24PermA = m24LWord m24AW :=
    eq_of_permCode24 (by rw [m24_code_a, permCode_m24LWord _ h2, h1])
  have hb : m24PermB = m24LWord m24BW :=
    eq_of_permCode24 (by rw [m24_code_b, permCode_m24LWord _ h4, h3])
  rw [ha, hb]
  exact ⟨m24U_mul_LWord _ h2 hx, m24U_mul_LWord _ h4 hx⟩

theorem m24_subset_U : (NativeSporadic.M24 : Set (Perm (Fin 24))) ⊆ m24U := by
  rw [m24_eq_closure]
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_m24U ?_
  rintro p hp s (rfl | rfl)
  · exact (m24U_mul_ab hp).1
  · exact (m24U_mul_ab hp).2

theorem m24_false_of_pow {H : Subgroup (Perm (Fin 24))} (h5 : ¬ 5 ∣ Nat.card H)
    (h7 : ¬ 7 ∣ Nat.card H) {y : Perm (Fin 24)} (hy : y ∈ H) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (hpow : powC24 m24oneC p (permCode y) = m24oneC) (hne : permCode y ≠ m24oneC) : False := by
  have hprime : p.Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨y, hy⟩
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_permCode24
    rw [Subgroup.coe_pow, permCode_pow24, Subgroup.coe_one, m24_code_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    have := congrArg (fun z : H => permCode (z : Perm (Fin 24))) h
    simpa [x, m24_code_one] using this
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  rcases hp with h | h
  · rw [h] at hdvd
    exact h5 hdvd
  · rw [h] at hdvd
    exact h7 hdvd

theorem m24_not_mem_of_bad {H : Subgroup (Perm (Fin 24))} (hTH : m24T ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {j : ℕ} (hj : j < 510) (hj8 : 8 ≤ j)
    (hD : m24DP j ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := m24_bad_check j hj hj8
  refine m24_false_of_pow h5 h7 (y := (m24DP j * m24TelE (m24Bad j / 256)) ^ (m24Bad j / 16 % 16))
    (pow_mem (mul_mem hD (hTH (m24TelE_mem _))) _) hp' ?_ ?_
  · rw [permCode_pow24, permCode_mul24, permCode_m24DP hj, permCode_m24TelE hi, m24_code_one]
    exact hpow
  · rw [permCode_pow24, permCode_mul24, permCode_m24DP hj, permCode_m24TelE hi, m24_code_one]
    exact hne

theorem m24_not_mem_of_excl {H : Subgroup (Perm (Fin 24))} (hTH : m24T ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {e : ℕ} (he : e < 10)
    (hDj : m24DP (m24EP e / 8) ∈ H) (hDk : m24DP (m24EP e % 8) ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := m24_excl_check e he
  have hj : m24EP e / 8 < 510 := by
    rw [m24EP, m24_ep_check]
    interval_cases e <;> norm_num
  have hk : m24EP e % 8 < 510 := by omega
  refine m24_false_of_pow h5 h7 (y := (m24DP (m24EP e / 8) * m24TelE (m24Excl e / 256) *
    m24DP (m24EP e % 8)) ^ (m24Excl e / 16 % 16))
    (pow_mem (mul_mem (mul_mem hDj (hTH (m24TelE_mem _))) hDk) _) hp' ?_ ?_
  · rw [permCode_pow24, permCode_mul24, permCode_mul24, permCode_m24DP hj, permCode_m24TelE hi,
      permCode_m24DP hk, m24_code_one]
    exact hpow
  · rw [permCode_pow24, permCode_mul24, permCode_mul24, permCode_m24DP hj, permCode_m24TelE hi,
      permCode_m24DP hk, m24_code_one]
    exact hne

theorem m24_cos {j : ℕ} (hj0 : 0 < j) (hj : j < 8) {t t' : Perm (Fin 24)} (ht : t ∈ m24T) :
    ∃ b < m24CN j, m24CR j b < 1024 ∧ ∃ w ∈ m24T,
      t * m24DP j * t' = m24TelE (m24CR j b) * m24DP j * (w * t') := by
  obtain ⟨i, hi, htc⟩ := m24T_sub ht
  obtain ⟨hs, hr, hcos⟩ := (m24_cos_check j hj hj0).2 i hi
  refine ⟨m24Cos j i / 1024, hs, hr, m24TelE (m24Cos j i % 1024), m24TelE_mem _, ?_⟩
  have key : t * m24DP j = m24TelE (m24CR j (m24Cos j i / 1024)) * m24DP j *
      m24TelE (m24Cos j i % 1024) := by
    apply eq_of_permCode24
    rw [permCode_mul24, permCode_mul24, permCode_mul24, htc, permCode_m24TelE hr,
      permCode_m24TelE (Nat.mod_lt _ (by norm_num)), permCode_m24DP (by omega)]
    exact hcos
  rw [key]
  group

theorem m24_mem_U_good {H : Subgroup (Perm (Fin 24))} (hTH : m24T ≤ H)
    (hH : H ≤ NativeSporadic.M24) (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) :
    ∀ h ∈ H, ∃ j < 8, m24DP j ∈ H ∧ ∃ t ∈ m24T, ∃ t' ∈ m24T, h = t * m24DP j * t' := by
  intro h hh
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := m24_subset_U (hH hh)
  have hD : m24DP j ∈ H := by
    have e : m24DP j = t⁻¹ * (t * m24DP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  rcases Nat.lt_or_ge j 8 with hj8 | hj8
  · exact ⟨j, hj8, hD, t, ht, t', ht', rfl⟩
  · exact (m24_not_mem_of_bad hTH h5 h7 hj hj8 hD).elim

@[expose] noncomputable def m24CP (X s : ℕ) : Perm (Fin 24) :=
  m24TelE (m24HC X s % 1024) * m24DP (m24HC X s / 1024)

theorem permCode_m24CP {X s : ℕ} (hX : X < 4) (hs : s < 9) : permCode (m24CP X s) = m24CC X s := by
  obtain ⟨-, hj, -⟩ := m24_hcs_check X hX
  rw [m24CP, permCode_mul24, permCode_m24TelE (Nat.mod_lt _ (by norm_num)),
    permCode_m24DP (by have := hj s hs; omega)]
  rfl

@[expose] def m24HSet (X : ℕ) : Set (Perm (Fin 24)) :=
  {x | ∃ s < 9, ∃ t ∈ m24T, x = m24CP X s * t}

theorem ncard_m24HSet_le (X : ℕ) : (m24HSet X).ncard ≤ 9 * Nat.card m24T := by
  have h : m24HSet X = Set.range fun q : Fin 9 × m24T => m24CP X q.1 * q.2 := by
    ext x
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.1.2, q.2, q.2.2, rfl⟩
  rw [h, ← Set.image_univ]
  calc _ ≤ (Set.univ : Set (Fin 9 × m24T)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 9 * Nat.card m24T := by rw [Set.ncard_univ, Nat.card_prod, Nat.card_fin]

theorem m24DP_mem_HSet {X j : ℕ} (hX : X < 4) (hj : j < 8)
    (hJ : (m24HJ.getD X []).contains j = true) : m24DP j ∈ m24HSet X := by
  obtain ⟨h0, -, hcov⟩ := m24_hcs_check X hX
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨0, by norm_num, 1, one_mem _, by simp [m24CP, h0, m24TelE_zero, m24DP_zero]⟩
  have hc := (m24_cos_check j hj hj0).1
  have hn : 0 < m24CN j := by
    have := ((m24_cos_check j hj hj0).2 0 (by norm_num)).1
    omega
  obtain ⟨s, hs, hse⟩ := hcov j hj hj0 hJ 0 hn
  refine ⟨s, hs, 1, one_mem _, ?_⟩
  rw [mul_one, m24CP, hse, hc]
  have h1 : (1024 * j + 0) % 1024 = 0 := by omega
  have h2 : (1024 * j + 0) / 1024 = j := by omega
  rw [h1, h2, m24TelE_zero, one_mul]

theorem m24_subset_HSet {H : Subgroup (Perm (Fin 24))} (hTH : m24T ≤ H)
    (hH : H ≤ NativeSporadic.M24) (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {X : ℕ}
    (hX : X < 4) (hgood : ∀ j < 8, m24DP j ∈ H → (m24HJ.getD X []).contains j = true) :
    (H : Set (Perm (Fin 24))) ⊆ m24HSet X := by
  intro h hh
  obtain ⟨h0, -, hcov⟩ := m24_hcs_check X hX
  obtain ⟨j, hj, hD, t, ht, t', ht', rfl⟩ := m24_mem_U_good hTH hH h5 h7 h hh
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨0, by norm_num, t * t', mul_mem ht ht', by simp [m24CP, h0, m24TelE_zero, m24DP_zero]⟩
  obtain ⟨b, hb, hbr, w, hw, e⟩ := m24_cos hj0 hj ht (t' := t')
  obtain ⟨s, hs, hse⟩ := hcov j hj hj0 (hgood j hj hD) b hb
  refine ⟨s, hs, w * t', mul_mem hw ht', ?_⟩
  rw [e, m24CP, hse]
  have h1 : (1024 * j + m24CR j b) % 1024 = m24CR j b := by omega
  have h2 : (1024 * j + m24CR j b) / 1024 = j := by omega
  rw [h1, h2, mul_assoc]

theorem m24_eq_HSet_of_subset {H : Subgroup (Perm (Fin 24))} {X : ℕ}
    (hsub : (H : Set (Perm (Fin 24))) ⊆ m24HSet X) (hcard : 9 * Nat.card m24T ≤ Nat.card H) :
    (H : Set (Perm (Fin 24))) = m24HSet X := by
  refine Set.eq_of_subset_of_ncard_le hsub ?_ ?_
  · rw [← Nat.card_coe_set_eq]
    exact (ncard_m24HSet_le X).trans hcard
  · have : Finite (m24HSet X) := by
      have h : m24HSet X = Set.range fun q : Fin 9 × m24T => m24CP X q.1 * q.2 := by
        ext x
        constructor
        · rintro ⟨s, hs, t, ht, rfl⟩
          exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
        · rintro ⟨q, rfl⟩
          exact ⟨q.1, q.1.2, q.2, q.2.2, rfl⟩
      rw [h]
      exact Set.finite_range _
    exact Set.toFinite _

theorem m24_classify {H : Subgroup (Perm (Fin 24))} (hTH : m24T ≤ H) (hH : H ≤ NativeSporadic.M24)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) (hcard : 9 * Nat.card m24T ≤ Nat.card H) :
    ∃ X < 3, (H : Set (Perm (Fin 24))) = m24HSet X := by
  have ex : ∀ e < 10, m24DP (m24EP e / 8) ∈ H → m24DP (m24EP e % 8) ∉ H :=
    fun e he hj hk => m24_not_mem_of_excl hTH h5 h7 he hj hk
  have hEP : ∀ e < 10, m24EP e = m24ExclP.getD e 0 := fun _ _ => rfl
  rw [m24_ep_check] at hEP
  have ex' : ∀ e < 10, ∀ j k, m24ExclP.getD e 0 = 8 * j + k → k < 8 → m24DP j ∈ H →
      m24DP k ∉ H := by
    intro e he j k hjk hk hj
    have h1 : m24EP e / 8 = j := by rw [m24EP, hjk]; omega
    have h2 : m24EP e % 8 = k := by rw [m24EP, hjk]; omega
    exact h2 ▸ ex e he (h1 ▸ hj)
  rw [m24_ep_check] at ex'
  have e51 := ex' 0 (by norm_num) 5 1 rfl (by norm_num)
  have e54 := ex' 1 (by norm_num) 5 4 rfl (by norm_num)
  have e56 := ex' 2 (by norm_num) 5 6 rfl (by norm_num)
  have e57 := ex' 3 (by norm_num) 5 7 rfl (by norm_num)
  have e62 := ex' 4 (by norm_num) 6 2 rfl (by norm_num)
  have e63 := ex' 5 (by norm_num) 6 3 rfl (by norm_num)
  have e67 := ex' 6 (by norm_num) 6 7 rfl (by norm_num)
  have e72 := ex' 7 (by norm_num) 7 2 rfl (by norm_num)
  have e74 := ex' 8 (by norm_num) 7 4 rfl (by norm_num)
  have e12 := ex' 9 (by norm_num) 1 2 rfl (by norm_num)
  have hgo : ∀ X < 4, (∀ j < 8, m24DP j ∈ H → (m24HJ.getD X []).contains j = true) →
      (H : Set (Perm (Fin 24))) = m24HSet X := fun X hX hg =>
    m24_eq_HSet_of_subset (m24_subset_HSet hTH hH h5 h7 hX hg) hcard
  by_cases h5' : m24DP 5 ∈ H
  · refine ⟨0, by norm_num, hgo 0 (by norm_num) fun j hj hD => ?_⟩
    interval_cases j
    · rfl
    · exact absurd hD (e51 h5')
    · rfl
    · rfl
    · exact absurd hD (e54 h5')
    · rfl
    · exact absurd h5' (fun h => e56 h hD)
    · exact absurd h5' (fun h => e57 h hD)
  by_cases h6' : m24DP 6 ∈ H
  · refine ⟨1, by norm_num, hgo 1 (by norm_num) fun j hj hD => ?_⟩
    interval_cases j
    · rfl
    · rfl
    · exact absurd hD (e62 h6')
    · exact absurd hD (e63 h6')
    · rfl
    · exact absurd hD h5'
    · rfl
    · exact absurd hD (e67 h6')
  by_cases h7' : m24DP 7 ∈ H
  · refine ⟨2, by norm_num, hgo 2 (by norm_num) fun j hj hD => ?_⟩
    interval_cases j
    · rfl
    · rfl
    · exact absurd hD (e72 h7')
    · rfl
    · exact absurd hD (e74 h7')
    · exact absurd hD h5'
    · exact absurd hD h6'
    · rfl
  · exfalso
    have hS := hgo 3 (by norm_num) fun j hj hD => by
      interval_cases j
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd hD h5'
      · exact absurd hD h6'
      · exact absurd hD h7'
    have h1 : m24DP 1 ∈ H := by
      rw [← SetLike.mem_coe, hS]
      exact m24DP_mem_HSet (by norm_num) (by norm_num) rfl
    have h2 : m24DP 2 ∈ H := by
      rw [← SetLike.mem_coe, hS]
      exact m24DP_mem_HSet (by norm_num) (by norm_num) rfl
    exact e12 h1 h2

@[expose] noncomputable def m24XE (X t : ℕ) : Perm (Fin 24) :=
  m24CP X ((m24HX.getD X []).getD t 0 / 1024) * m24TelE ((m24HX.getD X []).getD t 0 % 1024)

theorem permCode_m24XE {X t : ℕ} (hX : X < 3) (ht : t < 2) : permCode (m24XE X t) = m24XC X t := by
  obtain ⟨h1, h2, -⟩ := m24_x_check X hX
  have hs : (m24HX.getD X []).getD t 0 / 1024 < 9 := by interval_cases t <;> assumption
  rw [m24XE, permCode_mul24, permCode_m24CP (by omega) hs,
    permCode_m24TelE (Nat.mod_lt _ (by norm_num))]
  rfl

theorem m24_P0 {X : ℕ} (hX : X < 3) :
    m24XE X 0 ∈ m24HSet X ∧ m24XE X 1 ∈ m24HSet X ∧ orderOf (m24XE X 0) = 3 ∧
      orderOf (m24XE X 1) = 3 ∧ m24XE X 0 * m24XE X 1 = m24XE X 1 * m24XE X 0 ∧
      ∀ a < 3, ∀ b < 3, 0 < b → m24XE X 1 ^ b ≠ m24XE X 0 ^ a := by
  obtain ⟨hs1, hs2, h13, h1ne, h23, hcomm, hdis⟩ := m24_x_check X hX
  have hcodePow : ∀ (u : Perm (Fin 24)) (n : ℕ),
      permCode (u ^ n) = powC24 m24oneC n (permCode u) := fun u n => by
    rw [permCode_pow24, m24_code_one]
  have hc1 := permCode_m24XE hX (t := 0) (by norm_num)
  have hc2 := permCode_m24XE hX (t := 1) (by norm_num)
  have hd : ∀ a < 3, ∀ b < 3, 0 < b → m24XE X 1 ^ b ≠ m24XE X 0 ^ a := by
    intro a ha b hb hb0 h
    exact hdis a ha b hb hb0 (by rw [← hc1, ← hc2, ← hcodePow, ← hcodePow, h])
  have hpow1 : m24XE X 0 ^ 3 = 1 :=
    eq_of_permCode24 (by rw [hcodePow, hc1, m24_code_one]; exact h13)
  have hne1 : m24XE X 0 ≠ 1 := fun h => h1ne (by rw [← hc1, h, m24_code_one])
  have hpow2 : m24XE X 1 ^ 3 = 1 :=
    eq_of_permCode24 (by rw [hcodePow, hc2, m24_code_one]; exact h23)
  have hne2 : m24XE X 1 ≠ 1 := by
    intro h
    apply hd 0 (by norm_num) 1 (by norm_num) (by norm_num)
    rw [h, pow_zero, one_pow]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨_, hs1, _, m24TelE_mem _, rfl⟩, ⟨_, hs2, _, m24TelE_mem _, rfl⟩,
    orderOf_eq_prime hpow1 hne1, orderOf_eq_prime hpow2 hne2, ?_, hd⟩
  exact eq_of_permCode24 (by rw [permCode_mul24, permCode_mul24, hc1, hc2]; exact hcomm)

theorem m24_key_z {X : ℕ} (hX : X < 2) {K : Subgroup (Perm (Fin 24))}
    (hK : (K : Set (Perm (Fin 24))) = m24HSet X) (hTK : m24T ≤ K)
    (hcard : Nat.card K = 9 * Nat.card m24T) {Q : Subgroup (Perm (Fin 24))} (hQK : Q ≤ K)
    (hQ : Nat.card Q = 9) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ y₀ * m24Z0E = m24Z0E * y₀ ∧
      ∀ y ∈ Q, y * m24Z0E = m24Z0E * y → y ∈ Subgroup.zpowers y₀ := by
  obtain ⟨hx1K, hx2K, ho1, ho2, hc12, hd⟩ := m24_P0 (X := X) (by omega)
  rw [← hK] at hx1K hx2K
  obtain ⟨hP0, hP0el⟩ := card_sup_zpowers_of_comm ho1 ho2 hc12 hd
  have hP0K : Subgroup.zpowers (m24XE X 0) ⊔ Subgroup.zpowers (m24XE X 1) ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hx1K) (Subgroup.zpowers_le.mpr hx2K)
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact mul_ne_zero (by norm_num) Nat.card_pos.ne')
  obtain ⟨hz1, hz2⟩ := m24_z_check X hX
  have hz1' : m24XE X 0 * m24Z0E = m24Z0E * m24XE X 0 := eq_of_permCode24 (by
    rw [permCode_mul24, permCode_mul24, permCode_m24XE (by omega) (by norm_num), m24Z0E,
      permCode_m24TelE (by norm_num [m24Z0])]
    exact hz1)
  have hz2' : m24XE X 1 * m24Z0E ≠ m24Z0E * m24XE X 1 := fun h => hz2 (by
    have := congrArg permCode h
    rw [permCode_mul24, permCode_mul24, permCode_m24XE (by omega) (by norm_num), m24Z0E,
      permCode_m24TelE (by norm_num [m24Z0])] at this
    exact this)
  refine exists_inv_of_sylow_mul (fun z => z * m24Z0E = m24Z0E * z) (fun t ht z hz => ?_) hTK
    hP0K hQK hP0 hQ hcard m24T_not_three_dvd (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    ho1 hz1' (fun z hz hcz => ?_)
  · have h1 : t * m24Z0E = m24Z0E * t := m24Z0E_comm ht
    have h2 : t⁻¹ * m24Z0E = m24Z0E * t⁻¹ := m24Z0E_comm (inv_mem ht)
    calc t * z * t⁻¹ * m24Z0E = t * z * (t⁻¹ * m24Z0E) := by group
      _ = t * (z * m24Z0E) * t⁻¹ := by rw [h2]; group
      _ = t * (m24Z0E * z) * t⁻¹ := by rw [hz]
      _ = (t * m24Z0E) * z * t⁻¹ := by group
      _ = m24Z0E * (t * z * t⁻¹) := by rw [h1]; group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hP0el z hz
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · exfalso
      have hca : Commute (m24XE X 0 ^ a) m24Z0E := (Commute.pow_left hz1' a)
      have hcz' : Commute (m24XE X 0 ^ a * m24XE X 1 ^ b) m24Z0E := hcz
      have hcb : Commute (m24XE X 1 ^ b) m24Z0E := by
        have := (hca.inv_left).mul_left hcz'
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      have hpow3 : m24XE X 1 ^ 3 = 1 := by rw [← ho2]; exact pow_orderOf_eq_one _
      have hx2 : m24XE X 1 = (m24XE X 1 ^ b) ^ b := by
        rw [← pow_mul]
        interval_cases b
        · rw [one_mul, pow_one]
        · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hpow3, one_mul, pow_one]
      exact hz2' (by rw [hx2]; exact (hcb.pow_left b).eq)

@[expose] def m24Psi (z : Perm (Fin 24)) : Prop :=
  ∃ x ∈ NativeSporadic.M24, x ^ 7 = 1 ∧ x ≠ 1 ∧ x * z = z * x

theorem m24Psi_conj {k z : Perm (Fin 24)} (hk : k ∈ NativeSporadic.M24) (h : m24Psi z) :
    m24Psi (k * z * k⁻¹) := by
  obtain ⟨x, hx, hx7, hx1, hxz⟩ := h
  refine ⟨k * x * k⁻¹, mul_mem (mul_mem hk hx) (inv_mem hk), ?_, ?_, ?_⟩
  · rw [← MulAut.conj_apply, ← map_pow, hx7, map_one]
  · intro h
    apply hx1
    have : x = k⁻¹ * (k * x * k⁻¹) * k := by group
    rw [this, h]
    group
  · calc k * x * k⁻¹ * (k * z * k⁻¹) = k * (x * z) * k⁻¹ := by group
      _ = k * (z * x) * k⁻¹ := by rw [hxz]
      _ = k * z * k⁻¹ * (k * x * k⁻¹) := by group

theorem m24_key_psi {K : Subgroup (Perm (Fin 24))} (hK : (K : Set (Perm (Fin 24))) = m24HSet 2)
    (hKM : K ≤ NativeSporadic.M24) (hcard : Nat.card K = 9 * Nat.card m24T)
    {Q : Subgroup (Perm (Fin 24))} (hQK : Q ≤ K) (hQ : Nat.card Q = 9) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ ¬ m24Psi y₀ ∧
      ∀ y ∈ Q, ¬ m24Psi y → y ∈ Subgroup.zpowers y₀ := by
  obtain ⟨hx1K, hx2K, ho1, ho2, hc12, hd⟩ := m24_P0 (X := 2) (by norm_num)
  rw [← hK] at hx1K hx2K
  obtain ⟨hP0, hP0el⟩ := card_sup_zpowers_of_comm ho1 ho2 hc12 hd
  have hP0K : Subgroup.zpowers (m24XE 2 0) ⊔ Subgroup.zpowers (m24XE 2 1) ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hx1K) (Subgroup.zpowers_le.mpr hx2K)
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact mul_ne_zero (by norm_num) Nat.card_pos.ne')
  have hc1 := permCode_m24XE (X := 2) (t := 0) (by norm_num) (by norm_num)
  have hc2 := permCode_m24XE (X := 2) (t := 1) (by norm_num) (by norm_num)
  have hx1 : ¬ m24Psi (m24XE 2 0) := by
    rintro ⟨x, -, hx7, hx1, hxz⟩
    refine hx1 (eq_one_of_commute_of_pow_seven hxz hx7 (by rw [← ho1]; exact pow_orderOf_eq_one _)
      ?_ ?_)
    · rw [card_fixedPoints_eq_permCode, hc1, m24_fix_check]
      norm_num
    · rw [card_fixedPoints_eq_permCode, hc1, m24_fix_check]
      simp
  have hcodePow : ∀ (u : Perm (Fin 24)) (n : ℕ),
      permCode (u ^ n) = powC24 m24oneC n (permCode u) := fun u n => by
    rw [permCode_pow24, m24_code_one]
  have hY : ∀ e < 3, ∃ y : Perm (Fin 24), permCode y = m24YC e ∧ m24Psi y := by
    intro e he
    obtain ⟨hl, h7, hne, hcm⟩ := m24_psi_check e he
    let y : Perm (Fin 24) := if e = 0 then m24XE 2 1 else if e = 1 then m24XE 2 0 * m24XE 2 1
      else m24XE 2 0 * (m24XE 2 1 * m24XE 2 1)
    have hyc : permCode y = m24YC e := by
      simp only [y, m24YC]
      split_ifs
      · exact hc2
      · rw [permCode_mul24, hc1, hc2]
      · rw [permCode_mul24, permCode_mul24, hc1, hc2]
    refine ⟨y, hyc, m24LWord (m24PsiW.getD e []), m24LWord_mem _, ?_, ?_, ?_⟩
    · exact eq_of_permCode24 (by rw [hcodePow, permCode_m24LWord _ hl, m24_code_one]; exact h7)
    · intro h
      apply hne
      rw [← permCode_m24LWord _ hl, h, m24_code_one]
    · exact eq_of_permCode24 (by
        rw [permCode_mul24, permCode_mul24, permCode_m24LWord _ hl, hyc]
        exact hcm)
  have hpsi_pow : ∀ (y : Perm (Fin 24)) (m : ℕ), m24Psi y → m24Psi (y ^ m) := by
    rintro y m ⟨x, hx, hx7, hx1, hxy⟩
    exact ⟨x, hx, hx7, hx1, (Commute.pow_right hxy m).eq⟩
  refine exists_inv_of_sylow (m := Nat.card m24T) (fun z => ¬ m24Psi z) (fun k hk z hz h => ?_)
    hP0K hQK hP0 hQ hcard m24T_not_three_dvd (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    ho1 hx1 (fun z hz hcz => ?_)
  · apply hz
    have := m24Psi_conj (inv_mem (hKM hk)) h
    rwa [inv_inv, show k⁻¹ * (k * z * k⁻¹) * k = z by group] at this
  · obtain ⟨a, ha, b, hb, rfl⟩ := hP0el z hz
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · exfalso
      apply hcz
      obtain ⟨e, he, m, -, hem⟩ := m24_psi_rel_check a ha b hb hb0
      obtain ⟨y, hyc, hy⟩ := hY e he
      have : m24XE 2 0 ^ a * m24XE 2 1 ^ b = y ^ m := eq_of_permCode24 (by
        rw [permCode_mul24, hcodePow, hcodePow, hc1, hc2, hcodePow, hyc]
        exact hem)
      rw [this]
      exact hpsi_pow y m hy

@[expose] def carrierM24Equiv : NativeSporadic.Carrier .M24 ≃* ↥NativeSporadic.M24 :=
  MulEquiv.refl _

theorem noE9Config_m24 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ₀, hφ₀def⟩ : ∃ φ₀ : ↥L →* Perm (Fin 24),
      φ₀ = (Subgroup.subtype _).comp ((e.trans carrierM24Equiv) : ↥L →* ↥NativeSporadic.M24) :=
    ⟨_, rfl⟩
  have hφ₀ : Function.Injective φ₀ := by
    rw [hφ₀def]
    exact (Subgroup.subtype_injective _).comp (e.trans carrierM24Equiv).injective
  have hφ₀G : ∀ x, φ₀ x ∈ NativeSporadic.M24 := fun x => by rw [hφ₀def]; exact (Subtype.prop _)
  have hφ₀s : ∀ y ∈ NativeSporadic.M24, ∃ x, φ₀ x = y := by
    intro y hy
    obtain ⟨x, hx⟩ := (e.trans carrierM24Equiv).surjective ⟨y, hy⟩
    exact ⟨x, by rw [hφ₀def]; exact congrArg Subtype.val hx⟩
  obtain ⟨φ, hφ, hφG, hφs, hTφ⟩ :=
    E9Config.exists_model_conj hcfg hφ₀ hφ₀G hφ₀s m24T_le m24T_isPGroup
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (Perm (Fin 24)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  obtain ⟨TK, hTKdef⟩ : ∃ R : Subgroup (Perm (Fin 24)), R = ((T ⊓ L).subgroupOf L).map φ :=
    ⟨_, rfl⟩
  rw [← hTKdef] at hTφ
  have hTKK : TK ≤ K := by
    rw [hTKdef, hKdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  have hTK : m24T ≤ K := hTφ.trans hTKK
  have hKM : K ≤ NativeSporadic.M24 := by
    rw [hKdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφG _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hTKc : Nat.card TK = Nat.card (T ⊓ L : Subgroup A) := by
    rw [hTKdef, ← Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inl rfl)
  have h7 : ¬ 7 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inr (Or.inl rfl))
  have : Finite TK := Subgroup.instFiniteSubtypeMem _
  have hTle : Nat.card m24T ≤ Nat.card TK := Subgroup.card_le_of_le hTφ
  have hcardK : 9 * Nat.card m24T ≤ Nat.card K := by
    rw [hKc, hHc, ← hTKc]
    omega
  obtain ⟨X, hX, hKset⟩ := m24_classify hTK hKM h5 h7 hcardK
  have hK9 : Nat.card K = 9 * Nat.card m24T := by
    have h1 : Nat.card K ≤ 9 * Nat.card m24T := by
      rw [show Nat.card K = (K : Set (Perm (Fin 24))).ncard from Nat.card_coe_set_eq _, hKset]
      exact ncard_m24HSet_le X
    omega
  have hTKeq : TK = m24T := by
    refine (Subgroup.eq_of_le_of_card_ge hTφ ?_).symm
    rw [hKc, hHc, ← hTKc] at hK9
    omega
  obtain ⟨PK, hPKdef⟩ : ∃ R : Subgroup (Perm (Fin 24)), R = (P.subgroupOf L).map φ := ⟨_, rfl⟩
  have hPKK : PK ≤ K := by
    rw [hPKdef, hKdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left)
  have hPKc : Nat.card PK = 9 := by
    rw [hPKdef, ← Nat.card_congr ((P.subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hL := hcfg.normal
  have hfinish : ∀ (f : Perm (Fin 24) → Prop) (Inv : A → Prop),
      (∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ P, Inv y → Inv (t * y * t⁻¹)) →
      (∀ y : ↥L, Inv y ↔ f (φ y)) →
      (∃ y₀ ∈ PK, orderOf y₀ = 3 ∧ f y₀ ∧ ∀ y ∈ PK, f y → y ∈ Subgroup.zpowers y₀) → False := by
    intro f Inv hinv hIf ⟨y₀', hy₀'P, hy₀'o, hy₀'f, hy₀'max⟩
    rw [hPKdef] at hy₀'P
    obtain ⟨x₀, hx₀P, rfl⟩ := hy₀'P
    have hx₀P' : (x₀ : A) ∈ P := Subgroup.mem_subgroupOf.mp hx₀P
    refine E9Config.false_of_inv hcfg Inv hinv hx₀P' (fun h => ?_) ((hIf x₀).mpr hy₀'f)
      (fun y hyP hy => ?_)
    · have h1 : orderOf x₀ = 3 := by rw [← orderOf_injective φ hφ x₀]; exact hy₀'o
      have hx1 : x₀ = 1 := Subtype.ext h
      rw [hx1, orderOf_one] at h1
      omega
    · have hyL : y ∈ L := hcfg.le hyP
      have hmem : φ ⟨y, hyL⟩ ∈ PK := by
        rw [hPKdef]
        exact ⟨_, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩
      have hz := hy₀'max _ hmem ((hIf ⟨y, hyL⟩).mp hy)
      rw [← MonoidHom.map_zpowers] at hz
      obtain ⟨z, hz, hzφ⟩ := hz
      have hz' : (z : A) = y := by rw [hφ hzφ]
      rw [← hz']
      have := Subgroup.mem_map_of_mem L.subtype hz
      rwa [MonoidHom.map_zpowers] at this
  rcases Nat.lt_or_ge X 2 with hX2 | hX2
  ·
    refine hfinish (fun z => z * m24Z0E = m24Z0E * z)
      (fun y => ∀ z ∈ T ⊓ L, (∀ s ∈ T ⊓ L, z * s = s * z) → z * y = y * z) ?_ ?_
      (m24_key_z hX2 hKset hTK hK9 hPKK hPKc)
    · intro t ht y _ hy z hz hzc
      have hz' : t⁻¹ * z * t ∈ T ⊓ L :=
        ⟨T.mul_mem (T.mul_mem (T.inv_mem ht.1) hz.1) ht.1, by
          have := hL.conj_mem z hz.2 t⁻¹
          rwa [inv_inv] at this⟩
      have hzc' : ∀ s ∈ T ⊓ L, t⁻¹ * z * t * s = s * (t⁻¹ * z * t) := by
        intro s hs
        have hs' : t * s * t⁻¹ ∈ T ⊓ L :=
          ⟨T.mul_mem (T.mul_mem ht.1 hs.1) (T.inv_mem ht.1), hL.conj_mem s hs.2 t⟩
        have := hzc _ hs'
        calc t⁻¹ * z * t * s = t⁻¹ * (z * (t * s * t⁻¹)) * t := by group
          _ = t⁻¹ * ((t * s * t⁻¹) * z) * t := by rw [this]
          _ = s * (t⁻¹ * z * t) := by group
      have := hy _ hz' hzc'
      calc z * (t * y * t⁻¹) = t * ((t⁻¹ * z * t) * y) * t⁻¹ := by group
        _ = t * (y * (t⁻¹ * z * t)) * t⁻¹ := by rw [this]
        _ = t * y * t⁻¹ * z := by group
    · intro y
      constructor
      · intro h
        have hz0 : m24Z0E ∈ TK := by rw [hTKeq]; exact m24TelE_mem _
        rw [hTKdef] at hz0
        obtain ⟨z', hz', hz'φ⟩ := hz0
        have hz'T : (z' : A) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hz'
        have hcz := h z' hz'T fun s hs => by
          have hsK : φ ⟨s, hs.2⟩ ∈ TK := by
            rw [hTKdef]
            exact ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
          rw [hTKeq] at hsK
          have := m24Z0E_comm hsK
          rw [← hz'φ, ← map_mul, ← map_mul] at this
          exact congrArg Subtype.val (hφ this).symm
        have := congrArg φ (Subtype.ext hcz : z' * y = y * z')
        rw [map_mul, map_mul, hz'φ] at this
        exact this.symm
      · intro h z hz hzc
        have hzK : φ ⟨z, hz.2⟩ ∈ m24T := by
          rw [← hTKeq, hTKdef]
          exact ⟨_, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
        have hzc' : ∀ s ∈ m24T, φ ⟨z, hz.2⟩ * s = s * φ ⟨z, hz.2⟩ := by
          intro s hs
          rw [← hTKeq, hTKdef] at hs
          obtain ⟨s', hs', rfl⟩ := hs
          have := hzc s' (Subgroup.mem_subgroupOf.mp hs')
          rw [← map_mul, ← map_mul]
          exact congrArg φ (Subtype.ext this)
        have hcomm : φ ⟨z, hz.2⟩ * φ y = φ y * φ ⟨z, hz.2⟩ := by
          rcases m24_center hzK hzc' with h1 | h1
          · rw [h1, one_mul, mul_one]
          · rw [h1]
            exact h.symm
        rw [← map_mul, ← map_mul] at hcomm
        exact congrArg Subtype.val (hφ hcomm)
  ·
    have hX' : X = 2 := by omega
    subst hX'
    refine hfinish (fun z => ¬ m24Psi z)
      (fun y => ¬ ∃ x ∈ L, x ^ 7 = 1 ∧ x ≠ 1 ∧ x * y = y * x) ?_ ?_
      (m24_key_psi hKset hKM hK9 hPKK hPKc)
    · intro t ht y _ hy ⟨x, hxL, hx7, hx1, hxy⟩
      apply hy
      refine ⟨t⁻¹ * x * t, by simpa using hL.conj_mem x hxL t⁻¹, ?_, ?_, ?_⟩
      · rw [show t⁻¹ * x * t = t⁻¹ * x * t⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply, ← map_pow,
          hx7, map_one]
      · intro h
        apply hx1
        have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        rw [this, h]
        group
      · calc t⁻¹ * x * t * y = t⁻¹ * (x * (t * y * t⁻¹)) * t := by group
          _ = t⁻¹ * ((t * y * t⁻¹) * x) * t := by rw [hxy]
          _ = y * (t⁻¹ * x * t) := by group
    · intro y
      constructor
      · rintro h ⟨x', hx'M, hx'7, hx'1, hx'y⟩
        apply h
        obtain ⟨x, rfl⟩ := hφs x' hx'M
        refine ⟨x, x.2, ?_, ?_, ?_⟩
        · have : φ (x ^ 7) = φ 1 := by rw [map_pow, hx'7, map_one]
          exact congrArg Subtype.val (hφ this)
        · intro h1
          apply hx'1
          rw [show x = 1 from Subtype.ext h1, map_one]
        · have : φ (x * y) = φ (y * x) := by rw [map_mul, map_mul]; exact hx'y
          exact congrArg Subtype.val (hφ this)
      · rintro h ⟨x, hxL, hx7, hx1, hxy⟩
        apply h
        refine ⟨φ ⟨x, hxL⟩, hφG _, ?_, ?_, ?_⟩
        · rw [← map_pow]
          rw [show (⟨x, hxL⟩ : ↥L) ^ 7 = 1 from Subtype.ext hx7, map_one]
        · intro h1
          apply hx1
          have := hφ (h1.trans (map_one φ).symm)
          exact congrArg Subtype.val this
        · rw [← map_mul, ← map_mul]
          exact congrArg φ (Subtype.ext hxy)

theorem orderThree_m24 :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥NativeSporadic.M24 :=
    ⟨m24PermB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply eq_of_permCode24
    rw [Subgroup.coe_pow, permCode_pow24, Subgroup.coe_one, m24_code_one]
    show powC24 m24oneC 3 (permCode m24PermB) = m24oneC
    rw [m24_code_b]
    exact m24_three_check.1
  have hx1 : x ≠ 1 := by
    intro h
    apply m24_three_check.2
    have := congrArg (fun y : ↥NativeSporadic.M24 => permCode (y : Perm (Fin 24))) h
    simp only [x, Subgroup.coe_one, m24_code_one, m24_code_b] at this
    exact this
  rw [Nat.card_congr (e.trans carrierM24Equiv).toEquiv, ← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
