module

public import CFSG.Quasithin.Vol2.F134HSCheck
public import CFSG.Quasithin.Vol2.F134HSCover
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Vol2.F134Basic

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem eq_of_glCode20 {u v : GL (Fin 20) (ZMod 2)} (h : glCode20 u = glCode20 v) : u = v :=
  glCode20_injective h

theorem glCode20_hsUA : glCode20 hsUA = hsAC := matCode20_hsA

theorem glCode20_hsUB : glCode20 hsUB = hsBC := matCode20_hsB

theorem glCode20_one : glCode20 (1 : GL (Fin 20) (ZMod 2)) = hsOneC := matCode20_one

theorem glCode20_hsLetE {c : ℕ} (hc : c < 5) : glCode20 (hsLetE c) = hsLet c := by
  obtain ⟨h0, hpos⟩ := hs_let_check
  unfold hsLetE
  split_ifs with h
  · rw [h, h0, glCode20_hsUA]
  · rw [glCode20_pow, glCode20_one, glCode20_hsUB, hpos c hc (Nat.pos_of_ne_zero h)]

theorem glCode20_hsWord : ∀ w : List ℕ, (∀ c ∈ w, c < 5) → glCode20 (hsWord w) = hsWordC w
  | [], _ => glCode20_one
  | c :: w, hw => by
    rw [hsWord, hsWordC, glCode20_mul, glCode20_hsLetE (hw c List.mem_cons_self),
      glCode20_hsWord w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')]

theorem hsLetE_mem (c : ℕ) : hsLetE c ∈ hsGroup := by
  unfold hsLetE
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have h : hsUB ∈ hsGroup := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact pow_mem h c

theorem hsWord_mem : ∀ w : List ℕ, hsWord w ∈ hsGroup
  | [] => one_mem _
  | c :: w => mul_mem (hsLetE_mem c) (hsWord_mem w)

@[expose] noncomputable def hsTGen (k : ℕ) : GL (Fin 20) (ZMod 2) := hsWord (hsTGenW.getD k [])

@[expose] noncomputable def hsT : Subgroup (GL (Fin 20) (ZMod 2)) :=
  Subgroup.closure {x | ∃ k < 3, hsTGen k = x}

theorem glCode20_hsTGen {k : ℕ} (hk : k < 3) : glCode20 (hsTGen k) = hsTG k := by
  obtain ⟨h1, h2⟩ := hs_tgen_check k hk
  rw [hsTGen, glCode20_hsWord _ h2]
  exact h1

theorem hsT_le : hsT ≤ hsGroup := by
  rw [hsT, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact hsWord_mem _

theorem hsT_sub {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsT) : ∃ i < 512, glCode20 x = hsTel i := by
  refine closure_subset_of_right_closed (S := {x | ∃ k < 3, hsTGen k = x})
    (P := {x | ∃ i < 512, glCode20 x = hsTel i})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, by rw [glCode20_one, hs_tel_zero]⟩ ?_ hx
  rintro p ⟨i, hi, hp⟩ s ⟨k, hk, rfl⟩
  obtain ⟨h1, h2⟩ := hs_nxt_check i hi k hk
  exact ⟨_, h1, by rw [glCode20_mul, hp, glCode20_hsTGen hk, h2]⟩

theorem hsT_sup : ∀ i < 512, ∃ x ∈ hsT, glCode20 x = hsTel i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [glCode20_one, hs_tel_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := hs_par_check i hi hpos
      obtain ⟨y, hy, hyc⟩ := ih _ h1 (h1.trans hi)
      refine ⟨y * hsTGen (hsPar i % 4), mul_mem hy (Subgroup.subset_closure ⟨_, h2, rfl⟩), ?_⟩
      rw [glCode20_mul, hyc, glCode20_hsTGen h2, h3]

theorem hsT_isPGroup : IsPGroup 2 hsT := by
  intro x
  obtain ⟨i, hi, hx⟩ := hsT_sub x.2
  refine ⟨9, Subtype.ext (eq_of_glCode20 ?_)⟩
  rw [Subgroup.coe_pow, glCode20_pow_two_pow, hx, Subgroup.coe_one, glCode20_one]
  exact hs_pow_check i hi

@[expose] noncomputable def hsTelE (i : ℕ) : GL (Fin 20) (ZMod 2) :=
  if h : i < 512 then Classical.choose (hsT_sup i h) else 1

theorem hsTelE_mem (i : ℕ) : hsTelE i ∈ hsT := by
  unfold hsTelE
  split_ifs with h
  · exact (Classical.choose_spec (hsT_sup i h)).1
  · exact one_mem _

theorem glCode20_hsTelE {i : ℕ} (hi : i < 512) : glCode20 (hsTelE i) = hsTel i := by
  unfold hsTelE
  rw [dite_eq_left hi]
  exact (Classical.choose_spec (hsT_sup i hi)).2

theorem hsTelE_zero : hsTelE 0 = 1 :=
  eq_of_glCode20 (by rw [glCode20_hsTelE (by norm_num), hs_tel_zero, glCode20_one])

theorem hsUA_mem_hsT : hsUA ∈ hsT := by
  have h : hsUA = hsTelE 486 :=
    eq_of_glCode20 (by rw [glCode20_hsUA, glCode20_hsTelE (by norm_num), hs_a_check])
  rw [h]
  exact hsTelE_mem _

@[expose] noncomputable def hsDP (j : ℕ) : GL (Fin 20) (ZMod 2) := hsWord (hsDW.getD j [])

theorem glCode20_hsDP {j : ℕ} (hj : j < 270) : glCode20 (hsDP j) = hsD j := by
  obtain ⟨h1, h2⟩ := hs_d_check j hj
  rw [hsDP, glCode20_hsWord _ h2]
  exact h1

theorem hsDP_zero : hsDP 0 = 1 := by
  rw [hsDP, hs_dw_zero]
  rfl

@[expose] def hsU : Set (GL (Fin 20) (ZMod 2)) :=
  {x | ∃ j < 270, ∃ t ∈ hsT, ∃ t' ∈ hsT, x = t * hsDP j * t'}

theorem one_mem_hsU : (1 : GL (Fin 20) (ZMod 2)) ∈ hsU :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [hsDP_zero]; group⟩

theorem hsU_mul_T {x s : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) (hs : s ∈ hsT) : x * s ∈ hsU := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem hs_conj_step {a u g c v : GL (Fin 20) (ZMod 2)} (hu : u * g = g * c)
    (ha : a * g = g * v) : a * u * g = g * (v * c) := by
  rw [mul_assoc, hu, ← mul_assoc, ha, mul_assoc]

theorem hs_rearrange {t d a b g v x₁ d' x₂ : GL (Fin 20) (ZMod 2)} (hb : b * g = g * v)
    (hd : d * a * g = x₁ * d' * x₂) : t * d * (a * b) * g = t * x₁ * d' * (x₂ * v) := by
  have e1 : t * d * (a * b) * g = t * (d * a * (b * g)) := by simp only [mul_assoc]
  have e2 : t * x₁ * d' * (x₂ * v) = t * (x₁ * d' * x₂ * v) := by simp only [mul_assoc]
  rw [e1, e2, hb, ← mul_assoc (d * a) g v, hd]

theorem hsU_mul_of_data {jg nU nE m : ℕ} {uL cL R : List ℕ} {EAt PAt QAt DecAt : ℕ → ℕ}
    (hjg : jg < 270)
    (hconj : ∀ l < nU, uL.getD l 0 < 512 ∧ cL.getD l 0 < 512 ∧
      mulX20 (hsTel (uL.getD l 0)) (hsD jg) = mulX20 (hsD jg) (hsTel (cL.getD l 0)))
    (htree : EAt 0 = 0 ∧ ∀ p < nE, EAt p < 512 ∧ (0 < p → PAt p / 8 < p ∧ PAt p % 8 < nU ∧
      mulX20 (hsTel (EAt (PAt p / 8))) (hsTel (uL.getD (PAt p % 8) 0)) = hsTel (EAt p)))
    (htrans : ∀ i < 512, QAt i / 512 < m ∧ QAt i % 512 < nE ∧ R.getD (QAt i / 512) 0 < 512 ∧
      hsTel i = mulX20 (hsTel (R.getD (QAt i / 512) 0)) (hsTel (EAt (QAt i % 512))))
    (hdec : ∀ j < 270, ∀ s < m, DecAt (m * j + s) / 262144 < 270 ∧
      mulX20 (mulX20 (hsD j) (hsTel (R.getD s 0))) (hsD jg) =
        mulX20 (mulX20 (hsTel (DecAt (m * j + s) / 512 % 512)) (hsD (DecAt (m * j + s) / 262144)))
          (hsTel (DecAt (m * j + s) % 512)))
    {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) : x * hsDP jg ∈ hsU := by
  have hE : ∀ p < nE, ∃ v ∈ hsT, hsTelE (EAt p) * hsDP jg = hsDP jg * v := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      rcases Nat.eq_zero_or_pos p with rfl | hpos
      · exact ⟨1, one_mem _, by rw [htree.1, hsTelE_zero, one_mul, mul_one]⟩
      · obtain ⟨hEp, hrest⟩ := htree.2 p hp
        obtain ⟨hq, hl, hprod⟩ := hrest hpos
        obtain ⟨v, hv, hve⟩ := ih _ hq (hq.trans hp)
        obtain ⟨hEq, -⟩ := htree.2 _ (hq.trans hp)
        obtain ⟨hu, hc, hconj'⟩ := hconj _ hl
        have hug : hsTelE (uL.getD (PAt p % 8) 0) * hsDP jg =
            hsDP jg * hsTelE (cL.getD (PAt p % 8) 0) := eq_of_glCode20 (by
          rw [glCode20_mul, glCode20_mul, glCode20_hsTelE hu, glCode20_hsDP hjg,
            glCode20_hsTelE hc]
          exact hconj')
        have hsplit : hsTelE (EAt p) =
            hsTelE (EAt (PAt p / 8)) * hsTelE (uL.getD (PAt p % 8) 0) := eq_of_glCode20 (by
          rw [glCode20_mul, glCode20_hsTelE hEp, glCode20_hsTelE hEq, glCode20_hsTelE hu]
          exact hprod.symm)
        exact ⟨v * hsTelE (cL.getD (PAt p % 8) 0), mul_mem hv (hsTelE_mem _), by
          rw [hsplit]
          exact hs_conj_step hug hve⟩
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨i, hi, hc⟩ := hsT_sub ht'
  obtain ⟨hs, hp, hr, htr⟩ := htrans i hi
  obtain ⟨hEp, -⟩ := htree.2 _ hp
  have ht'eq : t' = hsTelE (R.getD (QAt i / 512) 0) * hsTelE (EAt (QAt i % 512)) :=
    eq_of_glCode20 (by
      rw [hc, glCode20_mul, glCode20_hsTelE hr, glCode20_hsTelE hEp]
      exact htr)
  obtain ⟨v, hv, hve⟩ := hE _ hp
  obtain ⟨hk, hdeq⟩ := hdec j hj _ hs
  generalize DecAt (m * j + QAt i / 512) = e at hk hdeq
  have hd : hsDP j * hsTelE (R.getD (QAt i / 512) 0) * hsDP jg =
      hsTelE (e / 512 % 512) * hsDP (e / 262144) * hsTelE (e % 512) := eq_of_glCode20 (by
    rw [glCode20_mul, glCode20_mul, glCode20_mul, glCode20_mul, glCode20_hsDP hj,
      glCode20_hsTelE hr, glCode20_hsDP hjg, glCode20_hsTelE (Nat.mod_lt _ (by norm_num)),
      glCode20_hsDP hk, glCode20_hsTelE (Nat.mod_lt _ (by norm_num))]
    exact hdeq)
  refine ⟨e / 262144, hk, t * hsTelE (e / 512 % 512), mul_mem ht (hsTelE_mem _),
    hsTelE (e % 512) * v, mul_mem (hsTelE_mem _) hv, ?_⟩
  rw [ht'eq]
  exact hs_rearrange hve hd

theorem hsU_mul_gOne {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) : x * hsDP 1 ∈ hsU :=
  hsU_mul_of_data (nU := 3) (nE := 256) (m := 2) (uL := hsGOneU) (cL := hsGOneC)
    (R := hsGOneR) (EAt := hsGOneEAt) (PAt := hsGOnePAt) (QAt := hsGOneQAt)
    (DecAt := hsGOneDecAt) (by norm_num) hs_gOne_conj hs_gOne_tree hs_gOne_trans hs_gOne_dec hx

theorem hsU_mul_gTwo {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) : x * hsDP 251 ∈ hsU :=
  hsU_mul_of_data (nU := 4) (nE := 128) (m := 4) (uL := hsGTwoU) (cL := hsGTwoC)
    (R := hsGTwoR) (EAt := hsGTwoEAt) (PAt := hsGTwoPAt) (QAt := hsGTwoQAt)
    (DecAt := hsGTwoDecAt) (by norm_num) hs_gTwo_conj hs_gTwo_tree hs_gTwo_trans hs_gTwo_dec hx

@[expose] noncomputable def hsBWLetE (l : ℕ) : GL (Fin 20) (ZMod 2) :=
  if l < 3 then hsTGen l else if l = 3 then hsDP 1 else hsDP 251

@[expose] noncomputable def hsBWord : List ℕ → GL (Fin 20) (ZMod 2)
  | [] => 1
  | l :: w => hsBWLetE l * hsBWord w

theorem glCode20_hsBWLetE (l : ℕ) : glCode20 (hsBWLetE l) = hsBWLet l := by
  unfold hsBWLetE hsBWLet
  split_ifs with h1 h2
  · exact glCode20_hsTGen h1
  · exact glCode20_hsDP (by norm_num)
  · exact glCode20_hsDP (by norm_num)

theorem glCode20_hsBWord : ∀ w : List ℕ, glCode20 (hsBWord w) = hsBWC w
  | [] => glCode20_one
  | l :: w => by rw [hsBWord, hsBWC, glCode20_mul, glCode20_hsBWLetE, glCode20_hsBWord w]

theorem hsU_mul_hsBWLetE {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) (l : ℕ) :
    x * hsBWLetE l ∈ hsU := by
  unfold hsBWLetE
  split_ifs with h1 h2
  · exact hsU_mul_T hx (Subgroup.subset_closure ⟨l, h1, rfl⟩)
  · exact hsU_mul_gOne hx
  · exact hsU_mul_gTwo hx

theorem hsU_mul_hsBWord : ∀ (w : List ℕ) {x : GL (Fin 20) (ZMod 2)}, x ∈ hsU →
    x * hsBWord w ∈ hsU
  | [], x, hx => by rw [hsBWord, mul_one]; exact hx
  | l :: w, x, hx => by
    rw [hsBWord, ← mul_assoc]
    exact hsU_mul_hsBWord w (hsU_mul_hsBWLetE hx l)

theorem hsUB_eq : hsUB = hsTelE 18 * hsBWord hsBW :=
  eq_of_glCode20 (by
    rw [glCode20_hsUB, glCode20_mul, glCode20_hsTelE (by norm_num), glCode20_hsBWord]
    exact hs_b_check)

theorem hsU_mul_b {x : GL (Fin 20) (ZMod 2)} (hx : x ∈ hsU) : x * hsUB ∈ hsU := by
  rw [hsUB_eq, ← mul_assoc]
  exact hsU_mul_hsBWord _ (hsU_mul_T hx (hsTelE_mem _))

theorem hsGroup_subset_hsU : (hsGroup : Set (GL (Fin 20) (ZMod 2))) ⊆ hsU := by
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_hsU ?_
  rintro p hp s (rfl | rfl)
  · exact hsU_mul_T hp hsUA_mem_hsT
  · exact hsU_mul_b hp

theorem hs_good_of_mem {H : Subgroup (GL (Fin 20) (ZMod 2))} (hTH : hsT ≤ H)
    (hp : ∀ p, p = 5 ∨ p = 7 ∨ p = 11 → ¬ p ∣ Nat.card H) {j : ℕ} (hj : j < 270) (hj3 : 3 ≤ j)
    (hD : hsDP j ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := hs_bad_check j hj hj3
  set p := hsBad j % 16 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(hsDP j * hsTelE (hsBad j / 512)) ^ (hsBad j / 16 % 32),
    pow_mem (mul_mem hD (hTH (hsTelE_mem _))) _⟩
  have hcode : glCode20 (x : GL (Fin 20) (ZMod 2)) = powC20 hsOneC (hsBad j / 16 % 32)
      (mulX20 (hsD j) (hsTel (hsBad j / 512))) := by
    show glCode20 ((hsDP j * hsTelE (hsBad j / 512)) ^ (hsBad j / 16 % 32)) = _
    rw [glCode20_pow, glCode20_mul, glCode20_hsDP hj, glCode20_hsTelE hi, glCode20_one]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_glCode20
    rw [Subgroup.coe_pow, glCode20_pow, hcode, Subgroup.coe_one, glCode20_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, glCode20_one]
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  exact hp p hp' hdvd

theorem hs_card_le {H : Subgroup (GL (Fin 20) (ZMod 2))} (hTH : hsT ≤ H)
    (hH : H ≤ hsGroup) (hp : ∀ p, p = 5 ∨ p = 7 ∨ p = 11 → ¬ p ∣ Nat.card H) :
    Nat.card H ≤ 5 * Nat.card hsT := by
  have hr₀ : hsTelE 0 = 1 := hsTelE_zero
  let c : Fin 5 → GL (Fin 20) (ZMod 2) := ![1, hsDP 1, hsTelE 3 * hsDP 1, hsDP 2,
    hsTelE 1 * hsDP 2]
  have hstep : ∀ {j : ℕ}, j = 1 ∨ j = 2 → ∀ {t t' : GL (Fin 20) (ZMod 2)}, t ∈ hsT → t' ∈ hsT →
      ∃ b < 2, ∃ w ∈ hsT,
        t * hsDP j * t' = hsTelE (if b = 0 then 0 else if j = 1 then 3 else 1) *
          hsDP j * (w * t') := by
    intro j hj t t' ht ht'
    have hj0 : 0 < j := by omega
    have hj3 : j < 3 := by omega
    have hj270 : j < 270 := by omega
    obtain ⟨i, hi, htc⟩ := hsT_sub ht
    obtain ⟨hs, hcos⟩ := hs_cos_check j hj3 hj0 i hi
    have hr : (if hsCos j i / 512 = 0 then 0 else if j = 1 then 3 else 1) < 512 := by
      split_ifs <;> norm_num
    refine ⟨hsCos j i / 512, hs, hsTelE (hsCos j i % 512), hsTelE_mem _, ?_⟩
    have key : t * hsDP j = hsTelE (if hsCos j i / 512 = 0 then 0 else if j = 1 then 3 else
        1) * hsDP j * hsTelE (hsCos j i % 512) := by
      apply eq_of_glCode20
      rw [glCode20_mul, glCode20_mul, glCode20_mul, htc, glCode20_hsTelE hr,
        glCode20_hsTelE (Nat.mod_lt _ (by norm_num)), glCode20_hsDP hj270]
      exact hcos
    rw [key]
    group
  have hcov : ∀ h ∈ H, ∃ s : Fin 5, ∃ t ∈ hsT, h = c s * t := by
    intro h hh
    obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hsGroup_subset_hsU (hH hh)
    have hD : hsDP j ∈ H := by
      have e : hsDP j = t⁻¹ * (t * hsDP j * t') * t'⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · interval_cases j
      · exact ⟨0, t * t', mul_mem ht ht', by rw [hsDP_zero]; simp [c]⟩
      · obtain ⟨b, hb, w, hw, e⟩ := hstep (Or.inl rfl) ht ht'
        interval_cases b
        · exact ⟨1, w * t', mul_mem hw ht', by rw [e]; simp [c, hr₀]⟩
        · exact ⟨2, w * t', mul_mem hw ht', by rw [e]; simp [c]⟩
      · obtain ⟨b, hb, w, hw, e⟩ := hstep (Or.inr rfl) ht ht'
        interval_cases b
        · exact ⟨3, w * t', mul_mem hw ht', by rw [e]; simp [c, hr₀]⟩
        · exact ⟨4, w * t', mul_mem hw ht', by rw [e]; simp [c]⟩
    · exact (hs_good_of_mem hTH hp hj hj3 hD).elim
  choose s t ht hst using fun h : H => hcov h h.2
  have hinj : Function.Injective fun h : H => ((s h, ⟨t h, ht h⟩) : Fin 5 × hsT) := by
    intro h h' e
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at e
    exact Subtype.ext ((hst h).trans (e.1 ▸ e.2 ▸ (hst h').symm))
  calc Nat.card H ≤ Nat.card (Fin 5 × hsT) := Nat.card_le_card_of_injective _ hinj
    _ = 5 * Nat.card hsT := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] noncomputable def carrierHSEquiv : NativeSporadic.Carrier .HS ≃* NativeSporadic.HS :=
  MulEquiv.refl _

theorem hs_embedding {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .HS) :
    ∃ φ : X →* GL (Fin 20) (ZMod 2), Function.Injective φ ∧ (∀ x, φ x ∈ hsGroup) ∧
      ∀ y ∈ hsGroup, ∃ x, φ x = y := by
  obtain ⟨ψ, -⟩ : ∃ ψ : X ≃* ↥hsGroup, ψ = (e.trans carrierHSEquiv).trans hsNativeEquiv :=
    ⟨_, rfl⟩
  refine ⟨(Subgroup.subtype _).comp (ψ : X →* ↥hsGroup), fun a b h => ψ.injective
    (Subgroup.subtype_injective _ h), fun x => (ψ x).2, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem noE9Config_hs :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := hs_embedding e
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨TL, hTLdef⟩ : ∃ R : Subgroup ↥L, R = hsT.comap φ₀ := ⟨_, rfl⟩
  have hTLmap : TL.map φ₀ = hsT := by
    rw [hTLdef]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ₀surj y (hsT_le hy)
    exact ⟨x, hy, rfl⟩
  have hTLc : Nat.card TL = Nat.card hsT := by
    rw [← hTLmap]
    exact Nat.card_congr (TL.equivMapOfInjective _ hφ₀).toEquiv
  have hTLp : IsPGroup 2 TL :=
    hsT_isPGroup.of_equiv ((TL.equivMapOfInjective _ hφ₀).trans
      (MulEquiv.subgroupCongr hTLmap)).symm
  have hUp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨Q, hQ⟩ := hTLp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) (hUp.toSylow hS.2.2) Q
  have hQU : ∀ x ∈ (Q : Subgroup ↥L), (MulAut.conj g)⁻¹ x ∈ (T ⊓ L).subgroupOf L := by
    intro x hx
    have hx' : x ∈ ((g • hUp.toSylow hS.2.2 : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hcardQ : Nat.card ((T ⊓ L).subgroupOf L) = Nat.card (Q : Subgroup ↥L) := by
    have := congrArg (fun R : Sylow 2 ↥L => Nat.card (R : Subgroup ↥L)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at this
    rw [← this, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _
      (MulAut.conj g).injective).toEquiv
  obtain ⟨φ, hφdef⟩ : ∃ φ : ↥L →* GL (Fin 20) (ZMod 2),
      φ = φ₀.comp (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef]
    exact hφ₀.comp (MulAut.conj g).injective
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (GL (Fin 20) (ZMod 2)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : hsT ≤ K := by
    intro y hy
    rw [← hTLmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hu := hQU x (hQ hx)
    rw [hKdef]
    refine ⟨(MulAut.conj g)⁻¹ x, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hu)), ?_⟩
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply,
      mul_inv_cancel, MulAut.one_apply]
  have hKM : K ≤ hsGroup := by
    rw [hKdef, hφdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφ₀mem _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hle := hs_card_le hTK hKM (fun p hp => by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow hp)
  have hTU : Nat.card hsT ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hcardQ, ← hTLc]
    exact Subgroup.card_le_of_le hQ
  have hpos : 0 < Nat.card hsT := Nat.card_pos
  rw [hKc, hHc] at hle
  omega

theorem orderThree_hs :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h3, hne, hw⟩ := hs_three_check
  obtain ⟨φ, hφ, hφmem, hφsurj⟩ := hs_embedding e
  obtain ⟨x, hx⟩ := hφsurj (hsWord hsThreeW) (hsWord_mem _)
  have hcode : glCode20 (hsWord hsThreeW) = hsWordC hsThreeW := glCode20_hsWord _ hw
  have hx3 : x ^ 3 = 1 := hφ (by
    rw [map_pow, hx, map_one]
    apply eq_of_glCode20
    rw [glCode20_pow, hcode, glCode20_one]
    exact h3)
  have hx1 : x ≠ 1 := fun h => hne (by rw [← hcode, ← hx, h, map_one, glCode20_one])
  rw [← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
