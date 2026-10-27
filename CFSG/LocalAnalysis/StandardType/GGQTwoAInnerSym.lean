module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin


private abbrev ggQ2xS_GL (m : ℕ) : Type := GGBCV m ≃ₗ[ZMod 3] GGBCV m

private lemma ggQ2xS_fin_eq_castSucc_or_last {m : ℕ} (i : Fin (m + 1)) :
    (∃ i' : Fin m, i = Fin.castSucc i') ∨ i = Fin.last m := by
  by_cases h : (i : ℕ) < m
  · exact Or.inl ⟨⟨i, h⟩, by ext; rfl⟩
  · refine Or.inr ?_
    ext
    rw [Fin.val_last]
    have := i.isLt
    omega

private lemma ggQ2xS_last_ne_castSucc {m : ℕ} (i : Fin m) :
    (Fin.last m : Fin (m + 1)) ≠ Fin.castSucc i := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_castSucc] at this
  omega

private lemma ggQ2xS_castSucc_ne_last {m : ℕ} (i : Fin m) :
    (Fin.castSucc i : Fin (m + 1)) ≠ Fin.last m :=
  (ggQ2xS_last_ne_castSucc i).symm

private lemma ggQ2xS_castSucc_inj {m : ℕ} {i j : Fin m}
    (h : (Fin.castSucc i : Fin (m + 1)) = Fin.castSucc j) : i = j :=
  Fin.ext (by simpa using congrArg Fin.val h)

private lemma ggQ2xS_castSucc_ne_castSucc {m : ℕ} {i j : Fin m} (h : i ≠ j) :
    (Fin.castSucc i : Fin (m + 1)) ≠ Fin.castSucc j :=
  fun hc => h (ggQ2xS_castSucc_inj hc)

private lemma ggQ2xS_swap_castSucc {m : ℕ} (i j k : Fin m) :
    (Equiv.swap (Fin.castSucc i) (Fin.castSucc j)) (Fin.castSucc k)
      = Fin.castSucc (Equiv.swap i j k) := by
  rw [Equiv.swap_apply_def]
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst hkj
      rw [if_neg (fun h => hki (ggQ2xS_castSucc_inj h)), if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg (fun h => hki (ggQ2xS_castSucc_inj h)),
        if_neg (fun h => hkj (ggQ2xS_castSucc_inj h)),
        Equiv.swap_apply_of_ne_of_ne hki hkj]

private lemma ggQ2xS_swap_castSucc_last {m : ℕ} (i j : Fin m) :
    (Equiv.swap (Fin.castSucc i) (Fin.castSucc j)) (Fin.last m) = Fin.last m :=
  Equiv.swap_apply_of_ne_of_ne (ggQ2xS_castSucc_ne_last i).symm
    (ggQ2xS_castSucc_ne_last j).symm

private lemma ggQ2xS_swap_last_castSucc {m : ℕ} (i k : Fin m) :
    (Equiv.swap (Fin.last m) (Fin.castSucc i)) (Fin.castSucc k)
      = if k = i then Fin.last m else Fin.castSucc k := by
  rw [Equiv.swap_apply_def, if_neg (ggQ2xS_castSucc_ne_last k)]
  by_cases h : k = i
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun hc => h (ggQ2xS_castSucc_inj hc)), if_neg h]

private lemma ggQ2xS_swap_last_last {m : ℕ} (i : Fin m) :
    (Equiv.swap (Fin.last m) (Fin.castSucc i)) (Fin.last m) = Fin.castSucc i :=
  Equiv.swap_apply_left _ _

private lemma ggQ2xS_swap_eq_iff {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) :
    Equiv.swap a b = Equiv.swap c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha := congrArg (fun e : Equiv.Perm α => e a) h
    rw [Equiv.swap_apply_left, Equiv.swap_apply_def] at ha
    by_cases hac : a = c
    · left
      exact ⟨hac, by rw [if_pos hac] at ha; exact ha⟩
    · by_cases had : a = d
      · right
        exact ⟨had, by rw [if_neg hac, if_pos had] at ha; exact ha⟩
      · rw [if_neg hac, if_neg had] at ha
        exact absurd ha.symm hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [Equiv.swap_comm]

private lemma ggQ2xS_dot_smul {m : ℕ} (a : ZMod 3) (v w : GGBCV m) :
    (a • v) ⬝ᵥ w = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf

private lemma ggQ2xS_dot_smul_right {m : ℕ} (a : ZMod 3) (v w : GGBCV m) :
    v ⬝ᵥ (a • w) = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf

private lemma ggQ2xS_norm_smul {m : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV m) :
    (a • c) ⬝ᵥ (a • c) = c ⬝ᵥ c := by
  rw [ggQ2xS_dot_smul, ggQ2xS_dot_smul_right]
  rw [show a * (a * (c ⬝ᵥ c)) = c ⬝ᵥ c from by
    rw [← mul_assoc, ggQ2x_mul_self_eq_one a ha, one_mul]]

private lemma ggQ2xS_scalar_smul {m : ℕ} (a x y : ZMod 3) (ha : a ≠ 0) (c : GGBCV m) :
    ((a * x) * y) • (a • c) = (x * y) • c := by
  rw [smul_smul]
  congr 1
  calc (a * x) * y * a = (a * a) * (x * y) := by ring
    _ = 1 * (x * y) := by rw [ggQ2x_mul_self_eq_one a ha]
    _ = x * y := by rw [one_mul]

private lemma ggQ2xS_refl_smul {m : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV m)
    (hc : c ⬝ᵥ c ≠ 0) (hac : (a • c) ⬝ᵥ (a • c) ≠ 0) :
    ggBCRefl (a • c) hac = ggBCRefl c hc := by
  apply LinearEquiv.ext
  intro v
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, ggQ2xS_dot_smul,
    ggQ2xS_norm_smul a ha c, ggQ2xS_scalar_smul a (c ⬝ᵥ v) (c ⬝ᵥ c) ha c]

private lemma ggQ2xS_dot_neg {m : ℕ} (c : GGBCV m) : (-c) ⬝ᵥ (-c) = c ⬝ᵥ c := by
  have h : (-c : GGBCV m) = (-1 : ZMod 3) • c :=
    (neg_one_smul (R := ZMod 3) (x := c)).symm
  simpa [h] using ggQ2xS_norm_smul (-1) (by decide) c

private lemma ggQ2xS_refl_neg {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hn : (-c) ⬝ᵥ (-c) ≠ 0) : ggBCRefl (-c) hn = ggBCRefl c hc := by
  have h1 : (-c : GGBCV m) = (-1 : ZMod 3) • c :=
    (neg_one_smul (R := ZMod 3) (x := c)).symm
  have hn' : (((-1 : ZMod 3) • c) ⬝ᵥ ((-1 : ZMod 3) • c)) ≠ 0 := by
    rw [← h1]; exact hn
  calc ggBCRefl (-c) hn
      = ggBCRefl ((-1 : ZMod 3) • c) hn' := by congr 1
    _ = ggBCRefl c hc := ggQ2xS_refl_smul (-1) (by decide) c hc hn'

private lemma ggQ2xS_refl_inv {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) :
    (ggBCRefl c hc)⁻¹ = ggBCRefl c hc :=
  Module.reflection_inv _

private lemma ggQ2xS_refl_proof_irrel {m : ℕ} (c : GGBCV m) (h1 h2 : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h1 = ggBCRefl c h2 := by
  rw [Subsingleton.elim h1 h2]

private lemma ggQ2xS_refl_congr {m : ℕ} {c c' : GGBCV m} (hc : c ⬝ᵥ c ≠ 0)
    (hc' : c' ⬝ᵥ c' ≠ 0) (h : c = c') : ggBCRefl c hc = ggBCRefl c' hc' := by
  subst h
  exact ggQ2xS_refl_proof_irrel c hc hc'

private lemma ggQ2xS_conj_refl {m : ℕ} (b : ggQ2xS_GL m)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) :
    b * ggBCRefl c hc * b⁻¹ = ggBCRefl (b c) (by rw [hb]; exact hc) := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  rw [show b⁻¹ = b.symm from rfl]
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2x_ggBCRefl_apply,
    ggQ2x_ggBCRefl_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]

private lemma ggQ2xS_conj_refl' {m : ℕ} (b : ggQ2xS_GL m)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) (hc' : (b c) ⬝ᵥ (b c) ≠ 0) :
    b * ggBCRefl c hc * b⁻¹ = ggBCRefl (b c) hc' := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  rw [show b⁻¹ = b.symm from rfl]
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2x_ggBCRefl_apply,
    ggQ2x_ggBCRefl_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]

private lemma ggQ2xS_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + p * d * q + q * d * (p + p * d * d) = r := by decide

private lemma ggQ2xS_refl_isometry {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (x y : GGBCV m) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV m) x, dotProduct_comm (c : GGBCV m) y]
  rw [ggQ2xS_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggQ2xS_dot_one {m : ℕ} (v : GGBCV m) :
    (1 : GGBCV m) ⬝ᵥ v = ∑ i, v i := by
  simp only [dotProduct, Pi.one_apply, one_mul]

private lemma ggQ2xS_dot_one_one (m : ℕ) :
    (1 : GGBCV m) ⬝ᵥ (1 : GGBCV m) = (m : ZMod 3) := by
  rw [ggQ2xS_dot_one]
  simp [Finset.sum_const, Finset.card_univ]

private lemma ggQ2xS_dot_one_single {m : ℕ} (i : Fin m) :
    (1 : GGBCV m) ⬝ᵥ (Pi.single i (1 : ZMod 3) : GGBCV m) = 1 := by
  rw [ggQ2xS_dot_one]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xS_dot_one_add_single (m : ℕ) (i : Fin m) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (1 + Pi.single i (1 : ZMod 3) : GGBCV m) = (m : ZMod 3) + 3 := by
  simp only [add_dotProduct, dotProduct_add, ggQ2xS_dot_one_one, ggQ2xS_dot_one_single,
    dotProduct_single_one, single_one_dotProduct, Pi.add_apply, Pi.one_apply,
    Pi.single_eq_same]
  ring_nf

private lemma ggQ2xS_dot_type1_type1 (m : ℕ) (i k : Fin m) (hik : i ≠ k) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (1 + Pi.single k (1 : ZMod 3) : GGBCV m) = (m : ZMod 3) + 2 := by
  simp only [add_dotProduct, dotProduct_add, ggQ2xS_dot_one_one, dotProduct_single_one,
    single_one_dotProduct, Pi.add_apply, Pi.one_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik)]
  ring_nf

private lemma ggQ2xS_sum_pi_single {m : ℕ} (i : Fin m) :
    (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV m) x) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xS_sum_sub_single {m : ℕ} (k l : Fin m) :
    (∑ x, (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) x) = 0 := by
  rw [show (∑ x, (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) x)
      = (∑ x, (Pi.single k (1 : ZMod 3) : GGBCV m) x) -
        (∑ x, (Pi.single l (1 : ZMod 3) : GGBCV m) x) from
    Finset.sum_sub_distrib _ _]
  rw [ggQ2xS_sum_pi_single, ggQ2xS_sum_pi_single, sub_self]

private lemma ggQ2xS_dot_type1_sub (m : ℕ) (i k l : Fin m) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m)
        = ((Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) i) := by
  rw [add_dotProduct, ggQ2xS_dot_one, single_one_dotProduct]
  rw [ggQ2xS_sum_sub_single, zero_add]

private lemma ggQ2xS_natCast_eq_two {m : ℕ} (h : m % 3 = 2) : (m : ZMod 3) = 2 := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, h]
  decide

private lemma ggQ2xS_sub_single_norm_ne {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ≠ 0 := by
  rw [ggQ2x_sub_single_norm i j hij]
  decide

private lemma ggQ2xS_one_add_single_norm_ne {m : ℕ} (hm : m % 3 = 2) (i : Fin m) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ≠ 0 := by
  rw [ggQ2xS_dot_one_add_single, ggQ2xS_natCast_eq_two hm]
  decide

@[irreducible] private def ggQ2xS_t1v (m : ℕ) (i : Fin m) : GGBCV m :=
  1 + Pi.single i (1 : ZMod 3)

private lemma ggQ2xS_t1v_norm_ne {m : ℕ} (hm3 : m % 3 = 2) (i : Fin m) :
    ggQ2xS_t1v m i ⬝ᵥ ggQ2xS_t1v m i ≠ 0 := by
  unfold ggQ2xS_t1v
  exact ggQ2xS_one_add_single_norm_ne hm3 i

@[irreducible] private def ggQ2xS_rv (m : ℕ) (i l : Fin m) : GGBCV m :=
  Pi.single i (1 : ZMod 3) - Pi.single l (1 : ZMod 3)

private lemma ggQ2xS_rv_norm_ne {m : ℕ} (i l : Fin m) (hil : i ≠ l) :
    ggQ2xS_rv m i l ⬝ᵥ ggQ2xS_rv m i l ≠ 0 := by
  unfold ggQ2xS_rv
  exact ggQ2xS_sub_single_norm_ne i l hil

private lemma ggQ2xS_rv_perm {m : ℕ} (i l : Fin m) (hil : i ≠ l) :
    ggPermHom m (Equiv.swap i l)
      = ggBCRefl (ggQ2xS_rv m i l) (ggQ2xS_rv_norm_ne i l hil) := by
  rw [ggPermHom_swap i l hil (ggQ2xS_sub_single_norm_ne i l hil)]
  exact ggQ2xS_refl_congr _ _ (by unfold ggQ2xS_rv; rfl)

private lemma ggQ2xS_type1_type1_dot {m : ℕ} (hm : m % 3 = 2) (i k : Fin m)
    (hik : i ≠ k) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (1 + Pi.single k (1 : ZMod 3) : GGBCV m) = 1 := by
  rw [ggQ2xS_dot_type1_type1 m i k hik, ggQ2xS_natCast_eq_two hm]
  decide

private lemma ggQ2xS_dot_one_add_single_eq {m : ℕ} (hm : m % 3 = 2) (i : Fin m) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (1 + Pi.single i (1 : ZMod 3) : GGBCV m) = -1 := by
  rw [ggQ2xS_dot_one_add_single, ggQ2xS_natCast_eq_two hm]
  decide

private lemma ggQ2xS_refl_type1_apply {m : ℕ} (hm : m % 3 = 2) (i : Fin m)
    (v : GGBCV m) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i) v
      = v - ((1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v) •
          (1 + Pi.single i (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2x_ggBCRefl_apply, ggQ2xS_dot_one_add_single_eq hm]
  have hneg : ((1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v) * (-1 : ZMod 3)
      = -((1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v) := mul_neg_one _
  have hs : (-((1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v)) •
      (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
      = -(((1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v) •
        (1 + Pi.single i (1 : ZMod 3) : GGBCV m)) := neg_smul _ _
  rw [hneg, hs, sub_eq_add_neg]
  rfl

private lemma ggQ2xS_dot_type1_sub_left {m : ℕ} (i l : Fin m) (hil : i ≠ l) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) = 1 := by
  rw [ggQ2xS_dot_type1_sub, Pi.sub_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hil]
  decide

private lemma ggQ2xS_dot_type1_sub_right {m : ℕ} (i k : Fin m) (hik : i ≠ k) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single k (1 : ZMod 3) - Pi.single i (1 : ZMod 3) : GGBCV m) = -1 := by
  rw [ggQ2xS_dot_type1_sub, Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hik,
    Pi.single_eq_same]
  decide

private lemma ggQ2xS_dot_type1_sub_other {m : ℕ} (i k l : Fin m) (hik : i ≠ k)
    (hil : i ≠ l) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) = 0 := by
  rw [ggQ2xS_dot_type1_sub, Pi.sub_apply,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hik,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hil]
  decide

private lemma ggQ2xS_refl_type1_sub_left {m : ℕ} (hm : m % 3 = 2) (i l : Fin m)
    (hil : i ≠ l) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i)
        (Pi.single i (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m)
      = (-(1 + Pi.single l (1 : ZMod 3) : GGBCV m)) := by
  rw [ggQ2xS_refl_type1_apply hm i, ggQ2xS_dot_type1_sub_left i l hil, one_smul]
  funext j
  rcases eq_or_ne j i with rfl | hji
  · rcases eq_or_ne j l with rfl | hjl
    · exact absurd rfl hil
    · simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.one_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjl]
      decide
  · rcases eq_or_ne j l with rfl | hjl
    · simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji, Pi.single_eq_same]
      decide
    · simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjl]
      decide

private lemma ggQ2xS_refl_t1v_sub_left {m : ℕ} (hm3 : m % 3 = 2) (i l : Fin m)
    (hil : i ≠ l) :
    ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)
        (Pi.single i (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m)
      = (-(ggQ2xS_t1v m l)) := by
  unfold ggQ2xS_t1v
  exact ggQ2xS_refl_type1_sub_left hm3 i l hil

private lemma ggQ2xS_refl_t1v_rv {m : ℕ} (hm3 : m % 3 = 2) (i l : Fin m) (hil : i ≠ l) :
    ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_rv m i l)
      = (-(ggQ2xS_t1v m l)) := by
  unfold ggQ2xS_t1v ggQ2xS_rv
  exact ggQ2xS_refl_type1_sub_left hm3 i l hil

private lemma ggQ2xS_refl_type1_sub_right {m : ℕ} (hm : m % 3 = 2) (i k : Fin m)
    (hik : i ≠ k) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i)
        (Pi.single k (1 : ZMod 3) - Pi.single i (1 : ZMod 3) : GGBCV m)
      = (1 + Pi.single k (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2xS_refl_type1_apply hm i, ggQ2xS_dot_type1_sub_right i k hik]
  funext j
  rcases eq_or_ne j k with rfl | hjk
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik)]
    decide
  · rcases eq_or_ne j i with rfl | hji
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hik, Pi.single_eq_same]
      decide
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjk,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji]
      decide

private lemma ggQ2xS_refl_type1_sub_other {m : ℕ} (hm : m % 3 = 2) (i k l : Fin m)
    (hik : i ≠ k) (hil : i ≠ l) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i)
        (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m)
      = (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2xS_refl_type1_apply hm i, ggQ2xS_dot_type1_sub_other i k l hik hil, zero_smul]
  exact sub_zero _

private lemma ggQ2xS_refl_type1_type1 {m : ℕ} (hm : m % 3 = 2) (i k : Fin m)
    (hik : i ≠ k) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i)
        (1 + Pi.single k (1 : ZMod 3) : GGBCV m)
      = (Pi.single k (1 : ZMod 3) - Pi.single i (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2xS_refl_type1_apply hm i, ggQ2xS_type1_type1_dot hm i k hik, one_smul]
  funext j
  rcases eq_or_ne j k with rfl | hjk
  · simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hik,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik)]
    decide
  · rcases eq_or_ne j i with rfl | hji
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hik, Pi.single_eq_same]
      decide
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjk,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji]
      decide

private lemma ggQ2xS_refl_type1_self {m : ℕ} (hm : m % 3 = 2) (i : Fin m) :
    ggBCRefl (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
        (ggQ2xS_one_add_single_norm_ne hm i)
        (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
      = (-(1 + Pi.single i (1 : ZMod 3) : GGBCV m)) := by
  rw [ggQ2xS_refl_type1_apply hm i, ggQ2xS_dot_one_add_single_eq hm]
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.add_apply,
      Pi.one_apply, Pi.single_eq_same]
    decide
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.add_apply,
      Pi.one_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji]
    decide

private lemma ggQ2xS_refl_t1v_type1 {m : ℕ} (hm3 : m % 3 = 2) (i k : Fin m)
    (hik : i ≠ k) :
    ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_t1v m k)
      = ggQ2xS_rv m k i := by
  unfold ggQ2xS_t1v ggQ2xS_rv
  exact ggQ2xS_refl_type1_type1 hm3 i k hik

private lemma ggQ2xS_refl_t1v_self {m : ℕ} (hm3 : m % 3 = 2) (i : Fin m) :
    ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_t1v m i)
      = (-(ggQ2xS_t1v m i)) := by
  unfold ggQ2xS_t1v
  exact ggQ2xS_refl_type1_self hm3 i

private lemma ggQ2xS_perm_one (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    ggPermHom m σ (1 : GGBCV m) = 1 := by
  funext i
  rw [ggPermHom_apply]
  rfl

private lemma ggQ2xS_perm_single (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (Pi.single i (1 : ZMod 3)) = Pi.single (σ i) 1 := by
  funext j
  rw [ggPermHom_apply]
  by_cases h : j = σ i
  · subst h
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (fun hc => h (by rw [← hc, Equiv.apply_symm_apply]))]

private lemma ggQ2xS_perm_one_add_single (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
      = 1 + Pi.single (σ i) (1 : ZMod 3) := by
  rw [map_add, ggQ2xS_perm_one, ggQ2xS_perm_single]

private lemma ggQ2xS_perm_t1v (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (ggQ2xS_t1v m i) = ggQ2xS_t1v m (σ i) := by
  unfold ggQ2xS_t1v
  rw [ggQ2xS_perm_one_add_single]

private lemma ggQ2xS_perm_isometry (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    ∀ x y : GGBCV m, (ggPermHom m σ x) ⬝ᵥ (ggPermHom m σ y) = x ⬝ᵥ y := by
  intro x y
  have hx : ggPermHom m σ x = x ∘ σ.symm := by funext j; rfl
  have hy : ggPermHom m σ y = y ∘ σ.symm := by funext j; rfl
  rw [hx, hy, dotProduct, dotProduct]
  exact Equiv.sum_comp σ.symm (fun i => x i * y i)

private lemma ggQ2xS_perm_t1v_comm {m : ℕ} (hm3 : m % 3 = 2) {i k l : Fin m}
    (hik : i ≠ k) (hil : i ≠ l) :
    ggPermHom m (Equiv.swap k l) *
        ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) *
        (ggPermHom m (Equiv.swap k l))⁻¹
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) := by
  have hb := ggQ2xS_perm_isometry m (Equiv.swap k l)
  have hc := ggQ2xS_t1v_norm_ne hm3 i
  have hc' : (ggPermHom m (Equiv.swap k l) (ggQ2xS_t1v m i)) ⬝ᵥ
      (ggPermHom m (Equiv.swap k l) (ggQ2xS_t1v m i)) ≠ 0 := by
    rw [hb]; exact hc
  have hconj := ggQ2xS_conj_refl' (ggPermHom m (Equiv.swap k l)) hb
    (ggQ2xS_t1v m i) hc hc'
  rw [hconj]
  rw [ggQ2xS_refl_congr _ _ (show ggPermHom m (Equiv.swap k l) (ggQ2xS_t1v m i)
    = ggQ2xS_t1v m i from by
      rw [ggQ2xS_perm_t1v]
      congr 1
      exact Equiv.swap_apply_of_ne_of_ne hik hil)]

@[irreducible] private noncomputable def ggQ2xS_root (m : ℕ) (i j : Fin m) : ggQ2xS_GL m :=
  ggPermHom m (Equiv.swap i j)

@[irreducible] private noncomputable def ggQ2xS_type1 (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_GL m :=
  ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i)

private lemma ggQ2xS_type1_eq_t1v (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_type1 m hm i
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i) := by
  unfold ggQ2xS_type1
  rfl

private noncomputable def ggQ2xS_phiP (m : ℕ) (hm : m % 3 = 2) (i j : Fin (m + 1)) :
    ggQ2xS_GL m :=
  if hi : (i : ℕ) < m then
    if hj : (j : ℕ) < m then ggQ2xS_root m ⟨i, hi⟩ ⟨j, hj⟩
    else ggQ2xS_type1 m hm ⟨i, hi⟩
  else
    if hj : (j : ℕ) < m then ggQ2xS_type1 m hm ⟨j, hj⟩
    else 1

private lemma ggQ2xS_phiP_cc (m : ℕ) (hm : m % 3 = 2) (i j : Fin m) :
    ggQ2xS_phiP m hm (Fin.castSucc i) (Fin.castSucc j)
      = ggPermHom m (Equiv.swap i j) := by
  simp only [ggQ2xS_phiP, ggQ2xS_root, Fin.val_castSucc, dif_pos i.isLt, dif_pos j.isLt]

private lemma ggQ2xS_phiP_cl (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm (Fin.castSucc i) (Fin.last m)
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i) := by
  simp only [ggQ2xS_phiP, ggQ2xS_type1, Fin.val_castSucc, Fin.val_last, dif_pos i.isLt,
    dif_neg (lt_irrefl m)]

private lemma ggQ2xS_phiP_lc (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm (Fin.last m) (Fin.castSucc i)
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i) := by
  simp only [ggQ2xS_phiP, ggQ2xS_type1, Fin.val_castSucc, Fin.val_last, dif_neg (lt_irrefl m),
    dif_pos i.isLt]

private lemma ggQ2xS_phiP_cl_t1v (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm (Fin.castSucc i) (Fin.last m)
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i) :=
  ggQ2xS_phiP_cl m hm i

private lemma ggQ2xS_phiP_lc_t1v (m : ℕ) (hm : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm (Fin.last m) (Fin.castSucc i)
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm i) :=
  ggQ2xS_phiP_lc m hm i

private lemma ggQ2xS_phiP_comm (m : ℕ) (hm : m % 3 = 2) (i j : Fin (m + 1)) :
    ggQ2xS_phiP m hm i j = ggQ2xS_phiP m hm j i := by
  rcases ggQ2xS_fin_eq_castSucc_or_last i with ⟨i', rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last j with ⟨j', rfl⟩ | rfl
    · rw [ggQ2xS_phiP_cc, ggQ2xS_phiP_cc, Equiv.swap_comm]
    · rw [ggQ2xS_phiP_cl, ggQ2xS_phiP_lc]
  · rcases ggQ2xS_fin_eq_castSucc_or_last j with ⟨j', rfl⟩ | rfl
    · rw [ggQ2xS_phiP_lc, ggQ2xS_phiP_cl]
    · rfl

private lemma ggQ2xS_phiP_of_swap_eq {m : ℕ} (hm : m % 3 = 2) {a b c d : Fin (m + 1)}
    (hab : a ≠ b) (hcd : c ≠ d) (h : Equiv.swap a b = Equiv.swap c d) :
    ggQ2xS_phiP m hm a b = ggQ2xS_phiP m hm c d := by
  rcases (ggQ2xS_swap_eq_iff hab hcd).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [ggQ2xS_phiP_comm]

private def ggQ2xS_T (m : ℕ) : Set (ggQ2xS_GL m) :=
  ggBCReflSet (ggARoots m ∪ {z : GGBCV m | ggAType1 z})

private lemma ggQ2xS_one_add_single_mem_type1 {m : ℕ} (i : Fin m) :
    (1 + Pi.single i (1 : ZMod 3) : GGBCV m) ∈ {z | ggAType1 z} := by
  refine ⟨1, by decide, i, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
    decide
  · intro j hj
    simp only [Pi.add_apply, Pi.one_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]
    decide

private lemma ggQ2xS_t1v_mem_type1 {m : ℕ} (i : Fin m) :
    ggQ2xS_t1v m i ∈ {z : GGBCV m | ggAType1 z} := by
  unfold ggQ2xS_t1v
  exact ggQ2xS_one_add_single_mem_type1 i

private lemma ggQ2xS_reflSet_mem {m : ℕ} {S : Set (GGBCV m)} {c : GGBCV m} (hcS : c ∈ S)
    (hc : c ⬝ᵥ c ≠ 0) : ggBCRefl c hc ∈ ggBCReflSet S :=
  ⟨c, hcS, hc, rfl⟩

private lemma ggQ2xS_phiP_mem {m : ℕ} (hm : m % 3 = 2) {a b : Fin (m + 1)} (hab : a ≠ b) :
    ggQ2xS_phiP m hm a b ∈ ggQ2xS_T m := by
  change ggQ2xS_phiP m hm a b ∈
    ggBCReflSet (ggARoots m ∪ {z : GGBCV m | ggAType1 z})
  rcases ggQ2xS_fin_eq_castSucc_or_last a with ⟨i, rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, rfl⟩ | rfl
    · have hij : i ≠ j := fun h => hab (by rw [h])
      rw [ggQ2xS_phiP_cc, ggPermHom_swap i j hij (ggQ2xS_sub_single_norm_ne i j hij)]
      exact ggQ2xS_reflSet_mem
        (Or.inl ⟨ggQ2x_wt_sub_single i j hij, ggQ2xS_sum_sub_single i j⟩)
        (ggQ2xS_sub_single_norm_ne i j hij)
    · rw [ggQ2xS_phiP_cl]
      exact ggQ2xS_reflSet_mem
        (Or.inr (ggQ2xS_t1v_mem_type1 i))
        (ggQ2xS_t1v_norm_ne hm i)
  · rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, rfl⟩ | rfl
    · rw [ggQ2xS_phiP_lc]
      exact ggQ2xS_reflSet_mem
        (Or.inr (ggQ2xS_t1v_mem_type1 j))
        (ggQ2xS_t1v_norm_ne hm j)
    · exact absurd rfl hab

private lemma ggQ2xS_sum_single {m : ℕ} (k : Fin m) (a : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m)) i = a := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_pi_single', mul_one]

private lemma ggQ2xS_sum_pair {m : ℕ} (k l : Fin m) (a b : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m) + b • (Pi.single l 1 : GGBCV m)) i = a + b := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2xS_sum_single, ggQ2xS_sum_single]

private lemma ggQ2xS_weight_two {m : ℕ} {v : GGBCV m} (hv : ggBCWt v = 2) :
    ∃ (i j : Fin m) (a b : ZMod 3), i ≠ j ∧ a ≠ 0 ∧ b ≠ 0 ∧
      v = a • (Pi.single i 1 : GGBCV m) + b • (Pi.single j 1 : GGBCV m) := by
  unfold ggBCWt at hv
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hv
  have hvi : v i ≠ 0 := by
    have hmem : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  have hvj : v j ≠ 0 := by
    have hmem : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  refine ⟨i, j, v i, v j, hij, hvi, hvj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, smul_eq_mul, mul_one, mul_zero, add_zero]
  · by_cases hkj : k = j
    · subst hkj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), smul_eq_mul, mul_one,
        mul_zero, zero_add]
    · have hvk : v k = 0 := by
        by_contra hne
        have hmem : k ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hne]
        rw [hS] at hmem
        simp [hki, hkj] at hmem
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, smul_zero, smul_zero, add_zero]
      exact hvk

private lemma ggQ2xS_aroots_classify {m : ℕ} {v : GGBCV m} (hv : v ∈ ggARoots m) :
    ∃ (i j : Fin m), i ≠ j ∧ ∃ a : ZMod 3, a ≠ 0 ∧
      v = a • (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
  obtain ⟨hw, hsum⟩ := hv
  obtain ⟨i, j, a, b, hij, ha, hb, hvij⟩ := ggQ2xS_weight_two hw
  have hab : a + b = 0 := by
    rw [hvij] at hsum
    rw [ggQ2xS_sum_pair] at hsum
    exact hsum
  refine ⟨i, j, hij, a, ha, ?_⟩
  have hb_eq : b = -a := (neg_eq_of_add_eq_zero_right hab).symm
  rw [hvij, hb_eq, smul_sub, sub_eq_add_neg]
  congr 1
  exact neg_smul a (Pi.single j 1 : GGBCV m)

private lemma ggQ2xS_type1_classify {m : ℕ} {z : GGBCV m} (hz : ggAType1 z) :
    ∃ (c : ZMod 3), c ≠ 0 ∧ ∃ i : Fin m,
      z = c • (1 + Pi.single i (1 : ZMod 3) : GGBCV m) := by
  obtain ⟨c, hc, i, hzi, hzj⟩ := hz
  refine ⟨c, hc, i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst hji
    rw [hzi]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, Pi.single_eq_same, smul_eq_mul]
    exact (by decide : ∀ c : ZMod 3, -c = c * 2) c
  · rw [hzj j hji]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji, smul_eq_mul, add_zero, mul_one]

private lemma ggQ2xS_type1_classify_v {m : ℕ} {z : GGBCV m} (hz : ggAType1 z) :
    ∃ (c : ZMod 3), c ≠ 0 ∧ ∃ i : Fin m, z = c • ggQ2xS_t1v m i := by
  obtain ⟨c, hc, i, hceq⟩ := ggQ2xS_type1_classify hz
  refine ⟨c, hc, i, ?_⟩
  rw [hceq]
  congr 1
  unfold ggQ2xS_t1v
  rfl

private lemma ggQ2xS_mem_param {m : ℕ} (hm : m % 3 = 2) {t : ggQ2xS_GL m}
    (ht : t ∈ ggQ2xS_T m) : ∃ a b : Fin (m + 1), a ≠ b ∧ t = ggQ2xS_phiP m hm a b := by
  rw [ggQ2xS_T] at ht
  obtain ⟨c, hcS, hc, rfl⟩ := ht
  rcases hcS with hcroot | hctype
  · obtain ⟨i, j, hij, a, ha, hceq⟩ := ggQ2xS_aroots_classify hcroot
    subst hceq
    refine ⟨Fin.castSucc i, Fin.castSucc j, ggQ2xS_castSucc_ne_castSucc hij, ?_⟩
    have hfij := ggQ2xS_sub_single_norm_ne i j hij
    rw [ggQ2xS_phiP_cc, ggPermHom_swap i j hij hfij]
    exact ggQ2xS_refl_smul a ha _ hfij hc
  · obtain ⟨c0, hc0, i, hceq⟩ := ggQ2xS_type1_classify_v hctype
    subst hceq
    refine ⟨Fin.last m, Fin.castSucc i, ggQ2xS_last_ne_castSucc i, ?_⟩
    have hfij := ggQ2xS_t1v_norm_ne hm i
    rw [ggQ2xS_phiP_lc]
    exact ggQ2xS_refl_smul c0 hc0 (ggQ2xS_t1v m i) hfij hc


private lemma ggQ2xS_wt_neg {m : ℕ} (v : GGBCV m) : ggBCWt (-v) = ggBCWt v := by
  unfold ggBCWt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
  constructor
  · intro h hv
    exact h (by rw [hv]; exact neg_zero)
  · intro h hv
    exact h (neg_eq_zero.mp hv)

private lemma ggQ2xS_wt_t1 {m : ℕ} (i : Fin m) :
    ggBCWt (1 + Pi.single i (1 : ZMod 3) : GGBCV m) = m := by
  apply ggQ2x_wt_eq_of_full
  intro j
  by_cases hji : j = i
  · subst hji
    simp only [Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
    decide
  · simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji]

private lemma ggQ2xS_wt_t1v {m : ℕ} (i : Fin m) : ggBCWt (ggQ2xS_t1v m i) = m := by
  unfold ggQ2xS_t1v
  exact ggQ2xS_wt_t1 i

private lemma ggQ2xS_exists_fresh {m : ℕ} (hm : 3 ≤ m) (i k : Fin m) :
    ∃ t : Fin m, t ≠ i ∧ t ≠ k := by
  have hcard : ({i, k} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    calc ({i, k} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
      _ < m := by omega
      _ = (Finset.univ : Finset (Fin m)).card := by rw [Finset.card_univ, Fintype.card_fin]
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨t, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ht⟩

private lemma ggQ2xS_refl_eq_refl {m : ℕ} {c d : GGBCV m} (hc : c ⬝ᵥ c ≠ 0)
    (hd : d ⬝ᵥ d ≠ 0) (h : ggBCRefl c hc = ggBCRefl d hd) : d = c ∨ d = -c := by
  have h1 := congrArg (fun e => e c) h
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply] at h1
  have hcc : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := ggQ2x_mul_self_eq_one _ hc
  rw [hcc, one_smul] at h1
  set t : ZMod 3 := (d ⬝ᵥ c) * (d ⬝ᵥ d) with ht
  have h2 : t • d = c := (add_left_cancel h1).symm
  have ht_ne : t ≠ 0 := by
    intro ht0
    have hc0 : c = 0 := by rw [← h2, ht0, zero_smul]
    exact hc (by rw [hc0]; exact zero_dotProduct (0 : GGBCV m))
  have ht_sq : t * t = 1 := ggQ2x_mul_self_eq_one t ht_ne
  have hdc : d = t • c := by
    calc d = (1 : ZMod 3) • d := (one_smul _ _).symm
      _ = (t⁻¹ * t) • d := by rw [inv_mul_cancel₀ ht_ne]
      _ = t⁻¹ • (t • d) := (smul_smul _ _ _).symm
      _ = t⁻¹ • c := by rw [h2]
      _ = t • c := by rw [inv_eq_of_mul_eq_one_right ht_sq]
  obtain ht1 | htn | ht0 := (by decide : ∀ x : ZMod 3, x = 1 ∨ x = -1 ∨ x = 0) t
  · left; rw [hdc, ht1, one_smul]
  · right; rw [hdc, htn]
    exact neg_one_smul (R := ZMod 3) (x := c)
  · exact absurd ht0 ht_ne

private lemma ggQ2xS_type1_eq_of_eq {m : ℕ} {i k : Fin m}
    (h : (1 + Pi.single i (1 : ZMod 3) : GGBCV m)
      = (1 + Pi.single k (1 : ZMod 3))) : i = k := by
  have h' : (Pi.single i (1 : ZMod 3) : GGBCV m) = Pi.single k 1 := add_left_cancel h
  have hk := congrFun h' k
  rw [Pi.single_eq_same] at hk
  by_contra hik
  rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik)] at hk
  exact (by decide : (1 : ZMod 3) ≠ 0) hk.symm

private lemma ggQ2xS_type1_ne_neg {m : ℕ} (hm : 3 ≤ m) {i k : Fin m}
    (h : (1 + Pi.single k (1 : ZMod 3) : GGBCV m)
      = -(1 + Pi.single i (1 : ZMod 3))) : False := by
  obtain ⟨t, hti, htk⟩ := ggQ2xS_exists_fresh hm i k
  have ht := congrFun h t
  simp only [Pi.neg_apply, Pi.add_apply, Pi.one_apply,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) htk,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hti] at ht
  exact (by decide : (1 : ZMod 3) ≠ -1) ht

private lemma ggQ2xS_type1_eq_of_eq_v {m : ℕ} {i k : Fin m}
    (h : ggQ2xS_t1v m i = ggQ2xS_t1v m k) : i = k := by
  unfold ggQ2xS_t1v at h
  exact ggQ2xS_type1_eq_of_eq h

private lemma ggQ2xS_type1_ne_neg_v {m : ℕ} (hm : 3 ≤ m) {i k : Fin m}
    (h : ggQ2xS_t1v m k = -(ggQ2xS_t1v m i)) : False := by
  unfold ggQ2xS_t1v at h
  exact ggQ2xS_type1_ne_neg hm h

private lemma ggQ2xS_phiP_inj {m : ℕ} (hm8 : 8 ≤ m) (hm3 : m % 3 = 2)
    {a b c d : Fin (m + 1)} (hab : a ≠ b) (hcd : c ≠ d)
    (h : ggQ2xS_phiP m hm3 a b = ggQ2xS_phiP m hm3 c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hm3' : 3 ≤ m := by omega
  rcases ggQ2xS_fin_eq_castSucc_or_last a with ⟨i, rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, rfl⟩ | rfl
    · have hij : i ≠ j := fun hh => hab (by rw [hh])
      rcases ggQ2xS_fin_eq_castSucc_or_last c with ⟨k, rfl⟩ | rfl
      · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
        · rw [ggQ2xS_phiP_cc, ggQ2xS_phiP_cc] at h
          have hkl : k ≠ l := fun hh => hcd (by rw [hh])
          have hswap : Equiv.swap i j = Equiv.swap k l := ggPermHom_injective m h
          rcases (ggQ2xS_swap_eq_iff hij hkl).mp hswap with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
          · exact Or.inl ⟨by rw [hik], by rw [hjl]⟩
          · exact Or.inr ⟨by rw [hil], by rw [hjk]⟩
        · exfalso
          rw [ggQ2xS_phiP_cc] at h
          rw [ggQ2xS_phiP_cl] at h
          rw [ggPermHom_swap i j hij (ggQ2xS_sub_single_norm_ne i j hij)] at h
          have hline := ggQ2xS_refl_eq_refl (ggQ2xS_sub_single_norm_ne i j hij)
            (ggQ2xS_t1v_norm_ne hm3 k) h
          have hwt : ggBCWt (ggQ2xS_t1v m k)
              = ggBCWt (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) := by
            rcases hline with h' | h'
            · rw [h']
            · rw [h', ggQ2xS_wt_neg]
          rw [ggQ2xS_wt_t1v, ggQ2x_wt_sub_single i j hij] at hwt
          omega
      · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
        · exfalso
          rw [ggQ2xS_phiP_cc] at h
          rw [ggQ2xS_phiP_lc] at h
          rw [ggPermHom_swap i j hij (ggQ2xS_sub_single_norm_ne i j hij)] at h
          have hline := ggQ2xS_refl_eq_refl (ggQ2xS_sub_single_norm_ne i j hij)
            (ggQ2xS_t1v_norm_ne hm3 l) h
          have hwt : ggBCWt (ggQ2xS_t1v m l)
              = ggBCWt (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) := by
            rcases hline with h' | h'
            · rw [h']
            · rw [h', ggQ2xS_wt_neg]
          rw [ggQ2xS_wt_t1v, ggQ2x_wt_sub_single i j hij] at hwt
          omega
        · exact absurd rfl hcd
    · rcases ggQ2xS_fin_eq_castSucc_or_last c with ⟨k, rfl⟩ | rfl
      · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
        · exfalso
          rw [ggQ2xS_phiP_cl] at h
          rw [ggQ2xS_phiP_cc] at h
          rw [ggPermHom_swap k l (fun hh => hcd (by rw [hh]))
            (ggQ2xS_sub_single_norm_ne k l (fun hh => hcd (by rw [hh])))] at h
          have hkl : k ≠ l := fun hh => hcd (by rw [hh])
          have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 i)
            (ggQ2xS_sub_single_norm_ne k l hkl) h
          have hwt : ggBCWt (ggQ2xS_t1v m i)
              = ggBCWt (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) := by
            rcases hline with h' | h'
            · rw [h']
            · rw [h', ggQ2xS_wt_neg]
          rw [ggQ2xS_wt_t1v, ggQ2x_wt_sub_single k l hkl] at hwt
          omega
        · rw [ggQ2xS_phiP_cl, ggQ2xS_phiP_cl] at h
          have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 i)
            (ggQ2xS_t1v_norm_ne hm3 k) h
          rcases hline with h' | h'
          · have hik : k = i := ggQ2xS_type1_eq_of_eq_v h'
            exact Or.inl ⟨by rw [hik], rfl⟩
          · exact (ggQ2xS_type1_ne_neg_v hm3' h').elim
      · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
        · rw [ggQ2xS_phiP_cl, ggQ2xS_phiP_lc] at h
          have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 i)
            (ggQ2xS_t1v_norm_ne hm3 l) h
          rcases hline with h' | h'
          · have hli : l = i := ggQ2xS_type1_eq_of_eq_v h'
            exact Or.inr ⟨by rw [hli], rfl⟩
          · exact (ggQ2xS_type1_ne_neg_v hm3' h').elim
        · exact absurd rfl hcd
  · have hb : ∃ j : Fin m, b = Fin.castSucc j := by
      rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, hj⟩ | hb
      · exact ⟨j, hj⟩
      · exact absurd hb.symm hab
    obtain ⟨j, rfl⟩ := hb
    rcases ggQ2xS_fin_eq_castSucc_or_last c with ⟨k, rfl⟩ | rfl
    · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
      · exfalso
        rw [ggQ2xS_phiP_lc] at h
        rw [ggQ2xS_phiP_cc] at h
        rw [ggPermHom_swap k l (fun hh => hcd (by rw [hh]))
          (ggQ2xS_sub_single_norm_ne k l (fun hh => hcd (by rw [hh])))] at h
        have hkl : k ≠ l := fun hh => hcd (by rw [hh])
        have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 j)
          (ggQ2xS_sub_single_norm_ne k l hkl) h
        have hwt : ggBCWt (ggQ2xS_t1v m j)
            = ggBCWt (Pi.single k (1 : ZMod 3) - Pi.single l (1 : ZMod 3) : GGBCV m) := by
          rcases hline with h' | h'
          · rw [h']
          · rw [h', ggQ2xS_wt_neg]
        rw [ggQ2xS_wt_t1v, ggQ2x_wt_sub_single k l hkl] at hwt
        omega
      · rw [ggQ2xS_phiP_lc, ggQ2xS_phiP_cl] at h
        have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 j)
          (ggQ2xS_t1v_norm_ne hm3 k) h
        rcases hline with h' | h'
        · have hkj : k = j := ggQ2xS_type1_eq_of_eq_v h'
          exact Or.inr ⟨rfl, by rw [hkj]⟩
        · exact (ggQ2xS_type1_ne_neg_v hm3' h').elim
    · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
      · rw [ggQ2xS_phiP_lc, ggQ2xS_phiP_lc] at h
        have hline := ggQ2xS_refl_eq_refl (ggQ2xS_t1v_norm_ne hm3 j)
          (ggQ2xS_t1v_norm_ne hm3 l) h
        rcases hline with h' | h'
        · have hlj : l = j := ggQ2xS_type1_eq_of_eq_v h'
          exact Or.inl ⟨rfl, by rw [hlj]⟩
        · exact (ggQ2xS_type1_ne_neg_v hm3' h').elim
      · exact absurd rfl hcd


private lemma ggQ2xS_quandle_cc {m : ℕ} (hm3 : m % 3 = 2) {i j : Fin m} (hij : i ≠ j)
    (c d : Fin (m + 1)) (hcd : c ≠ d) :
    ggQ2xS_phiP m hm3 (Fin.castSucc i) (Fin.castSucc j) * ggQ2xS_phiP m hm3 c d *
        (ggQ2xS_phiP m hm3 (Fin.castSucc i) (Fin.castSucc j))⁻¹
      = ggQ2xS_phiP m hm3
          ((Equiv.swap (Fin.castSucc i) (Fin.castSucc j)) c)
          ((Equiv.swap (Fin.castSucc i) (Fin.castSucc j)) d) := by
  rcases ggQ2xS_fin_eq_castSucc_or_last c with ⟨k, rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
    · rw [ggQ2xS_phiP_cc, ggQ2xS_phiP_cc, ggQ2xS_swap_castSucc, ggQ2xS_swap_castSucc,
        ggQ2xS_phiP_cc]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [Equiv.swap_apply_apply]
    · rw [ggQ2xS_phiP_cc, ggQ2xS_phiP_cl, ggQ2xS_swap_castSucc, ggQ2xS_swap_castSucc_last,
        ggQ2xS_phiP_cl]
      rw [ggQ2xS_conj_refl (ggPermHom m (Equiv.swap i j)) (ggQ2xS_perm_isometry m _) _ _]
      simp only [ggQ2xS_perm_t1v]
  · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
    · rw [ggQ2xS_phiP_cc, ggQ2xS_phiP_lc, ggQ2xS_swap_castSucc, ggQ2xS_swap_castSucc_last,
        ggQ2xS_phiP_lc]
      rw [ggQ2xS_conj_refl (ggPermHom m (Equiv.swap i j)) (ggQ2xS_perm_isometry m _) _ _]
      simp only [ggQ2xS_perm_t1v]
    · exact absurd rfl hcd

private lemma ggQ2xS_quandle_T_ii {m : ℕ} (hm3 : m % 3 = 2) {i l : Fin m} (hil : i ≠ l) :
    ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) *
        ggQ2xS_phiP m hm3 (Fin.castSucc i) (Fin.castSucc l) *
        (ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i))⁻¹
      = ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc l) := by
  rw [ggQ2xS_phiP_lc_t1v, ggQ2xS_phiP_cc, ggQ2xS_phiP_lc_t1v]
  rw [ggQ2xS_rv_perm (m := m) i l hil]
  have hb := ggQ2xS_refl_isometry (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)
  have hc' : (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_rv m i l)) ⬝ᵥ
      (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_rv m i l)) ≠ 0 := by
    rw [hb]; exact ggQ2xS_rv_norm_ne i l hil
  have hconj := @ggQ2xS_conj_refl' m (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)) hb
    (ggQ2xS_rv m i l) (ggQ2xS_rv_norm_ne i l hil) hc'
  rw [hconj]
  rw [ggQ2xS_refl_congr _ _ (ggQ2xS_refl_t1v_rv hm3 i l hil)]
  exact ggQ2xS_refl_neg (ggQ2xS_t1v m l) (ggQ2xS_t1v_norm_ne hm3 l)
    (by rw [ggQ2xS_dot_neg]; exact ggQ2xS_t1v_norm_ne hm3 l)

private lemma ggQ2xS_quandle_T_self {m : ℕ} (hm3 : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) *
        ggQ2xS_phiP m hm3 (Fin.castSucc i) (Fin.last m) *
        (ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i))⁻¹
      = ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) := by
  rw [ggQ2xS_phiP_comm m hm3 (Fin.castSucc i) (Fin.last m)]
  group

private lemma ggQ2xS_quandle_T_self' {m : ℕ} (hm3 : m % 3 = 2) (i : Fin m) :
    ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) *
        ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) *
        (ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i))⁻¹
      = ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) := by
  group

private lemma ggQ2xS_quandle_T_t1 {m : ℕ} (hm3 : m % 3 = 2) {i k : Fin m} (hik : i ≠ k) :
    ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) *
        ggQ2xS_phiP m hm3 (Fin.castSucc k) (Fin.last m) *
        (ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i))⁻¹
      = ggQ2xS_phiP m hm3 (Fin.castSucc k) (Fin.castSucc i) := by
  rw [ggQ2xS_phiP_lc_t1v, ggQ2xS_phiP_cl_t1v, ggQ2xS_phiP_cc,
    ggQ2xS_rv_perm (m := m) (i := k) (l := i) (fun h => hik h.symm)]
  have hb := ggQ2xS_refl_isometry (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)
  have hc' : (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_t1v m k)) ⬝ᵥ
      (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) (ggQ2xS_t1v m k)) ≠ 0 := by
    rw [hb]; exact ggQ2xS_t1v_norm_ne hm3 k
  have hconj := @ggQ2xS_conj_refl' m (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)) hb
    (ggQ2xS_t1v m k) (ggQ2xS_t1v_norm_ne hm3 k) hc'
  rw [hconj]
  rw [ggQ2xS_refl_congr _ _ (ggQ2xS_refl_t1v_type1 hm3 i k hik)]

private lemma ggQ2xS_quandle_T {m : ℕ} (hm3 : m % 3 = 2) (i : Fin m)
    (c d : Fin (m + 1)) (hcd : c ≠ d) :
    ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i) * ggQ2xS_phiP m hm3 c d *
        (ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i))⁻¹
      = ggQ2xS_phiP m hm3
          ((Equiv.swap (Fin.last m) (Fin.castSucc i)) c)
          ((Equiv.swap (Fin.last m) (Fin.castSucc i)) d) := by
  rcases ggQ2xS_fin_eq_castSucc_or_last c with ⟨k, rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
    · have hkl : k ≠ l := fun h => hcd (by rw [h])
      by_cases hki : k = i
      · subst k
        rw [ggQ2xS_swap_last_castSucc, ggQ2xS_swap_last_castSucc, if_pos rfl,
          if_neg (fun h => hkl (by rw [h]))]
        exact ggQ2xS_quandle_T_ii hm3 hkl
      · by_cases hli : l = i
        · subst l
          have hik : i ≠ k := fun h => hki h.symm
          rw [ggQ2xS_swap_last_castSucc, ggQ2xS_swap_last_castSucc, if_neg hki,
            if_pos rfl]
          rw [← ggQ2xS_phiP_comm m hm3 (Fin.castSucc i) (Fin.castSucc k),
            ggQ2xS_phiP_comm m hm3 (Fin.castSucc k) (Fin.last m)]
          exact ggQ2xS_quandle_T_ii hm3 hik
        · have hik : i ≠ k := fun h => hki h.symm
          have hil : i ≠ l := fun h => hli h.symm
          rw [ggQ2xS_swap_last_castSucc, ggQ2xS_swap_last_castSucc, if_neg hki,
            if_neg hli]
          rw [show ggQ2xS_phiP m hm3 (Fin.last m) (Fin.castSucc i)
              = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) from
              ggQ2xS_phiP_lc_t1v m hm3 i,
            show ggQ2xS_phiP m hm3 (Fin.castSucc k) (Fin.castSucc l)
              = ggPermHom m (Equiv.swap k l) from ggQ2xS_phiP_cc m hm3 k l]
          have hcomm := ggQ2xS_perm_t1v_comm hm3 hik hil
          have hbs : ggPermHom m (Equiv.swap k l) *
              ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i)
              = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) *
                ggPermHom m (Equiv.swap k l) := by
            have h := congrArg (fun x => x * ggPermHom m (Equiv.swap k l)) hcomm
            simpa [mul_assoc] using h
          have hsi2 : ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) *
              ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) = 1 := by
            simpa [ggQ2xS_refl_inv] using
              mul_inv_cancel (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i))
          rw [show (ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i))⁻¹
      = ggBCRefl (ggQ2xS_t1v m i) (ggQ2xS_t1v_norm_ne hm3 i) from
      ggQ2xS_refl_inv _ _, ← hbs, mul_assoc, hsi2, mul_one]
    · by_cases hki : k = i
      · subst k
        rw [ggQ2xS_swap_last_castSucc, Equiv.swap_apply_left, if_pos rfl]
        exact ggQ2xS_quandle_T_self hm3 i
      · rw [ggQ2xS_swap_last_castSucc, Equiv.swap_apply_left, if_neg hki]
        exact ggQ2xS_quandle_T_t1 hm3 (fun h => hki h.symm)
  · rcases ggQ2xS_fin_eq_castSucc_or_last d with ⟨l, rfl⟩ | rfl
    · by_cases hli : l = i
      · subst l
        rw [Equiv.swap_apply_left, ggQ2xS_swap_last_castSucc, if_pos rfl,
          ggQ2xS_phiP_comm m hm3 (Fin.castSucc i) (Fin.last m)]
        exact ggQ2xS_quandle_T_self' hm3 i
      · have hil : i ≠ l := fun h => hli h.symm
        rw [Equiv.swap_apply_left, ggQ2xS_swap_last_castSucc, if_neg hli,
          ggQ2xS_phiP_comm m hm3 (Fin.last m) (Fin.castSucc l),
          ← ggQ2xS_phiP_comm m hm3 (Fin.castSucc l) (Fin.castSucc i)]
        exact ggQ2xS_quandle_T_t1 hm3 hil
    · exact absurd rfl hcd

private lemma ggQ2xS_quandle {m : ℕ} (hm3 : m % 3 = 2) {a b c d : Fin (m + 1)}
    (hab : a ≠ b) (hcd : c ≠ d) :
    ggQ2xS_phiP m hm3 a b * ggQ2xS_phiP m hm3 c d * (ggQ2xS_phiP m hm3 a b)⁻¹
      = ggQ2xS_phiP m hm3 ((Equiv.swap a b) c) ((Equiv.swap a b) d) := by
  rcases ggQ2xS_fin_eq_castSucc_or_last a with ⟨i, rfl⟩ | rfl
  · rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, rfl⟩ | rfl
    · exact ggQ2xS_quandle_cc hm3 (fun hh => hab (by rw [hh])) c d hcd
    · rw [ggQ2xS_phiP_comm m hm3 (Fin.castSucc i) (Fin.last m),
        Equiv.swap_comm (Fin.castSucc i) (Fin.last m)]
      exact ggQ2xS_quandle_T hm3 i c d hcd
  · rcases ggQ2xS_fin_eq_castSucc_or_last b with ⟨j, rfl⟩ | rfl
    · exact ggQ2xS_quandle_T hm3 j c d hcd
    · exact absurd rfl hab

private lemma ggQ2xS_exists_conj {m : ℕ} (hm3 : m % 3 = 2)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ g ∈ ggBCReflGp (ggARoots m ∪ {z : GGBCV m | ggAType1 z}),
      ∀ a b : Fin (m + 1), a ≠ b →
        g * ggQ2xS_phiP m hm3 a b * g⁻¹ = ggQ2xS_phiP m hm3 (σ a) (σ b) := by
  let G : Subgroup (ggQ2xS_GL m) :=
    ggBCReflGp (ggARoots m ∪ {z : GGBCV m | ggAType1 z})
  let S : Subgroup (Equiv.Perm (Fin (m + 1))) :=
    { carrier := {τ | ∃ g ∈ G, ∀ a b, a ≠ b →
        g * ggQ2xS_phiP m hm3 a b * g⁻¹ = ggQ2xS_phiP m hm3 (τ a) (τ b)}
      one_mem' := by
        refine ⟨1, G.one_mem, ?_⟩
        intro a b _
        simp
      mul_mem' := by
        rintro σ τ ⟨g, hg, hg'⟩ ⟨h, hh, hh'⟩
        refine ⟨g * h, G.mul_mem hg hh, ?_⟩
        intro a b hab
        have hτ : τ a ≠ τ b := fun hh2 => hab (τ.injective hh2)
        rw [show (g * h) * ggQ2xS_phiP m hm3 a b * (g * h)⁻¹
            = g * (h * ggQ2xS_phiP m hm3 a b * h⁻¹) * g⁻¹ by group]
        rw [hh' a b hab, hg' (τ a) (τ b) hτ]
        rfl
      inv_mem' := by
        rintro σ ⟨g, hg, hg'⟩
        refine ⟨g⁻¹, G.inv_mem hg, ?_⟩
        intro a b hab
        have hσ : σ⁻¹ a ≠ σ⁻¹ b := fun hh2 => hab (by
          have := congrArg σ hh2
          simpa using this)
        have h1 := hg' (σ⁻¹ a) (σ⁻¹ b) hσ
        have h1' : g * ggQ2xS_phiP m hm3 (σ⁻¹ a) (σ⁻¹ b) * g⁻¹
            = ggQ2xS_phiP m hm3 a b := by
          rw [h1, show σ (σ⁻¹ a) = a from Equiv.apply_symm_apply σ a,
            show σ (σ⁻¹ b) = b from Equiv.apply_symm_apply σ b]
        have h2 : ggQ2xS_phiP m hm3 (σ⁻¹ a) (σ⁻¹ b)
            = g⁻¹ * ggQ2xS_phiP m hm3 a b * g := by
          calc ggQ2xS_phiP m hm3 (σ⁻¹ a) (σ⁻¹ b)
              = g⁻¹ * (g * ggQ2xS_phiP m hm3 (σ⁻¹ a) (σ⁻¹ b) * g⁻¹) * g := by
                group
            _ = g⁻¹ * ggQ2xS_phiP m hm3 a b * g := by rw [h1']
        rw [h2, inv_inv] }
  have htop : S = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro τ ⟨a, b, hab, rfl⟩
    refine ⟨ggQ2xS_phiP m hm3 a b, Subgroup.subset_closure (ggQ2xS_phiP_mem hm3 hab), ?_⟩
    intro c d hcd
    exact ggQ2xS_quandle hm3 hab hcd
  have hσ : σ ∈ S := by rw [htop]; exact Subgroup.mem_top σ
  obtain ⟨g, hg, hg'⟩ := hσ
  exact ⟨g, hg, hg'⟩

theorem ggQ2_A_inner_sym (m : ℕ) (hm : 8 ≤ m) (h2 : m % 3 = 2) :
    GGQ2QuandleInner (ggBCReflSet (ggARoots m ∪ {z | ggAType1 z}))
      (ggBCReflGp (ggARoots m ∪ {z | ggAType1 z})) := by
  classical
  intro π hπT hinj hπ
  have hm3 : m % 3 = 2 := h2
  have hk : 5 ≤ m + 1 := by omega
  let pairOf : (a b : Fin (m + 1)) → a ≠ b → Fin (m + 1) × Fin (m + 1) :=
    fun a b hab =>
      (Classical.choose (ggQ2xS_mem_param hm3 (hπT _ (ggQ2xS_phiP_mem hm3 hab))),
        Classical.choose (Classical.choose_spec
          (ggQ2xS_mem_param hm3 (hπT _ (ggQ2xS_phiP_mem hm3 hab)))))
  have pairOf_spec : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      (pairOf a b hab).1 ≠ (pairOf a b hab).2 ∧
      π (ggQ2xS_phiP m hm3 a b)
        = ggQ2xS_phiP m hm3 (pairOf a b hab).1 (pairOf a b hab).2 :=
    fun a b hab => by
      have h := ggQ2xS_mem_param hm3 (hπT _ (ggQ2xS_phiP_mem hm3 hab))
      change (Classical.choose h) ≠ Classical.choose (Classical.choose_spec h) ∧
        π (ggQ2xS_phiP m hm3 a b)
          = ggQ2xS_phiP m hm3 (Classical.choose h)
              (Classical.choose (Classical.choose_spec h))
      exact Classical.choose_spec (Classical.choose_spec h)
  let swapPair : (τ : Equiv.Perm (Fin (m + 1))) → τ.IsSwap → Fin (m + 1) × Fin (m + 1) :=
    fun τ h => (Classical.choose h, Classical.choose (Classical.choose_spec h))
  have swapPair_spec : ∀ (τ : Equiv.Perm (Fin (m + 1))) (h : τ.IsSwap),
      (swapPair τ h).1 ≠ (swapPair τ h).2 ∧
        τ = Equiv.swap (swapPair τ h).1 (swapPair τ h).2 :=
    fun τ h => Classical.choose_spec (Classical.choose_spec h)
  let pairSwap : (a b : Fin (m + 1)) → a ≠ b → Equiv.Perm (Fin (m + 1)) :=
    fun a b hab => Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2
  have pairSwap_eq : ∀ {a b c d : Fin (m + 1)} (hab : a ≠ b) (hcd : c ≠ d),
      ggQ2xS_phiP m hm3 a b = ggQ2xS_phiP m hm3 c d → pairSwap a b hab = pairSwap c d hcd := by
    intro a b c d hab hcd heq
    have h1 := (pairOf_spec a b hab).2
    have h2' := (pairOf_spec c d hcd).2
    have h3 : ggQ2xS_phiP m hm3 (pairOf a b hab).1 (pairOf a b hab).2
        = ggQ2xS_phiP m hm3 (pairOf c d hcd).1 (pairOf c d hcd).2 := by
      rw [← h1, heq, h2']
    rcases ggQ2xS_phiP_inj hm hm3 (pairOf_spec a b hab).1 (pairOf_spec c d hcd).1 h3 with
      ⟨e1, e2⟩ | ⟨e1, e2⟩
    · dsimp only [pairSwap]; rw [e1, e2]
    · dsimp only [pairSwap]; rw [e1, e2, Equiv.swap_comm]
  let π' : Equiv.Perm (Fin (m + 1)) → Equiv.Perm (Fin (m + 1)) := fun τ =>
    if h : τ.IsSwap then pairSwap (swapPair τ h).1 (swapPair τ h).2 (swapPair_spec τ h).1
    else τ
  have π'_swap : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      π' (Equiv.swap a b) = pairSwap a b hab := by
    intro a b hab
    have h : (Equiv.swap a b).IsSwap := ⟨a, b, hab, rfl⟩
    have hfun : π' (Equiv.swap a b)
        = pairSwap (swapPair (Equiv.swap a b) h).1 (swapPair (Equiv.swap a b) h).2
          (swapPair_spec (Equiv.swap a b) h).1 := dif_pos h
    rw [hfun]
    exact pairSwap_eq (swapPair_spec (Equiv.swap a b) h).1 hab
      (ggQ2xS_phiP_of_swap_eq hm3 (swapPair_spec (Equiv.swap a b) h).1 hab
        ((swapPair_spec (Equiv.swap a b) h).2.symm))
  have hπ'T : ∀ t ∈ ggTransp (m + 1), π' t ∈ ggTransp (m + 1) := by
    rintro t ⟨a, b, hab, rfl⟩
    rw [π'_swap a b hab]
    exact ⟨_, _, (pairOf_spec a b hab).1, rfl⟩
  have hinj' : Set.InjOn π' (ggTransp (m + 1)) := by
    rintro _ ⟨a, b, hab, rfl⟩ _ ⟨c, d, hcd, rfl⟩ hEq
    rw [π'_swap a b hab, π'_swap c d hcd] at hEq
    have hpa : (pairOf a b hab).1 ≠ (pairOf a b hab).2 := (pairOf_spec a b hab).1
    have hpc : (pairOf c d hcd).1 ≠ (pairOf c d hcd).2 := (pairOf_spec c d hcd).1
    have hswap : Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2
        = Equiv.swap (pairOf c d hcd).1 (pairOf c d hcd).2 := hEq
    have hphi : ggQ2xS_phiP m hm3 (pairOf a b hab).1 (pairOf a b hab).2
        = ggQ2xS_phiP m hm3 (pairOf c d hcd).1 (pairOf c d hcd).2 :=
      ggQ2xS_phiP_of_swap_eq hm3 hpa hpc hswap
    have hπeq : π (ggQ2xS_phiP m hm3 a b) = π (ggQ2xS_phiP m hm3 c d) := by
      rw [(pairOf_spec a b hab).2, (pairOf_spec c d hcd).2, hphi]
    have hphi2 : ggQ2xS_phiP m hm3 a b = ggQ2xS_phiP m hm3 c d :=
      hinj (ggQ2xS_phiP_mem hm3 hab) (ggQ2xS_phiP_mem hm3 hcd) hπeq
    rcases ggQ2xS_phiP_inj hm hm3 hab hcd hphi2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Equiv.swap_comm]
  have hπ' : ∀ s ∈ ggTransp (m + 1), ∀ t ∈ ggTransp (m + 1),
      π' (s * t * s⁻¹) = π' s * π' t * (π' s)⁻¹ := by
    rintro _ ⟨a, b, hab, rfl⟩ _ ⟨c, d, hcd, rfl⟩
    have hscd : (Equiv.swap a b) c ≠ (Equiv.swap a b) d :=
      fun hh => hcd ((Equiv.swap a b).injective hh)
    rw [← Equiv.swap_apply_apply, π'_swap _ _ hscd, π'_swap a b hab, π'_swap c d hcd]
    have hpa : (pairOf a b hab).1 ≠ (pairOf a b hab).2 := (pairOf_spec a b hab).1
    have hpc : (pairOf c d hcd).1 ≠ (pairOf c d hcd).2 := (pairOf_spec c d hcd).1
    have hdist : (Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).1
        ≠ (Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).2 :=
      fun hh => hpc ((Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2).injective hh)
    have hphi : ggQ2xS_phiP m hm3
          (pairOf ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).1
          (pairOf ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).2
        = ggQ2xS_phiP m hm3
            ((Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).1)
            ((Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).2) := by
      rw [← (pairOf_spec ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).2]
      rw [← ggQ2xS_quandle hm3 hab hcd]
      rw [hπ _ (ggQ2xS_phiP_mem hm3 hab) _ (ggQ2xS_phiP_mem hm3 hcd)]
      rw [(pairOf_spec a b hab).2, (pairOf_spec c d hcd).2]
      rw [ggQ2xS_quandle hm3 hpa hpc]
    have hR : pairSwap a b hab * pairSwap c d hcd * (pairSwap a b hab)⁻¹
        = Equiv.swap ((Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).1)
            ((Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2) (pairOf c d hcd).2) := by
      dsimp only [pairSwap]
      rw [← Equiv.swap_apply_apply]
    have hL : pairSwap ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd
        = Equiv.swap (pairOf ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).1
            (pairOf ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).2 := rfl
    rw [hR, hL]
    rcases ggQ2xS_phiP_inj hm hm3
        (pairOf_spec ((Equiv.swap a b) c) ((Equiv.swap a b) d) hscd).1 hdist hphi with
      ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Equiv.swap_comm]
  obtain ⟨g', hg'⟩ := ggQ2_quandle_aut_sym (m + 1) hk π' hπ'T hinj' hπ'
  obtain ⟨g, hgG, hgconj⟩ := ggQ2xS_exists_conj hm3 g'
  refine ⟨g, hgG, ?_⟩
  intro t ht
  obtain ⟨a, b, hab, rfl⟩ := ggQ2xS_mem_param hm3 ht
  have h1 := (pairOf_spec a b hab).2
  have h2' := hg' (Equiv.swap a b) ⟨a, b, hab, rfl⟩
  rw [π'_swap a b hab] at h2'
  have h3 : Equiv.swap (pairOf a b hab).1 (pairOf a b hab).2
      = Equiv.swap (g' a) (g' b) := by
    rw [Equiv.swap_apply_apply, ← h2']
  have hg'ab : g' a ≠ g' b := fun hh => hab (g'.injective hh)
  have h4 : ggQ2xS_phiP m hm3 (pairOf a b hab).1 (pairOf a b hab).2
      = ggQ2xS_phiP m hm3 (g' a) (g' b) :=
    ggQ2xS_phiP_of_swap_eq hm3 (pairOf_spec a b hab).1 hg'ab h3
  rw [h1, h4, hgconj a b hab]

end CFSG.StandardType

end
