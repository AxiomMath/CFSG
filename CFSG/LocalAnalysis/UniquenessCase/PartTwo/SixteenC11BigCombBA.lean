module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCls

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16c11_big_combb_zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private def s16c11_big_combb_T (j : Equiv.Perm (Fin 10)) : Finset (Fin 10) :=
  Finset.univ.filter fun i => i < j i

private lemma s16c11_big_combb_mem_T {j : Equiv.Perm (Fin 10)} {i : Fin 10} :
    i ∈ s16c11_big_combb_T j ↔ i < j i := by
  simp [s16c11_big_combb_T]

private lemma s16c11_big_combb_not_mem_T {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    {i : Fin 10} : i ∉ s16c11_big_combb_T j ↔ j i < i := by
  rw [s16c11_big_combb_mem_T, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h (hj_ne i), fun h => h.le⟩

private lemma s16c11_big_combb_j_not_mem_T_of_mem {j : Equiv.Perm (Fin 10)}
    (hj_ne : ∀ i, j i ≠ i) (hj_inv : ∀ i, j (j i) = i) {i : Fin 10}
    (h : i ∈ s16c11_big_combb_T j) : j i ∉ s16c11_big_combb_T j := by
  rw [s16c11_big_combb_not_mem_T hj_ne, hj_inv i]
  exact (s16c11_big_combb_mem_T).mp h

private lemma s16c11_big_combb_j_mem_T_of_not_mem {j : Equiv.Perm (Fin 10)}
    (hj_ne : ∀ i, j i ≠ i) (hj_inv : ∀ i, j (j i) = i) {i : Fin 10}
    (h : i ∉ s16c11_big_combb_T j) : j i ∈ s16c11_big_combb_T j := by
  rw [s16c11_big_combb_mem_T, hj_inv i]
  exact (s16c11_big_combb_not_mem_T hj_ne).mp h

private lemma s16c11_big_combb_image_T {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) :
    (s16c11_big_combb_T j).image j = (s16c11_big_combb_T j)ᶜ := by
  ext b
  rw [Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact s16c11_big_combb_j_not_mem_T_of_mem hj_ne hj_inv ha
  · intro hb
    exact ⟨j b, s16c11_big_combb_j_mem_T_of_not_mem hj_ne hj_inv hb, hj_inv b⟩

private lemma s16c11_big_combb_card_T {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) : (s16c11_big_combb_T j).card = 5 := by
  have himg := s16c11_big_combb_image_T hj_ne hj_inv
  have hcard : (s16c11_big_combb_T j)ᶜ.card = (s16c11_big_combb_T j).card := by
    rw [← himg, Finset.card_image_of_injective _ j.injective]
  have hsum := Finset.card_add_card_compl (s16c11_big_combb_T j)
  rw [Fintype.card_fin] at hsum
  omega

private lemma s16c11_big_combb_mem_T_zero {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i) :
    (0 : Fin 10) ∈ s16c11_big_combb_T j := by
  rw [s16c11_big_combb_mem_T]
  exact lt_of_le_of_ne (Fin.zero_le _) (hj_ne 0).symm

private lemma s16c11_big_combb_indT_add {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (a : Fin 10) :
    (if a ∈ s16c11_big_combb_T j then (0 : ZMod 2) else 1) +
        (if j a ∈ s16c11_big_combb_T j then 0 else 1) = 1 := by
  by_cases ha : a ∈ s16c11_big_combb_T j
  · rw [if_pos ha, if_neg (s16c11_big_combb_j_not_mem_T_of_mem hj_ne hj_inv ha)]
    decide
  · rw [if_neg ha, if_pos (s16c11_big_combb_j_mem_T_of_not_mem hj_ne hj_inv ha)]
    decide

private lemma s16c11_big_combb_sum_indT {j : Equiv.Perm (Fin 10)} :
    (∑ a, (if a ∈ s16c11_big_combb_T j then (0 : ZMod 2) else 1)) =
      (((s16c11_big_combb_T j)ᶜ.card : ℕ) : ZMod 2) := by
  rw [show (∑ a, (if a ∈ s16c11_big_combb_T j then (0 : ZMod 2) else 1)) =
      ∑ a ∈ Finset.univ, (if a ∉ s16c11_big_combb_T j then (1 : ZMod 2) else 0) from by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a ∈ s16c11_big_combb_T j <;> simp [h]]
  rw [Finset.sum_boole]
  have hfilter : Finset.univ.filter (fun a => a ∉ s16c11_big_combb_T j) =
      (s16c11_big_combb_T j)ᶜ := by
    ext a; simp
  rw [hfilter]

private lemma s16c11_big_combb_not_inv_add_one {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) {x : Fin 10 → ZMod 2} (hx : ∑ i, x i = 0)
    (hodd : ∀ i, x (j i) = x i + 1) : False := by
  let f : Fin 10 → ZMod 2 := fun a => x a + if a ∈ s16c11_big_combb_T j then 0 else 1
  have hfsum : ∑ a, f a = 0 := by
    refine Finset.sum_ninvolution (s := Finset.univ) (f := f) (g := j) ?_ ?_ ?_ ?_
    · intro a
      dsimp only [f]
      rw [hodd a]
      have hi := s16c11_big_combb_indT_add hj_ne hj_inv a
      calc (x a + (if a ∈ s16c11_big_combb_T j then (0 : ZMod 2) else 1)) +
            (x a + 1 + (if j a ∈ s16c11_big_combb_T j then 0 else 1))
          = (if a ∈ s16c11_big_combb_T j then (0 : ZMod 2) else 1) +
              (if j a ∈ s16c11_big_combb_T j then 0 else 1) + (x a + x a) + 1 := by ring
        _ = 1 + 0 + 1 := by rw [hi, CharTwo.add_self_eq_zero]
        _ = 0 := by decide
    · intro a _; exact hj_ne a
    · intro a; exact Finset.mem_univ _
    · intro a; exact hj_inv a
  have hf_eq : ∑ a, f a = (∑ a, x a) +
      (((s16c11_big_combb_T j)ᶜ.card : ℕ) : ZMod 2) := by
    dsimp only [f]
    rw [Finset.sum_add_distrib, s16c11_big_combb_sum_indT]
  have hsum_eq : ∑ a, x a = (((s16c11_big_combb_T j)ᶜ.card : ℕ) : ZMod 2) := by
    have : (∑ a, x a) + (((s16c11_big_combb_T j)ᶜ.card : ℕ) : ZMod 2) = 0 := by
      rw [← hf_eq]; exact hfsum
    exact CharTwo.add_eq_zero.mp this
  have hcomp : ((s16c11_big_combb_T j)ᶜ.card : ℕ) = 5 := by
    have hcard := s16c11_big_combb_card_T hj_ne hj_inv
    have hsum := Finset.card_add_card_compl (s16c11_big_combb_T j)
    rw [Fintype.card_fin] at hsum
    omega
  rw [hsum_eq, hcomp] at hx
  exact (by decide : (5 : ZMod 2) ≠ 0) hx

private lemma s16c11_big_combb_sum_comp (σ : Equiv.Perm (Fin 10)) {x : Fin 10 → ZMod 2}
    (hx : ∑ i, x i = 0) : ∑ i, x (σ⁻¹ i) = 0 := by
  rw [Equiv.sum_comp]
  exact hx

private lemma s16c11_big_combb_inv_sum {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) {x : Fin 10 → ZMod 2} (hInv : ∀ i, x (j i) = x i) :
    ∑ i, x i = 0 := by
  refine Finset.sum_ninvolution (s := Finset.univ) (f := x) (g := j) ?_ ?_ ?_ ?_
  · intro a
    rw [hInv a, CharTwo.add_self_eq_zero]
  · intro a _; exact hj_ne a
  · intro a; exact Finset.mem_univ _
  · intro a; exact hj_inv a

private lemma s16c11_big_combb_inv_fixed {E : Subgroup (Equiv.Perm (Fin 10))}
    {j : Equiv.Perm (Fin 10)} (hj_or : ∀ σ ∈ E, ∀ i, σ i = i ∨ σ i = j i)
    {x : Fin 10 → ZMod 2} (hx : ∑ i, x i = 0) (hInv : ∀ i, x (j i) = x i) :
    ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ (s16c11BigCls 10 x hx) =
      s16c11BigCls 10 x hx := by
  intro σ hσ
  rw [s16c11BigCls_modAct (hx' := s16c11_big_combb_sum_comp σ hx)]
  refine (s16c11BigCls_eq_iff).mpr (Or.inl ?_)
  funext i
  rcases hj_or σ⁻¹ (inv_mem hσ) i with h | h
  · rw [h]
  · rw [h, hInv]

private lemma s16c11_big_combb_fixed_inv {E : Subgroup (Equiv.Perm (Fin 10))}
    {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i) (hj_inv : ∀ i, j (j i) = i)
    (hj_or : ∀ σ ∈ E, ∀ i, σ i = i ∨ σ i = j i)
    (hj_surj : ∀ i, ∃ σ ∈ E, σ i = j i)
    {x : Fin 10 → ZMod 2} (hx : ∑ i, x i = 0)
    (hfix : ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ (s16c11BigCls 10 x hx) =
      s16c11BigCls 10 x hx) :
    ∀ i, x (j i) = x i := by
  have hcases : ∀ σ ∈ E, (∀ i, x (σ⁻¹ i) = x i) ∨ (∀ i, x (σ⁻¹ i) = x i + 1) := by
    intro σ hσ
    have h := hfix σ hσ
    rw [s16c11BigCls_modAct (hx' := s16c11_big_combb_sum_comp σ hx)] at h
    rcases (s16c11BigCls_eq_iff).mp h with h' | h'
    · left; intro i; rw [congr_fun h' i]
    · right; intro i
      have hi : x i = x (σ⁻¹ i) + 1 := congr_fun h' i
      rw [hi, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hno : ∀ σ ∈ E, ¬ (∀ i, x (σ⁻¹ i) = x i + 1) := by
    intro σ hσ h2
    have hodd : ∀ i, x (j i) = x i + 1 := by
      intro i
      rcases hj_or σ⁻¹ (inv_mem hσ) i with h | h
      · exfalso
        have hbad : ¬ (x i = x i + 1) := by
          rcases s16c11_big_combb_zmod2_eq_zero_or_eq_one (x i) with hxi | hxi <;>
            rw [hxi] <;> decide
        exact hbad (by simpa only [h] using h2 i)
      · exact by simpa only [h] using h2 i
    exact s16c11_big_combb_not_inv_add_one hj_ne hj_inv hx hodd
  intro i
  obtain ⟨σ, hσ, hσi⟩ := hj_surj i
  rcases hcases σ hσ with h | h
  · have h1 : x (σ⁻¹ (j i)) = x (j i) := h (j i)
    have h2 : σ⁻¹ (j i) = i := by rw [← hσi]; simp
    rw [h2] at h1
    exact h1.symm
  · exact absurd h (hno σ hσ)

private lemma s16c11_big_combb_normalize_inv {j : Equiv.Perm (Fin 10)}
    {x : Fin 10 → ZMod 2} (hInv : ∀ i, x (j i) = x i) :
    ∀ i, (fun k => x k + x 0) (j i) = (fun k => x k + x 0) i := by
  intro i
  show x (j i) + x 0 = x i + x 0
  rw [hInv i]

private lemma s16c11_big_combb_normalize_zero (x : Fin 10 → ZMod 2) :
    (fun k => x k + x 0) 0 = 0 :=
  CharTwo.add_self_eq_zero (x 0)

private lemma s16c11_big_combb_normalize_cls {x : Fin 10 → ZMod 2} {hx : ∑ i, x i = 0}
    {hx' : ∑ i, (x i + x 0) = 0} :
    s16c11BigCls 10 (fun k => x k + x 0) hx' = s16c11BigCls 10 x hx := by
  rcases s16c11_big_combb_zmod2_eq_zero_or_eq_one (x 0) with h0 | h0
  · refine (s16c11BigCls_eq_iff).mpr (Or.inl ?_)
    funext k
    rw [h0, add_zero]
  · refine (s16c11BigCls_eq_iff).mpr (Or.inr ?_)
    funext k
    show x k = (x k + x 0) + 1
    rw [h0, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private def s16c11_big_combb_extend {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (y : ↥(s16c11_big_combb_T j) → ZMod 2)
    (a : Fin 10) : ZMod 2 :=
  if ha : a ∈ s16c11_big_combb_T j then y ⟨a, ha⟩ else
    y ⟨j a, s16c11_big_combb_j_mem_T_of_not_mem hj_ne hj_inv ha⟩

private lemma s16c11_big_combb_extend_of_mem {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (y : ↥(s16c11_big_combb_T j) → ZMod 2) {a : Fin 10}
    (ha : a ∈ s16c11_big_combb_T j) :
    s16c11_big_combb_extend hj_ne hj_inv y a = y ⟨a, ha⟩ := by
  unfold s16c11_big_combb_extend
  rw [dif_pos ha]

private lemma s16c11_big_combb_extend_of_not_mem {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (y : ↥(s16c11_big_combb_T j) → ZMod 2) {a : Fin 10}
    (ha : a ∉ s16c11_big_combb_T j) :
    s16c11_big_combb_extend hj_ne hj_inv y a =
      y ⟨j a, s16c11_big_combb_j_mem_T_of_not_mem hj_ne hj_inv ha⟩ := by
  unfold s16c11_big_combb_extend
  rw [dif_neg ha]

private lemma s16c11_big_combb_extend_inv {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (y : ↥(s16c11_big_combb_T j) → ZMod 2) (a : Fin 10) :
    s16c11_big_combb_extend hj_ne hj_inv y (j a) =
      s16c11_big_combb_extend hj_ne hj_inv y a := by
  by_cases ha : a ∈ s16c11_big_combb_T j
  · have hja : j a ∉ s16c11_big_combb_T j := s16c11_big_combb_j_not_mem_T_of_mem hj_ne hj_inv ha
    rw [s16c11_big_combb_extend_of_not_mem hj_ne hj_inv y hja,
      s16c11_big_combb_extend_of_mem hj_ne hj_inv y ha]
    congr 1
    exact Subtype.ext (hj_inv a)
  · have hja : j a ∈ s16c11_big_combb_T j := s16c11_big_combb_j_mem_T_of_not_mem hj_ne hj_inv ha
    rw [s16c11_big_combb_extend_of_mem hj_ne hj_inv y hja,
      s16c11_big_combb_extend_of_not_mem hj_ne hj_inv y ha]

private lemma s16c11_big_combb_extend_zero {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) (y : ↥(s16c11_big_combb_T j) → ZMod 2)
    (hy : y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩ = 0) :
    s16c11_big_combb_extend hj_ne hj_inv y 0 = 0 := by
  rw [s16c11_big_combb_extend_of_mem hj_ne hj_inv y (s16c11_big_combb_mem_T_zero hj_ne)]
  exact hy

private def s16c11_big_combb_normVecEquiv {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) :
    {x : Fin 10 → ZMod 2 // (∀ i, x (j i) = x i) ∧ x 0 = 0} ≃
      {y : ↥(s16c11_big_combb_T j) → ZMod 2 // y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩ = 0} where
  toFun x := ⟨fun i => x.1 i.1, by
    show x.1 0 = 0
    exact x.2.2⟩
  invFun y := ⟨s16c11_big_combb_extend hj_ne hj_inv y.1,
    ⟨s16c11_big_combb_extend_inv hj_ne hj_inv y.1,
      s16c11_big_combb_extend_zero hj_ne hj_inv y.1 y.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    show s16c11_big_combb_extend hj_ne hj_inv (fun i => x.1 i.1) a = x.1 a
    by_cases ha : a ∈ s16c11_big_combb_T j
    · rw [s16c11_big_combb_extend_of_mem hj_ne hj_inv _ ha]
    · rw [s16c11_big_combb_extend_of_not_mem hj_ne hj_inv _ ha]
      exact x.2.1 a
  right_inv y := by
    apply Subtype.ext
    funext i
    show s16c11_big_combb_extend hj_ne hj_inv y.1 i.1 = y.1 i
    rw [s16c11_big_combb_extend_of_mem hj_ne hj_inv y.1 i.2]

private lemma s16c11_big_combb_card_ker_eval {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i)
    (hj_inv : ∀ i, j (j i) = i) :
    Nat.card {y : ↥(s16c11_big_combb_T j) → ZMod 2 //
      y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩ = 0} = 16 := by
  let e : (↥(s16c11_big_combb_T j) → ZMod 2) →+ ZMod 2 :=
    { toFun := fun y => y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective e := fun c => ⟨fun _ => c, rfl⟩
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective (f := e) hsurj
  have hdom : Nat.card (↥(s16c11_big_combb_T j) → ZMod 2) = 32 := by
    rw [Nat.card_fun, Nat.card_zmod]
    have : Nat.card ↥(s16c11_big_combb_T j) = 5 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact s16c11_big_combb_card_T hj_ne hj_inv
    rw [this]
    norm_num
  rw [Nat.card_zmod, hdom] at hcard
  have hker : Nat.card e.ker = 16 := by omega
  rw [← hker]
  exact Nat.card_congr (Equiv.refl _)

theorem s16c11_big_combb_card_fixed_classes {E : Subgroup (Equiv.Perm (Fin 10))}
    {j : Equiv.Perm (Fin 10)} (hj_ne : ∀ i, j i ≠ i) (hj_inv : ∀ i, j (j i) = i)
    (hj_or : ∀ σ ∈ E, ∀ i, σ i = i ∨ σ i = j i)
    (hj_surj : ∀ i, ∃ σ ∈ E, σ i = j i) :
    Nat.card {q : (FFModel.symDn 10).Mod //
      ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ q = q} = 16 := by
  classical
  let Φ : {x : Fin 10 → ZMod 2 // (∀ i, x (j i) = x i) ∧ x 0 = 0} →
      {q : (FFModel.symDn 10).Mod //
        ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ q = q} :=
    fun x => ⟨s16c11BigCls 10 x.1 (s16c11_big_combb_inv_sum hj_ne hj_inv x.2.1),
      s16c11_big_combb_inv_fixed hj_or (s16c11_big_combb_inv_sum hj_ne hj_inv x.2.1) x.2.1⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      have hcl : s16c11BigCls 10 x.1 (s16c11_big_combb_inv_sum hj_ne hj_inv x.2.1) =
          s16c11BigCls 10 y.1 (s16c11_big_combb_inv_sum hj_ne hj_inv y.2.1) :=
        congrArg Subtype.val hxy
      rcases (s16c11BigCls_eq_iff).mp hcl with h | h
      · exact Subtype.ext h.symm
      · exfalso
        have hy0 : y.1 0 = 0 := y.2.2
        rw [h] at hy0
        simp only [] at hy0
        have hx0 : x.1 0 = 0 := x.2.2
        rw [hx0] at hy0
        exact absurd hy0 (by decide)
    · intro q
      obtain ⟨x, hx, hqx⟩ := s16c11BigCls_surjective 10 q.1
      have hfix : ∀ σ ∈ E,
          (FFModel.symDn_isActionModel 10).modAct σ (s16c11BigCls 10 x hx) =
            s16c11BigCls 10 x hx := by
        intro σ hσ
        rw [← hqx]
        exact q.2 σ hσ
      have hInv := s16c11_big_combb_fixed_inv hj_ne hj_inv hj_or hj_surj hx hfix
      let x' : Fin 10 → ZMod 2 := fun k => x k + x 0
      have hInv' : ∀ i, x' (j i) = x' i := s16c11_big_combb_normalize_inv hInv
      have hx'sum : ∑ i, x' i = 0 := s16c11_big_combb_inv_sum hj_ne hj_inv hInv'
      have hx'0 : x' 0 = 0 := s16c11_big_combb_normalize_zero x
      refine ⟨⟨x', hInv', hx'0⟩, ?_⟩
      apply Subtype.ext
      show s16c11BigCls 10 x' hx'sum = q.1
      rw [hqx]
      exact s16c11_big_combb_normalize_cls
  have hcard1 : Nat.card {x : Fin 10 → ZMod 2 // (∀ i, x (j i) = x i) ∧ x 0 = 0} =
      Nat.card {q : (FFModel.symDn 10).Mod //
        ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ q = q} :=
    Nat.card_congr (Equiv.ofBijective Φ hbij)
  have hcard2 : Nat.card {x : Fin 10 → ZMod 2 // (∀ i, x (j i) = x i) ∧ x 0 = 0} =
      Nat.card {y : ↥(s16c11_big_combb_T j) → ZMod 2 //
        y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩ = 0} :=
    Nat.card_congr (s16c11_big_combb_normVecEquiv hj_ne hj_inv)
  have hcard3 : Nat.card {y : ↥(s16c11_big_combb_T j) → ZMod 2 //
        y ⟨0, s16c11_big_combb_mem_T_zero hj_ne⟩ = 0} = 16 :=
    s16c11_big_combb_card_ker_eval hj_ne hj_inv
  rw [← hcard1, hcard2, hcard3]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
