module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisDefs

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

theorem isComplement'_subgroupOf {G : Type*} [Group G] {N A L : Subgroup G} (hA : A ≤ N)
    (hL : L ≤ N) (hdisj : A ⊓ L = ⊥) (hmul : ∀ g ∈ N, ∃ a ∈ A, ∃ l ∈ L, a * l = g) :
    (A.subgroupOf N).IsComplement' (L.subgroupOf N) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hxA hxL
    have h1 : (x : G) ∈ A ⊓ L := ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxL⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  · ext x
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    obtain ⟨a, ha, l, hl, hal⟩ := hmul x x.2
    exact ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.mpr ha, ⟨l, hL hl⟩, Subgroup.mem_subgroupOf.mpr hl,
      Subtype.ext hal⟩

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem mat_entry_eq (g : antiSp K) (k l : Fin 4) :
    mat g 0 k * mat g 3 l + mat g 1 k * mat g 2 l + mat g 2 k * mat g 1 l +
      mat g 3 k * mat g 0 l = if k.val + l.val = 3 then 1 else 0 := by
  have := congrFun (congrFun (mem_antiSp.mp g.2) k) l
  rwa [transpose_mul_minorJ_mul_apply, minorJ_apply] at this

omit [CharP K 2] in
theorem mat_inv_apply (g : antiSp K) (i j : Fin 4) : mat g⁻¹ i j = mat g j.rev i.rev := by
  have hJ : (mat g)ᵀ * minorJ K * mat g = minorJ K := mem_antiSp.mp g.2
  have h1 : minorJ K * (mat g)ᵀ * minorJ K * mat g = 1 := by
    calc minorJ K * (mat g)ᵀ * minorJ K * mat g
        = minorJ K * ((mat g)ᵀ * minorJ K * mat g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, minorJ_mul_self]
  have h2 : mat g⁻¹ = minorJ K * (mat g)ᵀ * minorJ K :=
    (Matrix.coe_units_inv (g : GL (Fin 4) K)).trans (Matrix.inv_eq_left_inv h1)
  rw [h2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, Fin.rev]

@[expose] def FirstCol (g : antiSp K) : Prop :=
  mat g 1 0 = 0 ∧ mat g 2 0 = 0 ∧ mat g 3 0 = 0

omit [CharP K 2] in
theorem FirstCol.mul {g h : antiSp K} (hg : FirstCol g) (hh : FirstCol h) : FirstCol (g * h) := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨h1, h2, h3⟩ := hh
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mat_mul, Matrix.mul_apply, Fin.sum_univ_four, g1, g2, g3, h1, h2, h3]

omit [CharP K 2] in
theorem FirstCol.one : FirstCol (1 : antiSp K) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one]

omit [CharP K 2] in
theorem FirstCol.last_row {g : antiSp K} (h : FirstCol g) :
    mat g 0 0 * mat g 3 3 = 1 ∧ mat g 3 1 = 0 ∧ mat g 3 2 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e03 := mat_entry_eq g 0 3
  have e01 := mat_entry_eq g 0 1
  have e02 := mat_entry_eq g 0 2
  simp at e03 e01 e02
  rw [h1, h2, h3] at e03 e01 e02
  have hne : mat g 0 0 ≠ 0 := by
    intro h0
    rw [h0] at e03
    simp at e03
  refine ⟨by linear_combination e03, ?_, ?_⟩
  · have : mat g 0 0 * mat g 3 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left hne
  · have : mat g 0 0 * mat g 3 2 = 0 := by linear_combination e02
    exact (mul_eq_zero.mp this).resolve_left hne

omit [CharP K 2] in
theorem FirstCol.inv {g : antiSp K} (h : FirstCol g) : FirstCol g⁻¹ := by
  obtain ⟨-, l1, l2⟩ := h.last_row
  obtain ⟨-, -, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_inv_apply]
    simpa [Fin.rev] using l2
  · rw [mat_inv_apply]
    simpa [Fin.rev] using l1
  · rw [mat_inv_apply]
    simpa [Fin.rev] using h3

theorem firstCol_uElt (a b c d : K) : FirstCol (uElt a b c d) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat, glMat_uElt, uMat]

theorem firstCol_aElt (v : Fin 2 → K) (c : K) : FirstCol (aElt v c) :=
  firstCol_uElt _ _ _ _

omit [CharP K 2] in
theorem firstCol_dElt (l : Kˣ) : FirstCol (dElt l) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat, glMat_dElt, dMat]

theorem firstCol_sElt (M : SL₂ K) : FirstCol (sElt M) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat, glMat_sElt, sMat]

@[expose] def lineStab (K : Type) [Field K] [CharP K 2] : Subgroup (antiSp K) where
  carrier := {g | FirstCol g}
  mul_mem' := fun ha hb => FirstCol.mul ha hb
  one_mem' := FirstCol.one
  inv_mem' := fun ha => FirstCol.inv ha

theorem mem_lineStab {g : antiSp K} : g ∈ lineStab K ↔ FirstCol g :=
  Iff.rfl

theorem mat_normalForm (v : Fin 2 → K) (c : K) (l : Kˣ) (M : SL₂ K) :
    mat (aElt v c * (dElt l * sElt M)) =
      !![(l : K), v 1 * M 0 0 + v 0 * M 1 0, v 1 * M 0 1 + v 0 * M 1 1, c * ((l⁻¹ : Kˣ) : K);
        0, M 0 0, M 0 1, v 0 * ((l⁻¹ : Kˣ) : K);
        0, M 1 0, M 1 1, v 1 * ((l⁻¹ : Kˣ) : K);
        0, 0, 0, ((l⁻¹ : Kˣ) : K)] := by
  have hl : (l : K) * ((l⁻¹ : Kˣ) : K) = 1 := Units.mul_inv l
  rw [mat_mul, mat_mul]
  change glMat (aElt v c : GL (Fin 4) K) * (glMat (dElt l : GL (Fin 4) K) *
    glMat (sElt M : GL (Fin 4) K)) = _
  rw [glMat_aElt, glMat_dElt, glMat_sElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, dMat, sMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem firstCol_normalForm (v : Fin 2 → K) (c : K) (l : Kˣ) (M : SL₂ K) :
    FirstCol (aElt v c * (dElt l * sElt M)) :=
  (firstCol_aElt v c).mul ((firstCol_dElt l).mul (firstCol_sElt M))

theorem exists_normalForm {g : antiSp K} (h : FirstCol g) :
    ∃ (v : Fin 2 → K) (c : K) (l : Kˣ) (M : SL₂ K), g = aElt v c * (dElt l * sElt M) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨l1, l2, l3⟩ := h.last_row
  obtain ⟨h1, h2', h3⟩ := h
  have e12 := mat_entry_eq g 1 2
  have e13 := mat_entry_eq g 1 3
  have e23 := mat_entry_eq g 2 3
  simp at e12 e13 e23
  simp only [l2, l3] at e12 e13 e23
  have hl : IsUnit (mat g 0 0) := IsUnit.of_mul_eq_one (mat g 3 3) l1
  set l := hl.unit with hldef
  have hl' : mat g 0 0 = (l : K) := rfl
  have hdet : (mat g 1 1 * mat g 2 2 - mat g 1 2 * mat g 2 1 : K) = 1 := by
    linear_combination e12 - (mat g 1 2 * mat g 2 1) * h2
  obtain ⟨M₀, e00, e01, e10, e11⟩ : ∃ M₀ : SL₂ K, M₀ 0 0 = mat g 1 1 ∧ M₀ 0 1 = mat g 1 2 ∧
      M₀ 1 0 = mat g 2 1 ∧ M₀ 1 1 = mat g 2 2 :=
    ⟨⟨!![mat g 1 1, mat g 1 2; mat g 2 1, mat g 2 2], by
      rw [Matrix.det_fin_two]; simpa using hdet⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨![l * mat g 1 3, l * mat g 2 3], l * mat g 0 3, l, M₀, antiSp_ext ?_⟩
  refine Eq.trans ?_
    (mat_normalForm ![l * mat g 1 3, l * mat g 2 3] (l * mat g 0 3) l M₀).symm
  have hl2 : (l : K) * ((l⁻¹ : Kˣ) : K) = 1 := Units.mul_inv l
  have hl3 : ((l⁻¹ : Kˣ) : K) = mat g 3 3 := by
    rw [Units.val_inv_eq_inv_val, ← hl']
    exact (eq_inv_of_mul_eq_one_right l1).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h1, h2', h3, l2, l3, hl3, ← hl', e00, e01, e10, e11] <;> grind

theorem normalForm_unique {v v' : Fin 2 → K} {c c' : K} {l l' : Kˣ} {M M' : SL₂ K}
    (h : aElt v c * (dElt l * sElt M) = aElt v' c' * (dElt l' * sElt M')) :
    v = v' ∧ c = c' ∧ l = l' ∧ M = M' := by
  have h1 := congrArg mat h
  rw [mat_normalForm, mat_normalForm] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e12 := congrFun (congrFun h1 1) 2
  have e21 := congrFun (congrFun h1 2) 1
  have e22 := congrFun (congrFun h1 2) 2
  have e13 := congrFun (congrFun h1 1) 3
  have e23 := congrFun (congrFun h1 2) 3
  have e03 := congrFun (congrFun h1 0) 3
  simp at e00 e11 e12 e21 e22 e13 e23 e03
  have hl : l = l' := Units.ext e00
  subst hl
  have hli : ((l : K))⁻¹ ≠ 0 := inv_ne_zero (Units.ne_zero l)
  refine ⟨?_, mul_right_cancel₀ hli e03, rfl, ?_⟩
  · ext i
    fin_cases i
    · exact mul_right_cancel₀ hli e13
    · exact mul_right_cancel₀ hli e23
  · ext i j
    fin_cases i <;> fin_cases j <;> assumption

variable (K) in
@[expose] def rootU₂ : Subgroup (antiSp K) where
  carrier := {g | ∃ c : K, g = uElt 0 0 c 0}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨e, rfl⟩
    exact ⟨c + e, by rw [uElt_mul]; congr 1 <;> ring⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, by rw [uElt_inv]; congr 1; ring⟩

variable (K) in
@[expose] def rootU₁ : Subgroup (antiSp K) where
  carrier := {g | ∃ b : K, g = uElt 0 b 0 0}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨e, rfl⟩
    exact ⟨b + e, by rw [uElt_mul]; congr 1 <;> ring⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by rw [uElt_inv]; congr 1; ring⟩

theorem mem_rootU₂ {g : antiSp K} : g ∈ rootU₂ K ↔ ∃ c : K, g = uElt 0 0 c 0 :=
  Iff.rfl

theorem mem_rootU₁ {g : antiSp K} : g ∈ rootU₁ K ↔ ∃ b : K, g = uElt 0 b 0 0 :=
  Iff.rfl

theorem rootU₂_le_radA2 : rootU₂ K ≤ radA2 K := by
  rintro _ ⟨c, rfl⟩
  exact ⟨0, 0, c, rfl⟩

theorem rootU₁_le_radA1 : rootU₁ K ≤ radA1 K := by
  rintro _ ⟨b, rfl⟩
  exact ⟨b, 0, 0, rfl⟩

theorem aElt_zero (c : K) : aElt (0 : Fin 2 → K) c = uElt 0 0 c 0 := by
  simp [aElt]

theorem mem_radA2_iff {g : antiSp K} : g ∈ radA2 K ↔ ∃ (v : Fin 2 → K) (c : K), g = aElt v c := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨![b, a], c, by simp [aElt]⟩
  · rintro ⟨v, c, rfl⟩
    exact ⟨v 1, v 0, c, rfl⟩

theorem aElt_mem_radA2 (v : Fin 2 → K) (c : K) : aElt v c ∈ radA2 K :=
  mem_radA2_iff.mpr ⟨v, c, rfl⟩

theorem aElt_zero_mem_rootU₂ (c : K) : aElt (0 : Fin 2 → K) c ∈ rootU₂ K :=
  ⟨c, aElt_zero c⟩

theorem mul_uElt_of_firstCol {g : antiSp K} (h : FirstCol g) (c : K) :
    g * uElt 0 0 c 0 = uElt 0 0 ((mat g 0 0) ^ 2 * c) 0 * g := by
  obtain ⟨l1, l2, l3⟩ := h.last_row
  obtain ⟨h1, h2, h3⟩ := h
  apply antiSp_ext
  change mat g * uMat 0 0 c 0 = uMat 0 0 ((mat g 0 0) ^ 2 * c) 0 * mat g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3, l2, l3]
  grind

theorem conj_uElt_of_firstCol {g : antiSp K} (h : FirstCol g) (c : K) :
    g * uElt 0 0 c 0 * g⁻¹ = uElt 0 0 ((mat g 0 0) ^ 2 * c) 0 := by
  rw [mul_uElt_of_firstCol h, mul_inv_cancel_right]

theorem mem_normalizer_rootU₂_iff {g : antiSp K} :
    g ∈ Subgroup.normalizer (rootU₂ K : Set (antiSp K)) ↔ FirstCol g := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg
    obtain ⟨c', hc'⟩ := (hg (uElt 0 0 1 0)).mp ⟨1, rfl⟩
    have h2 : g * uElt 0 0 1 0 = uElt 0 0 c' 0 * g := by
      rw [← hc']
      group
    have key : ∀ i : Fin 4, mat g i 0 + mat g i 3 =
        mat g i 3 + (if i = 0 then c' * mat g 3 3 else 0) := by
      intro i
      have := congrFun (congrFun (congrArg mat h2) i) 3
      fin_cases i <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this ⊢ <;>
        grind
    refine ⟨?_, ?_, ?_⟩
    · simpa using key 1
    · simpa using key 2
    · simpa using key 3
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, conj_uElt_of_firstCol h c⟩
    · rintro ⟨c', hc'⟩
      have hx : x = g⁻¹ * uElt 0 0 c' 0 * g⁻¹⁻¹ := by
        rw [← hc']
        group
      rw [hx, conj_uElt_of_firstCol h.inv]
      exact ⟨_, rfl⟩

theorem normalizer_rootU₂_eq : Subgroup.normalizer (rootU₂ K : Set (antiSp K)) = lineStab K :=
  Subgroup.ext fun _ => mem_normalizer_rootU₂_iff

theorem mem_centralizer_rootU₂_iff {g : antiSp K} :
    g ∈ Subgroup.centralizer (rootU₂ K : Set (antiSp K)) ↔ FirstCol g ∧ mat g 0 0 = 1 := by
  constructor
  · intro hg
    have hF : FirstCol g :=
      mem_normalizer_rootU₂_iff.mp (Subgroup.centralizer_le_normalizer _ hg)
    refine ⟨hF, ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp hg (uElt 0 0 1 0) ⟨1, rfl⟩
    have h1 := mul_uElt_of_firstCol hF 1
    rw [← hc] at h1
    have h3 := mul_right_cancel h1
    have h4 := (uElt_inj h3).2.2.1
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h5 : (mat g 0 0 - 1) ^ 2 = 0 := by linear_combination -h4 + (1 - mat g 0 0) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h5
    exact sub_eq_zero.mp this
  · rintro ⟨hF, h1⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, rfl⟩
    have := mul_uElt_of_firstCol hF c
    rw [h1] at this
    simpa using this.symm

theorem centralizer_rootU₂_le_lineStab :
    Subgroup.centralizer (rootU₂ K : Set (antiSp K)) ≤ lineStab K := fun _ hg =>
  (mem_centralizer_rootU₂_iff.mp hg).1

theorem aElt_comm (v w : Fin 2 → K) (c e : K) : aElt v c * aElt w e = aElt w e * aElt v c := by
  rw [aElt_mul, aElt_mul]
  congr 1
  · exact add_comm v w
  · ring

theorem conj_aElt_normalForm (w : Fin 2 → K) (e : K) (l : Kˣ) (M : SL₂ K) (v : Fin 2 → K)
    (c : K) :
    (aElt w e * (dElt l * sElt M)) * aElt v c * (aElt w e * (dElt l * sElt M))⁻¹ =
      aElt ((l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) ((l : K) ^ 2 * c) := by
  have h1 : sElt M * aElt v c * (sElt M)⁻¹ =
      aElt ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) c := by
    rw [sElt_mul_aElt, mul_inv_cancel_right]
  have h2 : dElt l * aElt ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) c * (dElt l)⁻¹ =
      aElt ((l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) ((l : K) ^ 2 * c) := by
    rw [dElt_mul_aElt, mul_inv_cancel_right]
  have h3 : ∀ (y : Fin 2 → K) (c' : K), aElt w e * aElt y c' * (aElt w e)⁻¹ = aElt y c' := by
    intro y c'
    rw [aElt_comm w y e c', mul_inv_cancel_right]
  calc (aElt w e * (dElt l * sElt M)) * aElt v c * (aElt w e * (dElt l * sElt M))⁻¹
      = aElt w e * (dElt l * (sElt M * aElt v c * (sElt M)⁻¹) * (dElt l)⁻¹) * (aElt w e)⁻¹ := by
        group
    _ = _ := by rw [h1, h2, h3]

theorem conj_mem_radA2 {g : antiSp K} (h : FirstCol g) {x : antiSp K} (hx : x ∈ radA2 K) :
    g * x * g⁻¹ ∈ radA2 K := by
  obtain ⟨w, e, l, M, rfl⟩ := exists_normalForm h
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hx
  rw [conj_aElt_normalForm]
  exact aElt_mem_radA2 _ _

theorem radA2_le_lineStab : radA2 K ≤ lineStab K := by
  rintro _ ⟨a, b, c, rfl⟩
  exact firstCol_uElt a b c 0

theorem mem_normalizer_radA2_iff {g : antiSp K} :
    g ∈ Subgroup.normalizer (radA2 K : Set (antiSp K)) ↔ FirstCol g := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg
    have key : ∀ z ∈ radA2 K, ∀ i : Fin 4, (mat z * mat g) i 0 = mat g i 0 := by
      intro z hz i
      obtain ⟨a, b, c, ha⟩ := (hg (g⁻¹ * z * g)).mpr (by
        rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
        exact hz)
      have h1 : z * g = g * uElt a b c 0 := by
        rw [← ha]
        group
      have := congrFun (congrFun (congrArg mat h1) i) 0
      rw [mat_mul, mat_mul] at this
      rw [this]
      simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat]
    have k1 := key (uElt 0 1 0 0) ⟨0, 1, 0, rfl⟩
    have k2 := key (uElt 1 0 0 0) ⟨1, 0, 0, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have := k2 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
      linear_combination this
    · have := k1 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
      linear_combination this
    · have := k1 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
      linear_combination this
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_radA2 h hx
    · intro hx
      have := conj_mem_radA2 h.inv hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem normalizer_radA2_eq : Subgroup.normalizer (radA2 K : Set (antiSp K)) = lineStab K :=
  Subgroup.ext fun _ => mem_normalizer_radA2_iff

variable (K) in
@[expose] def leviHom₂ : SL₂ K × Kˣ →* antiSp K :=
  (sHom₂ K).noncommCoprod (dHom₂ K) (fun M l => sElt_mul_dElt M l)

theorem leviHom₂_apply (M : SL₂ K) (l : Kˣ) : leviHom₂ K (M, l) = sElt M * dElt l :=
  rfl

theorem leviHom₂_injective : Function.Injective (leviHom₂ K) := by
  rintro ⟨M, l⟩ ⟨M', l'⟩ h
  rw [leviHom₂_apply, leviHom₂_apply, sElt_mul_dElt, sElt_mul_dElt] at h
  have h' : aElt 0 0 * (dElt l * sElt M) = aElt 0 0 * (dElt l' * sElt M') := by
    rw [aElt_zero_zero, one_mul, one_mul]
    exact h
  obtain ⟨-, -, hl, hM⟩ := normalForm_unique h'
  rw [hl, hM]

theorem leviHom₂_range_le_lineStab : (leviHom₂ K).range ≤ lineStab K := by
  rintro _ ⟨⟨M, l⟩, rfl⟩
  rw [leviHom₂_apply, sElt_mul_dElt]
  have := firstCol_normalForm 0 0 l M
  rwa [aElt_zero_zero, one_mul] at this

omit [CharP K 2] in
theorem dElt_one : dElt (1 : Kˣ) = (1 : antiSp K) :=
  (dHom₂ K).map_one

theorem sElt_one : sElt (1 : SL₂ K) = (1 : antiSp K) :=
  (sHom₂ K).map_one

theorem radA2_inf_leviHom₂_range : radA2 K ⊓ (leviHom₂ K).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, ⟨⟨M, l⟩, hl⟩⟩
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hx
  rw [leviHom₂_apply, sElt_mul_dElt] at hl
  have h' : aElt v c * (dElt 1 * sElt 1) = aElt 0 0 * (dElt l * sElt M) := by
    simp [dElt_one, sElt_one, aElt_zero_zero, hl]
  obtain ⟨hv, hc, -, -⟩ := normalForm_unique h'
  rw [hv, hc, aElt_zero_zero]
  exact one_mem _

theorem isComplement'_lineStab :
    ((radA2 K).subgroupOf (lineStab K)).IsComplement'
      ((leviHom₂ K).range.subgroupOf (lineStab K)) :=
  isComplement'_subgroupOf radA2_le_lineStab leviHom₂_range_le_lineStab radA2_inf_leviHom₂_range
    (fun g hg => by
      obtain ⟨v, c, l, M, rfl⟩ := exists_normalForm hg
      exact ⟨aElt v c, aElt_mem_radA2 v c, leviHom₂ K (M, l), ⟨(M, l), rfl⟩, by
        rw [leviHom₂_apply, sElt_mul_dElt]⟩)

instance normal_radA2_subgroupOf_lineStab : ((radA2 K).subgroupOf (lineStab K)).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_radA2 g.2 hx⟩

theorem radA2_le_centralizer_rootU₂ :
    radA2 K ≤ Subgroup.centralizer (rootU₂ K : Set (antiSp K)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact radA2_comm (rootU₂_le_radA2 hh) hx

theorem sHom₂_range_le_centralizer_rootU₂ :
    (sHom₂ K).range ≤ Subgroup.centralizer (rootU₂ K : Set (antiSp K)) := by
  rintro _ ⟨M, rfl⟩
  rw [mem_centralizer_rootU₂_iff]
  exact ⟨firstCol_sElt M, by simp [mat, sHom₂_apply, glMat_sElt, sMat]⟩

theorem radA2_inf_sHom₂_range : radA2 K ⊓ (sHom₂ K).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, ⟨M, hl⟩⟩
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hx
  rw [sHom₂_apply] at hl
  have h' : aElt v c * (dElt 1 * sElt 1) = aElt 0 0 * (dElt 1 * sElt M) := by
    simp [dElt_one, sElt_one, aElt_zero_zero, hl]
  obtain ⟨hv, hc, -, -⟩ := normalForm_unique h'
  rw [hv, hc, aElt_zero_zero]
  exact one_mem _

abbrev rootC₂ (K : Type) [Field K] [CharP K 2] : Subgroup (antiSp K) :=
  Subgroup.centralizer ((rootU₂ K : Subgroup (antiSp K)) : Set (antiSp K))

theorem exists_aElt_mul_sElt {g : antiSp K} (hg : g ∈ rootC₂ K) :
    ∃ (v : Fin 2 → K) (c : K) (M : SL₂ K), g = aElt v c * sElt M := by
  obtain ⟨hF, h1⟩ := mem_centralizer_rootU₂_iff.mp hg
  obtain ⟨v, c, l, M, rfl⟩ := exists_normalForm hF
  have hl : (l : K) = 1 := by
    rw [mat_normalForm] at h1
    simpa using h1
  have hl1 : l = 1 := Units.ext hl
  subst hl1
  exact ⟨v, c, M, by rw [dElt_one, one_mul]⟩

theorem isComplement'_centralizer :
    ((radA2 K).subgroupOf (rootC₂ K)).IsComplement' ((sHom₂ K).range.subgroupOf (rootC₂ K)) :=
  isComplement'_subgroupOf radA2_le_centralizer_rootU₂ sHom₂_range_le_centralizer_rootU₂
    radA2_inf_sHom₂_range
    (fun g hg => by
      obtain ⟨v, c, M, rfl⟩ := exists_aElt_mul_sElt hg
      exact ⟨aElt v c, aElt_mem_radA2 v c, sHom₂ K M, ⟨M, rfl⟩, rfl⟩)

instance normal_radA2_subgroupOf_centralizer :
    ((radA2 K).subgroupOf (Subgroup.centralizer (rootU₂ K : Set (antiSp K)))).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_radA2 (centralizer_rootU₂_le_lineStab g.2) hx⟩

end KCRootAxis

end CFSG.RankThree.PartOne
