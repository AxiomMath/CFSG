module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSUDiag

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.StandardType.TableBUE

namespace KGPSU

open CFSG.StandardType.AutPSU CFSG.LieType.Universal.Unitary

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private def midSet (m : ℕ) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ i ≠ Fin.last m)

private theorem mem_midSet {i : Fin (m + 1)} :
    i ∈ midSet m ↔ i ≠ 0 ∧ i ≠ Fin.last m := by
  simp [midSet]

private def idxOne (m : ℕ) (hm : 1 ≤ m) : Fin (m + 1) := ⟨1, by omega⟩

private def idxLastMid (m : ℕ) : Fin (m + 1) := ⟨m - 1, by omega⟩

private theorem idxOne_mem_midSet (hm : 3 ≤ m) : idxOne m (by omega) ∈ midSet m := by
  rw [mem_midSet]
  constructor
  · intro h
    have := congrArg Fin.val h
    simp [idxOne] at this
  · intro h
    have := congrArg Fin.val h
    simp [idxOne, Fin.val_last] at this
    omega

private theorem idxOne_ne_idxLastMid (hm : 3 ≤ m) : idxOne m (by omega) ≠ idxLastMid m := by
  intro h
  have := congrArg Fin.val h
  simp [idxOne, idxLastMid] at this
  omega

private theorem rev_mem_midSet {i : Fin (m + 1)} (hi : i ∈ midSet m) :
    Fin.rev i ∈ midSet m := by
  rw [mem_midSet] at hi ⊢
  constructor
  · intro h
    apply hi.2
    have h' := congrArg Fin.rev h
    simpa using h'
  · intro h
    apply hi.1
    have h' := congrArg Fin.rev h
    simpa using h'

private theorem rev_eq_self_iff (i : Fin (m + 1)) :
    Fin.rev i = i ↔ 2 * i.val = m := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  · intro h
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

private theorem eq_of_rev_eq_self {i j : Fin (m + 1)} (hi : Fin.rev i = i)
    (hj : Fin.rev j = j) : i = j := by
  rw [rev_eq_self_iff] at hi hj
  apply Fin.ext
  omega

private theorem commute_single_entries {d : ℕ} {X : Matrix (Fin d) (Fin d) K} {a b : Fin d}
    (hab : a ≠ b) (h : X * single a b 1 = single a b 1 * X) :
    (∀ i, i ≠ a → X i a = 0) ∧ (∀ j, j ≠ b → X b j = 0) ∧ X a a = X b b := by
  classical
  have key := fun (i j : Fin d) => congrFun (congrFun (congrArg
    (fun M : Matrix (Fin d) (Fin d) K => M) h) i) j
  have hl : ∀ (i : Fin d), (∑ k, X i k * single a b 1 k b) = X i a := by
    intro i
    rw [Finset.sum_eq_single a]
    · simp
    · intro k _ hk
      rw [Matrix.single_apply, if_neg (fun hc => hk hc.1.symm), mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hr : ∀ (i : Fin d), (∑ k, single a b 1 i k * X k b) =
      if i = a then X b b else 0 := by
    intro i
    by_cases hia : i = a
    · subst hia
      rw [Finset.sum_eq_single b]
      · simp
      · intro k _ hk
        rw [Matrix.single_apply, if_neg (fun hc => hk hc.2.symm), zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    · rw [Finset.sum_eq_zero]
      · simp [hia]
      · intro k _
        rw [Matrix.single_apply, if_neg (fun hc => hia hc.1.symm), zero_mul]
  have hcol : ∀ i, X i a = if i = a then X b b else 0 := by
    intro i
    have h1 := key i b
    change (∑ k, X i k * single a b 1 k b) = (∑ k, single a b 1 i k * X k b) at h1
    rw [hl i, hr i] at h1
    exact h1
  have hl2 : ∀ (j : Fin d), (∑ k, X a k * single a b 1 k j) =
      if j = b then X a a else 0 := by
    intro j
    by_cases hjb : j = b
    · subst hjb
      rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hk
        rw [Matrix.single_apply, if_neg (fun hc => hk hc.1.symm), mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    · rw [Finset.sum_eq_zero]
      · simp [hjb]
      · intro k _
        rw [Matrix.single_apply, if_neg (fun hc => hjb hc.2.symm), mul_zero]
  have hr2 : ∀ (j : Fin d), (∑ k, single a b 1 a k * X k j) = X b j := by
    intro j
    rw [Finset.sum_eq_single b]
    · simp
    · intro k _ hk
      rw [Matrix.single_apply, if_neg (fun hc => hk hc.2.symm), zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have hrow : ∀ j, X b j = if j = b then X a a else 0 := by
    intro j
    have h1 := key a j
    change (∑ k, X a k * single a b 1 k j) = (∑ k, single a b 1 a k * X k j) at h1
    rw [hl2 j, hr2 j] at h1
    exact h1.symm
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [hcol i, if_neg hi]
  · rw [hrow j, if_neg hj]
  · have h1 := hcol a
    rw [if_pos rfl] at h1
    exact h1

private def rootMat (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  1 + single (Fin.last m) 0 1

private def y0Mat (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  1 + single 0 (Fin.last m) 1

private theorem last_ne_zero {m : ℕ} (hm : 1 ≤ m) :
    (Fin.last m : Fin (m + 1)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

private theorem isBlockOn_of_commute_root {X : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hm : 1 ≤ m) (hdet : X.det ≠ 0) (hR : X * rootMat m = rootMat m * X)
    (hY : X * y0Mat m = y0Mat m * X) :
    X 0 0 ≠ 0 ∧ IsBlockOn (midSet m) ((X 0 0)⁻¹ • X) := by
  classical
  have hR' : X * single (Fin.last m) 0 1 = single (Fin.last m) 0 1 * X := by
    simpa [rootMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] using hR
  have hY' : X * single 0 (Fin.last m) 1 = single 0 (Fin.last m) 1 * X := by
    simpa [y0Mat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] using hY
  obtain ⟨hcolR, hrowR, hdiagR⟩ :=
    commute_single_entries (last_ne_zero hm) hR'
  obtain ⟨hcolY, hrowY, hdiagY⟩ :=
    commute_single_entries (Ne.symm (last_ne_zero hm)) hY'
  have hα : X 0 0 ≠ 0 := by
    intro h0
    have hrow0 : ∀ j, X 0 j = 0 := by
      intro j
      by_cases hj : j = 0
      · subst hj; exact h0
      · exact hrowR j hj
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero 0 hrow0)
  refine ⟨hα, ?_⟩
  rintro i j (hi | hj)
  · have hi' : i = 0 ∨ i = Fin.last m := by
      by_contra h
      apply hi
      rw [mem_midSet]
      exact ⟨fun h0 => h (Or.inl h0), fun hl => h (Or.inr hl)⟩
    rcases hi' with rfl | rfl
    · by_cases hj0 : j = 0
      · subst hj0
        rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, inv_mul_cancel₀ hα]
      · have hX : X 0 j = 0 := hrowR j hj0
        rw [Matrix.smul_apply, smul_eq_mul, hX, Matrix.one_apply_ne (Ne.symm hj0), mul_zero]
    · by_cases hjl : j = Fin.last m
      · subst hjl
        rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, hdiagR, inv_mul_cancel₀ hα]
      · have hX : X (Fin.last m) j = 0 := hrowY j hjl
        rw [Matrix.smul_apply, smul_eq_mul, hX, Matrix.one_apply_ne (Ne.symm hjl), mul_zero]
  · have hj' : j = 0 ∨ j = Fin.last m := by
      by_contra h
      apply hj
      rw [mem_midSet]
      exact ⟨fun h0 => h (Or.inl h0), fun hl => h (Or.inr hl)⟩
    rcases hj' with rfl | rfl
    · by_cases hi0 : i = 0
      · subst hi0
        rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, inv_mul_cancel₀ hα]
      · have hX : X i 0 = 0 := hcolY i hi0
        rw [Matrix.smul_apply, smul_eq_mul, hX, Matrix.one_apply_ne hi0, mul_zero]
    · by_cases hil : i = Fin.last m
      · subst hil
        rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, hdiagR, inv_mul_cancel₀ hα]
      · have hX : X i (Fin.last m) = 0 := hcolR i hil
        rw [Matrix.smul_apply, smul_eq_mul, hX, Matrix.one_apply_ne hil, mul_zero]

noncomputable abbrev levi (h : UnitaryFieldData 2 f K) (m : ℕ)
    (hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))) : Subgroup (PJ h (m + 1)) :=
  Subgroup.centralizer {projU h (rootU m)} ⊓
    Subgroup.centralizer {projU h (lroot (unitaryInvolution K 2 f) hi₀)}

private theorem coe_rootU_mat (hm : 1 ≤ m) :
    (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = rootMat m := by
  rw [coe_rootU hm]
  rfl

private theorem coe_y0_mat {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))} :
    (((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = y0Mat m := by
  rw [coe_lroot]
  rfl

private theorem conjHom_projU_of_commute (h : UnitaryFieldData 2 f K) (m : ℕ)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    {x : SU (unitaryInvolution K 2 f) (m + 1)}
    (hx : (A : GL (Fin (m + 1)) K) * (x : GL (Fin (m + 1)) K) =
      (x : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K)) :
    primeFormConjHom h _ A (projU h x) = projU h x := by
  rw [projU_apply, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin (m + 1)) K) * ((suEquiv h x : XJ h (m + 1)) : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹ = ((suEquiv h x : XJ h (m + 1)) : GL (Fin (m + 1)) K)
  rw [coe_suEquiv]
  calc (A : GL (Fin (m + 1)) K) * (x : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K)⁻¹ =
      (x : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K)⁻¹ := by
        rw [hx]
    _ = (x : GL (Fin (m + 1)) K) := by group

private theorem conj_preserves_levi (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {x : PJ h (m + 1)} (hx : x ∈ levi h m hi₀) :
    (primeFormConjHom h _ A * c) x ∈ levi h m hi₀ := by
  obtain ⟨hxr, hxy⟩ := hx
  have hxr' : x * projU h (rootU m) = projU h (rootU m) * x :=
    (Subgroup.mem_centralizer_singleton_iff).mp hxr
  have hxy' : x * projU h (lroot (unitaryInvolution K 2 f) hi₀) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀) * x :=
    (Subgroup.mem_centralizer_singleton_iff).mp hxy
  have hcr : c (projU h (rootU m)) = projU h (rootU m) := compl_fixes_rootU h hm hc
  have hcy : c (projU h (lroot (unitaryInvolution K 2 f) hi₀)) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀) := compl_fixes_lroot h hc hi₀
  have hAr : primeFormConjHom h _ A (projU h (rootU m)) = projU h (rootU m) :=
    conjHom_projU_of_commute h m hA₁
  have hAy : primeFormConjHom h _ A (projU h (lroot (unitaryInvolution K 2 f) hi₀)) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀) :=
    conjHom_projU_of_commute h m hA₂
  have hc'r : (primeFormConjHom h _ A * c) (projU h (rootU m)) = projU h (rootU m) := by
    rw [MulAut.mul_apply, hcr, hAr]
  have hc'y : (primeFormConjHom h _ A * c) (projU h (lroot (unitaryInvolution K 2 f) hi₀)) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀) := by
    rw [MulAut.mul_apply, hcy, hAy]
  constructor
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
    calc (primeFormConjHom h _ A * c) x * projU h (rootU m) =
        (primeFormConjHom h _ A * c) x * (primeFormConjHom h _ A * c) (projU h (rootU m)) := by
          rw [hc'r]
      _ = (primeFormConjHom h _ A * c) (x * projU h (rootU m)) := by rw [map_mul]
      _ = (primeFormConjHom h _ A * c) (projU h (rootU m) * x) := by rw [hxr']
      _ = projU h (rootU m) * (primeFormConjHom h _ A * c) x := by rw [map_mul, hc'r])
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
    calc (primeFormConjHom h _ A * c) x *
        projU h (lroot (unitaryInvolution K 2 f) hi₀) =
        (primeFormConjHom h _ A * c) x *
          (primeFormConjHom h _ A * c) (projU h (lroot (unitaryInvolution K 2 f) hi₀)) := by
          rw [hc'y]
      _ = (primeFormConjHom h _ A * c)
          (x * projU h (lroot (unitaryInvolution K 2 f) hi₀)) := by rw [map_mul]
      _ = (primeFormConjHom h _ A * c)
          (projU h (lroot (unitaryInvolution K 2 f) hi₀) * x) := by rw [hxy']
      _ = projU h (lroot (unitaryInvolution K 2 f) hi₀) *
          (primeFormConjHom h _ A * c) x := by rw [map_mul, hc'y])

private theorem projU_surjective (h : UnitaryFieldData 2 f K) (m : ℕ) :
    Function.Surjective (projU h : SU (unitaryInvolution K 2 f) (m + 1) → PJ h (m + 1)) :=
  (QuotientGroup.mk'_surjective _).comp (suEquiv h).surjective

private theorem mem_ker_projU (h : UnitaryFieldData 2 f K) (m : ℕ)
    {x : SU (unitaryInvolution K 2 f) (m + 1)} :
    projU h x = (1 : PJ h (m + 1)) ↔
      (suEquiv h x) ∈ normOneScalars h (XJ h (m + 1)) (m + 1) := by
  rw [projU_apply, QuotientGroup.eq_one_iff]

private theorem one_add_single_sq {d : ℕ} [DecidableEq (Fin d)] {a b : Fin d} (hab : a ≠ b) :
    (1 + single a b (1 : K) : Matrix (Fin d) (Fin d) K) *
      (1 + single a b (1 : K)) = 1 := by
  have hzero : single a b (1 : K) * single a b (1 : K) = 0 :=
    Matrix.single_mul_single_of_ne (1 : K) a b a (hab.symm) (1 : K)
  have h2 : single a b (1 : K) + single a b (1 : K) = 0 := by
    ext i j
    rw [Matrix.add_apply]
    exact CharTwo.add_self_eq_zero _
  calc (1 + single a b (1 : K)) * (1 + single a b (1 : K))
      = 1 * (1 + single a b (1 : K)) +
          single a b (1 : K) * (1 + single a b (1 : K)) := by rw [Matrix.add_mul]
    _ = (1 + single a b (1 : K)) +
          (single a b (1 : K) + single a b (1 : K) * single a b (1 : K)) := by
        rw [Matrix.one_mul, Matrix.mul_add]
        simp only [Matrix.mul_one]
    _ = (1 + single a b (1 : K)) + (single a b (1 : K) + 0) := by rw [hzero]
    _ = 1 := by
        rw [add_zero]
        rw [show (1 : Matrix (Fin d) (Fin d) K) + single a b (1 : K) + single a b (1 : K) =
          1 + (single a b (1 : K) + single a b (1 : K)) by abel]
        rw [h2, add_zero]

private theorem rootMat_sq {m : ℕ} (hm : 1 ≤ m) :
    rootMat (K := K) m * rootMat (K := K) m = 1 := by
  rw [rootMat]
  exact one_add_single_sq (K := K) (d := m + 1) (a := Fin.last m) (b := 0)
    (last_ne_zero hm)

private theorem y0Mat_sq {m : ℕ} (hm : 1 ≤ m) :
    y0Mat (K := K) m * y0Mat (K := K) m = 1 := by
  rw [y0Mat]
  exact one_add_single_sq (K := K) (d := m + 1) (a := 0) (b := Fin.last m)
    (Ne.symm (last_ne_zero hm))

private theorem scalar_unit_eq_one {ζ : Kˣ} (hζ : ζ * ζ = 1) : ζ = 1 := by
  apply Units.ext
  have h : (ζ : K) * (ζ : K) = 1 := by
    rw [← Units.val_mul, hζ, Units.val_one]
  rcases (mul_self_eq_one_iff.mp h) with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]
    rfl

private theorem scalar_conj_eq_one {d : ℕ} (i : Fin d) {X R : GL (Fin d) K} {ζ : Kˣ}
    (hX : X * R * X⁻¹ = GeneralLinearGroup.scalar (Fin d) ζ * R) (hR : R * R = 1) :
    ζ = 1 ∧ X * R = R * X := by
  have hsqL : (X * R * X⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (X * R * X⁻¹) * (X * R * X⁻¹) = X * (R * R) * X⁻¹ := by group
      _ = 1 := by rw [hR]; group
  have hsqR : (GeneralLinearGroup.scalar (Fin d) ζ * R) ^ 2 =
      GeneralLinearGroup.scalar (Fin d) (ζ * ζ) := by
    have hcomm : R * GeneralLinearGroup.scalar (Fin d) ζ =
        GeneralLinearGroup.scalar (Fin d) ζ * R := (commute_scalar ζ R).eq
    rw [pow_two]
    calc (GeneralLinearGroup.scalar (Fin d) ζ * R) *
          (GeneralLinearGroup.scalar (Fin d) ζ * R)
        = GeneralLinearGroup.scalar (Fin d) ζ *
            (R * GeneralLinearGroup.scalar (Fin d) ζ) * R := by group
      _ = GeneralLinearGroup.scalar (Fin d) ζ *
            (GeneralLinearGroup.scalar (Fin d) ζ * R) * R := by rw [hcomm]
      _ = (GeneralLinearGroup.scalar (Fin d) ζ *
            GeneralLinearGroup.scalar (Fin d) ζ) * (R * R) := by group
      _ = GeneralLinearGroup.scalar (Fin d) (ζ * ζ) := by
            rw [hR, mul_one, ← map_mul]
  have hscalar : GeneralLinearGroup.scalar (Fin d) (ζ * ζ) = 1 := by
    rw [← hsqR, ← hX]
    exact hsqL
  have hζ2 : ζ * ζ = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    have h := congrArg (fun u : GL (Fin d) K =>
      ((u : Matrix (Fin d) (Fin d) K) i i)) hscalar
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  have hζ1 : ζ = 1 := scalar_unit_eq_one hζ2
  refine ⟨hζ1, ?_⟩
  have h : X * R * X⁻¹ = R := by
    rw [hX, hζ1]
    rw [show (GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) : GL (Fin d) K) = 1 from by
      apply Units.ext
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]]
    exact one_mul R
  calc X * R = (X * R * X⁻¹) * X := by group
    _ = R * X := by rw [h]

private theorem rootU_GL_sq (m : ℕ) (hm : 1 ≤ m) :
    ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  change (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
    (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1
  rw [coe_rootU_mat hm]
  exact rootMat_sq hm

private theorem y0_GL_sq (m : ℕ) (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))} :
    ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  change (((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
    GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
    (((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1
  rw [coe_y0_mat (hi₀ := hi₀)]
  exact y0Mat_sq hm

private theorem exists_lift_comm (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀) :
    ∃ S : SU (unitaryInvolution K 2 f) (m + 1), projU h S = g ∧
      (((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * rootMat (K := K) m =
        rootMat (K := K) m * ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) ∧
      (((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * y0Mat (K := K) m =
        y0Mat (K := K) m * ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
  classical
  obtain ⟨hgr, hgy⟩ := hg
  have hgr' : g * projU h (rootU m) = projU h (rootU m) * g :=
    (Subgroup.mem_centralizer_singleton_iff).mp hgr
  have hgy' : g * projU h (lroot (unitaryInvolution K 2 f) hi₀) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀) * g :=
    (Subgroup.mem_centralizer_singleton_iff).mp hgy
  obtain ⟨S, hS⟩ := projU_surjective h m g
  have hSR : projU h (S * rootU m) = projU h (rootU m * S) := by
    rw [map_mul, map_mul, hS, hgr']
  have hSY : projU h (S * lroot (unitaryInvolution K 2 f) hi₀) =
      projU h (lroot (unitaryInvolution K 2 f) hi₀ * S) := by
    rw [map_mul, map_mul, hS, hgy']
  let zR : SU (unitaryInvolution K 2 f) (m + 1) :=
    (S * rootU m) * (rootU m * S)⁻¹
  have hzR1 : projU h zR = (1 : PJ h (m + 1)) := by
    change projU h ((S * rootU m) * (rootU m * S)⁻¹) = 1
    rw [map_mul, map_inv, hSR, mul_inv_cancel]
  have hzRker : (suEquiv h zR) ∈ normOneScalars h (XJ h (m + 1)) (m + 1) :=
    (mem_ker_projU h m).mp hzR1
  obtain ⟨ζ, -, -, hζmat⟩ :=
    (mem_normOneScalars (h := h) (H := XJ h (m + 1)) (m := m + 1)).mp hzRker
  have hzRmat : ((zR : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      GeneralLinearGroup.scalar (Fin (m + 1)) ζ := by
    rw [← coe_suEquiv (h := h) (x := zR)]
    exact hζmat
  have hzRdef : ((zR : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      (S : GL (Fin (m + 1)) K) * ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) *
        ((((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
          (S : GL (Fin (m + 1)) K))⁻¹) := by
    change (((S * rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
      (((rootU m * S)⁻¹ : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)) = _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
  have hconjR : (S : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
      (S : GL (Fin (m + 1)) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin (m + 1)) ζ *
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) := by
    have h1 : (S : GL (Fin (m + 1)) K) *
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (S : GL (Fin (m + 1)) K)⁻¹ *
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin (m + 1)) ζ := by
      calc (S : GL (Fin (m + 1)) K) *
            ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
            (S : GL (Fin (m + 1)) K)⁻¹ *
            ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)⁻¹
          = (S : GL (Fin (m + 1)) K) *
            ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
            (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K))⁻¹ := by group
        _ = ((zR : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) := by
              rw [hzRdef]
        _ = GeneralLinearGroup.scalar (Fin (m + 1)) ζ := hzRmat
    calc (S : GL (Fin (m + 1)) K) *
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (S : GL (Fin (m + 1)) K)⁻¹ =
        ((S : GL (Fin (m + 1)) K) *
          ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
          (S : GL (Fin (m + 1)) K)⁻¹ *
          ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)⁻¹) *
          ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) := by
          group
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) ζ *
          ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) := by
          rw [h1]
  obtain ⟨hζ1, hcommR⟩ :=
    scalar_conj_eq_one (0 : Fin (m + 1)) hconjR (rootU_GL_sq m (by omega))
  have hSRmat : ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      rootMat (K := K) m = rootMat (K := K) m *
        ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have h : (S : GL (Fin (m + 1)) K) *
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
        ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
          (S : GL (Fin (m + 1)) K) := by
      calc (S : GL (Fin (m + 1)) K) *
            ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)
          = ((S : GL (Fin (m + 1)) K) *
              ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K)⁻¹) * (S : GL (Fin (m + 1)) K) := by group
        _ = ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K) := by rw [hcommR]; group
    have hmat := congrArg (fun u : GL (Fin (m + 1)) K =>
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) h
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
      coe_rootU_mat (by omega)] at hmat
    exact hmat
  let zY : SU (unitaryInvolution K 2 f) (m + 1) :=
    (S * lroot (unitaryInvolution K 2 f) hi₀) *
      (lroot (unitaryInvolution K 2 f) hi₀ * S)⁻¹
  have hzY1 : projU h zY = (1 : PJ h (m + 1)) := by
    change projU h ((S * lroot (unitaryInvolution K 2 f) hi₀) *
      (lroot (unitaryInvolution K 2 f) hi₀ * S)⁻¹) = 1
    rw [map_mul, map_inv, hSY, mul_inv_cancel]
  have hzYker : (suEquiv h zY) ∈ normOneScalars h (XJ h (m + 1)) (m + 1) :=
    (mem_ker_projU h m).mp hzY1
  obtain ⟨ξ, -, -, hξmat⟩ :=
    (mem_normOneScalars (h := h) (H := XJ h (m + 1)) (m := m + 1)).mp hzYker
  have hzYmat : ((zY : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      GeneralLinearGroup.scalar (Fin (m + 1)) ξ := by
    rw [← coe_suEquiv (h := h) (x := zY)]
    exact hξmat
  have hzYdef : ((zY : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      (S : GL (Fin (m + 1)) K) *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) *
        ((((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) * (S : GL (Fin (m + 1)) K))⁻¹) := by
    change (((S * lroot (unitaryInvolution K 2 f) hi₀ :
      SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
      (((lroot (unitaryInvolution K 2 f) hi₀ * S)⁻¹ :
        SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)) = _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
  have hconjY : (S : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) *
      (S : GL (Fin (m + 1)) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin (m + 1)) ξ *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) := by
    have h1 : (S : GL (Fin (m + 1)) K) *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) *
        (S : GL (Fin (m + 1)) K)⁻¹ *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin (m + 1)) ξ := by
      calc (S : GL (Fin (m + 1)) K) *
            ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
              GL (Fin (m + 1)) K) *
            (S : GL (Fin (m + 1)) K)⁻¹ *
            ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
              GL (Fin (m + 1)) K)⁻¹
          = (S : GL (Fin (m + 1)) K) *
            ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
              GL (Fin (m + 1)) K) *
            (((lroot (unitaryInvolution K 2 f) hi₀ : SU
                (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K))⁻¹ := by group
        _ = ((zY : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) := by
              rw [hzYdef]
        _ = GeneralLinearGroup.scalar (Fin (m + 1)) ξ := hzYmat
    calc (S : GL (Fin (m + 1)) K) *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) *
        (S : GL (Fin (m + 1)) K)⁻¹ =
        ((S : GL (Fin (m + 1)) K) *
          ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
            GL (Fin (m + 1)) K) *
          (S : GL (Fin (m + 1)) K)⁻¹ *
          ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
            GL (Fin (m + 1)) K)⁻¹) *
          ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
            GL (Fin (m + 1)) K) := by
          group
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) ξ *
          ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
            GL (Fin (m + 1)) K) := by
          rw [h1]
  obtain ⟨hξ1, hcommY⟩ :=
    scalar_conj_eq_one (0 : Fin (m + 1)) hconjY (y0_GL_sq m (by omega) (hi₀ := hi₀))
  have hSYmat : ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      y0Mat (K := K) m = y0Mat (K := K) m *
        ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have h : (S : GL (Fin (m + 1)) K) *
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) =
        ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) * (S : GL (Fin (m + 1)) K) := by
      calc (S : GL (Fin (m + 1)) K) *
            ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
              GL (Fin (m + 1)) K)
          = ((S : GL (Fin (m + 1)) K) *
              ((lroot (unitaryInvolution K 2 f) hi₀ : SU
                (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K)⁻¹) * (S : GL (Fin (m + 1)) K) := by group
        _ = ((lroot (unitaryInvolution K 2 f) hi₀ : SU
              (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
              (S : GL (Fin (m + 1)) K) := by rw [hcommY]; group
    have hmat := congrArg (fun u : GL (Fin (m + 1)) K =>
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) h
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
      coe_y0_mat (hi₀ := hi₀)] at hmat
    exact hmat
  exact ⟨S, hS, hSRmat, hSYmat⟩

private theorem exists_scalar_of_projU_eq (h : UnitaryFieldData 2 f K) (m : ℕ)
    {x y : SU (unitaryInvolution K 2 f) (m + 1)} (hxy : projU h x = projU h y) :
    ∃ ζ : Kˣ, ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (ζ : K) • ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  classical
  have hq : ((suEquiv h x * (suEquiv h y)⁻¹ : XJ h (m + 1)) : PJ h (m + 1)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← projU_apply, ← projU_apply,
      hxy, mul_inv_cancel]
  have hmem : (suEquiv h x * (suEquiv h y)⁻¹) ∈
      normOneScalars h (XJ h (m + 1)) (m + 1) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hq
  obtain ⟨ζ, -, -, hζ⟩ :=
    (mem_normOneScalars (h := h) (H := XJ h (m + 1)) (m := m + 1)).mp hmem
  have hζ' : ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((((y : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ =
      (ζ : K) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have h1 : ((suEquiv h x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((((suEquiv h y : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ =
        (ζ : K) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
      have h1gl : ((suEquiv h x * (suEquiv h y)⁻¹ : XJ h (m + 1)) :
          GL (Fin (m + 1)) K) = GeneralLinearGroup.scalar (Fin (m + 1)) ζ := hζ
      have h2 := congrArg (fun u : GL (Fin (m + 1)) K =>
        ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) h1gl
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, GeneralLinearGroup.coe_mul,
        GeneralLinearGroup.coe_inv, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal] using h2
    simpa only [coe_suEquiv] using h1
  refine ⟨ζ, ?_⟩
  have hy : ((((y : GL (Fin (m + 1)) K)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ *
      (((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) = 1 := by
    have hval : ((((y : GL (Fin (m + 1)) K)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ =
        (((y⁻¹ : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :=
      (GeneralLinearGroup.coe_inv (y : GL (Fin (m + 1)) K)).symm
    rw [hval, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      = ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (((((y : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ *
            ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
          rw [hy, Matrix.mul_one]
    _ = (((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((((y : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹) *
          ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
          rw [Matrix.mul_assoc]
    _ = ((ζ : K) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *
          ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by rw [hζ']
    _ = (ζ : K) • ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
          rw [Matrix.smul_mul, Matrix.one_mul]

private theorem zero_not_mem_midSet : (0 : Fin (m + 1)) ∉ midSet m := by
  rw [mem_midSet]
  exact fun h => h.1 rfl

private theorem exists_scalar_of_xj_eq (h : UnitaryFieldData 2 f K) (m : ℕ)
    {x y : XJ h (m + 1)} (hxy : (x : PJ h (m + 1)) = (y : PJ h (m + 1))) :
    ∃ ζ : Kˣ, ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (ζ : K) • ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  have hxy' : projU h ((suEquiv h).symm x) = projU h ((suEquiv h).symm y) := by
    rw [projU_apply, projU_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hxy
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_projU_eq h m hxy'
  exact ⟨ζ, hζ⟩

private theorem key_matrix_eq (h : UnitaryFieldData 2 f K) (m : ℕ) (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀, (primeFormConjHom h _ A * c) k ∈ levi h m hi₀ →
      g * (primeFormConjHom h _ A * c) k * g⁻¹ = k)
    {S : SU (unitaryInvolution K 2 f) (m + 1)} (hSπ : projU h S = g)
    {x : SU (unitaryInvolution K 2 f) (m + 1)} {xXJ : XJ h (m + 1)}
    (hxXJ : (xXJ : PJ h (m + 1)) =
      (primeFormConjHom h _ A * c) (projU h x))
    (hxL : projU h x ∈ levi h m hi₀) :
    ∃ ζ : Kˣ, ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((xXJ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (ζ : K) • (((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
  have hxL' : (primeFormConjHom h _ A * c) (projU h x) ∈ levi h m hi₀ :=
    conj_preserves_levi h hm hc hA₁ hA₂ hxL
  have hkeyx := hkey (projU h x) hxL hxL'
  have hkeyx' : g * ((primeFormConjHom h _ A * c) (projU h x)) = (projU h x) * g := by
    have h1 := congrArg (fun z => z * g) hkeyx
    simpa [mul_assoc] using h1
  have hq : ((suEquiv h S * xXJ : XJ h (m + 1)) : PJ h (m + 1)) =
      ((suEquiv h x * suEquiv h S : XJ h (m + 1)) : PJ h (m + 1)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    change projU h S * (xXJ : PJ h (m + 1)) = projU h x * projU h S
    rw [hxXJ, hSπ]
    exact hkeyx'
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_xj_eq h m hq
  refine ⟨ζ, ?_⟩
  simpa only [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, coe_suEquiv] using hζ

private theorem key_T_eq (h : UnitaryFieldData 2 f K) (m : ℕ) (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀, (primeFormConjHom h _ A * c) k ∈ levi h m hi₀ →
      g * (primeFormConjHom h _ A * c) k * g⁻¹ = k)
    {S : SU (unitaryInvolution K 2 f) (m + 1)} (hSπ : projU h S = g)
    {x y : SU (unitaryInvolution K 2 f) (m + 1)} {xXJ : XJ h (m + 1)}
    (hxXJ : (xXJ : PJ h (m + 1)) =
      (primeFormConjHom h _ A * c) (projU h x))
    (hxL : projU h x ∈ levi h m hi₀)
    (hxA_A : (xXJ : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) =
      (A : GL (Fin (m + 1)) K) * (y : GL (Fin (m + 1)) K)) :
    ∃ ζ : Kˣ, ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (((y : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (ζ : K) • ((((x : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
          GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
  obtain ⟨ζ, hζ⟩ := key_matrix_eq h m hm hc hA₁ hA₂ hg hkey hSπ hxXJ hxL
  refine ⟨ζ, ?_⟩
  have hA' := congrArg (fun u : GL (Fin (m + 1)) K =>
    ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) hxA_A
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul] at hA'
  have h1 := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) K =>
    M * ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) hζ
  rw [Matrix.mul_assoc, Matrix.smul_mul] at h1
  calc ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (((y : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      = (((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((xXJ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *
          ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
          rw [GeneralLinearGroup.coe_mul]
          simp only [Matrix.mul_assoc]
          rw [hA']
    _ = (ζ : K) • ((((x : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
            GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
          rw [GeneralLinearGroup.coe_mul]
          simpa only [Matrix.mul_assoc] using h1

private theorem isBlockOn_lroot {i : Fin (m + 1)} (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m) :
    IsBlockOn (midSet m) (((lroot (unitaryInvolution K 2 f) hi :
      SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  rw [coe_lroot]
  rintro a b (ha | hb)
  · have hia : i ≠ a := fun h => ha (h ▸ hiS)
    rw [Matrix.add_apply, Matrix.single_apply, if_neg (fun hc => hia hc.1), add_zero]
  · have hjb : Fin.rev i ≠ b := fun h => hb (h ▸ rev_mem_midSet hiS)
    rw [Matrix.add_apply, Matrix.single_apply, if_neg (fun hc => hjb hc.2), add_zero]

private theorem one_add_single_comm {d : ℕ} [DecidableEq (Fin d)] {a b c e : Fin d}
    (hbc : b ≠ c) (hea : e ≠ a) :
    (1 + single a b (1 : K) : Matrix (Fin d) (Fin d) K) * (1 + single c e (1 : K)) =
      (1 + single c e (1 : K)) * (1 + single a b (1 : K)) := by
  have hEF : single a b (1 : K) * single c e (1 : K) = 0 :=
    Matrix.single_mul_single_of_ne (1 : K) a b c hbc (1 : K)
  have hFE : single c e (1 : K) * single a b (1 : K) = 0 :=
    Matrix.single_mul_single_of_ne (1 : K) c e a hea (1 : K)
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hEF, hFE]
  abel

private theorem lroot_comm_rootMat {i : Fin (m + 1)} (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m) :
    (((lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * rootMat (K := K) m =
      rootMat (K := K) m *
        (((lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  rw [coe_lroot, rootMat]
  exact one_add_single_comm (mem_midSet.mp (rev_mem_midSet hiS)).2
    (Ne.symm (mem_midSet.mp hiS).1)

private theorem lroot_comm_y0Mat {i : Fin (m + 1)} (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m) :
    (((lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * y0Mat (K := K) m =
      y0Mat (K := K) m *
        (((lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  rw [coe_lroot, y0Mat]
  exact one_add_single_comm (mem_midSet.mp (rev_mem_midSet hiS)).1
    (Ne.symm (mem_midSet.mp hiS).2)

private theorem lroot_mem_levi (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {i : Fin (m + 1)} (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m) :
    projU h (lroot (unitaryInvolution K 2 f) hi) ∈ levi h m hi₀ := by
  have hxR : (lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) *
      rootU m = rootU m * lroot (unitaryInvolution K 2 f) hi := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Subgroup.coe_mul,
      GeneralLinearGroup.coe_mul, coe_rootU_mat (by omega)]
    exact lroot_comm_rootMat (K := K) (m := m) hi hiS
  have hxY : (lroot (unitaryInvolution K 2 f) hi : SU (unitaryInvolution K 2 f) (m + 1)) *
      lroot (unitaryInvolution K 2 f) hi₀ =
      lroot (unitaryInvolution K 2 f) hi₀ * lroot (unitaryInvolution K 2 f) hi := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Subgroup.coe_mul,
      GeneralLinearGroup.coe_mul, coe_y0_mat (hi₀ := hi₀)]
    exact lroot_comm_y0Mat (K := K) (m := m) hi hiS
  constructor
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      rw [← map_mul, ← map_mul, hxR])
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      rw [← map_mul, ← map_mul, hxY])

private theorem T_comm_single_middle (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀, (primeFormConjHom h _ A * c) k ∈ levi h m hi₀ →
      g * (primeFormConjHom h _ A * c) k * g⁻¹ = k)
    {S : SU (unitaryInvolution K 2 f) (m + 1)} (hSπ : projU h S = g)
    {i : Fin (m + 1)} (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m)
    (hT00 : (((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 ≠ 0) :
    (((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      single i (Fin.rev i) (1 : K) =
      single i (Fin.rev i) (1 : K) *
        (((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  let T : GL (Fin (m + 1)) K := (S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K)
  change ((T : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      single i (Fin.rev i) (1 : K) =
    single i (Fin.rev i) (1 : K) *
      ((T : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  let xsu : SU (unitaryInvolution K 2 f) (m + 1) :=
    lroot (unitaryInvolution K 2 f) hi
  let xXJ : XJ h (m + 1) := suEquiv h xsu
  let xA : XJ h (m + 1) :=
    ⟨(A : GL (Fin (m + 1)) K) * (xXJ : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹,
      conj_mem_gramSU h _ A.2 xXJ.2⟩
  have hxA_proj : (xA : PJ h (m + 1)) =
      (primeFormConjHom h _ A * c) (projU h xsu) := by
    rw [MulAut.mul_apply]
    change (xA : PJ h (m + 1)) =
      primeFormConjHom h _ A (c (projU h xsu))
    rw [show c (projU h xsu) = projU h xsu from compl_fixes_lroot h hc hi]
    rw [projU_apply, primeFormConjHom_mk]
  have hxA_A : (xA : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) =
      (A : GL (Fin (m + 1)) K) * (xsu : GL (Fin (m + 1)) K) := by
    change ((A : GL (Fin (m + 1)) K) * (xXJ : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹) * (A : GL (Fin (m + 1)) K) =
      (A : GL (Fin (m + 1)) K) * (xsu : GL (Fin (m + 1)) K)
    rw [coe_suEquiv]
    group
  obtain ⟨ζ, hEqT⟩ := key_T_eq h m (by omega) hc hA₁ hA₂ hg hkey hSπ
    hxA_proj (lroot_mem_levi h (by omega) hi hiS) hxA_A
  change ((T : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (((xsu : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (ζ : K) • ((((xsu : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((T : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) at hEqT
  have h00 := congrFun (congrFun hEqT (0 : Fin (m + 1))) (0 : Fin (m + 1))
  have hx00 : (((xsu : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 = 1 := by
    rw [coe_lroot, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
      if_neg (by
        intro hc'
        exact (mem_midSet.mp hiS).1 hc'.1)]
    simp
  have hx0 : ∀ j : Fin (m + 1), j ≠ 0 →
      (((xsu : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) j 0 = 0 := by
    intro j hj
    have hb := isBlockOn_lroot (f := f) (K := K) (m := m) hi hiS j 0
      (Or.inr zero_not_mem_midSet)
    rw [Matrix.one_apply, if_neg hj] at hb
    exact hb
  have hx0' : ∀ j : Fin (m + 1), j ≠ 0 →
      (((xsu : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 j = 0 := by
    intro j hj
    have hb := isBlockOn_lroot (f := f) (K := K) (m := m) hi hiS 0 j
      (Or.inl zero_not_mem_midSet)
    rw [Matrix.one_apply, if_neg (Ne.symm hj)] at hb
    exact hb
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h00
  rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hx0 j hj, mul_zero])
    (fun h => absurd (Finset.mem_univ 0) h)] at h00
  rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hx0' j hj, zero_mul])
    (fun h => absurd (Finset.mem_univ 0) h)] at h00
  rw [hx00] at h00
  simp only [mul_one, one_mul] at h00
  have hζ : ζ = 1 := by
    have hT00' : ((T : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 ≠ 0 := hT00
    have h00' : ((T : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 * 1 =
        ((T : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 * (ζ : K) := by
      rw [mul_one, mul_comm]
      exact h00
    have h1 : (1 : K) = (ζ : K) := mul_left_cancel₀ hT00' h00'
    exact Units.ext h1.symm
  rw [hζ, Units.val_one, one_smul] at hEqT
  have hx : (((xsu : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      1 + single i (Fin.rev i) (1 : K) := by
    rw [coe_lroot]
  rw [hx, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hEqT
  exact add_left_cancel hEqT

private theorem T_diagonal_and_ne (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀, (primeFormConjHom h _ A * c) k ∈ levi h m hi₀ →
      g * (primeFormConjHom h _ A * c) k * g⁻¹ = k)
    {S : SU (unitaryInvolution K 2 f) (m + 1)} (hSπ : projU h S = g)
    (hSR : ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      rootMat (K := K) m = rootMat (K := K) m *
        ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
    (hSY : ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      y0Mat (K := K) m = y0Mat (K := K) m *
        ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) :
    (∀ a b : Fin (m + 1), a ≠ b →
      ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a b = 0) ∧
    (∀ i : Fin (m + 1),
      ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i ≠ 0) := by
  let T : GL (Fin (m + 1)) K := (S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K)
  let Tm : Matrix (Fin (m + 1)) (Fin (m + 1)) K := (T : GL (Fin (m + 1)) K)
  change (∀ a b : Fin (m + 1), a ≠ b → Tm a b = 0) ∧ (∀ i : Fin (m + 1), Tm i i ≠ 0)
  have hTm : Tm = ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := rfl
  have hAdet : (((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin (m + 1)) K).isUnit).ne_zero
  have hSdet : (((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (S : GL (Fin (m + 1)) K).isUnit).ne_zero
  have hA1m : ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      rootMat (K := K) m = rootMat (K := K) m *
        ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have h := congrArg (fun u : GL (Fin (m + 1)) K =>
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) hA₁
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, coe_rootU_mat (by omega)] at h
    exact h
  have hA2m : ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      y0Mat (K := K) m = y0Mat (K := K) m *
        ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have h := congrArg (fun u : GL (Fin (m + 1)) K =>
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) hA₂
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, coe_y0_mat (hi₀ := hi₀)] at h
    exact h
  have hTR : Tm * rootMat (K := K) m = rootMat (K := K) m * Tm := by
    rw [hTm, Matrix.mul_assoc, hA1m, ← Matrix.mul_assoc, hSR, Matrix.mul_assoc]
  have hTY : Tm * y0Mat (K := K) m = y0Mat (K := K) m * Tm := by
    rw [hTm, Matrix.mul_assoc, hA2m, ← Matrix.mul_assoc, hSY, Matrix.mul_assoc]
  have hTdet : Tm.det ≠ 0 := by
    rw [hTm, Matrix.det_mul]
    exact mul_ne_zero hSdet hAdet
  obtain ⟨hT00, -⟩ := isBlockOn_of_commute_root (m := m) (by omega) hTdet hTR hTY
  have hmid : ∀ (i : Fin (m + 1)) (hi : i ≠ Fin.rev i) (hiS : i ∈ midSet m),
      Tm * single i (Fin.rev i) (1 : K) = single i (Fin.rev i) (1 : K) * Tm := by
    intro i hi hiS
    exact T_comm_single_middle h hm hc hA₁ hA₂ hg hkey hSπ hi hiS hT00
  have hcornerR : Tm * single (Fin.last m) 0 (1 : K) =
      single (Fin.last m) 0 (1 : K) * Tm := by
    simpa [rootMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] using hTR
  have hcornerY : Tm * single 0 (Fin.last m) (1 : K) =
      single 0 (Fin.last m) (1 : K) * Tm := by
    simpa [y0Mat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] using hTY
  have hlast0 : (Fin.last m : Fin (m + 1)) ≠ 0 := last_ne_zero (by omega)
  obtain ⟨hcolR, hrowR, hdiagR⟩ := commute_single_entries hlast0 hcornerR
  obtain ⟨hcolY, hrowY, hdiagY⟩ := commute_single_entries (Ne.symm hlast0) hcornerY
  have hdiag_all : ∀ a b : Fin (m + 1), a ≠ b → Tm a b = 0 := by
    intro a b hab
    by_cases hb0 : b = 0
    · subst hb0
      exact hcolY a hab
    by_cases hbl : b = Fin.last m
    · subst hbl
      exact hcolR a hab
    have hbS : b ∈ midSet m := mem_midSet.mpr ⟨hb0, hbl⟩
    by_cases hbrev : b = Fin.rev b
    · by_cases ha0 : a = 0
      · subst ha0
        exact hrowR b hb0
      by_cases hal : a = Fin.last m
      · subst hal
        exact hrowY b hbl
      have haS : a ∈ midSet m := mem_midSet.mpr ⟨ha0, hal⟩
      have harev : a ≠ Fin.rev a := by
        intro ha
        exact hab (eq_of_rev_eq_self ha.symm hbrev.symm)
      have hrev_ne : Fin.rev a ≠ Fin.rev (Fin.rev a) := by
        intro h
        exact harev (Fin.rev_injective h)
      have hrevS : Fin.rev a ∈ midSet m := rev_mem_midSet haS
      have hsingle := hmid (Fin.rev a) hrev_ne hrevS
      obtain ⟨-, hrow, -⟩ := commute_single_entries hrev_ne hsingle
      have hbne : b ≠ Fin.rev (Fin.rev a) := by
        simpa using (Ne.symm hab)
      have := hrow b hbne
      simpa using this
    · have hsingle := hmid b hbrev hbS
      obtain ⟨hcol, -, -⟩ := commute_single_entries hbrev hsingle
      exact hcol a hab
  refine ⟨hdiag_all, ?_⟩
  have hdiag : Tm = diagonal (fun i => Tm i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [hdiag_all i j hij]
      exact (Matrix.diagonal_apply_ne (fun i => Tm i i) hij).symm
  have hprod : ∏ i : Fin (m + 1), Tm i i ≠ 0 := by
    rwa [hdiag, Matrix.det_diagonal] at hTdet
  intro i
  exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)

private theorem diag_comm_one_add_single {d : ℕ} [DecidableEq (Fin d)] {t : Fin d → K}
    {i j : Fin d} (h : t i = t j) :
    Matrix.diagonal t * (1 + Matrix.single i j (1 : K)) =
      (1 + Matrix.single i j (1 : K)) * Matrix.diagonal t := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  ext a c
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with hac
  · obtain ⟨rfl, rfl⟩ := hac
    rw [h, mul_one, one_mul]
  · simp

private theorem diagonal_comm_rootMat {t : Fin (m + 1) → K} (h : t 0 = t (Fin.last m)) :
    Matrix.diagonal t * rootMat (K := K) m = rootMat (K := K) m * Matrix.diagonal t := by
  rw [rootMat]
  exact diag_comm_one_add_single h.symm

private theorem diagonal_comm_y0Mat {t : Fin (m + 1) → K} (h : t 0 = t (Fin.last m)) :
    Matrix.diagonal t * y0Mat (K := K) m = y0Mat (K := K) m * Matrix.diagonal t := by
  rw [y0Mat]
  exact diag_comm_one_add_single h

private theorem diagSU_mem_levi (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 1 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {t : Fin (m + 1) → K}
    (ht : ∀ a, unitaryInvolution K 2 f (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) (h0last : t 0 = t (Fin.last m)) :
    projU h (RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet) ∈
      levi h m hi₀ := by
  let D : SU (unitaryInvolution K 2 f) (m + 1) :=
    RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet
  have hDmat : (((D : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal t := by
    rw [show D = RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet from rfl,
      RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL]
  have hDR : D * rootU m = rootU m * D := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Subgroup.coe_mul,
      GeneralLinearGroup.coe_mul, hDmat, coe_rootU_mat (by omega)]
    exact diagonal_comm_rootMat (K := K) (m := m) h0last
  have hDY : D * lroot (unitaryInvolution K 2 f) hi₀ =
      lroot (unitaryInvolution K 2 f) hi₀ * D := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Subgroup.coe_mul,
      GeneralLinearGroup.coe_mul, hDmat, coe_y0_mat (hi₀ := hi₀)]
    exact diagonal_comm_y0Mat (K := K) (m := m) h0last
  constructor
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      rw [← map_mul, ← map_mul, hDR])
  · exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      rw [← map_mul, ← map_mul, hDY])

private theorem fieldAut_diagSU (h : UnitaryFieldData 2 f K) {φ : K ≃+* K}
    {n : ℕ} {t : Fin n → K}
    (ht : ∀ a, unitaryInvolution K 2 f (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) :
    primeFormFieldHom h (isPrimeFormGram_gramJ (n := n)) φ
        (projU h (RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet)) =
      projU h (RootDetectSU.diagSU (unitaryInvolution K 2 f) (fun a => φ (t a))
        (fun a => by
          rw [show unitaryInvolution K 2 f (φ (t a)) =
              φ (unitaryInvolution K 2 f (t a)) from by
            rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow]]
          rw [← map_mul, ht a, map_one])
        (by rw [← map_prod, hdet, map_one])) := by
  have hφσ : ∀ c, φ (unitaryInvolution K 2 f c) = unitaryInvolution K 2 f (φ c) := by
    intro c
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow]
  rw [projU_apply]
  change primeFormFieldHom h _ φ
      ((suEquiv h (RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet) :
        XJ h n) : PJ h n) = _
  rw [show primeFormFieldHom h (isPrimeFormGram_gramJ (n := n)) φ =
      primeFormFieldAut h _ φ from rfl, primeFormFieldAut_mk]
  rw [projU_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((glAut φ (suEquiv h (RootDetectSU.diagSU (unitaryInvolution K 2 f) t ht hdet) :
      GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  simp only [coe_glAut, coe_suEquiv, RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL]
  rw [Matrix.diagonal_map (map_zero φ)]

private theorem torus_phi_sq (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {φ : K ≃+* K}
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀,
      (primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_gramJ (n := m + 1)) φ) k ∈
        levi h m hi₀ →
      g * (primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_gramJ (n := m + 1)) φ) k *
        g⁻¹ = k)
    {S : SU (unitaryInvolution K 2 f) (m + 1)} (hSπ : projU h S = g)
    (hTne : ∀ i : Fin (m + 1),
      ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i ≠ 0)
    (e : K) (he : e ≠ 0) :
    φ e ^ 2 = e ^ 2 := by
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hσ : ∀ c, σ (σ c) = c := fun c => h.bar_bar c
  let b : Fin (m + 1) := idxOne m (by omega)
  have hb : b ≠ Fin.rev b := by
    dsimp [b]
    exact idxOne_ne_idxLastMid (by omega)
  let μ : K := σ e * e⁻¹
  let ν : K := e ^ 2
  have hμ0 : μ ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr he) (inv_ne_zero he)
  have hν0 : ν ≠ 0 := pow_ne_zero 2 he
  let t : Fin (m + 1) → K := RootDetectSU.pairDiag σ 0 μ * RootDetectSU.pairDiag σ b ν
  have htunit : ∀ a, σ (t a) * t (Fin.rev a) = 1 := by
    intro a
    dsimp [t]
    exact (by
      simpa only [Pi.mul_apply, map_mul] using
        RootDetectSU.unitary_mul (RootDetectSU.pairDiag_unitary hσ hi₀ hμ0)
          (RootDetectSU.pairDiag_unitary hσ hb hν0) a)
  have hσμ : σ μ = μ⁻¹ := by
    dsimp [μ]
    rw [map_mul, map_inv₀, hσ, _root_.mul_inv_rev, inv_inv]
  have hσν : σ ν = σ e ^ 2 := by
    dsimp [ν]
    rw [map_pow]
  have hdet : ∏ a, t a = 1 := by
    dsimp [t]
    rw [Finset.prod_mul_distrib, RootDetectSU.prod_pairDiag hi₀,
      RootDetectSU.prod_pairDiag hb, hσμ, inv_inv, hσν]
    dsimp [μ, ν]
    field_simp [he, (map_ne_zero σ).mpr he]
  have ht0 : t 0 = μ := by
    dsimp [t]
    rw [RootDetectSU.pairDiag_self]
    have h1 : (0 : Fin (m + 1)) ≠ b := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne] at this
    have h2 : (0 : Fin (m + 1)) ≠ Fin.rev b := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.rev] at this
      omega
    rw [RootDetectSU.pairDiag_of_ne h1 h2, mul_one]
  have htlast : t (Fin.last m) = μ := by
    dsimp [t]
    rw [show (Fin.last m : Fin (m + 1)) = Fin.rev (0 : Fin (m + 1)) from rfl,
      RootDetectSU.pairDiag_rev hi₀, hσμ, inv_inv]
    have h3 : (Fin.last m : Fin (m + 1)) ≠ b := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.val_last] at this
      omega
    have h4 : (Fin.last m : Fin (m + 1)) ≠ Fin.rev b := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.rev, Fin.val_last] at this
      omega
    rw [show Fin.rev (0 : Fin (m + 1)) = Fin.last m from rfl,
      RootDetectSU.pairDiag_of_ne h3 h4, mul_one]
  have htb : t b = ν := by
    dsimp [t]
    have h1 : b ≠ 0 := (mem_midSet.mp (idxOne_mem_midSet hm)).1
    have h2 : b ≠ Fin.rev 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.rev] at this
      omega
    rw [show RootDetectSU.pairDiag σ 0 μ b = 1 from
      RootDetectSU.pairDiag_of_ne h1 h2 μ]
    rw [RootDetectSU.pairDiag_self, one_mul]
  have htrev : t (Fin.rev b) = (σ ν)⁻¹ := by
    dsimp [t]
    have h1 : Fin.rev b ≠ 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.rev] at this
      omega
    have h2 : Fin.rev b ≠ Fin.last m := by
      intro hh
      have := congrArg Fin.val hh
      simp [b, idxOne, Fin.rev, Fin.val_last] at this
      omega
    rw [show RootDetectSU.pairDiag σ 0 μ (Fin.rev b) = 1 from
      RootDetectSU.pairDiag_of_ne h1 h2 μ]
    rw [RootDetectSU.pairDiag_rev hb, one_mul]
  let tφ : Fin (m + 1) → K := fun a => φ (t a)
  have htφ : ∀ a, σ (tφ a) * tφ (Fin.rev a) = 1 := by
    intro a
    dsimp [tφ]
    change unitaryInvolution K 2 f (φ (t a)) * φ (t (Fin.rev a)) = 1
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    rw [← map_pow, ← map_mul]
    have h : t a ^ 2 ^ f * t (Fin.rev a) = 1 := by
      have h' := htunit a
      change h.bar (t a) * t (Fin.rev a) = 1 at h'
      simpa [h.bar_apply] using h'
    rw [h, map_one]
  have hdetφ : ∏ a, tφ a = 1 := by
    dsimp [tφ]
    rw [← map_prod, hdet, map_one]
  let D : SU (unitaryInvolution K 2 f) (m + 1) :=
    RootDetectSU.diagSU σ t htunit hdet
  let Dφ : SU (unitaryInvolution K 2 f) (m + 1) :=
    RootDetectSU.diagSU σ tφ htφ hdetφ
  have hDmat : (((D : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      Matrix.diagonal t := by
    dsimp [D]
    rw [RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL]
  have hDφmat : (((Dφ : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      Matrix.diagonal tφ := by
    dsimp [Dφ]
    rw [RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL]
  have hxL : projU h D ∈ levi h m hi₀ :=
    diagSU_mem_levi h (by omega) htunit hdet (by rw [ht0, htlast])
  have hcD : primeFormFieldHom h (isPrimeFormGram_gramJ (n := m + 1)) φ
      (projU h D) = projU h Dφ := by
    dsimp [D, Dφ, tφ]
    exact fieldAut_diagSU h htunit hdet
  have hcφ : primeFormFieldHom h (isPrimeFormGram_gramJ (n := m + 1)) φ ∈ compl h := ⟨φ, rfl⟩
  let xXJ : XJ h (m + 1) :=
    ⟨(A : GL (Fin (m + 1)) K) * (suEquiv h Dφ : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹,
      conj_mem_gramSU h _ A.2 (suEquiv h Dφ).2⟩
  have hxXJ : (xXJ : PJ h (m + 1)) =
      (primeFormConjHom h _ A *
        primeFormFieldHom h (isPrimeFormGram_gramJ (n := m + 1)) φ) (projU h D) := by
    rw [MulAut.mul_apply, hcD]
    rw [projU_apply, primeFormConjHom_mk]
  have hxA_A : (xXJ : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) =
      (A : GL (Fin (m + 1)) K) * (Dφ : GL (Fin (m + 1)) K) := by
    change ((A : GL (Fin (m + 1)) K) * (suEquiv h Dφ : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹) * (A : GL (Fin (m + 1)) K) =
      (A : GL (Fin (m + 1)) K) * (Dφ : GL (Fin (m + 1)) K)
    rw [coe_suEquiv]
    group
  obtain ⟨ζ, hEqT⟩ := key_T_eq h m (by omega) hcφ hA₁ hA₂ hg hkey hSπ
    hxXJ hxL hxA_A
  have hentry : ∀ i, φ (t i) = (ζ : K) * t i := by
    intro i
    have hii := congrFun (congrFun hEqT i) i
    rw [hDφmat, hDmat] at hii
    rw [Matrix.mul_diagonal] at hii
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul] at hii
    have hii' : ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
        GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i *
        φ (t i) =
        ((((S : GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K) :
          GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i *
          ((ζ : K) * t i) := by
      calc _ = (ζ : K) * (t i * _) := hii
        _ = _ := by ring
    exact mul_left_cancel₀ (hTne i) hii'
  have h0 := hentry 0
  have hb' := hentry b
  have hrev := hentry (Fin.rev b)
  rw [ht0] at h0
  rw [htb] at hb'
  rw [htrev, hσν] at hrev
  have hσφ : ∀ c, σ (φ c) = φ (σ c) := by
    intro c
    change h.bar (φ c) = φ (h.bar c)
    rw [h.bar_apply, h.bar_apply, map_pow]
  have h1 : φ e ^ 2 = (ζ : K) * e ^ 2 := by
    rw [← hb']
    dsimp [ν]
    rw [map_pow]
  have h2 : (σ (φ e) ^ 2)⁻¹ = (ζ : K) * ((σ e) ^ 2)⁻¹ := by
    rw [← hrev, map_inv₀, hσφ, map_pow]
  have h3 : σ (φ e) * (φ e)⁻¹ = (ζ : K) * (σ e * e⁻¹) := by
    rw [← h0]
    dsimp [μ]
    rw [map_mul, map_inv₀, hσφ]
  have hζ4 : (ζ : K) ^ 4 = 1 := by
    have h3sq := congrArg (fun x : K => x ^ 2) h3
    have hmain : (φ e ^ 2) * ((σ (φ e) ^ 2)⁻¹) *
        (σ (φ e) * (φ e)⁻¹) ^ 2 =
        ((ζ : K) * e ^ 2) * ((ζ : K) * ((σ e) ^ 2)⁻¹) *
          (((ζ : K) * (σ e * e⁻¹)) ^ 2) := by
      rw [h1, h2, h3sq]
    field_simp [he, (map_ne_zero σ).mpr he, (map_ne_zero φ).mpr he,
      (map_ne_zero σ).mpr ((map_ne_zero φ).mpr he)] at hmain
    ring_nf at hmain ⊢
    exact hmain.symm
  have hζ2 : ζ * ζ = 1 := by
    apply scalar_unit_eq_one
    apply Units.ext
    change (ζ : K) * ζ * (ζ * ζ) = 1
    rw [show (ζ : K) * ζ * (ζ * ζ) = (ζ : K) ^ 4 from by ring]
    exact hζ4
  have hζ : ζ = 1 := scalar_unit_eq_one hζ2
  simpa [hζ] using h1

theorem eq_one_of_conj_levi (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev (0 : Fin (m + 1))}
    {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)}
    (hA₁ : (A : GL (Fin (m + 1)) K) *
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) =
      ((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K))
    (hA₂ : (A : GL (Fin (m + 1)) K) *
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) =
      ((lroot (unitaryInvolution K 2 f) hi₀ : SU (unitaryInvolution K 2 f) (m + 1)) :
        GL (Fin (m + 1)) K) * (A : GL (Fin (m + 1)) K))
    {g : PJ h (m + 1)} (hg : g ∈ levi h m hi₀)
    (hkey : ∀ k ∈ levi h m hi₀, (primeFormConjHom h _ A * c) k ∈ levi h m hi₀ →
      g * (primeFormConjHom h _ A * c) k * g⁻¹ = k) :
    c = 1 := by
  have hcKeep : c ∈ compl h := hc
  obtain ⟨φ, hφ⟩ := hc
  subst c
  obtain ⟨S, hSπ, hSR, hSY⟩ := exists_lift_comm h hm hg
  obtain ⟨-, hTne⟩ := T_diagonal_and_ne h hm hcKeep hA₁ hA₂ hg hkey hSπ hSR hSY
  have hφsq : ∀ e : K, e ≠ 0 → φ e ^ 2 = e ^ 2 := by
    intro e he
    exact torus_phi_sq h hm hA₁ hA₂ hg hkey hSπ hTne e he
  have hφfix : ∀ e : K, φ e = e := by
    intro e
    by_cases he : e = 0
    · subst he
      exact map_zero φ
    · have hsq := hφsq e he
      have hsum : φ e + e = 0 := by
        have hsq2 : (φ e + e) ^ 2 = 0 := by
          have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
          rw [add_sq, hsq, h2]
          simp only [zero_mul, zero_add, add_zero]
          exact CharTwo.add_self_eq_zero (e ^ 2)
        exact sq_eq_zero_iff.mp hsq2
      have := eq_neg_of_add_eq_zero_left hsum
      simpa [CharTwo.neg_eq] using this
  have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext hφfix
  rw [hφ1]
  exact map_one _
end KGPSU

end CFSG.StandardType

end
