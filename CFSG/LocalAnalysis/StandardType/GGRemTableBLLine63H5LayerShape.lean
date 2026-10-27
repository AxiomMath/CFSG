module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerFrame
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

section Count

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [DecidableEq Kˣ]

theorem card_filter_shift (σ : Equiv.Perm ι) (p : ι → Prop) [DecidablePred p] (f : ι → Kˣ)
    (ζ : Kˣ) (hp : ∀ j, p (σ j) ↔ p j) (hf : ∀ j, f (σ j) = ζ * f j) (u : Kˣ) :
    (Finset.univ.filter fun j => p j ∧ f j = u).card =
      (Finset.univ.filter fun j => p j ∧ f j = ζ * u).card := by
  refine Finset.card_nbij' σ σ.symm ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
    exact ⟨(hp j).mpr hj.1, by rw [hf, hj.2]⟩
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
    refine ⟨?_, ?_⟩
    · have := hp (σ.symm j)
      rw [Equiv.apply_symm_apply] at this
      exact this.mp hj.1
    · have h1 := hf (σ.symm j)
      rw [Equiv.apply_symm_apply] at h1
      exact mul_left_cancel (h1.symm.trans hj.2)
  · intro j _
    simp
  · intro j _
    simp

theorem card_filter_shift_cube (σ : Equiv.Perm ι) (p : ι → Prop) [DecidablePred p] (f : ι → Kˣ)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) (hp : ∀ j, p (σ j) ↔ p j)
    (hf : ∀ j, f (σ j) = ζ * f j) (hf3 : ∀ j, f j ^ 3 = 1) :
    (Finset.univ.filter p).card = 3 * (Finset.univ.filter fun j => p j ∧ f j = 1).card ∧
      (Finset.univ.filter fun j => p j ∧ f j = ζ).card =
        (Finset.univ.filter fun j => p j ∧ f j = 1).card ∧
      (Finset.univ.filter fun j => p j ∧ f j = ζ ^ 2).card =
        (Finset.univ.filter fun j => p j ∧ f j = 1).card := by
  have h1 := card_filter_shift σ p f ζ hp hf 1
  have h2 := card_filter_shift σ p f ζ hp hf ζ
  rw [mul_one] at h1
  rw [← sq] at h2
  have e1 : (Finset.univ.filter fun j => p j ∧ f j = ζ).card =
      (Finset.univ.filter fun j => p j ∧ f j = 1).card := h1.symm
  have e2 : (Finset.univ.filter fun j => p j ∧ f j = ζ ^ 2).card =
      (Finset.univ.filter fun j => p j ∧ f j = 1).card := h2.symm.trans e1
  refine ⟨?_, e1, e2⟩
  have hmem : ∀ j ∈ Finset.univ.filter p, f j ∈ ({1, ζ, ζ ^ 2} : Finset Kˣ) := by
    intro j _
    obtain ⟨i, hi, hij⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).mpr (hf3 j))
    rw [← hij]
    interval_cases i <;> simp
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  have hne1 : (1 : Kˣ) ≠ ζ := fun h => by
    have := hζ.pow_inj (i := 0) (j := 1) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne2 : (1 : Kˣ) ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 0) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne3 : ζ ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
    Finset.sum_singleton]
  simp only [Finset.filter_filter]
  rw [e1, e2]
  ring

end Count

section Frame

variable {K : Type} [Field K] {n : ℕ}

theorem conj_scalar_mul_six (P M : GL (Fin 6) K) (c : Kˣ) :
    P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) c * M) * P =
      GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by
  have h : P⁻¹ * GeneralLinearGroup.scalar (Fin 6) c = GeneralLinearGroup.scalar (Fin 6) c * P⁻¹ :=
    (commute_scalar c P⁻¹).eq
  calc P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) c * M) * P
      = (P⁻¹ * GeneralLinearGroup.scalar (Fin 6) c) * (M * P) := by group
    _ = (GeneralLinearGroup.scalar (Fin 6) c * P⁻¹) * (M * P) := by rw [h]
    _ = GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by group

theorem exists_perm_ne_zero_of_det {m : Type*} [Fintype m] [DecidableEq m] {R : Type*}
    [CommRing R] {M : Matrix m m R} (h : M.det ≠ 0) :
    ∃ σ : Equiv.Perm m, ∀ i, M (σ i) i ≠ 0 := by
  rw [Matrix.det_apply] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨σ, fun i hi => hσ ?_⟩
  have h0 : ∏ j, M (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [h0, smul_zero]

theorem pow_eq_one_of_conj_diag {P X : GL (Fin 6) K} {η : Fin 6 → Kˣ}
    (h : P⁻¹ * X * P = diagHom 6 η) {m : ℕ} (hX : X ^ m = 1) (j : Fin 6) : η j ^ m = 1 := by
  have h1 : (diagHom 6 η) ^ m = 1 := by
    rw [← h]
    have := conj_pow (a := P⁻¹) (b := X) (i := m)
    simp only [inv_inv] at this
    rw [this, hX]
    group
  have h2 : diagHom 6 (η ^ m) = diagHom 6 1 := by rw [map_pow, map_one, h1]
  have h3 := diagHom_injective 6 h2
  simpa using congrFun h3 j

theorem exists_frame_data_heis (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) :
    ∃ (P : GL (Fin 6) K) (_ : P ∈ primeFormUnitary hKd (idGram K 6)) (η ε : Fin 6 → Kˣ)
      (σ : Equiv.Perm (Fin 6)), P⁻¹ * X * P = diagHom 6 η ∧ P⁻¹ * Z * P = diagHom 6 ε ∧
        (∀ j, η (σ j) = ζ * η j) ∧ (∀ j, ε (σ j) = ε j) ∧ (∀ j, η j ^ 3 = 1) ∧
        ∀ j, ε j ^ 3 = 1 := by
  classical
  set U := primeFormUnitary hKd (idGram K 6) with hU
  let xs : ↥U := ⟨X, hX⟩
  let zs : ↥U := ⟨Z, hZ⟩
  have hxz : xs * zs = zs * xs := Subtype.ext hXZ
  have hpair : ({xs, zs} : Set ↥U).Pairwise Commute := by
    intro a ha b hb hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxz
    · exact hxz.symm
    · exact absurd rfl hab
  set G : Subgroup ↥U := Subgroup.closure {xs, zs} with hG
  letI : CommGroup G := Subgroup.closureCommGroupOfComm hpair
  have hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : G) ⟨b, hb⟩)
  have hpow : ∀ a ∈ G, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact Subtype.ext hX3
      · exact Subtype.ext hZ3
    | one => exact one_pow _
    | mul a b ha hb iha ihb =>
      rw [(show Commute a b from hcomm a ha b hb).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hKd Nat.prime_three hpq G
    hcomm hpow
  have hxG : xs ∈ G := Subgroup.subset_closure (by simp)
  have hzG : zs ∈ G := Subgroup.subset_closure (by simp)
  obtain ⟨η, hη⟩ := exists_diagHom_of_isDiag (hP xs hxG)
  obtain ⟨ε, hε⟩ := exists_diagHom_of_isDiag (hP zs hzG)
  set P' : GL (Fin 6) K := (P : GL (Fin 6) K) with hP'
  have hη' : P'⁻¹ * X * P' = diagHom 6 η := hη
  have hε' : P'⁻¹ * Z * P' = diagHom 6 ε := hε
  set Y' : GL (Fin 6) K := P'⁻¹ * Y * P' with hY'
  have hXY' : diagHom 6 η * Y' = GeneralLinearGroup.scalar (Fin 6) ζ * (Y' * diagHom 6 η) := by
    rw [← hη', hY']
    have e1 : (P'⁻¹ * X * P') * (P'⁻¹ * Y * P') = P'⁻¹ * (X * Y) * P' := by group
    have e2 : (P'⁻¹ * Y * P') * (P'⁻¹ * X * P') = P'⁻¹ * (Y * X) * P' := by group
    rw [e1, e2, hXY, conj_scalar_mul_six]
  have hYZ' : diagHom 6 ε * Y' = Y' * diagHom 6 ε := by
    rw [← hε', hY']
    have e1 : (P'⁻¹ * Z * P') * (P'⁻¹ * Y * P') = P'⁻¹ * (Z * Y) * P' := by group
    have e2 : (P'⁻¹ * Y * P') * (P'⁻¹ * Z * P') = P'⁻¹ * (Y * Z) * P' := by group
    rw [e1, e2, hYZ]
  have hdet : ((Y' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Y')).ne_zero
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det hdet
  refine ⟨P', P.2, η, ε, σ, hη', hε', fun j => ?_, fun j => ?_,
    pow_eq_one_of_conj_diag hη' hX3, pow_eq_one_of_conj_diag hε' hZ3⟩
  · have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) (σ j) j) hXY'
    simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    apply Units.ext
    have h2 : (η (σ j) : K) * (Y' : Matrix (Fin 6) (Fin 6) K) (σ j) j =
        ((ζ : K) * η j) * (Y' : Matrix (Fin 6) (Fin 6) K) (σ j) j := by
      rw [h1]
      ring
    exact mul_right_cancel₀ (hσ j) h2
  · have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) (σ j) j) hYZ'
    simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    apply Units.ext
    exact mul_right_cancel₀ (hσ j) (by rw [h1, mul_comm])

end Frame

section TwoBlocks

variable {K : Type} [Field K] {n : ℕ}

@[expose] def TwoBlocks (hKd : UnitaryFieldData 2 n K) (M : GL (Fin 6) K) : Prop :=
  ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∃ τ : Fin 6 → Kˣ, P⁻¹ * M * P = diagHom 6 τ ∧
    (∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3) ∧
    ∃ (v₁ v₂ : Kˣ) (S₁ S₂ : Finset (Fin 6)), v₁ ≠ v₂ ∧ (∀ i, i ∈ S₁ ↔ τ i = v₁) ∧
      (∀ i, i ∈ S₂ ↔ τ i = v₂) ∧ 2 ≤ S₁.card ∧ 2 ≤ S₂.card

theorem not_isComponentOf_layer_ggFix_of_twoBlocks (hKd : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {M : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h : TwoBlocks hKd M) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩)) := by
  obtain ⟨P, hP, τ, hMP, -, v₁, v₂, S₁, S₂, hv, hS₁, hS₂, h₁, h₂⟩ := h
  exact not_isComponentOf_layer_ggFix_of_conj_diag hKd hn hM hP hMP hv hS₁ hS₂ h₁ h₂

theorem twoBlocks_of_noncentral (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (k : ℕ) : TwoBlocks hKd (X * Z ^ k) := by
  classical
  obtain ⟨P, hP, η, ε, σ, hη, hε, hση, hσε, hη3, hε3⟩ :=
    exists_frame_data_heis hKd hpq hX hZ hX3 hZ3 hXY hXZ hYZ
  set τ : Fin 6 → Kˣ := η * ε ^ k with hτ
  have hτj : ∀ j, τ j = η j * ε j ^ k := fun j => rfl
  have hτ3 : ∀ j, τ j ^ 3 = 1 := fun j => by
    rw [hτj, mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hε3, one_pow, mul_one, hη3]
  have hτσ : ∀ j, τ (σ j) = ζ * τ j := fun j => by
    rw [hτj, hτj, hση, hσε]
    exact mul_assoc _ _ _
  obtain ⟨hsum, h1, h2⟩ := card_filter_shift_cube σ (fun _ => True) τ hζ (fun _ => Iff.rfl) hτσ hτ3
  simp only [true_and, Finset.filter_true, Finset.card_univ, Fintype.card_fin] at hsum h1 h2
  have hcls : ∀ u : Kˣ, u ^ 3 = 1 → (Finset.univ.filter fun j => τ j = u).card = 2 := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).mpr hu)
    interval_cases e
    · simp only [pow_zero]
      omega
    · simp only [pow_one]
      omega
    · omega
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  refine ⟨P, hP, τ, ?_, ?_, 1, ζ, Finset.univ.filter fun i => τ i = 1,
    Finset.univ.filter fun i => τ i = ζ, (hζ.ne_one (by norm_num)).symm, ?_, ?_, ?_, ?_⟩
  · have e : P⁻¹ * (X * Z ^ k) * P = (P⁻¹ * X * P) * (P⁻¹ * Z * P) ^ k := by
      have := conj_pow (a := P⁻¹) (b := Z) (i := k)
      simp only [inv_inv] at this
      rw [this]
      group
    rw [e, hη, hε, ← map_pow, ← map_mul]
  · intro i S hS
    have hSeq : S = Finset.univ.filter fun j => τ j = τ i :=
      Finset.ext fun j => by simp [hS j]
    rw [hSeq, hcls (τ i) (hτ3 i)]
    norm_num
  · intro i
    simp
  · intro i
    simp
  · rw [hcls 1 (one_pow 3)]
  · rw [hcls ζ hζ3]

theorem twoBlocks_of_central (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (hZs : Z ∉ LargeEvenScalars (Fin 6) K) : TwoBlocks hKd Z := by
  classical
  obtain ⟨P, hP, η, ε, σ, hη, hε, hση, hσε, hη3, hε3⟩ :=
    exists_frame_data_heis hKd hpq hX hZ hX3 hZ3 hXY hXZ hYZ
  have hnc : ∃ j₁ j₂, ε j₁ ≠ ε j₂ := by
    by_contra hcon
    push Not at hcon
    apply hZs
    have h1 : diagHom 6 ε = GeneralLinearGroup.scalar (Fin 6) (ε 0) :=
      diagHom_eq_scalar_iff.mpr fun k => hcon k 0
    have h2 : Z = P * (P⁻¹ * Z * P) * P⁻¹ := by group
    rw [hε, h1] at h2
    refine ⟨ε 0, ?_⟩
    rw [h2, (commute_scalar (ε 0) P).eq]
    group
  obtain ⟨j₁, j₂, hj⟩ := hnc
  have hdiv : ∀ v : Kˣ, ∃ m, (Finset.univ.filter fun i => ε i = v).card = 3 * m := by
    intro v
    obtain ⟨h1, -, -⟩ := card_filter_shift_cube σ (fun i => ε i = v) η hζ
      (fun j => by rw [hσε]) hση hη3
    exact ⟨_, h1⟩
  refine ⟨P, hP, ε, hε, ?_, ε j₁, ε j₂, Finset.univ.filter fun i => ε i = ε j₁,
    Finset.univ.filter fun i => ε i = ε j₂, hj, ?_, ?_, ?_, ?_⟩
  · intro i S hS
    have hSeq : S = Finset.univ.filter fun j => ε j = ε i :=
      Finset.ext fun j => by simp [hS j]
    obtain ⟨m, hm⟩ := hdiv (ε i)
    rw [hSeq]
    have hle : (Finset.univ.filter fun j => ε j = ε i).card ≤ 6 := by
      simpa using Finset.card_le_univ (Finset.univ.filter fun j => ε j = ε i)
    have hne6 : (Finset.univ.filter fun j => ε j = ε i).card ≠ 6 := by
      intro h6
      have hall : (Finset.univ.filter fun j => ε j = ε i) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using h6)
      have e1 : ε j₁ = ε i := by
        have : j₁ ∈ Finset.univ.filter fun j => ε j = ε i := by rw [hall]; exact Finset.mem_univ _
        simpa using this
      have e2 : ε j₂ = ε i := by
        have : j₂ ∈ Finset.univ.filter fun j => ε j = ε i := by rw [hall]; exact Finset.mem_univ _
        simpa using this
      exact hj (e1.trans e2.symm)
    omega
  · intro i
    simp
  · intro i
    simp
  · obtain ⟨m, hm⟩ := hdiv (ε j₁)
    have hpos : 0 < (Finset.univ.filter fun i => ε i = ε j₁).card :=
      Finset.card_pos.mpr ⟨j₁, by simp⟩
    omega
  · obtain ⟨m, hm⟩ := hdiv (ε j₂)
    have hpos : 0 < (Finset.univ.filter fun i => ε i = ε j₂).card :=
      Finset.card_pos.mpr ⟨j₂, by simp⟩
    omega

end TwoBlocks

end CFSG.StandardType.Line63.H5

end
