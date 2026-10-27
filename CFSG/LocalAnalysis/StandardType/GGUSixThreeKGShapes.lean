module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.Line63.H5

variable {K : Type} [Field K] {n : ℕ}

private theorem shapeBadMat_inv {hKd : UnitaryFieldData 2 n K} {M : GL (Fin 6) K}
    (h : ShapeBadMat hKd M) : ShapeBadMat hKd M⁻¹ := by
  obtain ⟨P, hP, τ, hMP, hshape⟩ := h
  refine ⟨P, hP, τ⁻¹, ?_, ?_⟩
  · rw [show P⁻¹ * M⁻¹ * P = (P⁻¹ * M * P)⁻¹ by group, hMP, ← map_inv]
  · rcases hshape with h3 | h2
    · obtain ⟨v₁, v₂, S₁, S₂, hv, hS₁, hS₂, h₁, h₂⟩ := h3
      refine Or.inl ⟨v₁⁻¹, v₂⁻¹, S₁, S₂, fun h' => hv (inv_injective h'), ?_, ?_, h₁, h₂⟩
      · intro i; rw [hS₁ i, Pi.inv_apply, _root_.inv_inj]
      · intro i; rw [hS₂ i, Pi.inv_apply, _root_.inv_inj]
    · obtain ⟨v₁, v₂, v₃, S₁, S₂, S₃, hv12, hv13, hv23, hS₁, hS₂, hS₃, h₁, h₂, h₃⟩ := h2
      refine Or.inr ⟨v₁⁻¹, v₂⁻¹, v₃⁻¹, S₁, S₂, S₃, fun h' => hv12 (inv_injective h'),
        fun h' => hv13 (inv_injective h'), fun h' => hv23 (inv_injective h'),
        ?_, ?_, ?_, h₁, h₂, h₃⟩
      · intro i; rw [hS₁ i, Pi.inv_apply, _root_.inv_inj]
      · intro i; rw [hS₂ i, Pi.inv_apply, _root_.inv_inj]
      · intro i; rw [hS₃ i, Pi.inv_apply, _root_.inv_inj]

theorem shapeBad_of_noncentral (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (k : ℕ) : ShapeBadMat hKd (X * Z ^ k) := by
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
  have hne1 : (1 : Kˣ) ≠ ζ := fun h => by
    have := hζ.pow_inj (i := 0) (j := 1) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne2 : (1 : Kˣ) ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 0) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne3 : ζ ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hconj : P⁻¹ * (X * Z ^ k) * P = diagHom 6 τ := by
    have e : P⁻¹ * (X * Z ^ k) * P = (P⁻¹ * X * P) * (P⁻¹ * Z * P) ^ k := by
      have := conj_pow (a := P⁻¹) (b := Z) (i := k)
      simp only [inv_inv] at this
      rw [this]
      group
    rw [e, hη, hε, ← map_pow, ← map_mul]
  refine ⟨P, hP, τ, hconj, Or.inr ⟨1, ζ, ζ ^ 2,
    Finset.univ.filter fun j => τ j = 1, Finset.univ.filter fun j => τ j = ζ,
    Finset.univ.filter fun j => τ j = ζ ^ 2, hne1, hne2, hne3, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i; simp
  · intro i; simp
  · intro i; simp
  · rw [hcls 1 (one_pow 3)]
  · rw [hcls ζ hζ3]
  · rw [hcls (ζ ^ 2) (by rw [← pow_mul, mul_comm 2 3, pow_mul, hζ3, one_pow])]

theorem shapeBad_of_central (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (hZs : Z ∉ LargeEvenScalars (Fin 6) K) : ShapeBadMat hKd Z := by
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
  have hcard₁ : (Finset.univ.filter fun i => ε i = ε j₁).card = 3 := by
    obtain ⟨m, hm⟩ := hdiv (ε j₁)
    have hpos : 0 < (Finset.univ.filter fun i => ε i = ε j₁).card :=
      Finset.card_pos.mpr ⟨j₁, by simp⟩
    have hle : (Finset.univ.filter fun i => ε i = ε j₁).card ≤ 6 := by
      simpa using Finset.card_le_univ (Finset.univ.filter fun i => ε i = ε j₁)
    have hne6 : (Finset.univ.filter fun i => ε i = ε j₁).card ≠ 6 := by
      intro h6
      have hall : (Finset.univ.filter fun i => ε i = ε j₁) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using h6)
      have e2 : ε j₂ = ε j₁ := by
        have : j₂ ∈ Finset.univ.filter fun i => ε i = ε j₁ := by
          rw [hall]; exact Finset.mem_univ _
        simpa using this
      exact hj e2.symm
    omega
  have hcard₂ : (Finset.univ.filter fun i => ε i = ε j₂).card = 3 := by
    obtain ⟨m, hm⟩ := hdiv (ε j₂)
    have hpos : 0 < (Finset.univ.filter fun i => ε i = ε j₂).card :=
      Finset.card_pos.mpr ⟨j₂, by simp⟩
    have hle : (Finset.univ.filter fun i => ε i = ε j₂).card ≤ 6 := by
      simpa using Finset.card_le_univ (Finset.univ.filter fun i => ε i = ε j₂)
    have hne6 : (Finset.univ.filter fun i => ε i = ε j₂).card ≠ 6 := by
      intro h6
      have hall : (Finset.univ.filter fun i => ε i = ε j₂) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using h6)
      have e1 : ε j₁ = ε j₂ := by
        have : j₁ ∈ Finset.univ.filter fun i => ε i = ε j₂ := by
          rw [hall]; exact Finset.mem_univ _
        simpa using this
      exact hj e1
    omega
  refine ⟨P, hP, ε, hε, Or.inl ⟨ε j₁, ε j₂,
    Finset.univ.filter fun i => ε i = ε j₁, Finset.univ.filter fun i => ε i = ε j₂,
    hj, ?_, ?_, hcard₁, hcard₂⟩⟩
  · intro i; simp
  · intro i; simp

theorem shapeBad_of_mono (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {x y z : GL (Fin 6) K} (hxu : x ∈ primeFormUnitary hKd (idGram K 6))
    (hyu : y ∈ primeFormUnitary hKd (idGram K 6)) (hzu : z ∈ primeFormUnitary hKd (idGram K 6))
    (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) {i j : ℕ} (hy3 : j = 0 ∨ y ^ 3 = 1) (hij : i ≠ 0 ∨ j ≠ 0) (hi : i < 3)
    (hj : j < 3) (k : ℕ) : ShapeBadMat hKd (x ^ i * y ^ j * z ^ k) := by
  set u : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) ζ with hu
  have hcu : ∀ g : GL (Fin 6) K, Commute u g := fun g => (commute_scalar ζ g).symm
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, hζ.pow_eq_one, map_one]
  have hxi3 : (x ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hyj3 : (y ^ j) ^ 3 = 1 := by
    rcases hy3 with hj0 | hy3
    · rw [hj0, pow_zero, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have hX3 : (x ^ i * y ^ j) ^ 3 = 1 := by
    have hq : x ^ i * y ^ j = u ^ (i * j) * (y ^ j * x ^ i) := pow_mul_pow_eq_central hcu hxy i j
    have hu3' : (u ^ (i * j)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu3, one_pow]
    rw [mul_pow_three_eq_central (fun g => (hcu g).pow_left _) hq hu3', hxi3, hyj3, one_mul]
  have hXu : x ^ i * y ^ j ∈ primeFormUnitary hKd (idGram K 6) :=
    mul_mem (pow_mem hxu i) (pow_mem hyu j)
  have hXz : (x ^ i * y ^ j) * z = z * (x ^ i * y ^ j) :=
    ((Commute.pow_left (show Commute x z from hxz) i).mul_left
      (Commute.pow_left (show Commute y z from hyz) j)).eq
  by_cases hi0 : i = 0
  · have hj0 : j ≠ 0 := hij.resolve_left (not_not.mpr hi0)
    have hcop : Nat.Coprime j 3 := by
      interval_cases j <;> first | exact absurd rfl hj0 | decide
    have hζ' : IsPrimitiveRoot (ζ ^ j)⁻¹ 3 := (hζ.pow_of_coprime j hcop).inv
    have hrel : (x ^ i * y ^ j) * x = GeneralLinearGroup.scalar (Fin 6) (ζ ^ j)⁻¹ *
        (x * (x ^ i * y ^ j)) := by
      rw [map_inv, map_pow, ← hu]
      calc (x ^ i * y ^ j) * x = (u ^ j)⁻¹ * (u ^ j * ((x ^ i * y ^ j) * x)) :=
            (inv_mul_cancel_left _ _).symm
        _ = (u ^ j)⁻¹ * (x * (x ^ i * y ^ j)) := by rw [← heis_pair_x hcu hxy i j]
    exact shapeBad_of_noncentral hKd hpq hXu hzu hX3 hz3 hζ' hrel hXz hxz k
  · have hcop : Nat.Coprime i 3 := by
      interval_cases i <;> first | exact absurd rfl hi0 | decide
    have hζ' : IsPrimitiveRoot (ζ ^ i) 3 := hζ.pow_of_coprime i hcop
    have hrel : (x ^ i * y ^ j) * y = GeneralLinearGroup.scalar (Fin 6) (ζ ^ i) *
        (y * (x ^ i * y ^ j)) := by
      rw [map_pow, ← hu]
      exact heis_pair_y hcu hxy i j
    exact shapeBad_of_noncentral hKd hpq hXu hzu hX3 hz3 hζ' hrel hXz hyz k

theorem shapeBad_of_central_pow (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {x y z : GL (Fin 6) K} (hxu : x ∈ primeFormUnitary hKd (idGram K 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram K 6)) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) K) {k : ℕ}
    (hk : k < 3) (hk0 : k ≠ 0) : ShapeBadMat hKd (z ^ k) := by
  have h := shapeBad_of_central hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs
  interval_cases k
  · exact absurd rfl hk0
  · rwa [pow_one]
  · have : z ^ 2 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz3])
    rw [this]
    exact shapeBadMat_inv h

end CFSG.StandardType.UnitSixThreeKG

end
