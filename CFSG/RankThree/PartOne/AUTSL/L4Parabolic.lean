module

public import CFSG.RankThree.PartOne.AUTSL.L4Core

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module

section Stabilizer

variable {K : Type*} [Field K]

theorem scalars_eq_bot_of_charTwo [CharP K 2] : scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have hc1 : (c : K) = 1 := by
    have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have h5 : ((c : K) - 1) ^ (2 ^ 2) = 0 := by
      rw [sub_pow_char_pow]
      simp [h4]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h5)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hA, hc1]
  simp

theorem mem_stabilizer_iff_forall {n : ℕ} (W : Submodule K (Fin n → K))
    (y : SpecialLinearGroup (Fin n) K) :
    y ∈ stabilizer W ↔ ∀ w ∈ W, (y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  rw [mem_stabilizer]
  constructor
  · intro h w hw
    have : (y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W.map (mulVecLin (y : Matrix (Fin n) (Fin n) K)) :=
      ⟨w, hw, rfl⟩
    rwa [h] at this
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact h w hw
    · exact LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' y) W

end Stabilizer

section Family

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem coe_mulVec_inv_mulVec {n : ℕ} (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

omit [Finite K] [CharP K 2] in
theorem coe_inv_mulVec_mulVec {n : ℕ} (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]

theorem exists_stab_family (J : Subgroup (SpecialLinearGroup (Fin 4) K))
    (S₀ : Sylow 2 (SpecialLinearGroup (Fin 4) K))
    (hJ : Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
      Set (SpecialLinearGroup (Fin 4) K)) ≤ J) :
    ∃ 𝒲 : Set (Submodule K (Fin 4 → K)), ∀ y : SpecialLinearGroup (Fin 4) K,
      y ∈ J ↔ ∀ W ∈ 𝒲, ∀ w ∈ W, (y : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W := by
  have hbot : scalars 4 K = ⊥ := scalars_eq_bot_of_charTwo
  have hinj : Function.Injective (proj 4 K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, hbot])
  have hsurj := proj_surjective 4 K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : SpecialLinearGroup (Fin 4) K ≃* projectiveSL 4 K :=
    MulEquiv.ofBijective (proj 4 K) ⟨hinj, hsurj⟩
  let S₁ : Sylow 2 (projectiveSL 4 K) := Sylow.mapSurjective hsurj S₀
  have hS₁ : ((S₁ : Subgroup (projectiveSL 4 K))) =
      (S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)).map (proj 4 K) :=
    Sylow.coe_mapSurjective hsurj S₀
  have hN : Subgroup.normalizer ((S₁ : Subgroup (projectiveSL 4 K)) : Set (projectiveSL 4 K)) =
      (Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K))).map (proj 4 K) := by
    rw [hS₁]
    exact (Subgroup.map_equiv_normalizer_eq (S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) ψ).symm
  have hmem : Subgroup.normalizer ((S₁ : Subgroup (projectiveSL 4 K)) : Set (projectiveSL 4 K)) ∈
      sylowNormalizers (projectiveSL 4 K) 2 := ⟨S₁, rfl⟩
  rw [(sylow_normalizers (n := 4) (K := K) 2 (by norm_num)).2.2.2.2] at hmem
  obtain ⟨V, hV, hVeq⟩ := hmem
  obtain ⟨g, hg⟩ := exists_map_standardFlag_eq hV
  have hflag := flagFamilyStabilizer_eq_map_conj hg
  have hNG : Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
      Set (SpecialLinearGroup (Fin 4) K)) =
      (upperTriangular 4 K).map (MulAut.conj g : SpecialLinearGroup (Fin 4) K →*
        SpecialLinearGroup (Fin 4) K) := by
    have h1 : (Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K))).map (proj 4 K) =
        (flagFamilyStabilizer V).map (proj 4 K) := by
      rw [← hN, hVeq]
      rfl
    rw [← hflag]
    exact Subgroup.map_injective hinj h1
  set A : Subgroup (SpecialLinearGroup (Fin 4) K) :=
    J.map (MulAut.conj g⁻¹ : SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 4) K)
    with hA
  have hAB : upperTriangular 4 K ≤ A := by
    intro u hu
    have h1 : MulAut.conj g u ∈ Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K))
        : Set (SpecialLinearGroup (Fin 4) K)) := by
      rw [hNG]
      exact ⟨u, hu, rfl⟩
    refine ⟨_, hJ h1, ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨hAeq, -⟩ := borel_overgroups A hAB
  refine ⟨{W | ∃ i ∈ borelOvergroupCuts A,
    W = (flagSpace 4 K i).map (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))}, fun y => ?_⟩
  have hyJ : y ∈ J ↔ MulAut.conj g⁻¹ y ∈ A := by
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨j, hj, hjy⟩
      have : j = y := by
        have := congrArg (MulAut.conj g) hjy
        simpa using this
      rwa [← this]
  have hconjmat : ((MulAut.conj g⁻¹ y : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = ((g⁻¹ : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
          (g : Matrix (Fin 4) (Fin 4) K) := by
    rw [MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
  have hconj : ∀ v : Fin 4 → K, ((MulAut.conj g⁻¹ y : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ v = ((g⁻¹ : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *ᵥ ((y : Matrix (Fin 4) (Fin 4) K) *ᵥ
          ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v)) := fun v => by
    rw [hconjmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hmemA : ∀ z, z ∈ A ↔ ∀ i ∈ borelOvergroupCuts A, z ∈ stabilizer (flagSpace 4 K i) :=
    fun z => by rw [← mem_flagStabilizer, ← hAeq]
  rw [hyJ, hmemA]
  constructor
  · intro h W hW w hw
    obtain ⟨i, hi, rfl⟩ := hW
    obtain ⟨v, hv, rfl⟩ := hw
    have h1 := (mem_stabilizer_iff_forall _ _).1 (h i hi) v hv
    rw [hconj] at h1
    refine ⟨_, h1, ?_⟩
    simp only [mulVecLin_apply]
    rw [coe_mulVec_inv_mulVec]
  · intro h i hi
    rw [mem_stabilizer_iff_forall]
    intro v hv
    have h1 := h _ ⟨i, hi, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hv'eq⟩ := h1
    rw [hconj]
    simp only [mulVecLin_apply] at hv'eq
    rw [← hv'eq, coe_inv_mulVec_mulVec]
    exact hv'

theorem l4_sl {K : Type} [Field K] [Finite K] [CharP K 2]
    {S : Subgroup (SpecialLinearGroup (Fin 4) K)} (hS : IsPGroup 2 S)
    (hsyl : ∃ S₀ : Sylow 2 (SpecialLinearGroup (Fin 4) K),
      Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K)) ≤
        Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)))
    {E B : Subgroup (SpecialLinearGroup (Fin 4) K)} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hBE : B ≤ E)
    (hBJ : B ≤ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)))
    (hB : Nat.card B = 25) (α : MulAut (SpecialLinearGroup (Fin 4) K))
    (hαB : B.map α.toMonoidHom = B) (hα3 : ∀ b ∈ B, (α ^ 3) b = b) (hα1 : ∃ b ∈ B, α b ≠ b)
    (x : MulAut (SpecialLinearGroup (Fin 4) K)) (hxB : ∀ b ∈ B, b⁻¹ * x b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)) ∧ ∀ e ∈ E, e⁻¹ * x e ∈ S := by
  obtain ⟨S₀, hS₀⟩ := hsyl
  obtain ⟨𝒲, h𝒲⟩ := exists_stab_family _ S₀ hS₀
  exact l4_core hS 𝒲 h𝒲 hEc hE5 hBE hBJ hB α hαB hα3 hα1 x hxB

end Family

end CFSG.RankThree.PartOne.AUTSL
