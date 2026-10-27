module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank Matrix Module

section SpStabilizer

variable {r : ℕ} {K : Type} [Field K]

theorem map_eq_of_forall_mem {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (hM : IsUnit M) (W : Submodule K (n → K)) (h : ∀ w ∈ W, M *ᵥ w ∈ W) :
    W.map (mulVecLin M) = W := by
  have hinj : Function.Injective (mulVecLin M) := by
    have := Matrix.mulVec_injective_iff_isUnit.2 hM
    exact this
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (mulVecLin M) hinj W)).symm

theorem mem_stabilizer_iff_forall_sp (W : Submodule K (Fin r ⊕ Fin r → K)) (y : StatedSp r K) :
    y ∈ stabilizer r K W ↔ ∀ w ∈ W,
      ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ W := by
  rw [mem_stabilizer]
  constructor
  · intro h w hw
    have : ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈
        W.map (mulVecLin ((y : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := ⟨w, hw, rfl⟩
    rwa [h] at this
  · intro h
    exact map_eq_of_forall_mem _ (y : GL (Fin r ⊕ Fin r) K).isUnit W h

end SpStabilizer

section SpFamily

variable {r : ℕ} {K : Type} [Field K]

theorem coe_mulVec_inv_mulVec_sp (g : StatedSp r K) (w : Fin r ⊕ Fin r → K) :
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      ((((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) = w := by
  have : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    simp
  rw [Matrix.mulVec_mulVec, this, Matrix.one_mulVec]

theorem coe_inv_mulVec_mulVec_sp (g : StatedSp r K) (w : Fin r ⊕ Fin r → K) :
    (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) = w := by
  have : (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp
  rw [Matrix.mulVec_mulVec, this, Matrix.one_mulVec]

theorem spScalars_eq_bot_of_charTwo [NeZero r] [CharP K 2] : spScalars r K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hg' := hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg'
  obtain ⟨c, hc⟩ := hg'
  have hmul : ∀ v : Fin r ⊕ Fin r → K,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        (c : K) • v := fun v => by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]
    ext x
    simp [mulVec_diagonal]
  have hform := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have hcc : (c : K) * (c : K) = 1 := by
    have h1 := congrFun (congrFun hform (Sum.inl 0)) (Sum.inr 0)
    have hg2 : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        Matrix.scalar (Fin r ⊕ Fin r) (c : K) := by
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
    rw [hg2] at h1
    simpa [Matrix.scalar_apply, Matrix.mul_apply, Matrix.fromBlocks, Matrix.diagonal,
      Matrix.transpose_apply] using h1
  have hc1 : (c : K) = 1 := by
    have h5 : ((c : K) - 1) ^ 2 = 0 := by
      have := sub_pow_char (R := K) (p := 2) (c : K) 1
      rw [this]
      simp [pow_two, hcc]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h5)
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Units.ext ?_)
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, hc1]
  simp

end SpFamily

section SpFamily2

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_stab_family_sp (hr : 1 ≤ r) (J : Subgroup (StatedSp r K))
    (S₀ : Sylow 2 (StatedSp r K))
    (hJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSp r K)) : Set (StatedSp r K)) ≤ J) :
    ∃ 𝒲 : Set (Submodule K (Fin r ⊕ Fin r → K)), ∀ y : StatedSp r K,
      y ∈ J ↔ ∀ W ∈ 𝒲, ∀ w ∈ W,
        ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ W := by
  have : NeZero r := ⟨by omega⟩
  have hbot : spScalars r K = ⊥ := spScalars_eq_bot_of_charTwo
  have hinj : Function.Injective (proj r K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, hbot])
  have hsurj := proj_surjective (r := r) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (proj r K) ⟨hinj, hsurj⟩
  let S₁ : Sylow 2 (StatedProj (StatedSp r K)) := Sylow.mapSurjective hsurj S₀
  have hS₁ : ((S₁ : Subgroup (StatedProj (StatedSp r K)))) =
      (S₀ : Subgroup (StatedSp r K)).map (proj r K) := Sylow.coe_mapSurjective hsurj S₀
  have hN : Subgroup.normalizer ((S₁ : Subgroup (StatedProj (StatedSp r K))) :
      Set (StatedProj (StatedSp r K))) =
      (Subgroup.normalizer ((S₀ : Subgroup (StatedSp r K)) : Set (StatedSp r K))).map
        (proj r K) := by
    rw [hS₁]
    exact (Subgroup.map_equiv_normalizer_eq (S₀ : Subgroup (StatedSp r K)) ψ).symm
  have hmem : Subgroup.normalizer ((S₁ : Subgroup (StatedProj (StatedSp r K))) :
      Set (StatedProj (StatedSp r K))) ∈
      LinearFlag.sylowNormalizers (StatedProj (StatedSp r K)) 2 := ⟨S₁, rfl⟩
  rw [(sylow_normalizers (r := r) (K := K) 2 hr).2.2.1] at hmem
  obtain ⟨F, hF, hFeq⟩ := hmem
  obtain ⟨g, hg⟩ := exists_map_flag_eq hF
  have hiso : isoFlagStabilizer r K F =
      (borelSubgroup r K).map (MulAut.conj g : StatedSp r K →* StatedSp r K) := by
    have hF' : isoFlagStabilizer r K F =
        isoFlagStabilizer r K fun i => (flag r K i).map (spAct g) := by
      ext h
      rw [mem_isoFlagStabilizer, mem_isoFlagStabilizer]
      exact forall_congr' fun i => forall_congr' fun hi => forall_congr' fun hir => by
        rw [hg i hi hir]
    rw [hF', isoFlagStabilizer_map, isoFlagStabilizer_flag]
    rfl
  have hNG : Subgroup.normalizer ((S₀ : Subgroup (StatedSp r K)) : Set (StatedSp r K)) =
      (borelSubgroup r K).map (MulAut.conj g : StatedSp r K →* StatedSp r K) := by
    have h1 : (Subgroup.normalizer ((S₀ : Subgroup (StatedSp r K)) :
        Set (StatedSp r K))).map (proj r K) = (isoFlagStabilizer r K F).map (proj r K) := by
      rw [← hN, hFeq]
      rfl
    rw [← hiso]
    exact Subgroup.map_injective hinj h1
  set A : Subgroup (StatedSp r K) :=
    J.map (MulAut.conj g⁻¹ : StatedSp r K →* StatedSp r K) with hA
  have hAB : borelSubgroup r K ≤ A := by
    intro u hu
    have h1 : MulAut.conj g u ∈ Subgroup.normalizer ((S₀ : Subgroup (StatedSp r K)) :
        Set (StatedSp r K)) := by
      rw [hNG]
      exact ⟨u, hu, rfl⟩
    refine ⟨_, hJ h1, ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨hAeq, -⟩ := borel_overgroups A hAB
  refine ⟨{W | ∃ i ∈ borelCuts K A, W = (flag r K i).map (spAct g)}, fun y => ?_⟩
  have hyJ : y ∈ J ↔ MulAut.conj g⁻¹ y ∈ A := by
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨j, hj, hjy⟩
      have : j = y := by
        have := congrArg (MulAut.conj g) hjy
        simpa using this
      rwa [← this]
  have hconjmat : (((MulAut.conj g⁻¹ y : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [MulAut.conj_apply, inv_inv]
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hconj : ∀ v : Fin r ⊕ Fin r → K,
      (((MulAut.conj g⁻¹ y : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
            (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v)) :=
    fun v => by
    rw [hconjmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hmemA : ∀ z, z ∈ A ↔ ∀ i ∈ borelCuts K A, z ∈ stabilizer r K (flag r K i) :=
    fun z => by rw [← mem_flagStabilizer, ← hAeq]
  rw [hyJ, hmemA]
  constructor
  · intro h W hW w hw
    obtain ⟨i, hi, rfl⟩ := hW
    obtain ⟨v, hv, rfl⟩ := hw
    have h1 := (mem_stabilizer_iff_forall_sp _ _).1 (h i hi) v hv
    rw [hconj] at h1
    refine ⟨_, h1, ?_⟩
    simp only [spAct, mulVecLin_apply]
    rw [coe_mulVec_inv_mulVec_sp]
  · intro h i hi
    rw [mem_stabilizer_iff_forall_sp]
    intro v hv
    have h1 := h _ ⟨i, hi, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hv'eq⟩ := h1
    rw [hconj]
    simp only [spAct, mulVecLin_apply] at hv'eq
    rw [← hv'eq, coe_inv_mulVec_mulVec_sp]
    exact hv'

end SpFamily2

section SpAut

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_matrix_form_sp (hr : 3 ≤ r) (β : MulAut (StatedSp r K)) :
    ∃ (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K), ∀ g : StatedSp r K,
      (((β g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
            ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have : NeZero r := ⟨by omega⟩
  have hbot : spScalars r K = ⊥ := spScalars_eq_bot_of_charTwo
  have hinj : Function.Injective (proj r K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, hbot])
  let ψ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (proj r K) ⟨hinj, proj_surjective⟩
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := r) (K := K) hr).2 (MulAut.congr ψ β)
  refine ⟨(A : GL (Fin r ⊕ Fin r) K), σ, fun g => ?_⟩
  have h1 : proj r K (β g) = proj r K (conjSp r K A (fieldSp r K σ g)) := by
    have h2 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ (proj r K g)) hα
    simp only [MulAut.mul_apply, conjAut_proj, fieldAut_proj] at h2
    rw [← h2]
    have hs : ψ.symm (proj r K g) = g := ψ.symm_apply_apply g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hs]
    rfl
  have h3 : β g = conjSp r K A (fieldSp r K σ g) := hinj h1
  rw [h3, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

end SpAut

end CFSG.RankThree.PartOne.AUTSL
