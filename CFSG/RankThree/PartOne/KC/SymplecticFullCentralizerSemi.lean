module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLift
public import CFSG.RankThree.PartOne.KC.ExactLiftingGeneric
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram)

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def semiConj (A : gsp r K) (σ : K ≃+* K) :
    StatedSp r K →* StatedSp r K :=
  (conjSp r K A).toMonoidHom.comp (fieldSp r K σ).toMonoidHom

theorem semiConj_apply (A : gsp r K) (σ : K ≃+* K) (g : StatedSp r K) :
    semiConj A σ g = conjSp r K A (fieldSp r K σ g) := rfl

theorem coe_semiConj (A : gsp r K) (σ : K ≃+* K) (g : StatedSp r K) :
    (((semiConj A σ g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
        (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [semiConj_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem alpha_apply_proj (A : gsp r K) (σ : K ≃+* K) (g : StatedSp r K) :
    (conjAut r K A * fieldAut r K σ) (proj r K g) = proj r K (semiConj A σ g) := rfl

theorem mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (t : G) :
    α * MulAut.conj t * α⁻¹ = MulAut.conj (α t) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem commute_conj_iff {G : Type*} [Group G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) (α : MulAut G) (t : G) :
    α * MulAut.conj t = MulAut.conj t * α ↔ α t = t := by
  constructor
  · intro h
    have h1 : MulAut.conj (α t) = MulAut.conj t := by
      rw [← mul_conj_mul_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    exact hinj h1
  · intro h
    have h1 := mul_conj_mul_inv α t
    rw [h] at h1
    calc α * MulAut.conj t = α * MulAut.conj t * α⁻¹ * α := (inv_mul_cancel_right _ _).symm
      _ = MulAut.conj t * α := by rw [h1]

theorem semiConj_eq_of_commute
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    (A : gsp r K) (σ : K ≃+* K) {G : Subgroup (StatedSp r K)}
    (hG : Group.IsPerfect G ∨ (proj r K).ker = ⊥)
    (hcomm : ∀ g ∈ G, (conjAut r K A * fieldAut r K σ) * MulAut.conj (proj r K g) =
      MulAut.conj (proj r K g) * (conjAut r K A * fieldAut r K σ)) :
    ∀ g ∈ G, semiConj A σ g = g := by
  rcases hG with hperf | hker
  · refine KCGeneric.fixed_of_commutes_of_perfect (spInnerLift r K) (fun z hz g => ?_)
      (semiConj A σ) (conjAut r K A * fieldAut r K σ) (fun g => ?_) hperf hcomm
    · rw [ker_spInnerLift hinj] at hz
      exact (Subgroup.mem_center_iff.mp (ker_proj_le_center hz) g).symm
    · rw [spInnerLift_apply, mul_conj_mul_inv, alpha_apply_proj, spInnerLift_apply]
  · intro g hg
    have h1 := (commute_conj_iff hinj _ _).mp (hcomm g hg)
    rw [alpha_apply_proj] at h1
    exact (MonoidHom.ker_eq_bot_iff _).mp hker h1

@[expose] def semilinMap (A : gsp r K) (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    Fin r ⊕ Fin r → K :=
  ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (σ ∘ v)

theorem semilinMap_add (A : gsp r K) (σ : K ≃+* K) (u v : Fin r ⊕ Fin r → K) :
    semilinMap A σ (u + v) = semilinMap A σ u + semilinMap A σ v := by
  unfold semilinMap
  rw [← Matrix.mulVec_add]
  congr 1
  ext i
  simp

theorem semilinMap_smul (A : gsp r K) (σ : K ≃+* K) (c : K) (v : Fin r ⊕ Fin r → K) :
    semilinMap A σ (c • v) = σ c • semilinMap A σ v := by
  unfold semilinMap
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

theorem semilinMap_zero (A : gsp r K) (σ : K ≃+* K) : semilinMap A σ 0 = 0 := by
  have := semilinMap_smul A σ 0 0
  simpa using this

theorem semilinMap_injective (A : gsp r K) (σ : K ≃+* K) :
    Function.Injective (semilinMap A σ) := by
  intro u v h
  unfold semilinMap at h
  have h1 := congrArg (fun w => (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  ext i
  exact σ.injective (congrFun h1 i)

theorem spForm_comp_ringEquiv (σ : K ≃+* K) (u w : Fin r ⊕ Fin r → K) :
    spForm r K (σ ∘ u) (σ ∘ w) = σ (spForm r K u w) := by
  have hJ : (gram K r).map σ = gram K r := formJ_map σ
  have hv2 : ∀ i, σ ((gram K r *ᵥ w) i) = (gram K r *ᵥ (⇑σ ∘ w)) i := by
    intro i
    have := RingHom.map_mulVec (σ : K →+* K) (gram K r) w i
    have h2 : (gram K r).map (σ : K →+* K) = gram K r := hJ
    rw [h2] at this
    exact this
  rw [spForm_apply, spForm_apply, dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hv2 i]
  rfl

theorem semilinMap_spForm [NeZero r] (A : gsp r K) (σ : K ≃+* K) (u w : Fin r ⊕ Fin r → K) :
    spForm r K (semilinMap A σ u) (semilinMap A σ w) =
      (multiplier r K A : K) * σ (spForm r K u w) := by
  unfold semilinMap
  rw [spForm_mulVec]
  have h1 := multiplier_spec A
  change (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      gram K r * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        (multiplier r K A : K) • gram K r at h1
  rw [h1, Matrix.toBilin'_apply', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← spForm_apply, spForm_comp_ringEquiv]

theorem semilinMap_comm (A : gsp r K) (σ : K ≃+* K) {g : StatedSp r K}
    (h : semiConj A σ g = g) (v : Fin r ⊕ Fin r → K) :
    semilinMap A σ (spEnd g v) = spEnd g (semilinMap A σ v) := by
  have h1 := coe_semiConj A σ g
  rw [h] at h1
  have hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have h2 : (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
          (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [← h1]
    rw [h2]
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hσv : ⇑σ ∘ (((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *ᵥ
        (⇑σ ∘ v) := by
    ext i
    exact RingHom.map_mulVec (σ : K →+* K) _ v i
  unfold semilinMap
  rw [spEnd_apply, spEnd_apply, hσv, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec]

end CFSG.RankThree.PartOne.KCSpFull
