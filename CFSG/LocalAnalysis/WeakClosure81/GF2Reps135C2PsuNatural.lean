module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.Quasithin CFSG.Open
open CFSG.QuasithinUnique.Setup.Layer
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private noncomputable def c2psunat_mulEquivVAdd (V : Type) [CommGroup V] :
    V ≃* Multiplicative (Additive V) where
  toFun v := Multiplicative.ofAdd (Additive.ofMul v)
  invFun w := Additive.toMul w.toAdd
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem c2psunat_binPsi_mulEquivVAdd {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] (φ : MulAut W) (w : Additive W) :
    binPsi (c2psunat_mulEquivVAdd W) φ w = mulAutLinear φ w := rfl

private noncomputable def c2psunat_mulVecEquiv {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (P : GL ι K) : (ι → K) ≃+ (ι → K) where
  toFun v := (P : Matrix ι ι K) *ᵥ v
  invFun v := ((P⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
  left_inv v := by
    show ((P⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((P : Matrix ι ι K) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    show (P : Matrix ι ι K) *ᵥ (((P⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ _ _

private theorem c2psunat_eq_one_of_fixed {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hfix : ∀ v : Fin n → K, M *ᵥ v = v) : M = 1 := by
  ext s t
  have h := congrFun (hfix (Pi.single t 1)) s
  rw [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.single_apply] at h
  rw [Matrix.one_apply]
  exact h

theorem w135c2_psu_natural {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (φ : SU (unitaryInvolution K 2 f) n →* ↥L)
    (hφ : Function.Surjective φ) (β : Additive W ≃+ (Fin n → K))
    (hβ : ∀ (g : SU (unitaryInvolution K 2 f) n) (w : Additive W),
      β (pslRep φ g w) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ β w) :
    IsSUn ↥L n f ∧ NatSUn L ⊤ ⊥ n f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz1 : φ z = 1 := MonoidHom.mem_ker.mp hz
    have hfix : ∀ v : Fin n → K, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
      intro v
      obtain ⟨w, rfl⟩ := β.surjective v
      have h := hβ z w
      have hpz : pslRep φ z w = w := by simp [pslRep_apply, hz1, mulAutLinear_one]
      rw [hpz] at h
      exact h.symm
    exact Subtype.ext (Units.ext (c2psunat_eq_one_of_fixed _ hfix))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  let eφ : SU (unitaryInvolution K 2 f) n ≃* ↥L := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have heφ : ∀ g, eφ g = φ g := fun g => rfl
  let Θ : ↥L ≃* ↥(StatedSU n (2 ^ f) K) := eφ.symm.trans (suToStated hK n)
  refine ⟨⟨K, inferInstance, inferInstance, hK, ⟨Θ⟩⟩,
    ⟨K, inferInstance, inferInstance, hK, ?_⟩⟩
  let P : GL (Fin n) K := wittMat hK n
  let ψ : Additive W ≃+ (Fin n → K) := β.trans (c2psunat_mulVecEquiv P)
  refine realizes_nat_of_equiv (c2psunat_mulEquivVAdd W) Θ ψ fun l w => ?_
  set g : SU (unitaryInvolution K 2 f) n := eφ.symm l with hg
  have hφg : φ g = l := by
    rw [← heφ, hg, MulEquiv.apply_symm_apply]
  have hpl : pslRep φ g w = mulAutLinear (l : MulAut W) w := by
    rw [pslRep_apply, hφg]
  have hΘ : (((Θ l : ↥(StatedSU n (2 ^ f) K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h1 : Θ l = suToStated hK n g := rfl
    rw [h1, coe_suToStated]
    simp only [Units.val_mul]
    rfl
  have hPP : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change (P : Matrix (Fin n) (Fin n) K) *ᵥ β (binPsi (c2psunat_mulEquivVAdd W) (l : MulAut W) w) =
    _
  rw [c2psunat_binPsi_mulEquivVAdd, ← hpl, hβ g w, hΘ]
  change _ = _ *ᵥ ((P : Matrix (Fin n) (Fin n) K) *ᵥ β w)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPP,
    Matrix.mul_one]

theorem w135c2_psu_natural_chev2 {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (φ : SU (unitaryInvolution K 2 1) n →* ↥L)
    (hφ : Function.Surjective φ) (β : Additive W ≃+ (Fin n → K))
    (hβ : ∀ (g : SU (unitaryInvolution K 2 1) n) (w : Additive W),
      β (pslRep φ g w) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ β w) :
    Chev2Natural W L :=
  Or.inr ⟨n, w135c2_psu_natural hK φ hφ β hβ⟩

end CFSG.LocalAnalysis.WeakClosure81
