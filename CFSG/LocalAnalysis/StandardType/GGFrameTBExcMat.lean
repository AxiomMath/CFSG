module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Facts
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

private theorem frameExcMat_entry_mul {τ : Tag} (u v : WeylGroup τ) (i j : Fin τ.rank) :
    (((u * v)⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j) =
      ∑ k, ((u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) k) *
        ((v⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) j) := by
  rw [mul_inv_rev, mul_smul, weyl_smul_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem frameExcMat_cartan_eq {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    τ.cartan = CartanMatrix.E τ.rank := by
  rcases hτ with rfl | rfl | rfl <;> exact cartanE_eq _

private theorem frameExcMat_simple_entry {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) (p q : Fin τ.rank) :
    ((((simple τ i)⁻¹ • (Pi.single p 1 : Fin τ.rank → ℤ)) q : ℤ) : ZMod 3) =
      (if p = q then 1 else 0) -
        (if q = i then ((CartanMatrix.E τ.rank p i : ℤ) : ZMod 3) else 0) := by
  rw [(coxeterSystem τ).inv_simple, simple_smul]
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [frameExcMat_cartan_eq hτ]
  push_cast
  by_cases hpq : p = q
  · rw [if_pos hpq.symm, if_pos hpq]
    by_cases hqi : q = i
    · rw [if_pos hqi, if_pos hqi, (CartanMatrix.E_isSymm τ.rank).apply i p]
    · rw [if_neg hqi, if_neg hqi]
  · rw [if_neg hpq, if_neg (Ne.symm hpq)]
    by_cases hqi : q = i
    · rw [if_pos hqi, if_pos hqi, (CartanMatrix.E_isSymm τ.rank).apply i p]
    · rw [if_neg hqi, if_neg hqi]

@[expose] noncomputable def frameAdMat (τ : Tag) :
    WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 3) where
  toFun u := Matrix.of fun i j => (((u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j : ℤ) : ZMod 3)
  map_one' := by
    ext i j
    by_cases h : i = j
    · simp [Pi.single_apply, Matrix.one_apply, h]
    · have h' : ¬ j = i := fun hji => h hji.symm
      simp [Pi.single_apply, h, h']
  map_mul' := fun u v => by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [frameExcMat_entry_mul]
    simp only [Int.cast_sum, Int.cast_mul]

theorem frameAdMat_mulVec (τ : Tag) (u : WeylGroup τ) (x : Fin τ.rank → ZMod 3) :
    (frameAdMat τ u).mulVec x = adAct τ 3 u x := by
  funext i
  simp [Matrix.mulVec, dotProduct, adAct, frameAdMat]

theorem frameAdMat_injective (τ : Tag) : Function.Injective (frameAdMat τ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  refine NoOffRest.eq_one_of_adAct (p := 3) (by norm_num) fun x => ?_
  rw [← frameAdMat_mulVec τ w x, hw]
  exact Matrix.one_mulVec x

theorem frameAdMat_simple {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    frameAdMat τ (simple τ i) = feS τ.rank i := by
  ext p q
  change ((((simple τ i)⁻¹ • (Pi.single p 1 : Fin τ.rank → ℤ)) q : ℤ) : ZMod 3) =
    feS τ.rank i p q
  rw [frameExcMat_simple_entry hτ]
  simp [feS]

end CFSG.StandardType.FrameRoute

end
