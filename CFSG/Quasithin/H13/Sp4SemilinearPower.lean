module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.Quasithin.H13.NQTermCommonSylow

public section

namespace CFSG.Quasithin.H13.Sp4

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Quasithin.H13.NQTerm CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut fieldSp conjSp
  spSemilinearAutGroup statedSp_le_gsp conjAut_proj fieldAut_proj coe_fieldSp coe_conjSp)
open scoped Pointwise

variable {k : Type} [Field k]

theorem conjAut_apply_eq (g : StatedSp 2 k) (x : StatedProj (StatedSp 2 k)) :
    conjAut 2 k ⟨g, statedSp_le_gsp g.2⟩ x = proj 2 k g * x * (proj 2 k g)⁻¹ := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change conjAut 2 k ⟨g, statedSp_le_gsp g.2⟩ (proj 2 k y) = _
  rw [conjAut_proj]
  have h : conjSp 2 k ⟨g, statedSp_le_gsp g.2⟩ y = g * y * g⁻¹ := Subtype.ext (by
    rw [coe_conjSp]
    rfl)
  rw [h, map_mul, map_mul, map_inv]
  rfl

theorem exists_ringEquiv_eq_pow [Finite k] [CharP k 2] (φ : k ≃+* k) :
    ∃ i : ℕ, ∀ x : k, φ x = x ^ (2 ^ i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  let g : k ≃ₐ[ZMod 2] k := AlgEquiv.ofRingEquiv (f := φ) fun x => by
    have h := RingHom.ext_zmod ((φ : k →+* k).comp (algebraMap (ZMod 2) k))
      (algebraMap (ZMod 2) k)
    exact congrArg (fun F : ZMod 2 →+* k => F x) h
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 k g
  refine ⟨i, fun x => ?_⟩
  have h := hi x
  rw [Nat.card_zmod] at h
  exact h

end CFSG.Quasithin.H13.Sp4
