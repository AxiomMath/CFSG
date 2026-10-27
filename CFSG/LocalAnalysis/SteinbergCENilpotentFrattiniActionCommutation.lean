module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis

open Subgroup
open scoped IsMulCommutative

namespace NilpotentFrattiniAction

variable {G : Type*} [Group G]

instance isElementaryAbelian_frattiniQuotient (r : ℕ) [Fact r.Prime] (Q : Type*) [Group Q]
    [Finite Q] [Fact (IsPGroup r Q)] : IsElementaryAbelian r (Q ⧸ frattini Q) :=
  isElementaryAbelian_quotient_frattini

theorem map_frattini_mulEquiv {Q : Type*} [Group Q] (e : Q ≃* Q) :
    (frattini Q).map (e : Q →* Q) = frattini Q := by
  rw [← MulEquiv.toMonoidHom_eq_coe]
  exact characteristic_iff_map_eq.mp inferInstance e

@[expose] noncomputable def frattiniConj (Q : Subgroup G) [Q.Normal] :
    G →* MulAut (Q ⧸ frattini Q) where
  toFun g := QuotientGroup.congr (frattini Q) (frattini Q) (MulAut.conjNormal g)
    (map_frattini_mulEquiv _)
  map_one' := by
    ext x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := by
    ext x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_mul]
    rfl

theorem frattiniConj_mk (Q : Subgroup G) [Q.Normal] (g : G) (q : Q) :
    frattiniConj Q g (q : Q ⧸ frattini Q) = ((MulAut.conjNormal g q : Q) : Q ⧸ frattini Q) :=
  QuotientGroup.congr_mk _ _ _ (map_frattini_mulEquiv _) q

@[expose] noncomputable def frattiniRep [Finite G] (r : ℕ) [Fact r.Prime] (Q : Subgroup G)
    [Q.Normal] [Fact (IsPGroup r Q)] :
    G →* LinearMap.GeneralLinearGroup (ZMod r) (Additive (Q ⧸ frattini Q)) :=
  Representation.asGroupHom
    { toFun := fun g => AddMonoidHom.toZModLinearMap r
        (MonoidHom.toAdditive (frattiniConj Q g).toMonoidHom)
      map_one' := by
        ext x
        change Additive.ofMul (frattiniConj Q 1 x.toMul) = x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        change Additive.ofMul (frattiniConj Q (g * h) x.toMul) =
          Additive.ofMul (frattiniConj Q g (frattiniConj Q h x.toMul))
        rw [map_mul]
        rfl }

theorem frattiniRep_apply [Finite G] (r : ℕ) [Fact r.Prime] (Q : Subgroup G) [Q.Normal]
    [Fact (IsPGroup r Q)] (g : G) (x : Q ⧸ frattini Q) :
    (frattiniRep r Q g : Additive (Q ⧸ frattini Q) →ₗ[ZMod r] Additive (Q ⧸ frattini Q))
      (Additive.ofMul x) = Additive.ofMul (frattiniConj Q g x) :=
  rfl

end NilpotentFrattiniAction

open NilpotentFrattiniAction

end CFSG.LocalAnalysis
