module

public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import CFSG.RankThree.GF2n.Parrott.LinearV

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def sigma1VComplementHom (h : Tim79a.ParrottHyp z) :
    QuotientV.V z →* QuotientV.V z where
  toFun v := v * conjV h (sigma1H3 D) v
  map_one' := by simp
  map_mul' v w := by
    letI : CommGroup (QuotientV.V z) := commGroupV h
    simp [map_mul, mul_assoc, mul_comm, mul_left_comm]

@[expose] noncomputable def mulEquivVAdd :
    QuotientV.V z ≃* Multiplicative (Additive (QuotientV.V z)) where
  toFun v := Multiplicative.ofAdd (Additive.ofMul v)
  invFun w := Additive.toMul w.toAdd
  left_inv v := rfl
  right_inv w := rfl
  map_mul' v w := rfl

@[expose] noncomputable def sigma1VLinearMap (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact mulAutToLinearMap
    (MulAut.congr (mulEquivVAdd (z := z)) (conjV h (sigma1H3 D)))

@[simp] theorem sigma1VLinearMap_apply (h : Tim79a.ParrottHyp z)
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    sigma1VLinearMap D h v =
      Additive.ofMul ((conjV h (sigma1H3 D)) (Additive.toMul v)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rfl

@[expose] noncomputable def sigma1VComplementAddMap (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact (MonoidHom.toAdditive (sigma1VComplementHom D h)).toZModLinearMap 2

@[simp] theorem sigma1VComplementAddMap_apply (h : Tim79a.ParrottHyp z)
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    sigma1VComplementAddMap D h v =
      Additive.ofMul ((sigma1VComplementHom D h) (Additive.toMul v)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rfl

@[expose] noncomputable def sigma1VComplementMap (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  LinearMap.id - sigma1VLinearMap D h

@[simp] theorem sigma1VComplementMap_apply (h : Tim79a.ParrottHyp z)
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    sigma1VComplementMap D h v = v - sigma1VLinearMap D h v := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rfl

end CFSG.RankThree.GF2n.Parrott
