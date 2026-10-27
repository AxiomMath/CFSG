module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def kHull15 (V₀ H : Subgroup G) : Subgroup G := conjClosure V₀ H

@[expose] def iHull15 (V₀ U H : Subgroup G) : Subgroup G := conjClosure (v1Sub15 V₀ U) H

structure Hyp1510 (V₀ V U S H P : Subgroup G) : Prop where
  fam : Fam15 V₀ V U S H
  sylow : IsSylowIn 2 P H
  V₀_le : V₀ ≤ P
  S_le : S ≤ P
  minimal : ∀ H' : Subgroup G, H' ≤ H → P ≤ H' → Fam15 V₀ V U S H' → H' = H

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem P_le (hP : Hyp1510 V₀ V U S H P) : P ≤ H := hP.sylow.le

theorem V₀_le_H (hP : Hyp1510 V₀ V U S H P) : V₀ ≤ H := hP.V₀_le.trans hP.P_le

theorem kHull15_le (hP : Hyp1510 V₀ V U S H P) : kHull15 V₀ H ≤ H :=
  conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hP.V₀_le_H hz)) (H.inv_mem hk)

theorem le_normalizer_kHull15 (V₀ H : Subgroup G) :
    H ≤ normalizer (kHull15 V₀ H : Set G) := le_normalizer_conjClosure _ _

theorem V₀_le_kHull15 (V₀ H : Subgroup G) : V₀ ≤ kHull15 V₀ H := le_conjClosure _ _

theorem le_normalizer_iHull15 (V₀ U H : Subgroup G) :
    H ≤ normalizer (iHull15 V₀ U H : Set G) := le_normalizer_conjClosure _ _

theorem v1Sub15_le_iHull15 (V₀ U H : Subgroup G) : v1Sub15 V₀ U ≤ iHull15 V₀ U H :=
  le_conjClosure _ _

theorem iHull15_le_kHull15 (V₀ U H : Subgroup G) : iHull15 V₀ U H ≤ kHull15 V₀ H :=
  conjClosure_mono (v1Sub15_le_left V₀ U) le_rfl

theorem iHull15_le_zSub15 (V₀ U H : Subgroup G) : iHull15 V₀ U H ≤ zSub15 V₀ U H :=
  conjClosure_mono le_sup_right le_rfl

theorem iHull15_le_pCoreOf (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    iHull15 V₀ U H ≤ pCoreOf 2 H :=
  (iHull15_le_zSub15 V₀ U H).trans (hP.fam.zSub15_le_pCoreOf h)

theorem pCoreOf_le_P (hP : Hyp1510 V₀ V U S H P) : pCoreOf 2 H ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pCoreOf_le_of_isSylowIn hP.sylow

theorem iHull15_le_P (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    iHull15 V₀ U H ≤ P :=
  (hP.iHull15_le_pCoreOf h).trans hP.pCoreOf_le_P

theorem comm_iHull15_sup (hP : Hyp1510 V₀ V U S H P) :
    ∀ x ∈ iHull15 V₀ U H ⊔ U, ∀ y ∈ iHull15 V₀ U H ⊔ U, x * y = y * x := by
  have hle : iHull15 V₀ U H ⊔ U ≤ zSub15 V₀ U H :=
    sup_le (iHull15_le_zSub15 V₀ U H) (le_sup_left.trans (le_conjClosure _ _))
  exact fun x hx y hy => hP.fam.comm x (hle hx) y (hle hy)

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81
