module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The normalizer of the fixed order-three subgroup inside omega -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Inside an omega subgroup containing `K ⊔ F`, the normalizer of `F` is
exactly the corresponding copy of `K ⊔ F`. -/
public theorem secondCase_a7_omega_normalizer_F_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hAleQ : od.K ⊔ od.F ≤ od.Q.map c.FU.subtype) :
    let QG : Subgroup G := od.Q.map c.FU.subtype
    let FQ : Subgroup QG := od.F.subgroupOf QG
    let AQ : Subgroup QG := (od.K ⊔ od.F).subgroupOf QG
    Subgroup.normalizer (FQ : Set QG) = AQ := by
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  have hFleA : od.F ≤ A := le_sup_right
  have hFleQ : od.F ≤ QG := hFleA.trans hAleQ
  let FQ : Subgroup QG := od.F.subgroupOf QG
  let AQ : Subgroup QG := A.subgroupOf QG
  ext x
  constructor
  · intro hx
    have hxNormF : (x : G) ∈ Subgroup.normalizer (od.F : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        let yQ : QG := ⟨y, hFleQ hy⟩
        have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
        have hconj :=
          (Subgroup.mem_normalizer_iff.mp hx yQ).mp hyFQ
        exact Subgroup.mem_subgroupOf.mp hconj
      · intro hy
        have hyQ : y ∈ QG := by
          have hconjQ : (x : G) * y * (x : G)⁻¹ ∈ QG := hFleQ hy
          have hbackQ := QG.mul_mem
            (QG.mul_mem (QG.inv_mem x.2) hconjQ) x.2
          simpa [mul_assoc] using hbackQ
        let yQ : QG := ⟨y, hyQ⟩
        have hconjFQ : x * yQ * x⁻¹ ∈ FQ :=
          Subgroup.mem_subgroupOf.mpr hy
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hx yQ).mpr hconjFQ)
    have hxM : (x : G) ∈ w.M := od.F_normalizer ▸ hxNormF
    apply Subgroup.mem_subgroupOf.mpr
    change (x : G) ∈ od.K ⊔ od.F
    rw [od.FU_inter_M_eq]
    exact ⟨hQGleFU x.2, hxM⟩
  · intro hx
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hxM : (x : G) ∈ w.M := by
      change (x : G) ∈ od.K ⊔ od.F at hxA
      rw [od.FU_inter_M_eq] at hxA
      exact hxA.2
    have hxNormF : (x : G) ∈ Subgroup.normalizer (od.F : Set G) := by
      rw [od.F_normalizer]
      exact hxM
    rw [Subgroup.mem_normalizer_iff]
    intro yQ
    constructor
    · intro hy
      have hyF : (yQ : G) ∈ od.F := Subgroup.mem_subgroupOf.mp hy
      have hconjF := (Subgroup.mem_normalizer_iff.mp hxNormF (yQ : G)).mp hyF
      exact Subgroup.mem_subgroupOf.mpr hconjF
    · intro hy
      have hconjF : (x : G) * (yQ : G) * (x : G)⁻¹ ∈ od.F :=
        Subgroup.mem_subgroupOf.mp hy
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hxNormF (yQ : G)).mpr hconjF)

end CFSG.GorensteinWalter
