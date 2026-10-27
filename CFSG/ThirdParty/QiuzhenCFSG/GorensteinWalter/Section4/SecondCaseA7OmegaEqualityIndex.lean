module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddRelativeIndexBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The equality branch of the A7 omega index argument -/

open scoped Pointwise

noncomputable section

namespace CFSG.GorensteinWalter

universe u

local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)

/-- If the characteristic omega subgroup is `K ⊔ F`, then equation (8)
holds: `B ⊔ F(U)` has relative index at most three in `U`. -/
public theorem secondCase_a7_omega_equality_relIndex_le_three
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (heq : od.K ⊔ od.F = od.Q.map c.FU.subtype) :
    (od.B ⊔ c.FU).relIndex c.U ≤ 3 := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let U : Subgroup G := c.U
  let : MulAction U (Subgroup G) :=
    MulAction.compHom (Subgroup G) U.subtype
  have hAcard : Nat.card A = 9 := by
    change Nat.card (od.K ⊔ od.F : Subgroup G) = 9
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hFleA : od.F ≤ A := le_sup_right
  have hAnormalU : IsNormalIn A U := by
    change IsNormalIn (od.K ⊔ od.F) c.U
    rw [heq]
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q
      od.Q_characteristic (fittingSubgroupOf_isNormalIn c.U)
  have mem_smul_iff (x : U) (y : G) (T : Subgroup G) :
      y ∈ x • T ↔ (x : G)⁻¹ * y * (x : G) ∈ T := by
    change y ∈ T.map (MulAut.conj (x : G)).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  let Orb := MulAction.orbit U od.F
  have hTcard : ∀ T : Orb, Nat.card T.1 = 3 := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    have hcard : Nat.card ↥(u • od.F : Subgroup G) = Nat.card od.F := by
      change Nat.card (od.F.map (MulAut.conj (u : G)).toMonoidHom) =
        Nat.card od.F
      exact Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective
    rw [← hu]
    exact hcard.trans od.F_card
  have hTleA : ∀ T : Orb, T.1 ≤ A := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    intro y hy
    have hySmul : y ∈ u • od.F := by
      change y ∈ (fun m : U => m • od.F) u
      rw [hu]
      exact hy
    have hpre : (u : G)⁻¹ * y * (u : G) ∈ od.F :=
      (mem_smul_iff u y od.F).mp hySmul
    have hpreA : (u : G)⁻¹ * y * (u : G) ∈ A := hFleA hpre
    have hconjA := hAnormalU.2 (u : G) u.2
      ((u : G)⁻¹ * y * (u : G)) hpreA
    simpa [mul_assoc] using hconjA
  let Pairs := Σ T : Orb, {x : T.1 // x ≠ 1}
  let target := {x : A // x ≠ 1}
  let f : Pairs → target := fun p =>
    ⟨⟨(p.2 : G), hTleA p.1 p.2.1.2⟩,
      by
        intro h1
        apply p.2.2
        apply Subtype.ext
        exact congrArg (fun z : A => (z : G)) h1⟩
  have hfInj : Function.Injective f := by
    rintro ⟨T, x⟩ ⟨S, y⟩ hxy
    have hvalG : (x : G) = (y : G) :=
      congrArg (fun z : target => ((z.1 : A) : G)) hxy
    have hyGne : (y : G) ≠ 1 := by
      intro h1
      apply y.2
      exact Subtype.ext h1
    have hxGne : (x : G) ≠ 1 := fun h1 =>
      hyGne (hvalG.symm.trans h1)
    have hxS : (x : G) ∈ S.1 := by
      rw [hvalG]
      exact y.1.2
    have hTS : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        T.1 S.1 (hTcard T) (hTcard S) x.1.2 hxS hxGne
    have hOrbEq : T = S := Subtype.ext hTS
    subst S
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvalG
    rw [hxy']
  have htargetCard : Nat.card target = 8 := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype target := Fintype.ofFinite target
    have hAF : Fintype.card A = 9 := by
      simpa [Nat.card_eq_fintype_card] using hAcard
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [hAF]
  have hpairCard : Nat.card Pairs = Nat.card Orb * 2 := by
    let : Fintype Orb := Fintype.ofFinite Orb
    rw [Nat.card_sigma]
    have hfiber : ∀ T : Orb, Nat.card {x : T.1 // x ≠ 1} = 2 := by
      intro T
      let : Fintype T.1 := Fintype.ofFinite T.1
      let : Fintype {x : T.1 // x ≠ 1} := Fintype.ofFinite _
      have hTF : Fintype.card T.1 = 3 := by
        simpa [Nat.card_eq_fintype_card] using hTcard T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp [hTF]
    simp_rw [hfiber]
    simp [mul_comm]
  have hOrbLe : Nat.card Orb ≤ 4 := by
    have hpairsLe : Nat.card Pairs ≤ Nat.card target :=
      Nat.card_le_card_of_injective f hfInj
    rw [hpairCard, htargetCard] at hpairsLe
    omega
  let NU : Subgroup U :=
    (Subgroup.normalizer (od.F : Set G)).comap U.subtype
  have hstab : MulAction.stabilizer U od.F = NU := by
    ext u
    rw [MulAction.mem_stabilizer_iff]
    change u • od.F = od.F ↔
      (u : G) ∈ Subgroup.normalizer (od.F : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hOrbIndex : Nat.card Orb = NU.index := by
    calc
      Nat.card Orb = Nat.card (U ⧸ MulAction.stabilizer U od.F) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer U od.F)
      _ = (MulAction.stabilizer U od.F).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer U od.F)).symm
      _ = NU.index := by rw [hstab]
  have hNUindexLe : NU.index ≤ 4 := by
    rw [← hOrbIndex]
    exact hOrbLe
  let N : Subgroup G := U ⊓ Subgroup.normalizer (od.F : Set G)
  have hNsub : N.subgroupOf U = NU := by
    ext x
    simp [N, NU]
  have hNrel : N.relIndex U = NU.index := by
    change (N.subgroupOf U).index = NU.index
    rw [hNsub]
  have hUodd : Odd (Nat.card U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hNrelLe : N.relIndex U ≤ 3 := by
    apply odd_relIndex_le_three_of_le_four N U hUodd
    rw [hNrel]
    exact hNUindexLe
  have hKleFU : od.K ≤ c.FU := by
    calc
      od.K ≤ od.K ⊔ od.F := le_sup_left
      _ = c.FU ⊓ w.M := od.FU_inter_M_eq
      _ ≤ c.FU := inf_le_left
  have hNleL : N ≤ od.B ⊔ c.FU := by
    intro x hx
    have hxM : x ∈ w.M := by
      rw [← od.F_normalizer]
      exact hx.2
    have hxKB : x ∈ od.K ⊔ od.B := by
      rw [od.U_inter_M_eq]
      exact ⟨hx.1, hxM⟩
    have hKBle : od.K ⊔ od.B ≤ od.B ⊔ c.FU :=
      sup_le (hKleFU.trans le_sup_right) le_sup_left
    exact hKBle hxKB
  have hNrelne : N.relIndex U ≠ 0 := by
    rw [hNrel]
    exact Nat.card_pos.ne'
  exact (Subgroup.relIndex_le_of_le_left hNleL hNrelne).trans hNrelLe

end CFSG.GorensteinWalter
