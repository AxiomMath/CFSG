module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGFrameFSxEndsCardJoinAux
import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGConfig.lt_bstar_of_bstar_eq_sup {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hsplit : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L))
    (hcen : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U →
      Bs ≤ Subgroup.normalizer (U : Set G) → U ≤ Subgroup.centralizer (L : Set G)) :
    B < Bs := by
  classical
  obtain ⟨-, hBs, hxB, hLx, h4⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcardE := FrameRoute.card_sup_zpowers_le_three_mul_card_inf hBs hxB hx1 hsplit
  have h81 : 81 ≤ Nat.card Bs := by norm_num at h4; exact h4
  have hEp : IsPGroup 3 ↥(Bs ⊓ L) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hBs.2 _ g.2.1)⟩
  have hEnc : ¬ IsCyclic ↥(Bs ⊓ L) := by
    intro hcyc
    have hexp : Monoid.exponent ↥(Bs ⊓ L) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hBs.2 _ g.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    have := Nat.le_of_dvd (by norm_num) hexp
    omega
  have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    FrameRoute.subgroupOf_centralizer_normal_of_sStar hS ⟨Bs ⊓ L, inf_le_right, hEp, hEnc⟩
  have hcen' : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U →
      Bs ⊓ L ≤ Subgroup.normalizer (U : Set G) → U ≤ Subgroup.centralizer (L : Set G) := by
    intro U hUL hU2 hEU
    have hxU : x ∈ Subgroup.normalizer (U : Set G) :=
      CFSG.GroupTheory.mem_normalizer_of_conj_mem fun u hu => by
        have hux : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp (hLx (hUL hu))
        rw [show x * u * x⁻¹ = u by rw [← hux, mul_assoc, mul_inv_cancel, mul_one]]
        exact hu
    refine hcen U hUL hU2 ?_
    rw [hsplit]
    exact sup_le (Subgroup.zpowers_le.mpr hxU) hEU
  obtain ⟨-, -, -, -, -, -, -, hST⟩ := hcfg.1
  obtain ⟨-, hT, -, -⟩ := hST
  have hne : B ≠ Bs := FrameRoute.ne_bstar_of_stdType_twoGroup hT hLx hLn hsplit
    fun T hT2 hTN hET => FrameRoute.le_centralizer_of_twoSubgroups_central Nat.prime_three
      (by norm_num) hEp inf_le_right hT2 hTN hET hcen'
  exact lt_of_le_of_ne hcfg.2.1.1 hne


theorem GGConfig.lt_bstar_of_inner {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥L)) 3)
    (hinner : ∀ b ∈ Bs, ∃ a : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * a)
    (hcen : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → Bs ≤ Subgroup.normalizer (U : Set G) →
      U ≤ Subgroup.centralizer (L : Set G)) :
    B < Bs := by
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hsplit : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) :=
    (FrameRoute.bstar_eq_sup_of_inner hBs hxB hx1 hLx hZ hinner hSC
      fun S hSL hSp => hS.2.2.2.2 S hSL hSp).2
  exact GGConfig.lt_bstar_of_bstar_eq_sup hcfg hsplit hcen

end CFSG.StandardType

end
