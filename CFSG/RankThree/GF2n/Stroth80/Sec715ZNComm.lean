module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNCommData
public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNCommExt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap CFSG.RankThree.GF2n.Stroth80.Sec715Torus
open scoped commutatorElement Matrix


theorem sec715ZNComm_holds (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hNO : Sec7NOrderStatement)
    (h711 : Stroth711StrongStatement) : Sec715ZNCommStatement := by
  intro G _ _ M Q Z B hc n t hs hp4 hn16 Z0 Zn hZ0 hZn hne hnc r hr L hL
  classical
  subst hn16
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  obtain ⟨K, hKf, hKfin, hchar, φ, u, u', E, hKZ, hrange, hker, hu, hu', huu', hLu₁, hLu₂, hdA⟩ :=
    sec715Cm_data h51 hPts hc hs hp4 hZ0 hZn hr
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hZ0n := sec715Spl_Z0_conj hc hZ0
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQM : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    hQM ρ (hRM hρ) y hy
  have hQZ0 : Q ≤ Z0 := hZ0.Q_le (hc.Q_le_Rt ht) hQn
  have hsecQ := sec715Cm_secHyp hc hs hZ0 hZn hr hdA
  have hsec₀ := SecHyp.of_isOppDecomp hdA hZnn hZ0n
  have hNQ : ∀ k ∈ hc.CN t, ∀ y ∈ Zn, ⁅k, y⁆ ∈ Q := fun k hk y hy => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZn.comm_mem hy hk)
  obtain ⟨M₀, iM₀, iA₀, κ₀, hκ₀, hkerκ₀⟩ := exists_sectionModule_ker hker hsec₀
    (fun k hk y hy => hQZ0 (hNQ k hk y hy))
  haveI : Finite M₀ := hκ₀.finite
  obtain ⟨Mm, iMm, iAm, κ, hκ, hkerκ⟩ := exists_sectionModule_ker hker hsecQ hNQ
  haveI : Finite Mm := hκ.finite
  have hΦ := viaMatrix_surjective (e := E.equiv) φ hrange
  have hk₀ : ∀ y ∈ (viaMatrix _ E.equiv φ hrange).ker, ∀ a : M₀, y • a = a := by
    intro y hy a
    rw [ker_viaMatrix] at hy
    exact hkerκ₀ y hy a
  have hk₁ : ∀ y ∈ (viaMatrix _ E.equiv φ hrange).ker, ∀ a : Mm, y • a = a := by
    intro y hy a
    rw [ker_viaMatrix] at hy
    exact hkerκ y hy a
  letI i₀ : DistribMulAction (Gom (quadPlus 4 K)) M₀ :=
    descendAction (viaMatrix _ E.equiv φ hrange) hΦ hk₀
  letI i₁ : DistribMulAction (Gom (quadPlus 4 K)) Mm :=
    descendAction (viaMatrix _ E.equiv φ hrange) hΦ hk₁
  have hsm₀ : ∀ (y : ↥(Rt M (LB M Q B) t)) (a : M₀),
      viaMatrix _ E.equiv φ hrange y • a = y • a := fun y a =>
    descendAction_smul (viaMatrix _ E.equiv φ hrange) hΦ hk₀ y a
  have hsm₁ : ∀ (y : ↥(Rt M (LB M Q B) t)) (a : Mm),
      viaMatrix _ E.equiv φ hrange y • a = y • a := fun y a =>
    descendAction_smul (viaMatrix _ E.equiv φ hrange) hΦ hk₁ y a
  have hK : 2 < Nat.card K := by
    have := hc.hyp.q4
    omega
  have hboth := sec715Cm_assemble hK E φ hrange hsm₀ hsm₁ hκ₀ hκ hsec₀ hsecQ hQZ0 hZ0Zn
    (fun z hz y hy => hZ0.comm_mem hz hy) hne
    (fun U hZU hUZn hUinv => sec715Cm_irr h51 hA hPts hNO h711 hc hs hp4 hZ0 hZn hne hZU hUZn
      hUinv)
    hu hu' huu' hLR hL2R hLu₁ hLu₂ (isCompl_fixedSub_of_isOppDecomp hZnn hκ₀ hdA hLR hL2R)
    (fixedSub_descend_Lom E φ hrange hkerκ₀ hLu₁) (fixedSub_descend_Lom E φ hrange hkerκ₀ hLu₂)
    (fixedSub_eq_secSub_of_isOppDecomp hZnn hκ₀ hdA hLR hL2R).1
    (fixedSub_eq_secSub_of_isOppDecomp hZnn hκ₀ hdA hLR hL2R).2
  rcases hL with rfl | rfl
  · exact hboth.1
  · exact hboth.2

end CFSG.RankThree.GF2n.Stroth80
