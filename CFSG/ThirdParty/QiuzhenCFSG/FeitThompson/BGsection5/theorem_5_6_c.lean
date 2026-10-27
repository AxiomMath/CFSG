module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_6_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.ZMod.Torsion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
import Mathlib.GroupTheory.Schreier
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_c

namespace CFSG
end CFSG
open CFSG

/-! # Shared infrastructure for Theorem 5.6(c) and 5.6(e) -/

private theorem CFSG.coprime_card_quotient_Op_p'p_of_hasPLengthOne
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hplen : HasPLengthOne (p := p) G) :
    Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) := by
  let q : G →* (G ⧸ Op_p'p p G) := QuotientGroup.mk' (Op_p'p p G)
  have hcore_top : pPrimeCore p (G ⧸ Op_p'p p G) = ⊤ := by
    let K : Subgroup (G ⧸ Op_p'p p G) := pPrimeCore p (G ⧸ Op_p'p p G)
    have hcomap_top : K.comap q = ⊤ := by
      have hplen' : Op_p'pp' p G = ⊤ := by
        simpa [HasPLengthOne] using hplen
      simpa [Op_p'pp', q, K] using hplen'
    calc
      K = (K.comap q).map q := by
            exact
              (Subgroup.map_comap_eq_self_of_surjective
                (f := q) (h := QuotientGroup.mk'_surjective (Op_p'p p G)) K).symm
      _ = (⊤ : Subgroup G).map q := by simp [hcomap_top]
      _ = ⊤ := by
            simpa using
              (Subgroup.map_top_of_surjective (f := q)
                (QuotientGroup.mk'_surjective (Op_p'p p G)))
  have hcopK : Nat.Coprime p (Nat.card (pPrimeCore p (G ⧸ Op_p'p p G))) :=
    pPrimeCore_coprime_card (p := p) (G := G ⧸ Op_p'p p G)
  simpa [hcore_top] using hcopK

public theorem CFSG.theorem_5_6_e_high_rank
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hSrank : 3 ≤ groupRank (S : Subgroup G)) (hplen : HasPLengthOne (p := p) G) :
    IsMulCommutative (G ⧸ Op_p'p p G) ∧ Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) := by
  classical
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd hp_dvd
  let N : Subgroup G := Subgroup.normalizer (S : Subgroup G)
  let L : Subgroup G := Op_p'p p G
  let φ : N →* MulAut S := Subgroup.normalizerMonoidHom (H := (S : Subgroup G))
  let A : Subgroup (MulAut S) := φ.range
  have hN_odd : Odd (Nat.card N) := by
    exact odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card N)
  have hAodd : Odd (Nat.card A) := by
    exact odd_of_card_dvd hN_odd (Subgroup.card_range_dvd φ)
  have hsolvA : Group.IsSolvable A := by
    exact Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  let _ : L.Normal := by
    dsimp [L]
    infer_instance
  have htop : N ⊔ L = ⊤ :=
    normalizer_sup_Op_p'p_eq_top_of_hasPLengthOne (G := G) (p := p) hplen S
  have hmap_top : N.map (QuotientGroup.mk' L) = ⊤ := by
    calc
      N.map (QuotientGroup.mk' L) =
          N.map (QuotientGroup.mk' L) ⊔ L.map (QuotientGroup.mk' L) := by
            have hLmap : L.map (QuotientGroup.mk' L) = ⊥ := by
              exact QuotientGroup.map_mk'_self (N := L)
            simp [hLmap]
      _ = (N ⊔ L).map (QuotientGroup.mk' L) := by rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup G).map (QuotientGroup.mk' L) := by rw [htop]
      _ = (⊤ : Subgroup (G ⧸ L)) := by
            simpa using
              (Subgroup.map_top_of_surjective (f := QuotientGroup.mk' L)
                (QuotientGroup.mk'_surjective L))
  let eNQ :
      N ⧸ L.subgroupOf N ≃* G ⧸ L :=
    (quotientSubgroupRangeEquiv N L).trans
      ((MulEquiv.subgroupCongr hmap_top).trans (Subgroup.topEquiv))
  have hcent_le_L : Subgroup.centralizer (S : Set G) ≤ L := by
    let T : Sylow p L := S.subtype
      (sylow_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen S)
    have hcentralizer :=
      centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable (G := G)
        (inferInstance : Group.IsSolvable G) p T
    have hTG_eq : T.1.map L.subtype = (S : Subgroup G) := by
      simp [T, L, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left (sylow_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen S)]
    simpa [hTG_eq, L] using hcentralizer
  have hker_eq : φ.ker = (Subgroup.centralizer (S : Subgroup G)).subgroupOf N := by
    simpa [φ, N] using
      (Subgroup.normalizerMonoidHom_ker (H := (S : Subgroup G)))
  have hker_le_Lsub : φ.ker ≤ L.subgroupOf N := by
    intro x hx
    have hxC : x ∈ (Subgroup.centralizer (S : Subgroup G)).subgroupOf N := by
      simpa [hker_eq] using hx
    exact hcent_le_L hxC
  let qφL : N ⧸ φ.ker →* N ⧸ L.subgroupOf N :=
    QuotientGroup.map φ.ker (L.subgroupOf N) (MonoidHom.id N) (by simpa using hker_le_Lsub)
  have hqφL_surj : Function.Surjective qφL := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf N) y
    refine ⟨QuotientGroup.mk' φ.ker n, ?_⟩
    simp [qφL]
  let eA : N ⧸ φ.ker ≃* A := QuotientGroup.quotientKerEquivRange φ
  let ψ : A →* N ⧸ L.subgroupOf N := qφL.comp eA.symm.toMonoidHom
  have hψ_surj : Function.Surjective ψ := by
    intro y
    rcases hqφL_surj y with ⟨x, hx⟩
    refine ⟨eA x, ?_⟩
    simp [ψ, hx]
  let χ : A →* G ⧸ L := eNQ.toMonoidHom.comp ψ
  have hχ_surj : Function.Surjective χ := by
    intro y
    rcases hψ_surj (eNQ.symm y) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp [χ, ha]
  have hderA_p : IsPGroup p (derivedSubgroup A) :=
    @theorem_5_5_a_high_rank_series_bridge p _ hpodd S _ _ hSnarrow hSrank A hsolvA hAodd
  have hderQ_p : IsPGroup p (derivedSubgroup (G ⧸ L)) := by
    have hmap_p : IsPGroup p ((derivedSubgroup A).map χ) :=
      IsPGroup.map (p := p) (H := derivedSubgroup A) hderA_p χ
    have hcomm_map_eq : (_root_.commutator A).map χ = _root_.commutator (G ⧸ L) := by
      have hmap := map_derivedSeries_eq (f := χ) hχ_surj 1
      rw [derivedSeries_one, derivedSeries_one] at hmap
      exact hmap
    have hcomm_p : IsPGroup p ((_root_.commutator A).map χ) := by
      change IsPGroup p ((derivedSeries A 1).map χ) at hmap_p
      rw [derivedSeries_one] at hmap_p
      exact hmap_p
    have hcommQ_p : IsPGroup p (_root_.commutator (G ⧸ L)) := by
      rw [← hcomm_map_eq]
      exact hcomm_p
    change IsPGroup p (derivedSeries (G ⧸ L) 1)
    rw [derivedSeries_one]
    exact hcommQ_p
  have hcopQ : Nat.Coprime p (Nat.card (G ⧸ L)) :=
    coprime_card_quotient_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen
  have hderQ_cop : Nat.Coprime p (Nat.card (derivedSubgroup (G ⧸ L))) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card (derivedSubgroup (G ⧸ L))) hcopQ
  have hderQ_card_eq_one : Nat.card (derivedSubgroup (G ⧸ L)) = 1 := by
    rcases hderQ_p.card_eq_or_dvd with h1 | hpdvd
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hderQ_cop) hpdvd
  have hderQ_bot : derivedSubgroup (G ⧸ L) = ⊥ := Subgroup.card_eq_one.mp hderQ_card_eq_one
  have hcomm_bot : _root_.commutator (G ⧸ L) = ⊥ := by
    change derivedSeries (G ⧸ L) 1 = ⊥ at hderQ_bot
    rw [derivedSeries_one] at hderQ_bot
    exact hderQ_bot
  have htop_comm_bot : ⁅(⊤ : Subgroup (G ⧸ L)), (⊤ : Subgroup (G ⧸ L))⁆ = ⊥ := by
    simpa [_root_.commutator_def] using hcomm_bot
  have htop_le_centralizer :
      (⊤ : Subgroup (G ⧸ L)) ≤ Subgroup.centralizer (((⊤ : Subgroup (G ⧸ L)) : Set (G ⧸ L))) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 htop_comm_bot
  have hcommQ : IsMulCommutative (G ⧸ L) := by
    refine ⟨⟨?_⟩⟩
    intro x y
    have hxcent : x ∈ Subgroup.centralizer (((⊤ : Subgroup (G ⧸ L)) : Set (G ⧸ L))) :=
      htop_le_centralizer (by simp)
    exact (hxcent y (by simp)).symm
  exact ⟨hcommQ, hcopQ⟩

/-! # Theorem 5.6(c) from BG Section 5 -/

public theorem CFSG.theorem_5_6_c
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hplen : 3 ≤ groupRank (S : Subgroup G) → HasPLengthOne p G) :
    HasNormalPComplement p (derivedSubgroup G) := by
  classical
  by_cases hSrank_le : groupRank (S : Subgroup G) ≤ 2
  · have hprank : primeRank p G ≤ 2 :=
      primeRank_le_two_of_sylow_groupRank_le_two (G := G) (p := p) (S := S) hSrank_le
    exact theorem_4_18_c (G := G) (p := p) (inferInstance : Group.IsSolvable G) hodd hp_dvd hprank
  · have hSrank : 3 ≤ groupRank (S : Subgroup G) := by omega
    have hplenG : HasPLengthOne (p := p) G := hplen hSrank
    have hcommQ : IsMulCommutative (G ⧸ Op_p'p p G) := by
      exact (theorem_5_6_e_high_rank
        (G := G) (p := p) hodd hp_dvd (S := S) hSnarrow hSrank hplenG).1
    have hder_le : derivedSubgroup G ≤ Op_p'p p G := by
      have hcomm_le :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := Op_p'p p G)).1 hcommQ
      change derivedSeries G 1 ≤ Op_p'p p G
      rw [derivedSeries_one]
      exact hcomm_le
    exact hasNormalPComplement_of_le (G := G) (p := p) hder_le
      (hasNormalPComplement_Op_p'p (G := G) (p := p))
