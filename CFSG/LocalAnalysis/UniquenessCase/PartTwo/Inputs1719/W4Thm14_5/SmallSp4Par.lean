module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.Quasithin.Vol2.Ch9KGFFSpConj
import CFSG.ClassicalInvolution.Q3.Q3T6LinSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.SteinbergBNLinearTwoOuterInvolutionRigidity
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.Vol2.KGNat
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSpEquiv)

theorem isL2_bar2_perfectCore_Q2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (j : Fin 2) :
    IsL2 (Bar2 (perfectCore (Q2 K j))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian (K := K) hK4
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) hK4
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore (Q2 K j)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab (blkN (K := K) j) (blkN_surjective hK4 j)
      (blkN_ker_isPGroup ⟨n, hK⟩ j)).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n)
    e.symm hmodel

theorem isSp4_bar2_hinf_self {G : Type} [Group G] [Finite G] {L : Subgroup G} {e : ℕ}
    (hS : IsSp4 ↥L e) : IsSp4 (Bar2 (Hinf L)) e := by
  obtain ⟨he, K, _, _, _, hK, ⟨φ⟩⟩ := K148.exists_antiSp_of_isSp4 hS
  have h3 : 3 ≤ Nat.card K := by
    have := K148.four_le_card he hK
    omega
  haveI : Group.IsPerfect ↥(StatedSp 2 K) :=
    CFSG.ClassicalInvolution.Q3.Q3T6.isPerfect_sp4_of_three_le h3
  haveI : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := (φ.trans (antiSpEquiv K)).symm.toMonoidHom)
      (φ.trans (antiSpEquiv K)).symm.surjective
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp inferInstance
  have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
    haveI : IsSimpleGroup ↥L := K148.isSimpleGroup_of_isSp4 hS
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_equiv
        ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)).isNilpotent
        (Group.IsPerfect.not_isNilpotent ↥L)
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq rfl hperf hO2
  exact CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hS

theorem nParam_eq_of_isSp4_parabolic {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {e n : ℕ} (hS : IsSp4 ↥L e) (hPL : P ≤ L) (hpar : IsParabolicTwo ↥L (P.subgroupOf L))
    (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n) : n = e := by
  obtain ⟨he, K, _, _, _, hK, ⟨φ⟩⟩ := K148.exists_antiSp_of_isSp4 hS
  set ψ : ↥L ≃* ↥(StatedSp 2 K) := φ.trans (antiSpEquiv K) with hψ
  set Pa : Subgroup ↥(StatedSp 2 K) := (P.subgroupOf L).map ψ.toMonoidHom with hPa
  have hPa' : P.subgroupOf L = Pa.map ψ.symm.toMonoidHom := by
    rw [hPa, Subgroup.map_map]
    ext x
    simp
  obtain ⟨χ₁⟩ := nonempty_bar2_hinf_subgroupOf hPL
  obtain ⟨χ₂⟩ := nonempty_bar2_hinf_map_mulEquiv ψ (P.subgroupOf L)
  have hL2 : IsL2 (Bar2 (Hinf Pa)) e → n = e := fun h =>
    kNshape_holds _ _ n e hN
      (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv (χ₂.trans χ₁.symm) h))
  have hparA : IsParabolic2 (⊤ : Subgroup ↥(StatedSp 2 K)) Pa := by
    obtain ⟨S, hSN⟩ := hpar.map ψ.toMonoidHom ψ.surjective
    exact ⟨le_top, S, CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S, inf_le_right.trans hSN⟩
  by_cases htop : Pa = ⊤
  ·
    have hPL' : P = L := by
      refine le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp ?_)
      rw [hPa', htop, Subgroup.map_top_of_surjective _ ψ.symm.surjective]
    rw [hPL'] at hN
    exact nParam_eq_of_isSp4 hN (isSp4_bar2_hinf_self hS) he
  · rcases CFSG.Quasithin.H13.Ch9.KGFF.sp4_perfectCore_parabolic_conj ⟨e, hK⟩ hparA htop with
      hbot | ⟨g, j, hj⟩
    ·
      refine absurd ?_ hinf
      have hPinf : Hinf P = (Hinf (P.subgroupOf L)).map L.subtype := by
        rw [Hinf_map L.subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
      rw [hPinf, hPa', Hinf_map_eq_bot ψ.symm Pa (by rw [Hinf_eq_perfectCore]; exact hbot),
        Subgroup.map_bot]
    ·
      apply hL2
      rw [Hinf_eq_perfectCore, hj, ← Hinf_eq_perfectCore (Q2 K j), Hinf_map]
      exact isL2_bar2_hinf_map_equiv (MulAut.conj g) (Q2 K j)
        (by rw [Hinf_eq_perfectCore]; exact isL2_bar2_perfectCore_Q2 hK he j)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
