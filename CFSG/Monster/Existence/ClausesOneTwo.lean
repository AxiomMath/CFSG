module

public import CFSG.Monster.Existence.ELevelFullness
public import CFSG.Monster.Existence.NormalizerF
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.Existence.FullnessAssembly
import Mathlib.Tactic.Group
public import Certificates.Certificate43
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6025
public import Certificates.Certificate3024
public import Certificates.Certificate3027
public import Certificates.Certificate3053
public import Certificates.Certificate8955
public import CFSG.Monster.B.TwoA.Co2Inv.Kernel
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem xfusion_of_census
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g) :
    ∀ y ∈ GmatGriess, IsConj xGriess y → ∃ g ∈ GmatGriess, g * xGriess * g⁻¹ = y := by
  intro y hy hxy
  set g : Gmat := ⟨y, hy⟩ with hgdef
  let ι : Gmat →* MGriess := Subgroup.inclusion Gmat_le_AutO
  have hιg : ι g = y := rfl
  have hy2 : orderOf y = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy
    rw [← SemiconjBy.orderOf_eq c (x := xGriess) (show c * xGriess = y * c by rw [← hc]; group)]
    exact orderOf_xGriess
  have hg2 : orderOf g = 2 := by
    rw [← orderOf_injective ι (Subgroup.inclusion_injective Gmat_le_AutO) g, hιg]
    exact hy2
  rcases hcensus g hg2 with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine ⟨ι c, c.2, ?_⟩
    rw [← hιg, ← hc, map_mul, map_mul, map_inv]
    rfl
  · exfalso
    have h' : IsConj tGriess y := by
      have := ι.map_isConj h
      rw [hιg] at this
      exact this
    exact not_isConj_xGriess_tGriess (hxy.trans h'.symm)

theorem natCard_Cgen_eq : Nat.card Cgen = 2 * Nat.card Cbar := by
  have h2 : Nat.card Zstar = 2 := by rw [Zstar, Nat.card_zpowers, orderOf_tStarC]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zstar, h2, mul_comm]

theorem monster_existence_clauses_one_two_of_inputs
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g)
    (hEb : ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f))
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    (hcount : Nat.card Gmat = 97239461142009186000 * Nat.card Cgen)
    (hS : Nat.card Cbar = 4154781481226426191177580544000000)
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B)) :
    (Finite MGriess ∧ IsSimpleGroup MGriess ∧ (∃ x y : MGriess, x * y ≠ y * x) ∧
      Nat.card MGriess = CFSG.Open.monsterOrder) ∧
    orderOf tGriess = 2 ∧ orderOf xGriess = 2 ∧ ¬ IsConj tGriess xGriess ∧
    (∀ t : MGriess, orderOf t = 2 → IsConj tGriess t ∨ IsConj xGriess t) ∧
    (∀ α, IsConj tGriess α → IsTwoACentralizer α) ∧
    (∀ ζ, IsConj xGriess ζ → IsTwoBCentralizer ζ) := by
  have hE := centralizer_FE_le_GmatGriess (xfusion_of_census hcensus) hEb
  have hNF := mem_Cgen_of_conj_uA hE hH
  obtain ⟨e⟩ := nonempty_DA_equiv_B_of hStroth hNF phiB rank_phiB_uBar_sub_one
  refine monster_existence_clauses_one_two_of hcensus e card_Cbar_eq_card_B ?_
  rw [hcount, natCard_Cgen_eq, hS]
  norm_num [CFSG.Open.monsterOrder]

end CFSG.Monster.Existence
