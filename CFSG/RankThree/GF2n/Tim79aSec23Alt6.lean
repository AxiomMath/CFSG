module

public import CFSG.RankThree.GF2n.Tim79aSec23Inv
public import CFSG.RankThree.GF2n.Tim79aSec23Degen
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
public import CFSG.ClassicalGroups.A6Klein.Invariant
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.GroupTheory

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem false_of_alt6 (hd : Sec23Data V H)
    (hnd : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4)
    (e : Xbar V H ⧸ Subgroup.center (Xbar V H) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨-, ψ, -, -⟩ := CFSG.QuasithinUnique.Unc25K1.A6Model.exists_pslEquiv
  set φ : Xbar V H ⧸ Subgroup.center (Xbar V H) ≃* CFSG.ClassicalGroups.A6Klein.K0 :=
    e.trans ψ.symm with hφ
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) := e.isSimpleGroup
  have h4 : 4 ≤ Nat.card (barOf V H V) := by
    rcases hc.card_barOf_V_eq_two_or_four_le with h2 | h4
    · exfalso
      obtain ⟨d, hdD, e', heD, h4'⟩ := hnd
      exact hc.degenerate_of_card_two hd h2 d hdD e' heD h4'
    · exact h4
  have hel : IsElemAbelian 2 ((Vtilde V H).map φ.toMonoidHom) :=
    hc.isElemAbelian_Vtilde.map _
  have hcard : 2 < Nat.card ((Vtilde V H).map φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective φ.injective, hc.card_Vtilde hd]
    omega
  obtain ⟨x, Λ, h1, h2, h3, h4'⟩ :=
    CFSG.ClassicalGroups.A6Klein.exists_inv_data_psl29 _ hel hcard
  obtain ⟨xA, ΛA, h1', h2', h3', h4''⟩ :=
    transfer_inv_data φ (Vtilde V H) x Λ h1 h2 h3 h4'
  exact hc.false_of_invariant hsimple hd xA ΛA h1' h2' h3' h4''

end MinCex

end CFSG.RankThree.GF2n.Tim79a
