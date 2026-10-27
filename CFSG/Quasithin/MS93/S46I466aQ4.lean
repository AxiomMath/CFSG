module

public import CFSG.Quasithin.MS93.S46I466aQC2

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S46.I466b
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

theorem relIndex_qv_le_sq (h464 : I464) (h465 : I465) {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) :
    (Qv _ α).relIndex (Qv _ β) ≤ Fintype.card F ^ 2 := by
  have hU := (h465 G M T L F φ c α β hα hαβ).1
  have hZ := h464 G M T L F φ c α β hα hαβ
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hβK : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  rw [← card_natImage_eq_relIndex h hφ hα hψ hβK]
  have hq2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact two_le_card_field
  rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ, I464.card_commutator_eq_pow hψ hβK,
    ← Nat.card_eq_fintype_card] at hU
  have hcomm : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 :=
    Nat.pow_right_injective hq2 hU
  have hfix : commN (natImage ψ (Qv (puAmalgam h.le) β)) ≤
      fixN (natImage ψ (Qv (puAmalgam h.le) β)) := by
    refine I464.commN_le_fixN_of_commutator_le_centralizer hψ hβK ?_
    rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ] at hZ
    exact hZ.trans (zh_le_centralizer _ β)
  have hfix2 : 2 ≤ Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) :=
    hcomm ▸ Submodule.finrank_mono hfix
  have hfix3 := Submodule.finrank_le (fixN (natImage ψ (Qv (puAmalgam h.le) β)))
  rw [Module.finrank_fin_fun] at hfix3
  have h1 := card_le_pow_finrank (natImage ψ (Qv (puAmalgam h.le) β))
  have h2 : (3 - Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β)))) *
      Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) ≤ 2 := by
    rw [hcomm]
    omega
  rw [← Nat.card_eq_fintype_card]
  exact h1.trans (Nat.pow_le_pow_right (by omega) h2)

theorem relIndex_qv_eq_of_edge {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) {α β α' β' : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hα' : IsMVtx _ α')
    (hα'β' : (puAmalgam h.le).treeGraph.Adj α' β') :
    (Qv (puAmalgam h.le) α').relIndex (Qv _ β') = (Qv (puAmalgam h.le) α).relIndex (Qv _ β) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hα' hα'β'
  rw [qv_smul, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem commutator_vv_le_zloc_of (h43 : S43) (h462 : I462) (h463 : I463) (h464 : I464)
    (h465 : I465) {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Hyp46 M T L φ) (hq : 4 ≤ Fintype.card F)
    (hS : ∀ α β : Vtx (puAmalgam c.pu.le), IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2)
    {z : Vtx (puAmalgam c.pu.le)} (hz : IsMVtx _ z) :
    ⁅Vv (puAmalgam c.pu.le) z, Vv _ z⁆ ≤ Zloc c.pu.le L z := by
  have hII := fun α β (hα : IsMVtx _ α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) =>
    exists_typeII_pair_at_edge h43 h462 h463 h464 h465 c hS hα hαβ
  have h464' := h464 G M T L F φ c
  have hsq := fun δ ρ (hδ : IsMVtx (puAmalgam c.pu.le) δ)
    (hδρ : (puAmalgam c.pu.le).treeGraph.Adj δ ρ) => (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  exact commutator_vv_le_zloc h hφ (centHyp_of_gen23 h hfull) hb4 hS h464' hsq hq hII hz

end CFSG.Quasithin.MS93.S46
