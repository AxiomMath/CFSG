module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
public import CFSG.RankThree.GF2n.Tim81.Sec6.Stmts
public import CFSG.GroupTheory.SubgroupSSupCommutative
public import CFSG.GroupTheory.TransferOrderFourCount

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private def sigmaSetCommuting (M V : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ sigmaSet M V ∧ ∀ Y ∈ sigmaSet M V, ⁅X, Y⁆ = ⊥}

private theorem conj_mem_sigmaSetCommuting (hS : Sec5Hyp M V) {m : G} (hm : m ∈ M)
    {X : Subgroup G} (hX : X ∈ sigmaSetCommuting M V) :
    conjSubgroup m X ∈ sigmaSetCommuting M V := by
  obtain ⟨hXmem, hXc⟩ := hX
  refine ⟨hS.conj_mem_sigmaSet hm hXmem, ?_⟩
  intro Y hY
  have hYm : conjSubgroup m⁻¹ Y ∈ sigmaSet M V := hS.conj_mem_sigmaSet (M.inv_mem hm) hY
  have hmap : ⁅conjSubgroup m X, Y⁆ = conjSubgroup m ⁅X, conjSubgroup m⁻¹ Y⁆ := by
    have hY' : Y = conjSubgroup m (conjSubgroup m⁻¹ Y) := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    conv_lhs => rw [hY']
    exact (Subgroup.map_commutator (H₁ := X) (H₂ := conjSubgroup m⁻¹ Y)
      (MulAut.conj m).toMonoidHom).symm
  rw [hmap, hXc _ hYm]
  exact Subgroup.map_bot _

private theorem conjSubgroup_iSup_sigmaSetCommuting_le (hS : Sec5Hyp M V) {m : G} (hm : m ∈ M) :
    conjSubgroup m (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) ≤
      ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) := by
  have hmap : conjSubgroup m (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) =
      ⨆ X : sigmaSetCommuting M V, conjSubgroup m (X : Subgroup G) :=
    Subgroup.map_iSup (MulAut.conj m).toMonoidHom _
  rw [hmap]
  exact iSup_le fun X => le_iSup (fun Y : sigmaSetCommuting M V => (Y : Subgroup G))
    ⟨conjSubgroup m (X : Subgroup G), conj_mem_sigmaSetCommuting hS hm X.2⟩

private theorem isMulCommutative_sup_sigmaSetCommuting (hS : Sec5Hyp M V) :
    IsMulCommutative ↥(V ⊔ ⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) := by
  have h := hS.toRootHyp
  have hVab : IsMulCommutative ↥V := h.toHyp.maxAb.prop.2.2
  have hXab : ∀ X : sigmaSetCommuting M V, IsMulCommutative ↥(X : Subgroup G) := by
    rintro ⟨X, hXmem, -⟩
    obtain ⟨g, rfl, -⟩ := hXmem
    letI := hVab
    exact Subgroup.map_isMulCommutative V (MulAut.conj g).toMonoidHom
  have hVcomm : ∀ X ∈ sigmaSetCommuting M V, ⁅V, X⁆ = ⊥ := by
    rintro X ⟨hXmem, -⟩
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (hS.le_M_of_mem_sigmaSet hXmem).2
  have hEq : V ⊔ ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) =
      sSup (insert V (sigmaSetCommuting M V)) := by
    rw [sSup_insert, sSup_eq_iSup']
  rw [hEq]
  refine CFSG.GroupTheory.isMulCommutative_sSup ?_
  intro A hA B hB
  rw [Set.mem_insert_iff] at hA hB
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact Subgroup.commutator_self_eq_bot_iff.mpr hVab
    · exact hVcomm B hB
  · rcases hB with rfl | hB
    · rw [Subgroup.commutator_comm]
      exact hVcomm A hA
    · by_cases hAB : A = B
      · subst hAB
        exact Subgroup.commutator_self_eq_bot_iff.mpr (hXab ⟨A, hA⟩)
      · exact hA.2 B hB.1

private theorem le_normalizer_sup_sigmaSetCommuting (hS : Sec5Hyp M V) :
    M ≤ Subgroup.normalizer
      ((V ⊔ ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) : Subgroup G) : Set G) := by
  have h := hS.toRootHyp
  intro m hm
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hVfix : conjSubgroup m V = V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer hm)
  have hWle : conjSubgroup m (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) ≤
      ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) :=
    conjSubgroup_iSup_sigmaSetCommuting_le hS hm
  have hWfix : conjSubgroup m (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) =
      ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) := by
    refine le_antisymm hWle ?_
    have hWle' : conjSubgroup m⁻¹ (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) ≤
        ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) :=
      conjSubgroup_iSup_sigmaSetCommuting_le hS (M.inv_mem hm)
    calc (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) =
          conjSubgroup m (conjSubgroup m⁻¹ (⨆ X : sigmaSetCommuting M V, (X : Subgroup G))) := by
            rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ ≤ conjSubgroup m (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) := conjSubgroup_mono hWle'
  rw [conjSubgroup_sup, hVfix, hWfix]

private theorem iSup_sigmaSetCommuting_le (hS : Sec5Hyp M V) :
    (⨆ X : sigmaSetCommuting M V, (X : Subgroup G)) ≤ V := by
  have h := hS.toRootHyp
  have hAM : V ⊔ ⨆ X : sigmaSetCommuting M V, (X : Subgroup G) ≤ M := by
    refine sup_le h.toHyp.le_M ?_
    exact iSup_le fun X => (hS.le_M_of_mem_sigmaSet X.2.1).1
  have hmax := h.toHyp.maxAb.le_of_ge
    ⟨hAM, le_normalizer_sup_sigmaSetCommuting hS, isMulCommutative_sup_sigmaSetCommuting hS⟩
    le_sup_left
  exact (sup_le_iff.mp hmax).2

theorem Sec5Hyp.exists_not_commute (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : ∃ U' ∈ sigmaSet M V, ⁅U, U'⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have h := hS.toRootHyp
  have hU0 : U ∈ sigmaSetCommuting M V := ⟨hU, hcon⟩
  have hUle : U ≤ V :=
    (le_iSup (fun X : sigmaSetCommuting M V => (X : Subgroup G)) ⟨U, hU0⟩).trans
      (iSup_sigmaSetCommuting_le hS)
  have hUV : U ≠ V := ne_of_mem_sigmaSet h hU
  obtain ⟨g, hUg, -⟩ := hU
  have hne : conjSubgroup g V ≠ V := by rwa [hUg] at hUV
  have hUinf : U ⊓ V = ⊥ := by
    rw [hUg, inf_comm]
    exact inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hne
  have hUbot : U = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hUinf]
    exact le_inf le_rfl hUle
  have hcard : Nat.card U = Nat.card V := by rw [hUg, card_conjSubgroup]
  rw [hUbot, Subgroup.card_bot] at hcard
  have h4 := h.four_le_card
  omega

theorem Sec6Hyp.exists_isL2Gen (hS : Sec6Hyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    ∃ U' ∈ sigmaSet M V, IsL2Gen U U' := by
  obtain ⟨U', hU', hne⟩ := hS.sec5.exists_not_commute hU
  rcases hS.res.s513 M V hS.sec5 U hU U' hU' with ⟨hcomm, -⟩ | ⟨hl2, -⟩
  · exact absurd hcomm hne
  · exact ⟨U', hU', hl2⟩

theorem Sec5Hyp.card_orbit_Pc (hS : Sec5Hyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    Nat.card (MulAction.orbit ↥(Pc M V) U) = Nat.card V ^ 2 := by
  letI : MulAction ↥(Pc M V) (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp (Pc M V).subtype)
  have hstab_eq : MulAction.stabilizer ↥(Pc M V) U =
      (Pc M V ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (Pc M V) := by
    ext p
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨p.2, conjSubgroup_eq_self_iff.mp h⟩,
      fun h => conjSubgroup_eq_self_iff.mpr h.2⟩
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥(Pc M V) U) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [hstab_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      hS.Pc_inf_normalizer_eq_centralizer hU]
  letI : Fintype ↥(Pc M V) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit ↥(Pc M V) U) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer ↥(Pc M V) U) := Fintype.ofFinite _
  have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := ↥(Pc M V)) (X := Subgroup G) U
  simp only [← Nat.card_eq_fintype_card] at horb
  have horb2 : Nat.card (MulAction.orbit ↥(Pc M V) U) *
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (U : Set G)) = Nat.card ↥(Pc M V) := by
    rw [← hstabcard]
    exact horb
  have h2 : Nat.card ↥(Pc M V) =
      Nat.card V ^ 2 * Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [← hS.card_Pc_inf_centralizer hU, mul_comm]
  exact Nat.mul_right_cancel (m := Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (U : Set G)))
    Nat.card_pos (horb2.trans h2)

theorem Sec5Hyp.sq_dvd_card_sigmaSet (hS : Sec5Hyp M V) :
    Nat.card V ^ 2 ∣ Nat.card (sigmaSet M V) := by
  classical
  letI : MulAction ↥(Pc M V) (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp (Pc M V).subtype)
  refine CFSG.GroupTheory.TransferOrderFour.dvd_card_of_forall_orbit
    (K := ↥(Pc M V)) (X := Subgroup G) (S := sigmaSet M V) ?_ (Nat.card V ^ 2) ?_
  · intro p X hX
    exact hS.conj_mem_sigmaSet (hS.toRootHyp.toHyp.Pc_le_M p.2) hX
  · intro X hX
    exact (hS.card_orbit_Pc hX) ▸ dvd_refl _

theorem Sec6Hyp.stmt60 (hS : Sec6Hyp M V) : Sec6.Stmt60 M V :=
  ⟨fun U hU => hS.exists_isL2Gen hU, hS.sec5.sq_dvd_card_sigmaSet,
    fun U hU => hS.sec5.V_le_commutator hU⟩

end CFSG.RankThree.GF2n.Tim81
