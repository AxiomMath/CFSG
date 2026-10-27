module

public import CFSG.OddTranspositions.PartThree.EightFive.Defs
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import CFSG.OddTranspositions.PartThree.EightSeven
public import CFSG.OddTranspositions.SevenOne
public import CFSG.OddTranspositions.TheoremTwo.Assembly
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isBenderGroup_of_disconnected_centSetBar (hT1 : TheoremOne) (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x)
    (hSq : Setup (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
      (centSetBar D ((u * v * w) ^ n)))
    (hdisc : Disconnected (centSetBar D ((u * v * w) ^ n))) :
    CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n))) := by
  let Kbar := localGroup D ((u * v * w) ^ n) ⧸
    CFSG.solvableRadical (localGroup D ((u * v * w) ^ n))
  have hrad : ∀ N : Subgroup Kbar, N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hsol => OddTransp.eq_bot_of_quotient_solvableRadical N hN hsol
  have hConclusion : Conclusion Kbar (centSetBar D ((u * v * w) ^ n)) :=
    hT1 Kbar (centSetBar D ((u * v * w) ^ n)) hSq.isClass hSq.oddT.1 hSq.oddT.2 hSq.gen
      hrad (exists_subgroup_of_disconnected hSq hdisc)
  obtain ⟨x, hx, y, hy, -, hxy, hxyD⟩ :=
    exists_meetsSq_centSetBar hS htri hn hn1 hord htrans
  exact isBenderGroup_of_conclusion hSq hx hy hxy hxyD hConclusion

theorem false_of_commute_mkCentSet (hS : Setup G D) {z : G}
    {u w v : G} (huC : u ∈ centSet D z) (hvC : v ∈ centSet D z) (hwC : w ∈ centSet D z)
    (hno : ¬ ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w)
    {ē : localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)}
    (hē_mem : ē ∈ centSetBar D z)
    (hē_u : Commute ē (mkCentSet D z u huC))
    (hē_v : Commute ē (mkCentSet D z v hvC))
    (hē_w : Commute ē (mkCentSet D z w hwC))
    (hne_u : ē ≠ mkCentSet D z u huC)
    (hne_v : ē ≠ mkCentSet D z v hvC)
    (hne_w : ē ≠ mkCentSet D z w hwC) :
    False := by
  obtain ⟨eL, heL_set, heL_mk⟩ := hē_mem
  have hcomm_eu : Commute eL ⟨u, mem_localGroup_of_mem huC⟩ :=
    commute_of_commute_mk_localGroup_of_ne hS heL_set huC
      (by rw [heL_mk]; exact hē_u) (by rw [heL_mk]; exact hne_u)
  have hcomm_ev : Commute eL ⟨v, mem_localGroup_of_mem hvC⟩ :=
    commute_of_commute_mk_localGroup_of_ne hS heL_set hvC
      (by rw [heL_mk]; exact hē_v) (by rw [heL_mk]; exact hne_v)
  have hcomm_ew : Commute eL ⟨w, mem_localGroup_of_mem hwC⟩ :=
    commute_of_commute_mk_localGroup_of_ne hS heL_set hwC
      (by rw [heL_mk]; exact hē_w) (by rw [heL_mk]; exact hne_w)
  have hcomm_eu_G : Commute (eL : G) u :=
    hcomm_eu.map (Subgroup.subtype (localGroup D z))
  have hcomm_ev_G : Commute (eL : G) v :=
    hcomm_ev.map (Subgroup.subtype (localGroup D z))
  have hcomm_ew_G : Commute (eL : G) w :=
    hcomm_ew.map (Subgroup.subtype (localGroup D z))
  exact hno ⟨(eL : G), heL_set.1, hcomm_eu_G, hcomm_ev_G, hcomm_ew_G⟩

theorem disconnected_centSetBar_of_theorem8_5At (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x)
    (hIH : Theorem8_5At
      (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n))))
    (hno : ¬ ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w)
    (hSq : Setup (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
      (centSetBar D ((u * v * w) ^ n)))
    (huC : u ∈ centSet D ((u * v * w) ^ n))
    (hvC : v ∈ centSet D ((u * v * w) ^ n))
    (hwC : w ∈ centSet D ((u * v * w) ^ n)) :
    Disconnected (centSetBar D ((u * v * w) ^ n)) := by
  by_contra hconn
  let Kbar := localGroup D ((u * v * w) ^ n) ⧸
    CFSG.solvableRadical (localGroup D ((u * v * w) ^ n))
  have hrad : ∀ N : Subgroup Kbar, N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hsol => OddTransp.eq_bot_of_quotient_solvableRadical N hN hsol
  have hnotO4 : ¬ O4PairData Kbar (centSetBar D ((u * v * w) ^ n)) := by
    intro hO4
    obtain ⟨x, hx, y, hy, -, hxy, hxyD⟩ :=
      exists_meetsSq_centSetBar hS htri hn hn1 hord htrans
    exact O4PairData.mul_not_mem hO4 hx hy hxyD
  have hC : HypothesisC (centSetBar D ((u * v * w) ^ n)) :=
    (nonempty_hypothesisC hSq hconn hrad).some
  have h85 : ∀ a b c : localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)),
      IsTriangle (centSetBar D ((u * v * w) ^ n)) a b c →
      IsThirdKind a b c →
      ∃ d ∈ centSetBar D ((u * v * w) ^ n),
        Commute d a ∧ Commute d c ∧ Commute d b :=
    hIH (centSetBar D ((u * v * w) ^ n)) hC hrad hnotO4
  let ubar := mkCentSet D ((u * v * w) ^ n) u huC
  let vbar := mkCentSet D ((u * v * w) ^ n) v hvC
  let wbar := mkCentSet D ((u * v * w) ^ n) w hwC
  have hu_mem : ubar ∈ centSetBar D ((u * v * w) ^ n) :=
    mem_centSetBar_mkCentSet huC
  have hv_mem : vbar ∈ centSetBar D ((u * v * w) ^ n) :=
    mem_centSetBar_mkCentSet hvC
  have hw_mem : wbar ∈ centSetBar D ((u * v * w) ^ n) :=
    mem_centSetBar_mkCentSet hwC
  obtain ⟨hne_uv, hcomm_uv, hmul_uv⟩ :=
    mkCentSet_u_v_spec hS htri hn hn1 hord htrans huC hvC
  have hnot_uw : ¬ Commute ubar wbar :=
    not_commute_mk_u_w hS htri hn hn1 hord rfl htrans huC hwC
      (mem_localGroup_of_mem huC) (mem_localGroup_of_mem hwC)
  have hnot_vw : ¬ Commute vbar wbar :=
    not_commute_mk_v_w_of_transitive hS htri hn hn1 hord htrans hvC hwC
      (mem_localGroup_of_mem hvC) (mem_localGroup_of_mem hwC)
  obtain ⟨ē, hē_mem, hē_ubar, hē_wbar⟩ :=
    exists_commute_commute_of_thirdKind hSq hconn h85 ubar hu_mem wbar hw_mem
  have hcent := centralizer_eq_of_mul_mem hSq hu_mem hv_mem hne_uv hcomm_uv hmul_uv
  have hē_vbar : Commute ē vbar := by
    have hmem : ē ∈ centSetBar D ((u * v * w) ^ n) ∩
        Subgroup.centralizer ({vbar} : Set Kbar) := by
      rw [← hcent.1]
      exact ⟨hē_mem, Subgroup.mem_centralizer_singleton_iff.mpr hē_ubar⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hne_eu : ē ≠ ubar := by
    intro h
    exact hnot_uw (h ▸ hē_wbar)
  have hne_ev : ē ≠ vbar := by
    intro h
    exact hnot_vw (h ▸ hē_wbar)
  have hne_ew : ē ≠ wbar := by
    intro h
    exact hnot_uw (h ▸ hē_ubar).symm
  exact false_of_commute_mkCentSet hS huC hvC hwC hno hē_mem
    hē_ubar hē_vbar hē_wbar hne_eu hne_ev hne_ew

theorem isBenderGroup_quotient_of_theorem8_5At (hT1 : TheoremOne) (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hIH : Theorem8_5At (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    (hno : ¬ ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w) :
    CFSG.BenderSuzuki.IsBenderGroup (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)) := by
  subst z
  have hSq : Setup (localGroup D ((u * v * w) ^ n) ⧸
      CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
      (centSetBar D ((u * v * w) ^ n)) :=
    setup_centSetBar_of_transitive hS htri hn hn1 hord htrans
  obtain ⟨huC, hvC, hwC, -⟩ := thirdKind_mem_centSet hS htri hn hord
  by_cases hdisc : Disconnected (centSetBar D ((u * v * w) ^ n))
  · exact isBenderGroup_of_disconnected_centSetBar hT1 hS htri hn hn1 hord htrans hSq hdisc
  · exact absurd
      (disconnected_centSetBar_of_theorem8_5At hS htri hn hn1 hord htrans hIH hno hSq huC hvC hwC)
      hdisc

end CFSG.OddTranspositions.PartThree
