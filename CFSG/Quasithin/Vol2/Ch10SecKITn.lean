module

public import CFSG.Quasithin.Vol2.Ch10SecKITc
public import CFSG.Quasithin.Vol2.Ch10SecKITf
public import CFSG.Quasithin.Vol2.Ch10SecKITj

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData)

variable {G : Type} [Group G] [Finite G] {L X : Subgroup G} {n : ℕ}

theorem IsNatBlock.abO2 (h : IsNatBlock X n) (hn : 2 ≤ n) : AbO2 ↥X := by
  refine ⟨fun u v => ?_, not_isPGroup_of_card (by omega) h.card⟩
  have hu : ((u : ↥X) : G) ∈ blockU X := (h.mem_blockU_iff u).mpr u.2
  have hv : ((v : ↥X) : G) ∈ blockU X := (h.mem_blockU_iff v).mpr v.2
  have hU := h.1.2.2.1.1
  have h1 := Subgroup.mem_centralizer_iff.mp (hU hv).2 _ (by rw [h.2.2.2]; exact hu)
  apply Subtype.ext
  apply Subtype.ext
  exact h1

theorem abO2_xbar (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L) :
    AbO2 ↥(modO2Image L X) := by
  rcases h.inf_cases hn hXL with hA | hB
  · obtain ⟨e⟩ := xbar_equiv_of_inf_eq_bot hXL hA
    exact (h.abO2 hn).of_equiv e
  · obtain ⟨-, hc, hp⟩ := xbar_card_B h hn hXL hB
    refine ⟨fun u v => ?_, not_isPGroup_of_card (by omega) hc⟩
    have : Subsingleton ↥(CFSG.pCore 2 ↥(modO2Image L X)) :=
      (Nat.card_eq_one_iff_unique.mp hp).1
    exact Subsingleton.elim _ _

theorem xbar_cards (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L) :
    (Nat.card ↥(modO2Image L X) = 2 ^ (3 * n) * oSL2 n ∧
        Nat.card ↥(CFSG.pCore 2 ↥(modO2Image L X)) = 2 ^ (2 * n)) ∨
      (Nat.card ↥(modO2Image L X) = 2 ^ n * oSL2 n ∧
        Nat.card ↥(CFSG.pCore 2 ↥(modO2Image L X)) = 1) := by
  rcases h.inf_cases hn hXL with hA | hB
  · exact Or.inl (xbar_card_A h hXL hA)
  · exact Or.inr (xbar_card_B h hn hXL hB).2

theorem inf_eq_bot_of_card (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L)
    (hc : Nat.card ↥(modO2Image L X) = 2 ^ (3 * n) * oSL2 n) : X ⊓ pCoreOf 2 L = ⊥ := by
  rcases h.inf_cases hn hXL with hA | hB
  · exact hA
  · exfalso
    have h2 := (xbar_card_B h hn hXL hB).2.1
    obtain ⟨h3, -⟩ := eq_of_card_eq (by omega) (by omega) (hc.symm.trans h2)
    omega

theorem inf_eq_U_of_card (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L)
    (hc : Nat.card ↥(modO2Image L X) = 2 ^ n * oSL2 n) : X ⊓ pCoreOf 2 L = blockU X := by
  rcases h.inf_cases hn hXL with hA | hB
  · exfalso
    have h2 := (xbar_card_A h hXL hA).1
    obtain ⟨h3, -⟩ := eq_of_card_eq (by omega) (by omega) (hc.symm.trans h2)
    omega
  · exact hB


theorem isAlt5_xbar (h : IsNatBlock X 2) (hXL : X ≤ L) (hB : X ⊓ pCoreOf 2 L = blockU X) :
    IsAlt 5 ↥(modO2Image L X) := by
  obtain ⟨⟨F, _, _, hF, ⟨e⟩⟩, -⟩ := xbar_card_B h le_rfl hXL hB
  obtain ⟨e₅⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.nonempty_sl2_equiv_alt5 (K := F)
    (by rw [hF]; norm_num)
  exact ⟨e.trans e₅⟩

omit [Finite G] in
theorem isAlt5_modO2_xbar (h : IsNatBlock X 2) (hXL : X ≤ L) :
    IsAlt 5 (ModO2 (modO2Image L X)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.nonempty_quot
  obtain ⟨eL⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.lbar_modO2_equiv (Γ := G) hXL
  obtain ⟨e₅⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.nonempty_sl2_equiv_alt5 (K := F)
    (by rw [hF]; norm_num)
  exact ⟨(eL.trans e).trans e₅⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
