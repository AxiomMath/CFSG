module

public import CFSG.Quasithin.Vol2.Ch10SecKITq
public import CFSG.Quasithin.Vol2.Ch10SecKITm
public import CFSG.Quasithin.Vol2.Ch10SecKITo
public import CFSG.Quasithin.Vol2.Ch10SecKITp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData)
open CFSG.Quasithin.Vol2.Ch10.SecC.C10KH (isPSL_of_top isAlt_of_top isHat_of_top)

theorem isSporadic_of_top {Y : Type} [Group Y] {s : TauCeti.SporadicName}
    (h : IsSporadic s ↥(⊤ : Subgroup Y)) : IsSporadic s Y := by
  obtain ⟨e⟩ := h
  exact ⟨Subgroup.topEquiv.symm.trans e⟩

variable {G : Type} [Group G] [Finite G] {M T L X X₁ X₂ : Subgroup G} {n : ℕ}

theorem concl_of_C2 (hLF : Ch10.A312LeviField) (hK1 : KGRank2ParabolicOrder)
    (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T) (hXL : X ≤ L)
    (h : IsNatBlock X n) (hn : 2 ≤ n) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hC2 : A312C2 (modO2Image L X) ⊤) : IsPSL 3 2 n ↥L ∨ IsSL3 (2 ^ n) ↥L := by
  have hcards := xbar_cards h hn hXL
  obtain ⟨hY, hc⟩ := lie_case hLF hK1 hn hC2 (abO2_xbar h hn hXL)
    (hcards.imp And.left And.left)
  have hA := inf_eq_bot_of_card h hn hXL hc
  have hodd := index_odd_of_sl3 (by omega) hY hc
  have hQ := pCore_eq_bot hT hL hX hXL h hA hq hodd
  rcases hY with hY | hY
  · exact Or.inl (isPSL_of_equiv (equivOfPCoreEqBot hQ) hY)
  · exact Or.inr (isSL3_of_equiv (equivOfPCoreEqBot hQ) hY)


theorem false_of_J4 (hK5 : KGJ4NoA5Block) (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M)
    (hX : X ∈ lFamily T) (hXL : X ≤ L) (h : IsNatBlock X 2)
    (hc : Nat.card ↥(modO2Image L X) = 60 ∨ Nat.card ↥(modO2Image L X) = 960)
    (hY : IsSporadic .J4 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))) : False := by
  obtain ⟨h1, h2⟩ := hK5 _ (isSporadic_of_top hY) _ (C10E4.isSylowTwoOf_quot hT hL) _
    (xbar_mem_lFamily hT hL hX hXL)
  rcases hc with hc | hc
  · exact h1 (isAlt5_xbar h hXL (inf_eq_U_of_card h le_rfl hXL hc))
  · have hA := inf_eq_bot_of_card h le_rfl hXL hc
    obtain ⟨n1, n2, -⟩ := natCond_xbar h hXL hA
    exact h2 ⟨n1, n2⟩

omit [Finite G] in
theorem false_of_cross (hc : Nat.card ↥(modO2Image L X) = 960)
    (ho : OutA5 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hJ4 : ¬ IsSporadic .J4 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))) : False := by
  apply not_dvd_64_of_outA5 ho hJ4
  rw [Subgroup.card_top]
  exact (show 64 ∣ 960 by norm_num).trans (hc ▸ Subgroup.card_subgroup_dvd_card _)

theorem false_of_M22 (hK4 : KGMathieuNatBlock) (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M)
    (hX₁ : X₁ ∈ lFamily T) (hX₂ : X₂ ∈ lFamily T) (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L)
    (h₁ : IsNatBlock X₁ 2) (h₂ : IsNatBlock X₂ 2) (hne : modO2Image L X₁ ≠ modO2Image L X₂)
    (hc₁ : Nat.card ↥(modO2Image L X₁) = 960) (hc₂ : Nat.card ↥(modO2Image L X₂) = 960)
    (hY : IsSporadic .M22 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsHat ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
        (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : False := by
  apply hne
  refine hK4 _ (hY.imp isSporadic_of_top isHat_of_top) _ (C10E4.isSylowTwoOf_quot hT hL) _
    (xbar_mem_lFamily hT hL hX₁ hX₁L) _ (xbar_mem_lFamily hT hL hX₂ hX₂L) ?_
  rintro B (rfl | rfl)
  · exact natCond_xbar h₁ hX₁L (inf_eq_bot_of_card h₁ le_rfl hX₁L hc₁)
  · exact natCond_xbar h₂ hX₂L (inf_eq_bot_of_card h₂ le_rfl hX₂L hc₂)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
