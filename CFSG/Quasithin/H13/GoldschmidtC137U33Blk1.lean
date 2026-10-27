module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.H13.GoldschmidtC137Blk
public import CFSG.Quasithin.H13.GoldschmidtC137U33Cfg

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem isG2Block_of_c132 {L : Subgroup G} (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048)
    (h : CFSG.Quasithin.IsG2Block L ∨ CFSG.Quasithin.IsAltBlockType L 6 ∨
      CFSG.Quasithin.IsSp4Block L ∨ CFSG.Quasithin.IsHatA6Block L ∨
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ CFSG.Quasithin.IsModO2Surj L α) :
    CFSG.Quasithin.IsG2Block L := by
  rcases h with hg | ha | hs | hh | ⟨n, F, hF, hFin, α, hcard, hmod⟩
  · exact hg
  · exfalso
    have := card_of_isAltBlockType ha
    omega
  · exfalso
    obtain ⟨-, F, hF, hFin, hc4, α, hα, hker, -⟩ := hs
    have h1 := card_quot_of_surj α hα hker
    have h2 : Nat.card F = 2 ^ 2 := by
      rw [Nat.card_eq_fintype_card, hc4]
      norm_num
    rw [Vol2.Ch10.SecA.card_Sp4_pow h2] at h1
    omega
  · exfalso
    have h1 : A6.IsHatA6 L := ⟨hh.2.1.1.1, hh.2.1.2.1, hh.2.1.2.2⟩
    have := card_of_hatA6 h1
    omega
  · exfalso
    have h1 := card_quot_of_surj α hmod.1 hmod.2
    rw [card_statedSL_three1527d] at h1
    have hn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
    rw [hn] at h1
    exact sl3_num_ne n (by omega)

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem V_le_pCore : V ≤ pCoreOf 2 L := by
  have hVn : V ≤ normalizer (L : Set G) := h.hred.1.trans h.hn
  have hVL' : ⁅V, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hVn
  rw [h.hVL] at hVL'
  exact le_pCoreOf_of_le_normalizer 2 hVL' h.hLN (B2F.isPGroup_of_isElemAbelian h.hVe)

theorem V_le_blockU : V ≤ blockU L := by
  rw [← h.hVL]
  exact Subgroup.commutator_mono h.V_le_pCore le_rfl

theorem blockU_eq_sup (hshort : IsShort2 L) : blockU L = V ⊔ blockZ L := by
  have hconj : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ = z := fun l hl z hz => by
    have := Subgroup.mem_centralizer_iff.1 hz.2 l hl
    rw [this]
    group
  have hZn : L ≤ normalizer ((blockZ L : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hl' := le_normalizer_blockU L hl
    constructor
    · intro hz
      rw [hconj l hl z hz]
      exact hz
    · intro hz
      have h1 := hconj l⁻¹ (L.inv_mem hl) _ hz
      have h2 : l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z := by group
      rw [h2] at h1
      rw [h1]
      exact hz
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hW : L ≤ normalizer ((V ⊔ blockZ L : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup h.hLN hZn
  rcases hshort.2.2.2.2.2 (V ⊔ blockZ L) le_sup_right (sup_le h.V_le_blockU hZU) hW with hW1 | hW1
  · exfalso
    apply h.hV0
    have hVZ : V ≤ blockZ L := le_sup_left.trans hW1.le
    have : ⁅V, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hVZ.trans inf_le_right)
    rw [← h.hVL, this]
  · exact hW1.symm

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
