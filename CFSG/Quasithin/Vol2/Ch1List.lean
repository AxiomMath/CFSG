
module

public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem map_mem_lFamily_quotient (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    {S B : Subgroup X} (hNS : N ≤ S) (hB : B ∈ lFamily S) :
    B.map (QuotientGroup.mk' N) ∈ lFamily (S.map (QuotientGroup.mk' N)) := by
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hker : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have hkerle : (QuotientGroup.mk' N).ker ≤ B ⊔ S := by
    rw [QuotientGroup.ker_mk']; exact hNS.trans le_sup_right
  have hBbar := map_mem_cComp_of_le (QuotientGroup.mk' N) hker hkerle hB'
  rw [Subgroup.map_sup] at hBbar
  exact hBbar

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem modO2Image_mem_lFamily {H S B : Subgroup G} (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) :
    modO2Image H B ∈ lFamily ((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hBS : B ⊔ S ≤ H := sup_le hBH hS.1
  have hB'' : B.subgroupOf H ∈ lFamily (S.subgroupOf H) := by
    show B.subgroupOf H ∈ cComp (B.subgroupOf H ⊔ S.subgroupOf H)
    rw [← Subgroup.subgroupOf_sup hBH hS.1]
    exact subgroupOf_mem_cComp_of_le hBS hB
  exact map_mem_lFamily_quotient (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group _)
    (pCore_two_le_subgroupOf hS) hB''

theorem lemma_1_2_4_list_of_a3_sq {H S B L : Subgroup G}
    (h312 : A312Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) (hL : L ∈ cComp H) (hBL : B ≤ L) :
    modO2Image H B = modO2Image H L ∨ A312Case (modO2Image H B) (modO2Image H L) ∨
      A312Nonquasi (modO2Image H B) (modO2Image H L) := by
  have hSbar := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨L', hL', hBL', huniq, hlist⟩ := h312 _ hSbar _ (modO2Image_mem_lFamily hS hBH hB)
  have hLbar : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_mem_cComp hL
  have hBLbar : modO2Image H B ≤ modO2Image H L :=
    Subgroup.map_mono (fun x hx => hBL hx)
  have heq : modO2Image H L = L' := huniq _ hLbar hBLbar
  rw [heq]
  exact hlist

theorem lemma_1_2_4_list (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h312 : A312ForSQTK) {H S B L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H) (hB : B ∈ lFamily S)
    (hL : L ∈ cComp H) (hBL : B ≤ L) :
    modO2Image H B = modO2Image H L ∨ A312Case (modO2Image H B) (modO2Image H L) ∨
      A312Nonquasi (modO2Image H B) (modO2Image H L) :=
  lemma_1_2_4_list_of_a3_sq (h312 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hH)) hS hBH hB hL
    hBL

end Ambient

end CFSG.Quasithin
