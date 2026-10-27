module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.LocalAnalysis

open Subgroup CFSG.Assembly.Quasithin

theorem Ccomponent_in_local_family {G : Type*} [Group G] [Finite G] {H S L : Subgroup G}
    (hH : CFSG.Assembly.pCoreOf 2 H ≠ ⊥) (hS : IsPGroup 2 S) (hSH : S ≤ H)
    (hSsyl : ¬ 2 ∣ (S.subgroupOf H).index) (hL : quasithinIsCComponent L H) :
    (L ≤ H ∧ quasithinIsLocal S L) ∧ quasithinIsLocal S L := by
  rw [CFSG.Quasithin.EmptyFaithfulMultiple.quasithinIsCComponent_assembly_iff_open] at hL
  have hLH : L ≤ H := CFSG.Quasithin.le_of_mem_cComp hL
  have hMH : L ⊔ S ≤ H := sup_le hLH hSH
  have hLM : quasithinIsCComponent L (L ⊔ S) := by
    rw [CFSG.Quasithin.EmptyFaithfulMultiple.quasithinIsCComponent_assembly_iff_open]
    exact CFSG.Quasithin.cComp_mem_of_le hL le_sup_left hMH
  have hSM : ¬ 2 ∣ (S.subgroupOf (L ⊔ S)).index := by
    intro h
    apply hSsyl
    have hmul := relIndex_mul_relIndex S (L ⊔ S) H le_sup_right hMH
    rw [relIndex, relIndex, relIndex] at hmul
    rw [← hmul]
    exact h.mul_right _
  have hO : CFSG.Assembly.pCoreOf 2 (L ⊔ S) ≠ ⊥ := by
    intro h
    apply hH
    have hle := CFSG.Quasithin.pCoreOf_le_pCoreOf_of_sylow (p := 2) hMH hS le_sup_right hSsyl
    have h' : CFSG.Open.pCoreOf 2 (L ⊔ S) = ⊥ := h
    exact le_bot_iff.mp (h' ▸ hle)
  have hloc : quasithinIsLocal S L := ⟨hS, hLM, hSM, hO⟩
  exact ⟨⟨hLH, hloc⟩, hloc⟩

end CFSG.LocalAnalysis
