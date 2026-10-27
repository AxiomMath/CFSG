module

public import CFSG.Walter.Cited.SuzukiCases
public import CFSG.Walter.Cited.CentralSplit
public import CFSG.Walter.ReeOrder.JT.Cited

public section

namespace CFSG.Walter

open scoped MatrixGroups

namespace Suzuki

variable {M : Type} [Group M] [Finite M]

namespace Hyp

variable (h : Hyp M)
include h

theorem le_center_core (hs : IsSimpleGroup (M ⧸ CFSG.pPrimeCore 2 M)) :
    CFSG.pPrimeCore 2 M ≤ Subgroup.center M := by
  set O := CFSG.pPrimeCore 2 M with hO
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hPO := h.le_centralizer_core P
  have : Nontrivial (P : Subgroup M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h.card_sylow P]
    norm_num
  obtain ⟨⟨t, htP⟩, ht1⟩ := exists_ne (1 : (P : Subgroup M))
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have ht2 := h.orderOf_eq_two htP ht1'
  have hOt : O ≤ Subgroup.centralizer ({t} : Set M) := fun o ho =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hPO htP) o ho)
  have hOab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((h.comm t ht2).is_comm.comm ⟨a, hOt ha⟩ ⟨b, hOt hb⟩)
  set C := Subgroup.centralizer (O : Set M) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hmap : C.map (QuotientGroup.mk' O) = ⊤ := by
    have := hCn.map _ (QuotientGroup.mk'_surjective O)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' O)) with h1 | h1
    · exfalso
      have htO : t ∈ O := by
        have : (t : M ⧸ O) ∈ C.map (QuotientGroup.mk' O) := ⟨t, hPO htP, rfl⟩
        rw [h1, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff t).mp this
      have : t ∈ (P : Subgroup M) ⊓ O := ⟨htP, htO⟩
      rw [h.sylow_inf_core P, Subgroup.mem_bot] at this
      exact ht1' this
    · exact h1
  have hCO : C ⊔ O = ⊤ := by
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' O) C
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  have hOC : O ≤ C := fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hOab b hb a ha
  have hCtop : C = ⊤ := by rw [← hCO, sup_eq_left.mpr hOC]
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg o ho).symm

end Hyp

end Suzuki

theorem suzukiFourGroupTheorem :
    JT.SuzukiFourGroupTheorem := by
  intro M _ _ hV hconj hCab
  have h : Suzuki.Hyp M := ⟨hV, hconj, hCab⟩
  rcases h.quotient_cases with ⟨T, hTn, hT4⟩ | ⟨hs, h60⟩
  · exact Or.inl (h.normal_of_quotient hTn hT4)
  · right
    have hcen := h.le_center_core hs
    obtain ⟨L, hL, hd⟩ := Suzuki.exists_isInternalDirectProduct (CFSG.pPrimeCore 2 M)
      Suzuki.odd_card_pPrimeCore hcen h60
    refine ⟨L, CFSG.pPrimeCore 2 M, hL, ?_, Suzuki.odd_card_pPrimeCore, hd⟩
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hcen b.2) a)⟩⟩

end CFSG.Walter
