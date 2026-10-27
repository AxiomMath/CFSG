module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Cfg
public import CFSG.Quasithin.H13.GoldschmidtC137U33Facts

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem concl4_of_line (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
    (hl : G2Line (autI h.hVe L) (autI h.hVe P)) :
    Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
      l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      P ≤ normalizer (l : Set G) := by
  obtain ⟨l', hl1, hl2, hl3⟩ := hl
  have hPN : ∀ q ∈ P, q ∈ normalizer (V : Set G) := fun q hq => h.hXN (h.hPX.le hq)
  have hfwd : ∀ q ∈ P, ∀ x ∈ l'.map (C124.blkVal h.hVe),
      q * x * q⁻¹ ∈ l'.map (C124.blkVal h.hVe) := by
    rintro q hq _ ⟨w, hw, rfl⟩
    have hφ := hl3 (convI h.hVe ⟨q, hPN q hq⟩) (convI_mem_autI h.hVe hq (hPN q hq)) w hw
    refine ⟨_, hφ, ?_⟩
    rw [C124.blkVal_apply, C124.blkVal_apply, convI_apply_val]
  refine ⟨hF.card_X, l'.map (C124.blkVal h.hVe), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hw : IntMod.mk h.hVe ⟨x, hx.1⟩ ∈ fixV (autI h.hVe L) :=
      (mem_fixV_autI h.hVe h.hLN _).2 hx.2
    exact ⟨_, hl1 hw, rfl⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.val_mem
  · rw [Subgroup.card_map_of_injective (C124.blkVal_injective h.hVe), hl2,
      card_fixV_autI h.hVe h.hLN]
  · intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd p hp x, fun hx => ?_⟩
    have := hfwd p⁻¹ (P.inv_mem hp) _ hx
    simpa [mul_assoc] using this

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
