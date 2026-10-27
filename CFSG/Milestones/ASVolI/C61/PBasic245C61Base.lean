module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56
open CFSG.QuasithinUnique.C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem pCoreOf_ne_bot (hcs : burnsideC56_CS G T M H S L) : pCoreOf 2 H ≠ ⊥ := fun h =>
  blockU_ne_bot (isShort hcs) (le_bot_iff.mp (h ▸ blockU_le_pCoreOf_general hcs))

theorem normT_le_of_isMaxElemAbelian (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G}
    (hSM : S ≤ M₀) (hMT : M₀ ≤ T) {x : G} (hx : x ∈ M₀)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian S A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) : normT T S ≤ M₀ := by
  have hHP : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have h244 : ∀ y, y ∈ T → y ∈ normalizer (pCoreOf 2 H : Set G) → y ∈ S := fun y hyT hyN => by
    have e := hcs.l244 (pCoreOf 2 H) (pCoreOf_ne_bot hcs) (pCoreOf_le_S hcs) hHP
    have : y ∈ T ⊓ normalizer (pCoreOf 2 H : Set G) := ⟨hyT, hyN⟩
    rwa [e] at this
  intro σ hσ
  have hσT : σ ∈ T := hσ.1
  have hσN : σ ∈ normalizer (S : Set G) := hσ.2
  have hP : IsMaxElemAbelian S (pCoreOf 2 H) := (hA _).mpr (Or.inl rfl)
  have hP' := isMaxElemAbelian_conjSubgroup hP hσN
  rcases (hA _).mp hP' with h | h
  · exact hSM (h244 σ hσT (conjSubgroup_eq_iff_mem_normalizer.mp h))
  · rw [conjR_eq] at h
    have h' : conjSubgroup (pCoreOf 2 H) (σ * x⁻¹) = pCoreOf 2 H := by
      rw [← conjSubgroup_conjSubgroup, h, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    have hσx : σ * x⁻¹ ∈ S :=
      h244 _ (mul_mem hσT (inv_mem (hMT hx))) (conjSubgroup_eq_iff_mem_normalizer.mp h')
    have e : σ = (σ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (hSM hσx) hx

theorem normT_eq (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian S A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) : normT T S = M₀ :=
  le_antisymm (normT_le_of_isMaxElemAbelian hcs hSM hMT hx hA) fun _ hm =>
    ⟨hMT hm, normalizer_of_relIndex_two hSM h2 hm⟩

end C56

end CFSG.QuasithinUnique.burnsideC56_P
