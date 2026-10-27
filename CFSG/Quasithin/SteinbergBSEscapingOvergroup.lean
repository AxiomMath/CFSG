module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup

variable {G : Type*} [Group G]

theorem le_pCore_of_normal {p : ℕ} {K : Subgroup G} {Q : Subgroup K} [Q.Normal]
    (hQ : IsPGroup p Q) : Q ≤ pCore p K :=
  le_sSup ⟨inferInstance, hQ⟩

theorem le_of_minimal_escaping_overgroup [Finite G] (T : Sylow 2 G) {M H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hH2 : pCore 2 H ≠ ⊥)
    (hmin : ∀ K : Subgroup G, (T : Subgroup G) ≤ K → pCore 2 K ≠ ⊥ → ¬ K ≤ M → K ≤ H → K = H)
    {K : Subgroup G} (hTK : (T : Subgroup G) ≤ K) (hKH : K < H) : K ≤ M := by
  by_contra hKM
  refine hKH.ne (hmin K hTK ?_ hKM hKH.le)
  set Q : Subgroup G := (pCore 2 H).map H.subtype with hQ
  have hQT : Q ≤ T := by
    have h1 := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype hTH)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 hx
  have hQK : Q ≤ K := hQT.trans hTK
  have hQn : (Q.subgroupOf K).Normal := ⟨fun x hx k => by
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨(k : G) * y * (k : G)⁻¹, mul_mem (mul_mem (hKH.le k.2) y.2) (inv_mem (hKH.le k.2))⟩,
      ?_, ?_⟩
    · exact (pCore_normal (p := 2) (G := H)).conj_mem y hy ⟨k, hKH.le k.2⟩
    · simp [← hyx]⟩
  have hQp : IsPGroup 2 (Q.subgroupOf K) := by
    have h1 : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := H)).map H.subtype
    exact h1.of_equiv (subgroupOfEquivOfLe hQK).symm
  have hQ1 : Q.subgroupOf K ≠ ⊥ := by
    intro h
    apply hH2
    rw [eq_bot_iff]
    intro x hx
    have h1 : ((x : G) : G) ∈ Q := ⟨x, hx, rfl⟩
    have h2 : (⟨x, hQK h1⟩ : K) ∈ Q.subgroupOf K := h1
    rw [h, mem_bot] at h2
    exact (mem_bot).2 (Subtype.ext (congrArg (Subtype.val : K → G) h2))
  intro h
  exact hQ1 (le_bot_iff.1 (h ▸ le_pCore_of_normal hQp))

theorem source_minimal_escaping_overgroup_unique_sylow_maximal [Finite G] (T : Sylow 2 G)
    {M H : Subgroup G} (hTM : normalizer ((T : Subgroup G) : Set G) ≤ M)
    (hTH : (T : Subgroup G) ≤ H) (hH2 : pCore 2 H ≠ ⊥) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, (T : Subgroup G) ≤ K → pCore 2 K ≠ ⊥ → ¬ K ≤ M → K ≤ H → K = H) :
    ¬ ((T : Subgroup G).subgroupOf H).Normal ∧ (T : Subgroup G) ≤ H ⊓ M ∧ H ⊓ M < H ∧
      (∀ K : Subgroup G, (T : Subgroup G) ≤ K → K < H → K ≤ H ⊓ M) ∧
      (∀ K : Subgroup G, H ⊓ M ≤ K → K ≤ H → K = H ⊓ M ∨ K = H) ∧
      ∀ K : Subgroup G, (T : Subgroup G) ≤ K → K < H →
        (∀ L : Subgroup G, K ≤ L → L ≤ H → L = K ∨ L = H) → K = H ⊓ M := by
  have hTHM : (T : Subgroup G) ≤ H ⊓ M := le_inf hTH (le_normalizer.trans hTM)
  have hlt : H ⊓ M < H := lt_of_le_of_ne inf_le_left fun h => hHM (h ▸ inf_le_right)
  have hle : ∀ K : Subgroup G, (T : Subgroup G) ≤ K → K < H → K ≤ H ⊓ M := fun K hTK hKH =>
    le_inf hKH.le (le_of_minimal_escaping_overgroup T hTH hH2 hmin hTK hKH)
  refine ⟨fun hn => hHM ((normal_subgroupOf_iff_le_normalizer hTH).1 hn |>.trans hTM), hTHM, hlt,
    hle, fun K hMK hKH => ?_, fun K hTK hKH hmax => ?_⟩
  · by_cases hK : K = H
    · exact Or.inr hK
    · exact Or.inl (le_antisymm (hle K (hTHM.trans hMK) (lt_of_le_of_ne hKH hK)) hMK)
  · rcases hmax (H ⊓ M) (hle K hTK hKH) inf_le_left with h | h
    · exact h.symm
    · exact absurd h hlt.ne

end CFSG.Quasithin.SteinbergBS
