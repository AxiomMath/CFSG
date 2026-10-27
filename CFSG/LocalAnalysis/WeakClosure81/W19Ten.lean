module

public import CFSG.LocalAnalysis.WeakClosure81.W19TenA
public import CFSG.LocalAnalysis.WeakClosure81.W19TenK
public import CFSG.LocalAnalysis.WeakClosure81.W19TenR
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEleven
public import CFSG.LocalAnalysis.WeakClosure81.W19TenStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

section Certified


theorem card_V₀_and_sq (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : Card196Four D V p X) {E F : Subgroup G} (hE : Hyp198 D X E F) (hFE : F < E)
    (hEV : E ≤ V) {g : G} (hA : conjSubgroup V g ≤ D.T) (hAE : ¬ ⁅conjSubgroup V g, E⁆ ≤ F) :
    Nat.card ↥V₀ = 2 ∧ g ^ 2 ∉ D.M := by
  obtain ⟨hAV, B, hB, hcard⟩ := Hyp198.nine c h162 h4 hE hFE hA hAE
  obtain ⟨R, hRVg, hR4, hΓ⟩ := c.exists_four_group hE hFE hEV hB hAV hcard
  have h197 := Hyp198.hyp197 c hE hFE hA hAE
  obtain ⟨K, hK⟩ := c.exists_conf196 hA (h197.not_comm_le_pCoreOf c)
  obtain ⟨k, -, hk, hs⟩ := c.exists_inCalOStar h162 hK
  obtain ⟨h1, h2, h3⟩ := Hyp65.one_facts_conj hk hs
  have h := fourteen_eleven (M := D.M) (V₀ := V₀) (V := V) (X := conjSubgroup V₀ (g * k * g⁻¹))
    (R := R) (g := g) c.setting.isElemAbelian c.V₀_le_V c.setting.pair.le_normalizer
    (c.setting.normalizer₀ c.ne_bot) (c.setting.ti₀ c.ne_bot).1
    (fun v hv hv₀ => (c.setting.gen c.ne_bot v hv hv₀).symm) (hK.g_not_mem_M c) hRVg hR4 hΓ h1 h2
    h3.le
  rw [h3] at h
  exact h

theorem nineteen_ten (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) (h4 : Card196Four D V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hFE : F < E) (hEV : E ≤ V)
    (hXE : ¬ ⁅X, E⁆ ≤ F) :
    Nat.card ↥V₀ = 2 ∧ (∃ g : G, conjSubgroup V g ≤ D.T ∧ ¬ ⁅conjSubgroup V g, E⁆ ≤ F) ∧
      ∀ g : G, conjSubgroup V g ≤ D.T → ¬ ⁅conjSubgroup V g, E⁆ ≤ F → g ^ 2 ∉ D.M := by
  obtain ⟨g₀, hA₀, hAE₀⟩ := c.exists_conj_not_comm_le h4 hE hXE
  exact ⟨(c.card_V₀_and_sq h162 h4 hE hFE hEV hA₀ hAE₀).1, ⟨g₀, hA₀, hAE₀⟩,
    fun g hA hAE => (c.card_V₀_and_sq h162 h4 hE hFE hEV hA hAE).2⟩

end Certified

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
