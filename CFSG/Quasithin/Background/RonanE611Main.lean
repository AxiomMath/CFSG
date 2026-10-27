module

public import CFSG.Quasithin.Background.RonanE611Comp
public import CFSG.Quasithin.Background.RonanE611BlockCase

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof

section Component

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

theorem component_case (h68 : E68Stmt) (hBK : E68BorelKernel) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hn : 1 < E3.mQuot V U) (hH : ¬ CharTwo (Subgroup.centralizer (U : Set G))) :
    ∃ L X : Subgroup G, Concl h U L X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hO : oddCoreIn H = ⊥ := oddCoreIn_eq_bot_of_maximal h hU hmax hn
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, IsComponentIn L H := by
    by_contra hno
    push Not at hno
    exact hH (DoubleA3.charTwo_of_no_component hno hO)
  obtain ⟨hLM, hcases⟩ := h68 G T M V U L hV h hU hL
  have hLH : L ≤ H := hL.1
  have hCL := cv_eq h hU hmax hL hLM
  unfold E68Case1 E68Case2 E68Case3 E68Case4 E68Case5 at hcases
  rw [hCL] at hcases
  rcases hcases with ⟨k, htype, hZ, hBor, hcyc, hcard, hk, -, -⟩ |
      ⟨k, -, htype, -, -, ⟨hBor, ⟨-, A, hUA, hAV, -, hAM⟩ | ⟨-, h1⟩⟩ |
        ⟨hPS, hPlt, hPmax, hk, hcyc⟩⟩ |
      ⟨-, -, -, h1, -⟩ | ⟨-, ⟨A, hUA, hAV, hA1, hAM⟩, -, -⟩ | ⟨-, -, h1, -⟩
  · subst hk
    have hs := setting_of h hU hmax hn hL hLM hcyc hcard
    rcases htype with ⟨-, h1⟩ | ⟨-, -, h2⟩ | ⟨-, h3⟩ | ⟨-, h4⟩
    · obtain ⟨X, hX⟩ := concl_of_bender h hU hn hBK hs hO hcyc hcard hZ hBor (Or.inl h1)
      exact ⟨L, X, hX⟩
    · obtain ⟨X, hX⟩ := concl_of_bender h hU hn hBK hs hO hcyc hcard hZ hBor (Or.inr (Or.inl h2))
      exact ⟨L, X, hX⟩
    · obtain ⟨X, hX⟩ := concl_of_lin3 h hU hn hs hO hcyc hcard hZ hBor h3
      exact ⟨L, X, hX⟩
    · obtain ⟨X, hX⟩ := concl_of_bender h hU hn hBK hs hO hcyc hcard hZ hBor (Or.inr (Or.inr h4))
      exact ⟨L, X, hX⟩
  · exact absurd (hmax A hUA hAV.le) fun hle => hAM (inf_le_right.trans hle)
  · omega
  · subst hk
    obtain ⟨hcyc', hcard'⟩ := hcyc hn
    have hs := setting_of h hU hmax hn hL hLM hcyc' hcard'
    rcases htype with ⟨-, hmodel⟩ | ⟨h1, -⟩
    · obtain ⟨X, hX⟩ := concl_of_sp4 h hU hn hs hO hcyc' hcard' hmodel hPS hPlt hPmax
      exact ⟨L, X, hX⟩
    · omega
  · omega
  · have hne : U ≠ A := fun he => by
      rw [he, hA1] at hn
      exact lt_irrefl 1 hn
    exact absurd (hmax A (lt_of_le_of_ne hUA hne) hAV) fun hle => hAM (inf_le_right.trans hle)
  · omega

end Component

theorem e611_holds (h68 : E68Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hBK : E68BorelKernel) :
    Stmt := by
  intro G _ _ T M V U h hU hmax hn
  by_cases hH : CharTwo (Subgroup.centralizer (U : Set G))
  · exact block_case hC129 h hU hmax hn hH
  · exact component_case h68 hBK h hU (fun W h1 h2 => hmax W h2 h1) hn hH

end CFSG.Quasithin.RonanE611
