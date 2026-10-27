module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206h
import CFSG.LocalAnalysis.UniquenessCase.UC22S206e
import CFSG.LocalAnalysis.UniquenessCase.UC22S206f
import CFSG.LocalAnalysis.UniquenessCase.UC22S206i
import CFSG.LocalAnalysis.UniquenessCase.UC22S206j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore ptCore_le_ptPre nonempty_quot_ptCore)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G]

theorem uc22s206k_false [Finite G] (hU : uniqueFourUnique G) {M L : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M)
    (hchar : M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M)
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ M = ptPre α i)
    (hF : ⁅((ptCore α i).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)),
      CFSG.fittingSubgroup (Bar2 M)⁆ ≠ ⊥)
    (h74 : ∀ p : ℕ, p ∈ uniqueFourSigma M → IsStronglyPEmbedded p M → 5 ≤ p →
      ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ M →
        2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Y : Set G)) →
        CFSG.Open.pCoreOf 2 M ⊓ normalizer (Y : Set G) ≠ ⊥ → normalizer (Y : Set G) ≤ M) :
    False := by
  have hKM : ptCore α i ≤ M := by
    refine (ptCore_le_ptPre α i).trans ?_
    rw [← hLM]
    exact inf_le_right
  obtain ⟨p, hp, hp2, -, hC⟩ := uc22s206c_critical hKM
    (CFSG.Quasithin.perfectCore_perfect (ptPre α i))
    (nonempty_quot_ptCore α hα hker (by norm_num) i) hF
  unfold CriticalSection206 at hC
  obtain ⟨R, hRc, -, hRexp, -, -, -, -, d, -, hd4, e, φ, hφker, hφ⟩ := hC
  haveI := hRc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hx, -, hx3, hy7, hxy, E, -, hE, hE8, hyE, hfix⟩ := uc22s206g_lift α hα hker i
    (φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))) hφker
  have hg7 : (φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))) y ^ 7
      = 1 := by
    rw [← map_pow, ← hy7, pow_orderOf_eq_one, map_one]
  have h6 := uc22s206e_six_GL hp2 hE hE8 hg7 hyE hfix
  have hd6 : 6 ≤ d := h6.trans ((Submodule.finrank_le _).trans (Module.finrank_fin_fun _).le)
  have h3r : 3 < CFSG.Open.pRank p M := by
    by_contra hle
    have := hd4 (not_lt.mp hle)
    omega
  obtain ⟨hσ, hsp, hp3, hp7⟩ := uc22s206g_coprime hU hM α hα hLM hp hp2 h3r
  have hh3 : (φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))) x ^ 3
      = 1 := by
    rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
  have h1 := uc22s206f_one_lt_GL hp7 hh3 hg7
    (by rw [← map_inv, ← map_mul, ← map_mul, hxy, map_pow]) h6
  have hrank := uc22s206i_two_le_pRank hKM hp hp2 hp3 hRexp e φ hφ hx3 h1
  have hQ := uc22s206j_pCoreOf_inf_centralizer_ne_bot hKM hchar hp hp2 hp3 e φ hφ hx3 hxy h6
  have hCN : centralizer (zpowers (x : G) : Set G) ≤ normalizer (zpowers (x : G) : Set G) :=
    centralizer_le_normalizer _
  have hx1 : (x : G) ≠ 1 := by
    intro h
    rw [show x = 1 from Subtype.ext h, orderOf_one] at hx3
    omega
  have hN := h74 p hσ hsp (Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3)
    (zpowers (x : G)) (by rw [Ne, zpowers_eq_bot]; exact hx1) (zpowers_le.mpr (hKM x.2))
    (hrank.trans (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf_left _ hCN)))
    (fun hbot => hQ (eq_bot_iff.mpr ((inf_le_inf_left _ hCN).trans (eq_bot_iff.mp hbot))))
  exact uc22s206h_normalizer_not_le α hα hker hLM hx hx3 hN

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
