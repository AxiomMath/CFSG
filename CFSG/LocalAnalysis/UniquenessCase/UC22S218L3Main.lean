module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3Ex
import CFSG.LocalAnalysis.UniquenessCase.UC22S218CenL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three_L3 (hGA : GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsL3 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig)
    (hgen : ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1 ∧ (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center (Bar2 L))))) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  refine uc22s218n_pRank_le_three_of_facts_ex D Ch hSg h614 h211 h76 hH c hL (torusFacts218_L3 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp ?_
  ·
    have h1 : ℓ ∣ Nat.gcd 3 (2 ^ n - 1) := hdvd.trans (card_center_bar2_dvd_of_isL3 hGA hL hX hn)
    have hℓ3 : ℓ = 3 :=
      (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (h1.trans (Nat.gcd_dvd_left _ _))
    have h3n : 3 ∣ 2 ^ n - 1 := hℓ3 ▸ h1.trans (Nat.gcd_dvd_right _ _)
    subst hℓ3
    exact ⟨fun h => h.2 rfl, fun h => h h3n⟩
  · intro hT hO h4 hN s r hs hsn hr hrs hrK
    have := hN
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hLM : L ≤ D.M := hL.1.le
    have hp1 : p ∣ 2 ^ n - 1 := by
      by_contra h
      exact hO h
    have hp3 : p = 3 := by
      by_contra h
      exact hT ⟨hp1, h⟩
    have hgen' : ¬ 3 ∣ n ∧ ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) :=
      ⟨fun h => hgen ⟨hp3, hp3 ▸ hp1, Or.inl h⟩, fun h => hgen ⟨hp3, hp3 ▸ hp1, Or.inr h⟩⟩
    subst hp3
    have h2n : 2 ∣ n := by
      by_contra h
      exact uc22s218_l3_not_three_dvd (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)) hp1
    have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (by rw [← h]; exact hrs)
    have hpK : ¬ 3 ∣ Nat.card (CFSG.solvableRadical ↥L) :=
      not_dvd_card_solvableRadical hL.2.2 hpp hp2 hgen'.2
    have haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (BarInf L))) ≤ 3 := by
      have := uc22s218_l3_pRank_mulAut_le_two hX h2n hgen'.1
      omega
    obtain ⟨T, hTc, hTE, y, hyT, hyo⟩ := uc22s218_l3_torus_order_three hX hp1
    obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ :=
      hTE r hr (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)) hr3
    refine uc22s218_exists_pair_of_kernel hLM (CFSG.solvableRadical ↥L) hpp hr (Ne.symm hr3) hpK
      hrK haut h4 hE₀ hE₀c hyo (fun e he => hTc y hyT e (hE₀T he)) ?_
    by_contra hcen
    have hy1 := uc22s218_l3_center_eq_one hX y fun x =>
      (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
    rw [hy1, orderOf_one] at hyo
    exact hpp.one_lt.ne hyo

end CFSG.LocalAnalysis.UniquenessCase.UC22
