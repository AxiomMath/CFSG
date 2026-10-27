module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S219Sig3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S219R898
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineTorus
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UCKP898D
import CFSG.LocalAnalysis.UniquenessCase.UCKP3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_9Sig3_of_r847E3SU3 {D : Data G} {Ch : Choice2011 G} (hsig : D.sig.Nonempty)
    (h211 : S21_1 D Ch) (h847 : R847E3SU3 D) (htor : S21_9TorusN D Ch)
    (h898 : ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n → ∀ s : ℕ, Odd s → s ∣ n →
      ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 → (n = 3 ∨ n ≠ 3 * r) →
        ∀ X : Subgroup G, X ≤ L → Nat.card X = r → normalizer (X : Set G) ≤ D.M →
          X ∈ uniqueSet D.M) :
    S21_9Sig3 D Ch := by
  intro h1930 c L hL hLN n hSU hnp _
  obtain ⟨s, r, hs, hsn, hr, hrs, hres⟩ : ∃ s r : ℕ, Odd s ∧ s ∣ n ∧ r.Prime ∧
      r ∣ 2 ^ s - 1 ∧ (n = 3 ∨ n ≠ 3 * r) := by
    by_cases h21 : n = 21
    · subst h21
      exact ⟨7, 127, ⟨3, by norm_num⟩, by norm_num, by norm_num, by norm_num,
        Or.inr (by norm_num)⟩
    obtain hpow | ⟨s, hsp, hsn, hs⟩ := Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
    · exact absurd hpow hnp
    have hne : 2 ^ s - 1 ≠ 1 := by
      have h2 : 2 < 2 ^ s := by
        simpa using Nat.pow_lt_pow_right (by norm_num : 1 < 2) hsp.one_lt
      omega
    obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd hne
    refine ⟨s, r, hs, hsn, hr, hrs, ?_⟩
    rcases eq_or_ne n 3 with hn3 | hn3
    · exact Or.inl hn3
    · refine Or.inr fun h => h21 ?_
      obtain rfl : r = 7 := UC6S898.eq_seven_of_residual hr hs hsn hrs (Or.inr h)
      omega
  obtain ⟨X, hXc, hXL, hXN⟩ := htor h1930 c L hL hLN n hSU s hs hsn r hr hrs
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  have hXU : X ∉ uniqueSet D.M :=
    not_mem_uniqueSet_of_le_normalizer D Ch h211 h1930 c (by rw [hXc]; exact hr)
      (by rw [hXc]; exact hr.odd_of_ne_two hr2) (hXL.trans hL.1.le) hXN
  have hN : ¬ normalizer (X : Set G) ≤ D.M := fun hN =>
    hXU (h898 L hL n hSU s hs hsn r hr hrs hres X hXL hXc hN)
  have hdvdn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  obtain ⟨p, hp⟩ := hsig
  rcases h847 L hL hLN n hSU X hXL r hr hr2 hdvdn hXc p hp with h | ⟨rfl, hn⟩
  · exact absurd h hN
  · exact ⟨hn, hp⟩

theorem s21_9Sig3_dataOfSetup_of_r847E3SU3
    (hG : CFSG.Open.GriessAllModelsStatement) (hSE : StronglyEmbeddedFive)
    (hSE3 : StronglyEmbeddedThree) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) {Ch : Choice2011 G}
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h846 : F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h847 : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) :
    S21_9Sig3 (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_9Sig3_of_r847E3SU3 (UC6S846.sigmaStd_dataOfSetup hS S).nonempty h211 h847
    (s21_9TorusN_of _ Ch uc22pwCartanSU3_holds)
    (fun _ hL _ hX _ hs hsn _ hr hrs hres _ hXL hXc hXN =>
      uc22s219r_mem_uniqueSet _ (UC6S846.sigmaStd_dataOfSetup hS S) h846
        (UCK.u3Center_of_griess hG) UCK.u3Range (UCK.u3FixInner_of_griess hG)
        (UCK.u3FixField_holds hG) (UCK.u3Trio_of_griess hG).1 (UCK.u3Trio_of_griess hG).2.1
        (UCK.u3Trio_of_griess hG).2.2 (PartTwo.Three.r76Sig_dataOfSetup hSE hSE3 hS S)
        (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S) hL hX hs hsn hr hrs hres hXL hXc hXN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
