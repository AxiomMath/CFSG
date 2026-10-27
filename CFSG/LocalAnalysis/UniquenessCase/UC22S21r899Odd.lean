module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s21r899_sp_of_odd_factor {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n m : ℕ} (hLS : IsL2 (Bar2 L) n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ}
    (hp : p ∈ D.sig) (hp3 : p ≠ 3) (hn : n = p * m) (hpn : p ∣ 2 ^ n + 1)
    (hrm : r ∣ 2 ^ m - 1) : IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  refine uc22s21r899_sp_of_lift hSg hfour h614 h76 hL hc3 (Or.inl hLS) hs hsn hr hrs hp hp3 ?_
  intro K₁ h1S K₂ h2S hne A₀ hA₀M hA₀el hA₀c hA₀N a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  exact uc22r8100b_exists_comm_lift (uc22p2214_calC_of_mem_conjSetOf hL h1S)
    (uc22p2214_calC_of_mem_conjSetOf hL h2S) hne (uc22s21r899_isL2_of_mem h1S hLS)
    (uc22s21r899_isL2_of_mem h2S hLS) hn hpp hp2 hpn hr hr2 hrm hA₀M hA₀el hA₀c
    (hA₀N K₁ h1S) (hA₀N K₂ h2S) ha₁ ha₂ ha₁o ha₂o

end CFSG.LocalAnalysis.UniquenessCase.UC22
