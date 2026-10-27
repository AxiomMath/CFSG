module

public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftOne
public import CFSG.Quasithin.Background.E2TwoCLie

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem e22BorelLift_lie (hTor : E22TorusCover)
    {H T MH K : Subgroup Γ} (hmin : MinParabolic H T MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hL : E22LieCases H T MH K) : ∃ n : ℕ, 2 ≤ n ∧ E22BorelLift H T MH n := by
  dsimp only [E22LieCases] at hL
  rcases hL with ⟨hJ, t, ht, -, hMeq, n, hn, hty, hB⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB⟩ | ⟨n, hn, hty, -, hB⟩⟩
  · exact ⟨n, hn, BorelLift.lift_one hTor hmin hK hHK hJ ht hMeq hn hty hB⟩
  · exact ⟨n, hBen.1, BorelLift.lift_two hTor hmin hK hHK hTK hJ hBen.1 (Or.inl hBen) hB⟩
  · exact ⟨n, hn, BorelLift.lift_two hTor hmin hK hHK hTK hJ hn (Or.inr hty) hB⟩

theorem e22BorelLift (hE : E22StatementC) (hTor : E22TorusCover)
    {H T MH : Subgroup Γ} (hmin : MinParabolic H T MH) (hSQ : SQTKGroup ↥H)
    (hn : 1 < E1.nParam H) : ∃ n : ℕ, 2 ≤ n ∧ E1.nParam H ≤ n ∧ E22BorelLift H T MH n := by
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd (E1.solvable_nParam_le_one hs) (not_le.mpr hn)
  obtain ⟨⟨K, hK, hHK, -, hc⟩, -⟩ := hE.exists_cases hmin hSQ hns
  dsimp only [E22CasesC] at hc
  rcases hc with ⟨hJ, t, ht, -, hMeq, h1⟩ | ⟨hTK, hJ, h2⟩
  · rcases h1 with ⟨n, hn2, hty, hB, hnH⟩ | ⟨_, _, _, _, _, _, hnH⟩
    · exact ⟨n, hn2, hnH, BorelLift.lift_one hTor hmin hK hHK hJ ht hMeq hn2 hty hB⟩
    · exact absurd hn (by rw [hnH]; exact lt_irrefl 1)
  · rcases h2 with ⟨n, hBen, hB, hnH, -⟩ | ⟨n, -, hty, -, hB, hnH, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH⟩ | ⟨_, _, _, _, _, hnH⟩
    · exact ⟨n, hBen.1, hnH,
        BorelLift.lift_two hTor hmin hK hHK hTK hJ hBen.1 (Or.inl hBen) hB⟩
    · have hn2 := E22A.two_le_of_one_lt_of_le hn hnH
      have hty' : IsPSL 3 2 n ↥(star MH H K) ∨ IsPSp4 2 n ↥(star MH H K) := by
        rcases hty with h | h
        · exact Or.inl h
        · right
          rw [IsSp4Prime] at h
          split_ifs at h with h1
          · omega
          · exact h
      exact ⟨n, hn2, hnH, BorelLift.lift_two hTor hmin hK hHK hTK hJ hn2 (Or.inr hty') hB⟩
    · exact absurd hn (by rw [hnH]; exact lt_irrefl 1)
    · exact absurd hn (by rw [hnH]; exact lt_irrefl 1)

end E2

end CFSG.Quasithin
