module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmtUn
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem stroth717_of_cases_un (h78 : Stroth78Statement) (hA : Step717CaseAStatement)
    (hInv : Sec717InvStatement)
    (hNU : Step717NotUnitaryStatement) (h711S : Stroth711StrongStatement)
    (h713 : Stroth713Statement) (hNR : Sec7NormZ0Statement)
    (hZV : Sec7ZVStatement) (hNL : Sec7NormLB'Statement) (h27 : Tim81StrothUnStatement)
    (hSub : Step7HypSub'Statement) : Stroth717Statement := by
  intro G _ _ M Q Z B _ hc n t h5 hlarge hp3
  have hs : Sec7Hyp hc n t :=
    ⟨h5, fun hp2 => by have := hp3.eq_of_plus hp2; omega, ⟨3, by norm_num, Or.inl hp3⟩, hlarge⟩
  have hN9 : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    rcases h78 G M Q Z B hc n t h5 hlarge hs.notPlus4 3 (by norm_num) (Or.inl hp3) with
      ⟨-, -, hN⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h5', -⟩ | ⟨h6, -⟩
    · exact hN
    all_goals omega
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc h5.mem
  by_cases hcase : ∃ L : Subgroup G, Sec717L hc t Z0 L ∧
      ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L
  · obtain ⟨L, hL, hLn⟩ := hcase
    exact Or.inr (hA G M Q Z B hc n t hs hp3 Z0 hZ0 L hL hLn)
  · have hcase' : ∀ L : Subgroup G, Sec717L hc t Z0 L →
        ∃ k ∈ NormH0 M Z Z0, conjSubgroup k L ≠ L := by
      intro L hL
      by_contra hno
      exact hcase ⟨L, hL, fun k hk => by
        by_contra hne
        exact hno ⟨k, hk, hne⟩⟩
    have hn4 : ¬ OmegaPlusNat hc t 4 := fun h => by have := hp3.eq_of_plus h; omega
    have hnom : ¬ OmegaMinusNat hc t 2 := fun h => by
      have := omegaPlusNat_eq_omegaMinusNat (by norm_num) hp3 h
      omega
    have hN' := h711S G M Q Z B hc n t hs
    have hF := h713 G M Q Z B hc n t hs hn4 Z0 hZ0
    have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
    have hMA := step717MaxAb_of_inv hInv G M Q Z B hc n t hs hp3 Z0 hZ0 hcase' hN' hF
    rcases h27 G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF
        (hNL G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF) 9 hN9 with ⟨m, hm9, hU⟩ | ⟨g, hg, hle, hne⟩
    · have hm6 : m = 6 := by omega
      subst hm6
      exact absurd hU (hNU G M Q Z B hc n t hs hp3)
    · exact Or.inl (hSub G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF
        (invAbelian_of_inv717 hInv hc hs hp3 hZ0) ⟨g, hg, hle, hne⟩).subConfig

end CFSG.RankThree.GF2n.Stroth80
