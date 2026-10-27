module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycTwoP3M4_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16h_e3_cyclic_two_p3m4
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4) :
    (∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) ∨ Case164_4 D V₀ V hV L := by
  by_cases hW : ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))
  · exact Or.inl hW
  · have hsig_sub : ∀ q ∈ D.sig, q = 3 := by
      intro q hq
      rcases hres q hq with h | ⟨h7, -, -⟩
      · exact h.trans hp3
      · omega
    have h3mem : 3 ∈ D.sig := by
      obtain ⟨q, hq⟩ := S.hx.sig_nonempty
      exact (hsig_sub q hq) ▸ hq
    have hsig : D.sig = {3} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨h3mem, fun q hq => hsig_sub q hq⟩
    refine Or.inr ⟨3, Or.inl rfl, hp3 ▸ hLp, ?_, hsig, ?_,
      s16h_e3_CycTwoP3M4_fstar D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW⟩
    · rw [s16h_e3_CycTwoP3M4_dParam_three]
      omega
    · exact s16h_pRank_eq_three D S hr3 h3mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
