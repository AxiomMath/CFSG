module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem twelve_nineteen (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D)
    (h613 : UC6.R6_13 D) (hhyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h1111 : F11.R111 D) (h112 : F11.R112 D) (h126 : R126 D) (h127 : R127 D)
    (h1211 : R1211_1 D) (h111 : W3Thm111 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    D.sig = D.sig1 := by
  have h3 : D.sig3 = ∅ := h1111 V₀ V (h.hyp11 h127)
  have h2 : D.sig2 = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun p hp => ?_
    obtain ⟨P, P₀, hH⟩ := hhyp612 p hp
    have hpσ : p ∈ D.sig := by
      rw [D.sig_sub]
      exact Or.inl (Or.inr hp)
    have hpP : p.Prime := (D.sig_prime p hpσ).1
    have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
    have hk2 : D.k ≤ 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      split_ifs <;> norm_num
    have hm3 : MBarGT D.M V₀ V 3 := TwelveNineteen.mBarGT_three D hstd h613 h112 h127 hH h
    have hmk : MBarGT D.M V₀ V (D.k + 1) := TwelveShort.mBarGT_mono hm3 (by omega)
    have hP₁ := TwelveNineteen.inP11_P1 D hstd h613 hH
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
      · have hV1 : InCalV1 D.M D.T V := hW.1.1
        have hVV : InCalV D.M V := hV1.1
        have hV' : IsElemAbelian 2 V := hVV.2.2.2
        have hm2 : MBarGT D.M ⊥ V 2 := TwelveShort.mBarGT_mono hm3 (by omega)
        have hgt : D.k + 1 < E3.sParam hV' :=
          TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hmk
        obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
        have hS : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
        have hE : E1.InE D.k H₀ := h126 H₀ hmin
        have hW0 : E3.wClos V 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D hVV
        obtain ⟨X, hXM, hXp, hexp, hbig, hperm⟩ := TwelveNineteen.exists_permutes D hstd h613 hH
        have hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU D.M Y := fun Y hYX hYnc =>
          h61 p hpσ Y (hYX.trans hXM) (hXp.to_le hYX) hYnc
        exact hmin.1.2.1 (six_sixteen_one_i_uncond hV' D.maxLocal hS (TwelveShort.one_le_k D) hE
          hW0 hgt hpP hp2 hXM hexp hbig hperm hUY)
      · exact absurd rfl h0.1.1
    · exact h1211 V₀ V h ⟨_, hP₁⟩ hV0 hmk
  rw [D.sig_sub, h2, h3, Set.union_empty, Set.union_empty]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
