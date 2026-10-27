module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenLocal
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenDFam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem maxOver_eq_inf_or {H M A : Subgroup G} (hAM : A ≤ M) (hAH : A ≤ H) (hHM : ¬ H ≤ M)
    (hcard : (maxOver H A).ncard = 1) :
    maxOver H A = {M ⊓ H} ∨ ∃ N, IsMaxSubgroupIn H N ∧ M ⊓ H < N ∧ ¬ N ≤ M := by
  obtain ⟨N, hN⟩ := Set.ncard_eq_one.1 hcard
  have hlt : M ⊓ H < H :=
    lt_of_le_of_ne inf_le_right fun heq => hHM (heq ▸ inf_le_left)
  obtain ⟨N', hN'max, hMN'⟩ := exists_isMaxSubgroupIn hlt
  have hN'mem : N' ∈ maxOver H A := ⟨hN'max, (le_inf hAM hAH).trans hMN'⟩
  rw [hN, Set.mem_singleton_iff] at hN'mem
  subst hN'mem
  by_cases hNeq : M ⊓ H = N'
  · left
    rw [hN, hNeq]
  · right
    refine ⟨N', hN'max, lt_of_le_of_ne hMN' hNeq, fun hNM => hNeq ?_⟩
    exact le_antisymm hMN' (le_inf hNM hN'max.le)

theorem fiveTen_final {H M T : Subgroup G} {Ω : Set (Subgroup G)} (hJ : kerMOf M H = ⊥)
    (h : FiveTenHyp H M T Ω)
    (hstar : ∀ X : Subgroup G, ⊥ < X → X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X →
      H ⊓ normalizer (X : Set G) ≤ M) :
    FiveTenConc H M Ω ∨ FiveTenDescent H M Ω := by
  obtain ⟨A, hA, hA1, hAM, D, S, hDH, hAS, hST, hSD, hDM, hcard⟩ := h.exists_dFam
  have hZW : E1.weakClosure S Ω ≤ E1.weakClosure T Ω := weakClosure_mono Ω hST
  have hZc : E1.weakClosure (E1.weakClosure S Ω) Ω = E1.weakClosure S Ω :=
    weakClosure_weakClosure S Ω
  have hZ1 : ⊥ < E1.weakClosure S Ω := by
    refine bot_lt_iff_ne_bot.2 fun hbot => hA1 ?_
    have hle : A ≤ E1.weakClosure S Ω := E1.le_weakClosure hA hAS
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  have hZM : H ⊓ normalizer (E1.weakClosure S Ω : Set G) ≤ M := hstar _ hZ1 hZW hZc
  by_cases hDlt : D < H
  · exact Or.inr (FiveTenDescent.of_restrict h.invColl hDlt hSD hZM hDM)
  · have hDeq : D = H := eq_of_le_of_not_lt hDH hDlt
    have hAH : A ≤ H := hAS.trans (hST.trans h.sylow.le)
    have hcard' : (maxOver H A).ncard = 1 := hDeq ▸ hcard
    rcases maxOver_eq_inf_or hAM hAH h.not_le hcard' with hmax | ⟨N, hN, hMN, hNM⟩
    · left
      refine ⟨A, hA, hAM, H, le_rfl, hAH, le_rfl, ?_, ?_⟩
      · rw [hJ]
        exact fun hAbot => hA1 (le_bot_iff.1 hAbot)
      · rw [hJ, sup_bot_eq]
        exact hmax
    · right
      have hTN : T ≤ N := (le_inf h.le_M h.sylow.le).trans hMN.le
      have hTN' : IsSylowIn 2 T N :=
        E1.isSylowIn_two_iff.2 (B6.isSylowTwoOf_mono (E1.isSylowIn_two_iff.1 h.sylow) hTN hN.1.le)
      exact FiveTenDescent.of_restrict h.invColl hN.1 hTN' h.normalizer_le hNM

theorem fiveTen_step {H M T : Subgroup G} {Ω : Set (Subgroup G)} (hJ : kerMOf M H = ⊥)
    (h : FiveTenHyp H M T Ω) : FiveTenConc H M Ω ∨ FiveTenDescent H M Ω := by
  rcases fiveTen_local hJ h with hd | hstar
  · exact Or.inr hd
  · exact fiveTen_final hJ h hstar

end CFSG.LocalAnalysis.WeakClosure81
