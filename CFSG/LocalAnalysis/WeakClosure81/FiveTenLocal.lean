module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenMaxU
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenPGrp
public import CFSG.LocalAnalysis.WeakClosure81.FiveKer
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenRestrict

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_normalizer_le {K M Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsSylowIn 2 Q (M ⊓ K)) (hN : K ⊓ normalizer (Q : Set G) ≤ M) : IsSylowIn 2 Q K := by
  obtain ⟨P, hP, hQP⟩ := exists_isSylowIn_ge 2 hQK hQ.isPGroup
  by_cases hPQ : Q = P
  · rw [hPQ]
    exact hP
  · exfalso
    have hlt : Q < P ⊓ normalizer (Q : Set G) :=
      lt_inf_normalizer_of_isPGroup hP.isPGroup hQP hPQ
    have hRK : P ⊓ normalizer (Q : Set G) ≤ M ⊓ K :=
      le_inf ((inf_le_inf_right _ hP.le).trans hN) (inf_le_left.trans hP.le)
    have hR : IsSylowIn 2 (P ⊓ normalizer (Q : Set G)) (M ⊓ K) :=
      isSylowIn_of_le_of_isPGroup hQ hlt.le hRK (hP.isPGroup.to_le inf_le_left)
    have h1 : Nat.card Q = Nat.card (P ⊓ normalizer (Q : Set G) : Subgroup G) := by
      rw [hQ.card_eq, hR.card_eq]
    exact absurd h1 (Subgroup.card_lt_of_lt hlt).ne

theorem lt_weakClosure_inf_normalizer {H T U : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hUW : U < E1.weakClosure T Ω) (hU : E1.weakClosure U Ω = U) :
    U < E1.weakClosure (T ⊓ normalizer (U : Set G)) Ω := by
  have hWT : E1.weakClosure T Ω ≤ T := E1.weakClosure_le
  obtain ⟨B, hB, hBW, hBN, hBU⟩ := exists_mem_le_normalizer_of_lt hΩ (hWT.trans hTH)
    (hT.to_le hWT) (weakClosure_weakClosure T Ω) hUW hU
  have hUT : U ≤ T := hUW.le.trans hWT
  have hUQ : U ≤ E1.weakClosure (T ⊓ normalizer (U : Set G)) Ω := by
    calc U = E1.weakClosure U Ω := hU.symm
      _ ≤ _ := weakClosure_mono Ω (le_inf hUT Subgroup.le_normalizer)
  refine lt_of_le_of_ne hUQ fun heq => hBU ?_
  rw [heq]
  exact E1.le_weakClosure hB (le_inf (hBW.trans hWT) hBN)

theorem inf_normalizer_weakClosure_le {H M T U Q : Subgroup G} {Ω : Set (Subgroup G)}
    (hQT : Q ≤ T) (hUQ : U < E1.weakClosure Q Ω)
    (hmax : ∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X → U < X →
      H ⊓ normalizer (X : Set G) ≤ M) :
    H ⊓ normalizer (E1.weakClosure Q Ω : Set G) ≤ M :=
  hmax _ (weakClosure_mono Ω hQT) (weakClosure_weakClosure Q Ω) hUQ

theorem inf_normalizer_le_of_weakClosure {H M Q : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (h : H ⊓ normalizer (E1.weakClosure Q Ω : Set G) ≤ M) :
    H ⊓ normalizer (Q : Set G) ≤ M := by
  intro x hx
  apply h
  refine ⟨hx.1, ?_⟩
  have h1 : A1b.conjSub x Q = Q := B6.conjSub_eq_self hx.2
  have h2 := conjSub_weakClosure hΩ hx.1 Q
  rw [h1] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem eq_bot_of_le_normalizer {H M U : Subgroup G} (hUH : U ≤ H) (hUM : U ≤ M)
    (hHU : H ≤ normalizer (U : Set G)) (hJ : kerMOf M H = ⊥) : U = ⊥ := by
  have hN : (U.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUH]
    intro u h hu hh
    exact (Subgroup.mem_normalizer_iff.1 (hHU hh) u).1 hu
  have hle := le_kerMOf_of_normal hUH hN hUM
  rw [hJ] at hle
  exact le_bot_iff.1 hle

theorem fiveTenDescent_of_good_U {H M T U : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) (hUW : U < E1.weakClosure T Ω) (hU : E1.weakClosure U Ω = U)
    (hn : ¬ H ⊓ normalizer (U : Set G) ≤ M)
    (hmax : ∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X → U < X →
      H ⊓ normalizer (X : Set G) ≤ M)
    (hsyl : IsSylowIn 2 (T ⊓ normalizer (U : Set G)) (M ⊓ (H ⊓ normalizer (U : Set G))))
    (hlt : H ⊓ normalizer (U : Set G) < H) : FiveTenDescent H M Ω := by
  have hUV : U < E1.weakClosure (T ⊓ normalizer (U : Set G)) Ω :=
    lt_weakClosure_inf_normalizer h.invColl h.sylow.le h.sylow.isPGroup hUW hU
  have hV : H ⊓ normalizer (E1.weakClosure (T ⊓ normalizer (U : Set G)) Ω : Set G) ≤ M :=
    inf_normalizer_weakClosure_le inf_le_left hUV hmax
  have hQ : H ⊓ normalizer ((T ⊓ normalizer (U : Set G) : Subgroup G) : Set G) ≤ M :=
    inf_normalizer_le_of_weakClosure h.invColl hV
  have hS : IsSylowIn 2 (T ⊓ normalizer (U : Set G)) (H ⊓ normalizer (U : Set G)) :=
    isSylowIn_of_normalizer_le (le_inf (inf_le_left.trans h.sylow.le) inf_le_right) hsyl
      ((inf_le_inf_right _ inf_le_left).trans hQ)
  exact FiveTenDescent.of_restrict h.invColl hlt hS hV hn

theorem fiveTen_local {H M T : Subgroup G} {Ω : Set (Subgroup G)} (hJ : kerMOf M H = ⊥)
    (h : FiveTenHyp H M T Ω) :
    FiveTenDescent H M Ω ∨
      ∀ X : Subgroup G, ⊥ < X → X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X →
        H ⊓ normalizer (X : Set G) ≤ M := by
  obtain ⟨U, hUW, hU, hn, hmax, hsyl⟩ := exists_good_U h
  have hUW' : U < E1.weakClosure T Ω := by
    refine lt_of_le_of_ne hUW fun heq => hn ?_
    rw [heq]
    exact h.normalizer_le
  by_cases hlt : H ⊓ normalizer (U : Set G) < H
  · exact Or.inl (fiveTenDescent_of_good_U h hUW' hU hn hmax hsyl hlt)
  · right
    have hKH : H ⊓ normalizer (U : Set G) = H := eq_of_le_of_not_lt inf_le_left hlt
    have hHU : H ≤ normalizer (U : Set G) := fun x hx => by
      have hx' : x ∈ H ⊓ normalizer (U : Set G) := by
        rw [hKH]
        exact hx
      exact hx'.2
    have hUT : U ≤ T := hUW.trans E1.weakClosure_le
    have hUbot : U = ⊥ :=
      eq_bot_of_le_normalizer (hUT.trans h.sylow.le) (hUT.trans h.le_M) hHU hJ
    intro X hX hXW hXc
    refine hmax X hXW hXc ?_
    rw [hUbot]
    exact hX

end CFSG.LocalAnalysis.WeakClosure81
