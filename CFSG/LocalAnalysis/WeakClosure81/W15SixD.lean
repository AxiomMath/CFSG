module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixB
public import CFSG.LocalAnalysis.WeakClosure81.FiveTen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem exists_pair156_le_S (h : Cex15 M V₀ V U S) :
    ∃ A X : Subgroup G, IsPair156 M V₀ (centralizer (U : Set G)) A X ∧ A ≤ S := by
  have hH := h.hyp
  have hSH : S ≤ centralizer (U : Set G) := h.S_le_centralizer
  have hinv := E3.isInvColl_gammaSet hH.elemAbelian₀ 0 (centralizer (U : Set G))
  have hweak : E1.weakClosure S (E3.gammaSet V₀ 0 (centralizer (U : Set G))) =
      E3.wClos V₀ 0 S := E3.weakClosure_gammaSet hSH
  have hyp : FiveTenHyp (centralizer (U : Set G)) M S
      (E3.gammaSet V₀ 0 (centralizer (U : Set G))) :=
    ⟨hinv, h.isSylowIn_centralizer, by
      rw [hweak]; exact inf_le_right.trans h.normalizer_wClos_zero_le, h.not_le⟩
  obtain ⟨A, hA, hAS, X, hXH, hAX, -, hnot, hmax⟩ :=
    FiveTenConc.exists_le_sylow hinv h.isSylowIn_centralizer h.S_le_M (fiveTenAt_all _ M S _ hyp)
  obtain ⟨-, g, hAg, hq⟩ := hA
  exact ⟨A, X, ⟨⟨g, (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup
    (hH.isPGroup.to_le hH.h6.le) g) hAg).1 hq⟩, hXH, hAX, hAS.trans h.S_le_M, hnot, hmax⟩, hAS⟩

end Cex15

structure IsMinPair156 (M V₀ H S A X : Subgroup G) : Prop where
  pair : IsPair156 M V₀ H A X
  A_le_S : A ≤ S
  minimal : ∀ A' X' : Subgroup G, IsPair156 M V₀ H A' X' → A' ≤ S → Nat.card X ≤ Nat.card X'

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem exists_isMinPair156 (h : Cex15 M V₀ V U S) :
    ∃ A X : Subgroup G, IsMinPair156 M V₀ (centralizer (U : Set G)) S A X := by
  classical
  let P : ℕ → Prop := fun n => ∃ A X : Subgroup G,
    IsPair156 M V₀ (centralizer (U : Set G)) A X ∧ A ≤ S ∧ Nat.card X = n
  have hP : ∃ n, P n := by
    obtain ⟨A, X, hAX, hAS⟩ := h.exists_pair156_le_S
    exact ⟨_, A, X, hAX, hAS, rfl⟩
  obtain ⟨A, X, hAX, hAS, hn⟩ := Nat.find_spec hP
  refine ⟨A, X, ⟨hAX, hAS, fun A' X' hA'X' hA'S => ?_⟩⟩
  rw [hn]
  exact Nat.find_min' hP ⟨A', X', hA'X', hA'S, rfl⟩

end Cex15

namespace IsMinPair156

variable {M V₀ H S A X : Subgroup G}

theorem toPairAt (h : IsMinPair156 M V₀ H S A X) : IsPairAt M X A :=
  h.pair.toPairAt

theorem unique_max (h : IsMinPair156 M V₀ H S A X) {N : Subgroup G} (hNX : N ≤ X) (hAN : A ≤ N)
    (hN : N ≠ X) : N ≤ M := by
  have hp := h.toPairAt
  by_cases hNK : N ⊔ kerMOf M X = X
  · exfalso
    obtain ⟨-, hpN⟩ := hp.restrict hNX hAN hNK
    have hpair : IsPair156 M V₀ H A N :=
      ⟨h.pair.conj, hNX.trans h.pair.le_H, hAN, h.pair.A_le_M, hpN.not_le_ker, hpN.maxOver_eq⟩
    exact hN (Subgroup.eq_of_le_of_card_ge hNX (h.minimal A N hpair h.A_le_S))
  · have hle : N ⊔ kerMOf M X ≤ X := sup_le hNX (kerMOf_le_group M X)
    exact le_sup_left.trans (hp.le_M_of_proper hle hNK (hAN.trans le_sup_left) le_sup_right)

theorem normal_inf_ker (h : IsMinPair156 M V₀ H S A X) {T : Subgroup G} (hT : IsSylowIn 2 T X)
    (hAT : A ≤ T) : ((T ⊓ kerMOf M X).subgroupOf X).Normal := by
  have hp := h.toPairAt
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hKn : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hT₀K : IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X) := hT.inf_normal hKX hKn
  have hfr := frattini_isSylowIn hKX hKn hT₀K
  have hTN : T ≤ normalizer ((T ⊓ kerMOf M X : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxK⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), conj_mem_kerMOf (hT.le ht) hxK⟩
    · rintro ⟨hxT, hxK⟩
      refine ⟨?_, ?_⟩
      · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · have := conj_mem_kerMOf (hT.le (T.inv_mem ht)) hxK
        simpa [mul_assoc] using this
  set X₁ : Subgroup G := X ⊓ normalizer ((T ⊓ kerMOf M X : Subgroup G) : Set G) with hX₁
  have hX₁X : X₁ ≤ X := inf_le_left
  have hAX₁ : A ≤ X₁ := le_inf h.pair.A_le (hAT.trans hTN)
  have hsup : X₁ ⊔ kerMOf M X = X := by
    refine le_antisymm (sup_le hX₁X hKX) fun x hx => ?_
    obtain ⟨y, hy, n, hnX, hnN, hyn⟩ := hfr x hx
    rw [← hyn]
    exact (X₁ ⊔ kerMOf M X).mul_mem (Subgroup.mem_sup_right hy)
      (Subgroup.mem_sup_left ⟨hnX, hnN⟩)
  obtain ⟨-, hp₁⟩ := hp.restrict hX₁X hAX₁ hsup
  have hpair : IsPair156 M V₀ H A X₁ :=
    ⟨h.pair.conj, hX₁X.trans h.pair.le_H, hAX₁, h.pair.A_le_M, hp₁.not_le_ker, hp₁.maxOver_eq⟩
  have hX₁eq : X₁ = X :=
    Subgroup.eq_of_le_of_card_ge hX₁X (h.minimal A X₁ hpair h.A_le_S)
  have hXN : X ≤ normalizer ((T ⊓ kerMOf M X : Subgroup G) : Set G) := fun x hx => by
    have : x ∈ X₁ := by rw [hX₁eq]; exact hx
    exact this.2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hT.le)).2 hXN

theorem odd_relIndex_inf_ker (h : IsMinPair156 M V₀ H S A X) {T : Subgroup G}
    (hT : IsSylowIn 2 T X) : Odd ((T ⊓ kerMOf M X).relIndex (kerMOf M X)) := by
  have hK : IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X) :=
    hT.inf_normal (kerMOf_le_group M X) (normal_subgroupOf_kerMOf M X)
  have := hK.not_dvd_relIndex
  exact Nat.odd_iff.2 (by omega)

end IsMinPair156

end CFSG.LocalAnalysis.WeakClosure81
