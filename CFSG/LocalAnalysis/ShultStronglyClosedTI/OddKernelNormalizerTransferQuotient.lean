module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.LocalAnalysis.ComponentClassification.TwoRankTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalPrimeSupplement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.RankThreeEvenClassification.Helpers

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem coprime_kernel_full_normalizer_image
    {F : Type v} [Group F] (f : G →* F) (hf : Function.Surjective f)
    (p : ℕ) (hp : p.Prime) (hkernel : Nat.Coprime p (Nat.card f.ker))
    (A : Subgroup G) (hA : IsPGroup p A) :
    (Subgroup.normalizer (A : Set G)).map f =
      Subgroup.normalizer (A.map f : Set F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p A) := ⟨hA⟩
  let q := QuotientGroup.mk' f.ker
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : e.toMonoidHom.comp q = f := by
    ext x
    rfl
  have hnative : Subgroup.normalizer (A.map q : Set (G ⧸ f.ker)) =
      (Subgroup.normalizer (A : Set G)).map q :=
    CFSG.normalizer_map_quotient_eq_map_normalizer p A f.ker inferInstance hkernel
  calc
    (Subgroup.normalizer (A : Set G)).map f =
        ((Subgroup.normalizer (A : Set G)).map q).map e.toMonoidHom := by
      rw [Subgroup.map_map, he]
    _ = (Subgroup.normalizer (A.map q : Set (G ⧸ f.ker))).map e.toMonoidHom := by
      rw [hnative]
    _ = Subgroup.normalizer ((A.map q).map e.toMonoidHom : Set F) :=
      Subgroup.map_equiv_normalizer_eq _ e
    _ = Subgroup.normalizer (A.map f : Set F) := by
      rw [Subgroup.map_map, he]

omit [Finite G] in
theorem quotient_restriction_of_normal_supplement
    (W M : Subgroup G) [W.Normal] (hsup : W ⊔ M = ⊤) :
    Function.Surjective ((QuotientGroup.mk' W).comp M.subtype) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W y
  obtain ⟨w, hw, m, hm, heq⟩ := Subgroup.mem_sup_of_normal_left.mp
    (show g ∈ W ⊔ M from hsup.symm ▸ Subgroup.mem_top g)
  refine ⟨⟨m, hm⟩, ?_⟩
  have hwq : QuotientGroup.mk' W w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
  change QuotientGroup.mk' W m = QuotientGroup.mk' W g
  rw [← heq, map_mul, hwq, one_mul]

theorem odd_normal_supplement_full_two_sylow
    (W M : Subgroup G) [W.Normal] (hWodd : Odd (Nat.card W))
    (hsup : W ⊔ M = ⊤) (P : Sylow 2 M) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := (P : Subgroup M).map M.subtype
  have hModd : Odd M.index := hWodd.of_dvd_nat
    (index_dvd_normal_supplement_card W M hsup)
  have hPodd : Odd (P : Subgroup M).index := Nat.not_even_iff_odd.mp
    (fun hEven => P.not_dvd_index hEven.two_dvd)
  have hAodd : Odd A.index := by
    rw [Subgroup.index_map_subtype]
    exact hPodd.mul hModd
  exact ⟨(P.isPGroup'.map M.subtype).toSylow hAodd.not_two_dvd_nat, rfl⟩

theorem odd_normal_supplement_two_rank
    (W M : Subgroup G) [W.Normal] (hWodd : Odd (Nat.card W))
    (hsup : W ⊔ M = ⊤) : twoRank G = twoRank M := by
  let P : Sylow 2 M := Classical.choice inferInstance
  obtain ⟨Q, hQ⟩ := odd_normal_supplement_full_two_sylow W M hWodd hsup P
  have hmaprank : CFSG.Open.pRank 2 ((P : Subgroup M).map M.subtype) =
      CFSG.Open.pRank 2 (P : Subgroup M) :=
    (pRank_eq_of_subgroup_equiv 2 Nat.prime_two (P : Subgroup M)
      ((P : Subgroup M).map M.subtype)
      ((P : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective)).symm
  change CFSG.Open.pRank 2 (⊤ : Subgroup G) = CFSG.Open.pRank 2 (⊤ : Subgroup M)
  rw [← pRank_eq_sylow 2 Nat.prime_two Q, hQ, hmaprank,
    pRank_eq_sylow 2 Nat.prime_two P]

omit [Finite G] in
theorem odd_normal_supplement_single_involution_class
    (W M : Subgroup G) [W.Normal] (hWodd : Odd (Nat.card W))
    (hsup : W ⊔ M = ⊤) (z : G)
    (hclass : ∀ x : G, IsInvolution x → x ∈ involutionPointClass z) :
    ∀ s t : M, IsInvolution s → IsInvolution t →
      ∃ n : M, rightConjugateElem s n = t := by
  let q := QuotientGroup.mk' W
  let f := q.comp M.subtype
  have hkernel : Odd (Nat.card f.ker) := odd_kernel_subgroup_restriction q
    (by rw [QuotientGroup.ker_mk']; exact hWodd) M
  have hf : Function.Surjective f := quotient_restriction_of_normal_supplement W M hsup
  intro s t hs ht
  have hsG : IsInvolution (s : G) :=
    ⟨fun heq => hs.1 (Subtype.ext heq), congrArg Subtype.val hs.2⟩
  have htG : IsInvolution (t : G) :=
    ⟨fun heq => ht.1 (Subtype.ext heq), congrArg Subtype.val ht.2⟩
  obtain ⟨a, ha⟩ := hclass s hsG
  obtain ⟨b, hb⟩ := hclass t htG
  let g := a⁻¹ * b
  have hg : rightConjugateElem (s : G) g = (t : G) := by
    rw [← ha, ← hb]
    dsimp only [g, rightConjugateElem]
    group
  obtain ⟨n, hn⟩ := hf (q g)
  have himage : f (rightConjugateElem s n) = f t := by
    change q ((n : G)⁻¹ * (s : G) * n) = q (t : G)
    rw [map_mul, map_mul, map_inv]
    change q (n : G) = q g at hn
    rw [hn]
    simpa only [rightConjugateElem, map_mul, map_inv] using congrArg q hg
  obtain ⟨k, _hk, hk⟩ := involutions_kernel_conjugate f hkernel
    (isInvolution_rightConjugateElem hs) ht himage
  exact ⟨n * k, (rightConjugateElem_comp s n k).symm.trans hk⟩

theorem single_involution_class_hull_two_rank
    (s : G) (hclass : ∀ x : G, IsInvolution x → x ∈ involutionPointClass s) :
    twoRank (involutionPointHull s) = twoRank G := by
  obtain ⟨A, _hAtop, hA, hcard⟩ := pRank_attained 2 Nat.prime_two (⊤ : Subgroup G)
  have hAle : A ≤ involutionPointHull s := by
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1.symm ▸ (involutionPointHull s).one_mem
    · exact Subgroup.subset_closure (hclass x ⟨hx1, hA.2 x hx⟩)
  rw [CFSG.ComponentClassification.TwoRankTransport.subgroup]
  change CFSG.Open.pRank 2 (involutionPointHull s) = CFSG.Open.pRank 2 (⊤ : Subgroup G)
  apply le_antisymm (pRank_mono 2 Nat.prime_two le_top)
  exact le_csSup (pRank_bddAbove 2 Nat.prime_two (involutionPointHull s))
    ⟨A, hAle, hA, hcard⟩

end CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer
