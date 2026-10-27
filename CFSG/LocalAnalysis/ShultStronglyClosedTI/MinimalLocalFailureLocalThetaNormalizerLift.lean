module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeComplementNormalizerLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
import CFSG.Foundations.MaxOrderThompsonImage
public import CFSG.Foundations.MaxOrderThompsonDefs

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore

universe u v

variable {G : Type u} {F : Type v} [Group G] [Finite G] [Group F]

theorem orderZJ_image_of_coprime_kernel {p : ℕ} (hp : p.Prime)
    (f : G →* F) (hkernel : Nat.Coprime p (Nat.card f.ker))
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    ((orderZJ Q).map Q.subtype).map f =
      (orderZJ (Q.map f)).map (Q.map f).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  exact CFSG.map_ambientOrderZJ_of_coprime_card_ker f hkernel hQ

theorem orderZJ_normal_complement_normalizer_lift {p : ℕ} (hp : p.Prime)
    (W : Subgroup G) [W.Normal] (hW : Nat.Coprime p (Nat.card W))
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (himage : (((orderZJ Q).map Q.subtype).map (QuotientGroup.mk' W)).Normal) :
    W ⊔ Subgroup.normalizer ((orderZJ Q).map Q.subtype : Set G) = ⊤ := by
  exact CFSG.RankThreeEvenClassification.Helpers.prime_complement_normal_image_normalizer_sup
    p hp W ((orderZJ Q).map Q.subtype) (hp.coprime_iff_not_dvd.mp hW)
    (hQ.to_le (Subgroup.map_subtype_le _)) himage

theorem orderZJ_normal_complement_normalizer_product {p : ℕ} (hp : p.Prime)
    (W : Subgroup G) [W.Normal] (hW : Nat.Coprime p (Nat.card W))
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (himage : (((orderZJ Q).map Q.subtype).map (QuotientGroup.mk' W)).Normal) :
    ∀ g : G, ∃ w ∈ W,
      ∃ n ∈ Subgroup.normalizer ((orderZJ Q).map Q.subtype : Set G), w * n = g := by
  intro g
  apply Subgroup.mem_sup_of_normal_left.mp
  rw [orderZJ_normal_complement_normalizer_lift hp W hW Q hQ himage]
  exact Subgroup.mem_top g

theorem odd_normal_supplement_involution_conjugate
    (W M : Subgroup G) [W.Normal] (hW : Odd (Nat.card W))
    (hsup : W ⊔ M = ⊤) {z : G} (hz : IsInvolution z) :
    ∃ w : G, w ∈ W ∧ rightConjugateElem z w ∈ M ∧
      IsInvolution (rightConjugateElem z w) := by
  let f := QuotientGroup.mk' W
  have hkernel : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hW
  have himage : f z ∈ M.map f := by
    obtain ⟨w, hw, n, hn, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp
      (show z ∈ W ⊔ M from hsup.symm ▸ Subgroup.mem_top z)
    refine Subgroup.mem_map.mpr ⟨n, hn, ?_⟩
    have hwone : f w = 1 := by
      apply MonoidHom.mem_ker.mp
      rwa [QuotientGroup.ker_mk']
    rw [← hprod, map_mul, hwone, one_mul]
  obtain ⟨s, hsM, hs, hfs⟩ := involution_lift_in_subgroup_of_odd_kernel
    f hkernel M (involution_image_of_odd_kernel f hkernel hz) himage
  obtain ⟨w, hw, hconj⟩ := involutions_kernel_conjugate f hkernel hz hs hfs.symm
  rw [QuotientGroup.ker_mk'] at hw
  exact ⟨w, hw, hconj.symm ▸ hsM, hconj.symm ▸ hs⟩

theorem orderZJ_odd_normal_complement_involution {p : ℕ} (hp : p.Prime)
    (W : Subgroup G) [W.Normal] (hW : Nat.Coprime p (Nat.card W))
    (hWodd : Odd (Nat.card W)) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (himage : (((orderZJ Q).map Q.subtype).map (QuotientGroup.mk' W)).Normal)
    {z : G} (hz : IsInvolution z) :
    ∃ w : G, w ∈ W ∧
      rightConjugateElem z w ∈ Subgroup.normalizer ((orderZJ Q).map Q.subtype : Set G) ∧
      IsInvolution (rightConjugateElem z w) :=
  odd_normal_supplement_involution_conjugate W _ hWodd
    (orderZJ_normal_complement_normalizer_lift hp W hW Q hQ himage) hz

end CFSG.ShultStronglyClosedTI.LocalTheta
