module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransferQuotient
public import CFSG.Assembly.OrderReductions.ThompsonQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer

open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem coprime_kernel_same_image_noncentral_action
    {F : Type v} [Group F] (f : G →* F) (p : ℕ) (hp : p.Prime)
    (hkernel : Nat.Coprime p (Nat.card f.ker))
    (A : Subgroup G) (hA : IsPGroup p A) (z s : G)
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) (hfs : f s = f z)
    (hnoncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G)) :
    ¬ A ≤ Subgroup.centralizer ({s} : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  have hinjective :=
    CFSG.OrderReductions.ThompsonQuotient.prime_subgroup_injective_of_coprime_kernel
      p f (hp.coprime_iff_not_dvd.mp hkernel) A hA
  intro hcentral
  apply hnoncentral
  intro a ha
  have hsa : a * s = s * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcentral ha)
  have hconjA : rightConjugateElem a z ∈ A :=
    (Subgroup.mem_normalizer_iff''.mp hzA a).mp ha
  have himage : f (rightConjugateElem a z) = f a := by
    simp only [rightConjugateElem, map_mul, map_inv]
    rw [← hfs, mul_assoc, ← map_mul, hsa, map_mul, inv_mul_cancel_left]
  have hfixed : rightConjugateElem a z = a :=
    congrArg Subtype.val (hinjective
      (show f.subgroupMap A ⟨rightConjugateElem a z, hconjA⟩ =
        f.subgroupMap A ⟨a, ha⟩ from Subtype.ext himage))
  have hcomm := congrArg (fun x : G => z * x) hfixed
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  simpa only [rightConjugateElem, ← mul_assoc, mul_inv_cancel, one_mul] using hcomm

theorem involution_lift_normalizing_prime_subgroup
    {F : Type v} [Group F] (f : G →* F) (hf : Function.Surjective f)
    (p : ℕ) (hp : p.Prime) (hodd : Odd (Nat.card f.ker))
    (hkernel : Nat.Coprime p (Nat.card f.ker))
    (A : Subgroup G) (hA : IsPGroup p A)
    {y : F} (hy : IsInvolution y)
    (hynorm : y ∈ Subgroup.normalizer (A.map f : Set F)) :
    ∃ s : G, s ∈ Subgroup.normalizer (A : Set G) ∧
      IsInvolution s ∧ f s = y := by
  have himage : y ∈ (Subgroup.normalizer (A : Set G)).map f := by
    rw [coprime_kernel_full_normalizer_image f hf p hp hkernel A hA]
    exact hynorm
  exact involution_lift_in_subgroup_of_odd_kernel f hodd
    (Subgroup.normalizer (A : Set G)) hy himage

theorem odd_prime_normal_supplement_simultaneous_normalizer_lift
    (p : ℕ) (hp : p.Prime) (W M : Subgroup G) [W.Normal]
    (hWodd : Odd (Nat.card W)) (hWcop : Nat.Coprime p (Nat.card W))
    (hsup : W ⊔ M = ⊤) (A : Subgroup G) (hAM : A ≤ M)
    (hA : IsPGroup p A) (z : G) (hz : IsInvolution z)
    (hzA : z ∈ Subgroup.normalizer (A : Set G))
    (hnoncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ w : G, w ∈ W ∧ rightConjugateElem z w ∈ M ∧
      rightConjugateElem z w ∈ Subgroup.normalizer (A : Set G) ∧
      ¬ A ≤ Subgroup.centralizer ({rightConjugateElem z w} : Set G) ∧
      IsInvolution (rightConjugateElem z w) := by
  let q := QuotientGroup.mk' W
  let f := q.comp M.subtype
  let AM := A.subgroupOf M
  have hqodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hWodd
  have hqcop : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hWcop
  have hf : Function.Surjective f := quotient_restriction_of_normal_supplement W M hsup
  have hfodd : Odd (Nat.card f.ker) := odd_kernel_subgroup_restriction q hqodd M
  have hker : f.ker = W.comap M.subtype := by
    ext x
    change q (x : G) = 1 ↔ (x : G) ∈ W
    exact QuotientGroup.eq_one_iff _
  have hfcop : Nat.Coprime p (Nat.card f.ker) := by
    rw [hker]
    exact hWcop.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective W M.subtype M.subtype_injective)
  have hAMp : IsPGroup p AM := hA.comap_of_injective M.subtype M.subtype_injective
  have hAMimage : AM.map f = A.map q := by
    change (A.subgroupOf M).map (q.comp M.subtype) = A.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAM]
  have hynorm : q z ∈ Subgroup.normalizer (AM.map f : Set (G ⧸ W)) := by
    rw [hAMimage]
    exact (Subgroup.le_normalizer_map (H := A) q) (Subgroup.mem_map_of_mem q hzA)
  obtain ⟨s, hsAM, hs, hfs⟩ := involution_lift_normalizing_prime_subgroup
    f hf p hp hfodd hfcop AM hAMp (involution_image_of_odd_kernel q hqodd hz) hynorm
  have hsG : IsInvolution (s : G) :=
    ⟨fun heq => hs.1 (Subtype.ext heq), congrArg Subtype.val hs.2⟩
  have hsAnorm : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
    have hm := (Subgroup.le_normalizer_map (H := AM) M.subtype)
      (Subgroup.mem_map_of_mem M.subtype hsAM)
    change (s : G) ∈ Subgroup.normalizer ((A.subgroupOf M).map M.subtype : Set G) at hm
    rwa [Subgroup.map_subgroupOf_eq_of_le hAM] at hm
  change q (s : G) = q z at hfs
  have hsnoncentral := coprime_kernel_same_image_noncentral_action q p hp hqcop
    A hA z (s : G) hzA hfs hnoncentral
  obtain ⟨w, hw, hconj⟩ := involutions_kernel_conjugate q hqodd hz hsG hfs.symm
  rw [QuotientGroup.ker_mk'] at hw
  refine ⟨w, hw, ?_, ?_, ?_, ?_⟩
  · rw [hconj]
    exact s.property
  · rw [hconj]
    exact hsAnorm
  · rw [hconj]
    exact hsnoncentral
  · rw [hconj]
    exact hsG

end CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer
