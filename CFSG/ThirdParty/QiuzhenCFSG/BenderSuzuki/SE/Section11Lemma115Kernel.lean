module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma112
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientCore

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: identification of the normalizer-action kernel

This module proves the source assertion `N₀* = P`.  The point-stabilizer
core is first viewed in the ambient group, put inside `V` using the checked
Lemma 10.1 normalizer equality, and then identified by Lemma 11.2.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The ambient image of the kernel of the `N_X(P)`-action on `Omega_P` is
exactly the distinguished subgroup `P`. -/
public theorem lemma115_actionKernel_image_eq_P
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    (lemma103NZeroStar M d.choice.P).map
      (lemma103NStar d.choice.P).subtype = d.choice.P := by
  let P : Subgroup X := d.choice.P
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let K : Subgroup X := core.map Nstar.subtype
  have hPcore : P ≤ K := by
    intro x hx
    simpa [K, core, Nstar, P] using
      lemma105_P_le_actionKernel (M := M) hx
  have hKD : K ≤ D := by
    simpa [K, core, Nstar, P, D] using
      lemma103_pointStabilizerCore_le_pairStabilizer ht
        (d.choice.P_le_V.trans inf_le_left)
  have hKV : K ≤ V := by
    have hDodd : Odd (Nat.card D) := by
      simpa [D] using hM.inf_rightConjugate_card_odd htM
    have hDinv : rightConjugate D t = D := by
      simpa [D] using inf_rightConjugate_invariant_of_isInvolution M ht
    have hPne : P ≠ ⊥ := by
      intro hPbot
      exact d.choice.initial.card_P_prime.ne_one (by simp [P, hPbot])
    have hPfixed : PeterfalviCentralizersTrivial D t P := by
      simpa [D, P] using d.choice.P_fixedPointFree
    have hnormeq : normalizerIn D P = normalizerIn V P :=
      lemma101_normalizer_eq_of_fixedPointFree ht hDodd hDinv
        (by simpa [V] using d.choice.P_le_V) hPne hPfixed
    intro x hx
    have hxNstar : x ∈ Nstar := by
      rcases hx with ⟨n, hn, rfl⟩
      exact n.property
    have hxN : x ∈ normalizerIn D P := by
      change x ∈ Subgroup.normalizer (P : Set X) at hxNstar
      exact ⟨hKD hx, hxNstar⟩
    have hxNV : x ∈ normalizerIn V P := by
      rw [← hnormeq]
      exact hxN
    exact hxNV.1
  have hKnorm : normalizerIn M P ≤ Subgroup.normalizer (K : Set X) := by
    letI : core.Normal := by
      dsimp [core, Nstar]
      infer_instance
    have hNstarNorm : Nstar ≤ Subgroup.normalizer (K : Set X) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rcases hx with ⟨z, hz, rfl⟩
        exact Subgroup.mem_map_of_mem Nstar.subtype
          (Subgroup.Normal.conj_mem inferInstance z hz ⟨k, hk⟩)
      · intro hx
        rcases hx with ⟨z, hz, hzx⟩
        refine ⟨(⟨k, hk⟩ : Nstar)⁻¹ * z * ⟨k, hk⟩, ?_, ?_⟩
        · simpa using Subgroup.Normal.conj_mem inferInstance z hz
            ((⟨k, hk⟩ : Nstar)⁻¹)
        · calc
            (((⟨k, hk⟩ : Nstar)⁻¹ * z * ⟨k, hk⟩ : Nstar) : X) =
                k⁻¹ * ((z : Nstar) : X) * k := by rfl
            _ = k⁻¹ * (k * x * k⁻¹) * k := by
              change k⁻¹ * Nstar.subtype z * k = _
              rw [hzx]
            _ = x := by simp [mul_assoc]
    intro x hx
    apply hNstarNorm
    change x ∈ Subgroup.normalizer (P : Set X)
    exact hx.2
  have hKeq : K = P :=
    lemma_11_2 hM ht htM d83 h84 d K hPcore hKV hKnorm
  simpa [K, core, Nstar, P] using hKeq

end CFSG.BenderSuzuki
