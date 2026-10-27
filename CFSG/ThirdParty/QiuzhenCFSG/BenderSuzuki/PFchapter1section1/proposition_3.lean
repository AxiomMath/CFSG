module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_d

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 3
-/

private theorem rightConjugate_rightConjugate_for_prop3
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    rightConjugate (rightConjugate H a) b = rightConjugate H (a * b) := by
  simp [rightConjugate, Subgroup.conjBy_conjBy, mul_inv_rev]

private theorem rightConjugate_eq_self_of_mem_for_prop3
    {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H) :
    rightConjugate H g = H := by
  rw [rightConjugate, Subgroup.conjBy]
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hginv_inv : g⁻¹⁻¹ ∈ H := by
      simpa using hg
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hy) hginv_inv
  · intro hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    · simp [mul_assoc]

private theorem rightConjugateElem_mem_rightConjugate_for_prop3
    {G : Type*} [Group G] {H : Subgroup G} {x g : G}
    (hx : x ∈ H) :
    rightConjugateElem x g ∈ rightConjugate H g := by
  rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
  exact ⟨x, hx, by simp⟩

private theorem mem_normalizer_of_conjBy_eq_for_prop3
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ H.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp⟩
    simpa [h] using hxconj
  · intro hx
    have h_inv : H.conjBy g⁻¹ = H := by
      simpa [h] using (Subgroup.conjBy_inv H g)
    have hxpre : x ∈ H.conjBy g⁻¹ := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      simp [mul_assoc]
    simpa [h_inv] using hxpre

private theorem mem_normalizer_of_rightConjugate_eq_self_for_prop3
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : rightConjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  apply mem_normalizer_of_conjBy_eq_for_prop3
  have h' : H.conjBy g⁻¹ = H := by
    simpa [rightConjugate] using h
  simpa [h'] using (Subgroup.conjBy_inv' H g)

private theorem isInvolution_mul_t_of_mem_peterfalviKSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {k : G}
    (hk : k ∈ peterfalviKSet D t) :
    IsInvolution (k * t) := by
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have htk : t * k * t = k⁻¹ := by
    simpa [peterfalviKSet, rightConjugateElem, htinv, mul_assoc] using hk.2
  constructor
  · intro hkt
    have hkH : k ∈ H := hA1.D_le_H hk.1
    have hk_eq_tinv : k = t⁻¹ := by
      calc
        k = k * 1 := by simp
        _ = k * (t * t⁻¹) := by simp
        _ = (k * t) * t⁻¹ := by rw [mul_assoc]
        _ = t⁻¹ := by rw [hkt]; simp
    have hk_eq_t : k = t := by
      simpa [htinv] using hk_eq_tinv
    exact hA1.t_not_mem_H (hk_eq_t ▸ hkH)
  · calc
      (k * t) ^ 2 = k * (t * k * t) := by simp [pow_two, mul_assoc]
      _ = k * k⁻¹ := by rw [htk]
      _ = 1 := by simp

private theorem mul_t_not_mem_H_of_mem_peterfalviKSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {k : G}
    (hk : k ∈ peterfalviKSet D t) :
    k * t ∉ H := by
  intro hktH
  have hkH : k ∈ H := hA1.D_le_H hk.1
  have htH : t ∈ H := by
    have hmem : k⁻¹ * (k * t) ∈ H :=
      H.mul_mem (H.inv_mem hkH) hktH
    simpa [mul_assoc] using hmem
  exact hA1.t_not_mem_H htH

private theorem rightConjugate_mul_t_eq_t_of_mem_peterfalviKSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {k : G}
    (hk : k ∈ peterfalviKSet D t) :
    rightConjugate H (k * t) = rightConjugate H t := by
  have hkH : k ∈ H := hA1.D_le_H hk.1
  calc
    rightConjugate H (k * t) =
        rightConjugate (rightConjugate H k) t :=
      (rightConjugate_rightConjugate_for_prop3 H k t).symm
    _ = rightConjugate H t := by
      rw [rightConjugate_eq_self_of_mem_for_prop3 hkH]

private theorem rightConjugateElem_mul_t_eq_inv_of_involutions
    {G : Type*} [Group G] {u t : G}
    (hu : IsInvolution u) (ht : IsInvolution t) :
    rightConjugateElem (u * t) t = (u * t)⁻¹ := by
  have huinv : u⁻¹ = u := hu.inv_eq_self
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  simp [rightConjugateElem, huinv, htinv, htt, mul_assoc]

private theorem mul_t_mem_H_of_target_for_prop3
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {u : G}
    (hueq : rightConjugate H u = rightConjugate H t) :
    u * t ∈ H := by
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hHt_t : rightConjugate (rightConjugate H t) t = H := by
    calc
      rightConjugate (rightConjugate H t) t = rightConjugate H (t * t) :=
        rightConjugate_rightConjugate_for_prop3 H t t
      _ = H := by
        rw [htt]
        exact rightConjugate_eq_self_of_mem_for_prop3 H.one_mem
  have hHut : rightConjugate H (u * t) = H := by
    calc
      rightConjugate H (u * t) =
          rightConjugate (rightConjugate H u) t :=
        (rightConjugate_rightConjugate_for_prop3 H u t).symm
      _ = rightConjugate (rightConjugate H t) t := by rw [hueq]
      _ = H := hHt_t
  have hnorm : u * t ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_of_rightConjugate_eq_self_for_prop3 hHut
  have hnormH := (proposition_1_d H D Q t hA1).2
  simpa [hnormH] using hnorm

private theorem mul_t_mem_peterfalviKSet_of_target_for_prop3
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {u : G}
    (hu : IsInvolution u)
    (hueq : rightConjugate H u = rightConjugate H t) :
    u * t ∈ peterfalviKSet D t := by
  have hutH : u * t ∈ H :=
    mul_t_mem_H_of_target_for_prop3 H D Q t hA1 hueq
  have hconj_inv :
      rightConjugateElem (u * t) t = (u * t)⁻¹ :=
    rightConjugateElem_mul_t_eq_inv_of_involutions hu hA1.involution_t
  have hut_t_H : rightConjugateElem (u * t) t ∈ H := by
    simpa [hconj_inv] using H.inv_mem hutH
  have hutHt : u * t ∈ rightConjugate H t := by
    have hmem :=
      rightConjugateElem_mem_rightConjugate_for_prop3
        (H := H) (g := t) hut_t_H
    have hinv := rightConjugateElem_involutive_of_isInvolution
      hA1.involution_t
    simpa [hinv (u * t)] using hmem
  have hutD : u * t ∈ D := by
    rw [hA1.D_eq]
    exact ⟨hutH, hutHt⟩
  exact ⟨hutD, hconj_inv⟩

public theorem proposition_3
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card {x : G // x ∈ peterfalviKSet D t} =
        Nat.card {x : G // x ∈ H ∧ IsInvolution x} ∧
      ∀ s : G, s ∈ H → IsInvolution s →
        ∀ y : G, y ∈ H ∧ IsInvolution y ↔
          ∃ k : G, k ∈ peterfalviKSet D t ∧ rightConjugateElem s k = y := by
  classical
  let KType : Type _ := {x : G // x ∈ peterfalviKSet D t}
  let Target : Type _ :=
    {u : G // IsInvolution u ∧ rightConjugate H u = rightConjugate H t}
  let HInv : Type _ := {x : G // x ∈ H ∧ IsInvolution x}
  have hKTarget : Nat.card KType = Nat.card Target := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun k =>
          ⟨k.1 * t,
            isInvolution_mul_t_of_mem_peterfalviKSet H D Q t hA1 k.2,
            rightConjugate_mul_t_eq_t_of_mem_peterfalviKSet H D Q t hA1 k.2⟩
        invFun := fun u =>
          ⟨u.1 * t,
            mul_t_mem_peterfalviKSet_of_target_for_prop3 H D Q t hA1 u.2.1 u.2.2⟩
        left_inv := by
          intro k
          apply Subtype.ext
          have htt : t * t = 1 := by
            simpa [pow_two] using hA1.involution_t.sq_eq_one
          simp [mul_assoc, htt]
        right_inv := by
          intro u
          apply Subtype.ext
          have htt : t * t = 1 := by
            simpa [pow_two] using hA1.involution_t.sq_eq_one
          simp [mul_assoc, htt] }
  have hTargetH : Nat.card Target = Nat.card HInv := by
    simpa [Target, HInv] using proposition_2_d H D Q t hA1
  have hK_card : Nat.card KType = Nat.card HInv :=
    hKTarget.trans hTargetH
  refine ⟨by simpa [KType, HInv] using hK_card, ?_⟩
  intro s hsH hsI y
  let phi : KType → HInv := fun k =>
    ⟨rightConjugateElem s (k : G),
      ⟨by
        exact
          H.mul_mem
            (H.mul_mem (H.inv_mem (hA1.D_le_H k.property.1)) hsH)
            (hA1.D_le_H k.property.1),
        isInvolution_rightConjugateElem hsI⟩⟩
  have hsQ : s ∈ Q :=
    involution_mem_Q_of_mem_H H D Q t hA1 s hsH hsI
  obtain ⟨_hforward, hsurjOutside⟩ := proposition_2_c H D Q t hA1 s hsQ hsI
  let Out : Type _ := {u : G // IsInvolution u ∧ u ∉ H}
  let fOut : Out → Out := fun u =>
    ⟨rightConjugateElem s (u : G),
      ⟨(proposition_2_c H D Q t hA1 s hsQ hsI).1
          (u : G) u.property.1 u.property.2 |>.1,
        (proposition_2_c H D Q t hA1 s hsQ hsI).1
          (u : G) u.property.1 u.property.2 |>.2⟩⟩
  have hsurjOut : Function.Surjective fOut := by
    intro v
    obtain ⟨u, huI, huH, hsu⟩ :=
      hsurjOutside (v : G) v.property.1 v.property.2
    refine ⟨⟨u, ⟨huI, huH⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [fOut] using hsu
  have hinjOut : Function.Injective fOut :=
    (Finite.injective_iff_surjective (f := fOut)).mpr hsurjOut
  have hphi_inj : Function.Injective phi := by
    intro k₁ k₂ hk
    have hconj :
        rightConjugateElem s ((k₁ : G) * t) =
          rightConjugateElem s ((k₂ : G) * t) := by
      calc
        rightConjugateElem s ((k₁ : G) * t) =
            rightConjugateElem (rightConjugateElem s (k₁ : G)) t :=
          (rightConjugateElem_comp s (k₁ : G) t).symm
        _ = rightConjugateElem (rightConjugateElem s (k₂ : G)) t := by
          rw [show rightConjugateElem s (k₁ : G) =
              rightConjugateElem s (k₂ : G) from congrArg Subtype.val hk]
        _ = rightConjugateElem s ((k₂ : G) * t) :=
          rightConjugateElem_comp s (k₂ : G) t
    let u₁ : Out :=
      ⟨(k₁ : G) * t,
        ⟨isInvolution_mul_t_of_mem_peterfalviKSet H D Q t hA1 k₁.property,
          mul_t_not_mem_H_of_mem_peterfalviKSet H D Q t hA1 k₁.property⟩⟩
    let u₂ : Out :=
      ⟨(k₂ : G) * t,
        ⟨isInvolution_mul_t_of_mem_peterfalviKSet H D Q t hA1 k₂.property,
          mul_t_not_mem_H_of_mem_peterfalviKSet H D Q t hA1 k₂.property⟩⟩
    have hu_eq : u₁ = u₂ := by
      apply hinjOut
      apply Subtype.ext
      simpa [fOut, u₁, u₂] using hconj
    apply Subtype.ext
    have hval : (k₁ : G) * t = (k₂ : G) * t := by
      simpa [u₁, u₂] using congrArg Subtype.val hu_eq
    have hcancel : (k₁ : G) * t * t⁻¹ = (k₂ : G) * t * t⁻¹ := by
      rw [hval]
    simpa [mul_assoc] using hcancel
  haveI : Fintype KType := Fintype.ofFinite KType
  haveI : Fintype HInv := Fintype.ofFinite HInv
  have hcard_fintype : Fintype.card KType = Fintype.card HInv := by
    simpa [Nat.card_eq_fintype_card] using hK_card
  have hphi_surj : Function.Surjective phi :=
    (Fintype.bijective_iff_injective_and_card phi).mpr
      ⟨hphi_inj, hcard_fintype⟩ |>.2
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := hphi_surj ⟨y, hy⟩
    refine ⟨(k : G), k.property, ?_⟩
    simpa [phi] using congrArg Subtype.val hk
  · rintro ⟨k, hkK, rfl⟩
    exact
      ⟨H.mul_mem
          (H.mul_mem (H.inv_mem (hA1.D_le_H hkK.1)) hsH)
          (hA1.D_le_H hkK.1),
        isInvolution_rightConjugateElem hsI⟩

end PFchapter1section1
end CFSG.BenderSuzuki



