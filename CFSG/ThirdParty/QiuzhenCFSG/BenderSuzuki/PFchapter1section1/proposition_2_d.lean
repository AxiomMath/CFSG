module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_d
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_c

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 2(d)
-/

private theorem exists_involution_mem_Q_for_prop2d
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ s : G, s ∈ Q ∧ IsInvolution s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo_dvd_Q : 2 ∣ Nat.card Q := hA1.Q_even.two_dvd
  obtain ⟨sQ, hsQ_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Q) 2 htwo_dvd_Q
  let s : G := sQ
  have hs_order : orderOf s = 2 := by
    simp [s, hsQ_order]
  have hs_pow_ne :=
    (orderOf_eq_prime_iff (x := s) (p := 2)).mp hs_order
  exact ⟨s, sQ.property, ⟨hs_pow_ne.2, hs_pow_ne.1⟩⟩

private theorem rightConjugate_rightConjugate
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    rightConjugate (rightConjugate H a) b = rightConjugate H (a * b) := by
  simp [rightConjugate, Subgroup.conjBy_conjBy, mul_inv_rev]

public theorem rightConjugate_eq_self_of_mem
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

private theorem rightConjugateElem_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {x g : G}
    (hx : x ∈ H) :
    rightConjugateElem x g ∈ rightConjugate H g := by
  rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
  exact ⟨x, hx, by simp⟩

private theorem mem_normalizer_of_conjBy_eq
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

private theorem mem_normalizer_of_rightConjugate_eq_self
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : rightConjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  apply mem_normalizer_of_conjBy_eq
  have h' : H.conjBy g⁻¹ = H := by
    simpa [rightConjugate] using h
  simpa [h'] using (Subgroup.conjBy_inv' H g)

private theorem not_mem_H_of_rightConjugate_eq_t
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {u : G}
    (hu_eq : rightConjugate H u = rightConjugate H t) :
    u ∉ H := by
  intro huH
  have hHt : rightConjugate H t = H := by
    calc
      rightConjugate H t = rightConjugate H u := hu_eq.symm
      _ = H := rightConjugate_eq_self_of_mem huH
  have ht_norm : t ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_of_rightConjugate_eq_self hHt
  have hnormH := (proposition_1_d H D Q t hA1).2
  have htH : t ∈ H := by
    simpa [hnormH] using ht_norm
  exact hA1.t_not_mem_H htH

private theorem rightConjugateElem_mem_of_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {x t : G}
    (ht : IsInvolution t) (hx : x ∈ rightConjugate H t) :
    rightConjugateElem x t ∈ H := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hleft : t * (t * y) = y := by
    rw [← mul_assoc, htt, one_mul]
  have hval :
      rightConjugateElem ((MulAut.conj t⁻¹).toMonoidHom y) t = y := by
    simpa [rightConjugateElem, MulAut.conj_apply, htinv, htt, mul_assoc] using hleft
  rw [hval]
  exact hy

private theorem not_isInvolution_of_mem_H_and_rightConjugate_t
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {x : G}
    (hxH : x ∈ H) (hxHt : x ∈ rightConjugate H t) :
    ¬ IsInvolution x := by
  obtain ⟨_, _, hodd⟩ := proposition_1_a H D Q t hA1 t hA1.t_not_mem_H
  exact
    not_isInvolution_of_mem_odd_subgroup
      (rightConjugate H t ⊓ H) hodd ⟨hxHt, hxH⟩

private theorem rightConjugateElem_mem_rightConjugate_t_iff
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {s u : G}
    (hsH : s ∈ H) (hs : IsInvolution s)
    (_hu : IsInvolution u) (_huH : u ∉ H) :
    rightConjugateElem s u ∈ rightConjugate H t ↔
      rightConjugate H u = rightConjugate H t := by
  constructor
  · intro hsuHt
    have hutH : u * t ∈ H := by
      by_contra hut_not_H
      obtain ⟨_, _, hodd⟩ := proposition_1_a H D Q t hA1 (u * t) hut_not_H
      have hsu_in_H : rightConjugateElem s (u * t) ∈ H := by
        have hmem :=
          rightConjugateElem_mem_of_mem_rightConjugate hA1.involution_t hsuHt
        simpa [rightConjugateElem_comp] using hmem
      have hsu_in_Hut : rightConjugateElem s (u * t) ∈ rightConjugate H (u * t) :=
        rightConjugateElem_mem_rightConjugate (H := H) (g := u * t) hsH
      exact False.elim
        ((not_isInvolution_of_mem_odd_subgroup
          (rightConjugate H (u * t) ⊓ H) hodd ⟨hsu_in_Hut, hsu_in_H⟩)
          (isInvolution_rightConjugateElem hs))
    have hHut : rightConjugate H (u * t) = H :=
      rightConjugate_eq_self_of_mem hutH
    have htt : t * t = 1 := by
      simpa [pow_two] using hA1.involution_t.sq_eq_one
    have hu_eq : (u * t) * t = u := by
      simp [mul_assoc, htt]
    calc
      rightConjugate H u = rightConjugate H ((u * t) * t) := by
        rw [hu_eq]
      _ = rightConjugate (rightConjugate H (u * t)) t :=
        (rightConjugate_rightConjugate H (u * t) t).symm
      _ = rightConjugate H t := by
        rw [hHut]
  · intro hHu
    have hsHu : rightConjugateElem s u ∈ rightConjugate H u :=
      rightConjugateElem_mem_rightConjugate (H := H) (g := u) hsH
    simpa [hHu] using hsHu

public theorem proposition_2_d
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card {u : G // IsInvolution u ∧ rightConjugate H u = rightConjugate H t} =
      Nat.card {u : G // u ∈ H ∧ IsInvolution u} := by
  classical
  obtain ⟨s, hsQ, hs⟩ := exists_involution_mem_Q_for_prop2d H D Q t hA1
  have hsH : s ∈ H := hA1.Q_le_H hsQ
  obtain ⟨hforward, hsurjOutside⟩ := proposition_2_c H D Q t hA1 s hsQ hs
  let Target : Type _ :=
    {u : G // IsInvolution u ∧ rightConjugate H u = rightConjugate H t}
  let HtInv : Type _ := {x : G // x ∈ rightConjugate H t ∧ IsInvolution x}
  let HInv : Type _ := {x : G // x ∈ H ∧ IsInvolution x}
  let Out : Type _ := {u : G // IsInvolution u ∧ u ∉ H}
  let fOut : Out → Out := fun u =>
    ⟨rightConjugateElem s (u : G),
      ⟨(hforward (u : G) u.property.1 u.property.2).1,
        (hforward (u : G) u.property.1 u.property.2).2⟩⟩
  have hsurjOut : Function.Surjective fOut := by
    intro v
    obtain ⟨u, hu, huH, hsu⟩ := hsurjOutside (v : G) v.property.1 v.property.2
    refine ⟨⟨u, ⟨hu, huH⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [fOut] using hsu
  have hinjOut : Function.Injective fOut :=
    (Finite.injective_iff_surjective (f := fOut)).mpr hsurjOut
  let F : Target → HtInv := fun u =>
    ⟨rightConjugateElem s (u : G),
      ⟨by
        have hsHu : rightConjugateElem s (u : G) ∈ rightConjugate H (u : G) :=
          rightConjugateElem_mem_rightConjugate (H := H) (g := (u : G)) hsH
        simpa [u.property.2] using hsHu,
      isInvolution_rightConjugateElem hs⟩⟩
  have hF_inj : Function.Injective F := by
    intro u v huv
    have huH : (u : G) ∉ H :=
      not_mem_H_of_rightConjugate_eq_t H D Q t hA1 u.property.2
    have hvH : (v : G) ∉ H :=
      not_mem_H_of_rightConjugate_eq_t H D Q t hA1 v.property.2
    let uOut : Out := ⟨(u : G), ⟨u.property.1, huH⟩⟩
    let vOut : Out := ⟨(v : G), ⟨v.property.1, hvH⟩⟩
    have hOut : fOut uOut = fOut vOut := by
      apply Subtype.ext
      simpa [F, fOut, uOut, vOut] using congrArg Subtype.val huv
    have huvOut := hinjOut hOut
    apply Subtype.ext
    simpa [uOut, vOut] using congrArg Subtype.val huvOut
  have hF_surj : Function.Surjective F := by
    intro y
    have hyH : (y : G) ∉ H := by
      intro hyH
      exact
        (not_isInvolution_of_mem_H_and_rightConjugate_t H D Q t hA1
          hyH y.property.1) y.property.2
    obtain ⟨u, hu, huH, hsu⟩ := hsurjOutside (y : G) y.property.2 hyH
    have hEq : rightConjugate H u = rightConjugate H t :=
      (rightConjugateElem_mem_rightConjugate_t_iff H D Q t hA1 hsH hs hu huH).mp
        (by simpa [hsu] using y.property.1)
    refine ⟨⟨u, ⟨hu, hEq⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [F] using hsu
  let C : HtInv → HInv := fun x =>
    ⟨rightConjugateElem (x : G) t,
      ⟨rightConjugateElem_mem_of_mem_rightConjugate hA1.involution_t x.property.1,
        isInvolution_rightConjugateElem x.property.2⟩⟩
  have hC_inj : Function.Injective C := by
    intro x y hxy
    apply Subtype.ext
    have hval :
        rightConjugateElem (x : G) t = rightConjugateElem (y : G) t := by
      simpa [C] using congrArg Subtype.val hxy
    have hinv := rightConjugateElem_involutive_of_isInvolution hA1.involution_t
    calc
      (x : G) = rightConjugateElem (rightConjugateElem (x : G) t) t :=
        (hinv (x : G)).symm
      _ = rightConjugateElem (rightConjugateElem (y : G) t) t := by
        rw [hval]
      _ = (y : G) := hinv (y : G)
  have hC_surj : Function.Surjective C := by
    intro y
    refine
      ⟨⟨rightConjugateElem (y : G) t,
        ⟨rightConjugateElem_mem_rightConjugate (H := H) (g := t) y.property.1,
          isInvolution_rightConjugateElem y.property.2⟩⟩, ?_⟩
    apply Subtype.ext
    exact rightConjugateElem_involutive_of_isInvolution hA1.involution_t (y : G)
  have hTargetHt : Nat.card Target = Nat.card HtInv :=
    Nat.card_congr (Equiv.ofBijective F ⟨hF_inj, hF_surj⟩)
  have hHtH : Nat.card HtInv = Nat.card HInv :=
    Nat.card_congr (Equiv.ofBijective C ⟨hC_inj, hC_surj⟩)
  simpa [Target, HtInv, HInv] using hTargetHt.trans hHtH

end PFchapter1section1
end CFSG.BenderSuzuki
