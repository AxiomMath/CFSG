module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingIntersections
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizer cosets under strong embedding

This file proves `[IG; 17.8(ii)]`: if `z` is an involution in a strongly
embedded subgroup `M`, every right coset `C_X(z) * x` outside `M` contains
exactly one involution.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

public theorem
    mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq
    {X : Type u} [Group X] {z a b : X} :
    a * b⁻¹ ∈ Subgroup.centralizer ({z} : Set X) ↔
      rightConjugateElem z a = rightConjugateElem z b := by
  let c : X := a * b⁻¹
  have ha : a = c * b := by
    simp [c]
  constructor
  · intro hc
    have hcomm : c * z = z * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcfix : rightConjugateElem z c = z := by
      dsimp [rightConjugateElem]
      calc
        c⁻¹ * z * c = c⁻¹ * (z * c) := by rw [mul_assoc]
        _ = c⁻¹ * (c * z) := by rw [hcomm]
        _ = z := by simp
    rw [ha, ← rightConjugateElem_comp, hcfix]
  · intro hab
    have hcfix : rightConjugateElem z c = z := by
      calc
        rightConjugateElem z c =
            rightConjugateElem
              (rightConjugateElem z a) b⁻¹ := by
          dsimp [c]
          rw [rightConjugateElem_comp]
        _ = rightConjugateElem
              (rightConjugateElem z b) b⁻¹ := by rw [hab]
        _ = rightConjugateElem z (b * b⁻¹) := by
          rw [rightConjugateElem_comp]
        _ = z := by simp [rightConjugateElem]
    change c ∈ Subgroup.centralizer ({z} : Set X)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (fun y : X => c * y) hcfix
    simpa [rightConjugateElem, mul_assoc] using h.symm

namespace IsStronglyEmbedded

/-- If `z` is an involution in a strongly embedded subgroup `M`, every right
coset `C_X(z) * x` with `x ∉ M` contains exactly one involution.  Membership
in that right coset is written as `t * x⁻¹ ∈ C_X(z)`.  This is
`[IG; 17.8(ii)]`. -/
public theorem existsUnique_involution_in_centralizer_rightCoset
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z x : X}
    (hzM : z ∈ M) (hz : IsInvolution z) (hxM : x ∉ M) :
    ∃! t : X,
      t * x⁻¹ ∈ Subgroup.centralizer ({z} : Set X) ∧ IsInvolution t := by
  classical
  let Iout := {t : X // IsInvolution t ∧ t ∉ M}
  let phi : Iout → Iout := fun t =>
    ⟨rightConjugateElem z t, isInvolution_rightConjugateElem hz, by
      intro hztM
      apply t.property.2
      apply hM.mem_of_involution_mem_rightConjugate hztM
        (rightConjugateElem_mem_rightConjugate hzM)
      exact isInvolution_rightConjugateElem hz⟩
  have hphiSurj : Function.Surjective phi := by
    intro v
    have hzv : z ≠ (v : X) := by
      intro h
      exact v.property.2 (h ▸ hzM)
    obtain ⟨t, ht, hzt⟩ :=
      exists_involution_conjugator_of_odd_product hz v.property.1 hzv
        (hM.orderOf_mul_odd_of_mem_not_mem
          hzM hz v.property.2 v.property.1)
    have htM : t ∉ M := by
      intro htM
      apply v.property.2
      rw [← hzt]
      exact M.mul_mem (M.mul_mem (M.inv_mem htM) hzM) htM
    refine ⟨⟨t, ht, htM⟩, ?_⟩
    apply Subtype.ext
    exact hzt
  have hphiInj : Function.Injective phi :=
    Finite.injective_iff_surjective.mpr hphiSurj
  let s : X := rightConjugateElem z x
  have hs : IsInvolution s := isInvolution_rightConjugateElem hz
  have hsM : s ∉ M := by
    intro hsM
    exact hxM (hM.mem_of_involution_mem_rightConjugate hsM
      (rightConjugateElem_mem_rightConjugate hzM) hs)
  have hzs : z ≠ s := by
    intro h
    exact hsM (h ▸ hzM)
  obtain ⟨t, ht, hzt⟩ :=
    exists_involution_conjugator_of_odd_product hz hs hzs
      (hM.orderOf_mul_odd_of_mem_not_mem hzM hz hsM hs)
  have htCoset :
      t * x⁻¹ ∈ Subgroup.centralizer ({z} : Set X) :=
    mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mpr hzt
  refine ⟨t, ⟨htCoset, ht⟩, ?_⟩
  intro a ha
  have haM : a ∉ M := by
    intro haM
    apply hxM
    have hacM : a * x⁻¹ ∈ M :=
      hM.centralizer_le hzM hz ha.1
    have hxEq : x = (a * x⁻¹)⁻¹ * a := by
      simp
    rw [hxEq]
    exact M.mul_mem (M.inv_mem hacM) haM
  have htM : t ∉ M := by
    intro htM
    apply hxM
    have htcM : t * x⁻¹ ∈ M :=
      hM.centralizer_le hzM hz htCoset
    have hxEq : x = (t * x⁻¹)⁻¹ * t := by
      simp
    rw [hxEq]
    exact M.mul_mem (M.inv_mem htcM) htM
  have hconj : rightConjugateElem z a = rightConjugateElem z t :=
    (mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mp ha.1).trans
      (mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mp
        htCoset).symm
  have hsub : (⟨a, ha.2, haM⟩ : Iout) = ⟨t, ht, htM⟩ := by
    apply hphiInj
    apply Subtype.ext
    exact hconj
  exact congrArg Subtype.val hsub

private theorem exists_centralizer_mul_inf_rightConjugate
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    ∀ m : X, m ∈ M →
      ∃ c : X, c ∈ Subgroup.centralizer ({z} : Set X) ∧
        ∃ d : X, d ∈ M ⊓ rightConjugate M t ∧ m = c * d := by
  intro m hmM
  let x : X := t * m⁻¹
  have hxM : x ∉ M := by
    intro hxM
    apply htM
    have htm : t = x * m := by
      simp [x]
    rw [htm]
    exact M.mul_mem hxM hmM
  obtain ⟨u, huCoset, huInv⟩ :=
    (hM.existsUnique_involution_in_centralizer_rightCoset
      hzM hz hxM).exists
  let c : X := u * x⁻¹
  let d : X := m⁻¹ * c
  have hc : c ∈ Subgroup.centralizer ({z} : Set X) := huCoset
  have hcM : c ∈ M := hM.centralizer_le hzM hz hc
  have hdM : d ∈ M := M.mul_mem (M.inv_mem hmM) hcM
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have huEq : u = c * t * m⁻¹ := by
    simp [c, x, ht.inv_eq_self, htt, mul_assoc]
  have huSq : (c * t * m⁻¹) * (c * t * m⁻¹) = 1 := by
    simpa [huEq, pow_two] using huInv.sq_eq_one
  have hcore := congrArg (fun y : X => c⁻¹ * y * m) huSq
  have htdt : rightConjugateElem d t = d⁻¹ := by
    change t⁻¹ * d * t = d⁻¹
    rw [ht.inv_eq_self]
    dsimp [d]
    calc
      t * (m⁻¹ * c) * t = c⁻¹ * m := by
        simpa [mul_assoc] using hcore
      _ = (m⁻¹ * c)⁻¹ := by simp
  have hdInvConj : d⁻¹ ∈ rightConjugate M t := by
    rw [← htdt]
    exact rightConjugateElem_mem_rightConjugate hdM
  have hdConj : d ∈ rightConjugate M t := by
    have := (rightConjugate M t).inv_mem hdInvConj
    simpa using this
  have hdD : d ∈ M ⊓ rightConjugate M t := ⟨hdM, hdConj⟩
  refine ⟨c, hc, d⁻¹, (M ⊓ rightConjugate M t).inv_mem hdD, ?_⟩
  simp [d]

open scoped Pointwise

/-- With `C = C_X(z)` and `D = M ⊓ M^t`, one has the exact source
decomposition `C * D = M`.  This is the product assertion in
`[IG; 17.8(iii)]`. -/
public theorem centralizer_mul_inf_rightConjugate_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    (Subgroup.centralizer ({z} : Set X) : Set X) *
        ((M ⊓ rightConjugate M t : Subgroup X) : Set X) = (M : Set X) := by
  ext m
  constructor
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact M.mul_mem (hM.centralizer_le hzM hz hc) hd.1
  · intro hm
    obtain ⟨c, hc, d, hd, hcd⟩ :=
      exists_centralizer_mul_inf_rightConjugate
        hM hzM hz ht htM m hm
    exact ⟨c, hc, d, hd, hcd.symm⟩

/-- Lattice form of the product decomposition in `[IG; 17.8(iii)]`. -/
public theorem centralizer_sup_inf_rightConjugate_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    Subgroup.centralizer ({z} : Set X) ⊔
        (M ⊓ rightConjugate M t) = M := by
  apply le_antisymm
  · exact sup_le (hM.centralizer_le hzM hz) inf_le_left
  · intro m hm
    obtain ⟨c, hc, d, hd, rfl⟩ :=
      exists_centralizer_mul_inf_rightConjugate
        hM hzM hz ht htM m hm
    have hcSup : c ∈ Subgroup.centralizer ({z} : Set X) ⊔
        (M ⊓ rightConjugate M t) :=
      (show Subgroup.centralizer ({z} : Set X) ≤
        Subgroup.centralizer ({z} : Set X) ⊔
          (M ⊓ rightConjugate M t) from le_sup_left) hc
    have hdSup : d ∈ Subgroup.centralizer ({z} : Set X) ⊔
        (M ⊓ rightConjugate M t) :=
      (show M ⊓ rightConjugate M t ≤
        Subgroup.centralizer ({z} : Set X) ⊔
          (M ⊓ rightConjugate M t) from le_sup_right) hd
    exact (Subgroup.centralizer ({z} : Set X) ⊔
      (M ⊓ rightConjugate M t)).mul_mem hcSup hdSup

end IsStronglyEmbedded
end CFSG.BenderSuzuki
