module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCentralizerCosets
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

/-!
# Counting consequences of strong embedding

This module contains the Proposition 3.6 conjugacy and centralizer-counting
facts that depend only on the checked strong-embedding interfaces.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement

universe u

private abbrev involutionsInSubgroup
    {X : Type u} [Group X] (M : Subgroup X) :=
  {x : X // x ∈ M ∧ IsInvolution x}

private abbrev involutionsInRightCoset
    {X : Type u} [Group X] (M : Subgroup X) (t : X) :=
  {s : X // IsInvolution s ∧ s * t ∈ M}

namespace IsStronglyEmbedded

private theorem involutions_conjugate_by_inf_rightConjugate_core
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t a b : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (haM : a ∈ M) (ha : IsInvolution a)
    (hbM : b ∈ M) (hb : IsInvolution b) :
    ∃ d : X, d ∈ M ⊓ rightConjugate M t ∧
      rightConjugateElem a d = b := by
  obtain ⟨m, hmM, ham⟩ := hM.involutions_conjugate_in haM ha hbM hb
  have hprod :=
    hM.centralizer_mul_inf_rightConjugate_eq haM ha ht htM
  have hmProd :
      m ∈ (Subgroup.centralizer ({a} : Set X) : Set X) *
        ((M ⊓ rightConjugate M t : Subgroup X) : Set X) := by
    rw [hprod]
    exact hmM
  rcases hmProd with ⟨c, hc, d, hd, hcd⟩
  have hac : rightConjugateElem a c = a := by
    have hcomm : c * a = a * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    dsimp [rightConjugateElem]
    calc
      c⁻¹ * a * c = c⁻¹ * (a * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * a) := by rw [hcomm]
      _ = a := by simp
  refine ⟨d, hd, ?_⟩
  calc
    rightConjugateElem a d =
        rightConjugateElem (rightConjugateElem a c) d := by rw [hac]
    _ = rightConjugateElem a (c * d) := by
      rw [rightConjugateElem_comp]
    _ = rightConjugateElem a m :=
      congrArg (rightConjugateElem a) hcd
    _ = b := ham

/-- The unique-involution centralizer-coset theorem identifies the
involutions in the right coset `M * t` with the involutions in `M`. -/
private noncomputable def involutionsInRightCosetEquivInvolutionsIn
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    involutionsInRightCoset M t ≃ involutionsInSubgroup M := by
  let F : involutionsInRightCoset M t → involutionsInSubgroup M :=
    fun s =>
      ⟨rightConjugateElem z ((s : X) * t),
        ⟨M.mul_mem
            (M.mul_mem (M.inv_mem s.property.2) hzM) s.property.2,
          isInvolution_rightConjugateElem hz⟩⟩
  have hnotM (s : involutionsInRightCoset M t) : (s : X) ∉ M := by
    intro hsM
    apply htM
    have htEq : t = (s : X)⁻¹ * ((s : X) * t) := by simp
    rw [htEq]
    exact M.mul_mem (M.inv_mem hsM) s.property.2
  have hFInjective : Function.Injective F := by
    intro s₁ s₂ hs
    have hconj :
        rightConjugateElem z ((s₁ : X) * t) =
          rightConjugateElem z ((s₂ : X) * t) :=
      congrArg Subtype.val hs
    have hcosetProduct :
        ((s₁ : X) * t) * ((s₂ : X) * t)⁻¹ ∈
          Subgroup.centralizer ({z} : Set X) :=
      mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mpr hconj
    have hcoset :
        (s₁ : X) * (s₂ : X)⁻¹ ∈
          Subgroup.centralizer ({z} : Set X) := by
      have heq :
          ((s₁ : X) * t) * ((s₂ : X) * t)⁻¹ =
            (s₁ : X) * (s₂ : X)⁻¹ := by
        group
      rw [← heq]
      exact hcosetProduct
    obtain ⟨u, hu, hunique⟩ :=
      hM.existsUnique_involution_in_centralizer_rightCoset
        hzM hz (hnotM s₂)
    have hs₁u : (s₁ : X) = u :=
      hunique _ ⟨hcoset, s₁.property.1⟩
    have hs₂u : (s₂ : X) = u :=
      hunique _ ⟨by simp, s₂.property.1⟩
    apply Subtype.ext
    exact hs₁u.trans hs₂u.symm
  have hFSurjective : Function.Surjective F := by
    intro y
    obtain ⟨d, hdD, hzy⟩ :=
      involutions_conjugate_by_inf_rightConjugate_core hM
        ht htM hzM hz y.property.1 y.property.2
    let x : X := d * t
    have hxM : x ∉ M := by
      intro hxM
      apply htM
      have htEq : t = d⁻¹ * x := by simp [x]
      rw [htEq]
      exact M.mul_mem (M.inv_mem hdD.1) hxM
    obtain ⟨s, hsCoset, hsInv⟩ :=
      (hM.existsUnique_involution_in_centralizer_rightCoset
        hzM hz hxM).exists
    let c : X := s * x⁻¹
    have hcM : c ∈ M := hM.centralizer_le hzM hz hsCoset
    have hstEq : s * t = c * d := by
      simp [c, x, ht.inv_eq_self, mul_assoc]
    have hstM : s * t ∈ M := by
      rw [hstEq]
      exact M.mul_mem hcM hdD.1
    let sMt : involutionsInRightCoset M t :=
      ⟨s, hsInv, hstM⟩
    refine ⟨sMt, ?_⟩
    apply Subtype.ext
    change rightConjugateElem z (s * t) = (y : X)
    have hcoset :
        (s * t) * d⁻¹ ∈ Subgroup.centralizer ({z} : Set X) := by
      simpa [x, ht.inv_eq_self, mul_assoc] using hsCoset
    exact
      (mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mp hcoset).trans
        hzy
  exact Equiv.ofBijective F ⟨hFInjective, hFSurjective⟩

/-! A small public projection of the preceding coset equivalence.  It is the
source-faithful form of the fact used in Lemma 3.10: every involution of the
base stabilizer is represented by an element of the Peterfalvi anti-fixed
set.  No generation or maximality conclusion is part of this interface. -/

public theorem exists_mem_peterfalviKSet_of_involution_mem
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t y : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hyM : y ∈ M) (hy : IsInvolution y) :
    ∃ k : X,
      k ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        rightConjugateElem z k = y := by
  rcases
    (involutionsInRightCosetEquivInvolutionsIn hM hzM hz ht htM).surjective
      ⟨y, hyM, hy⟩ with ⟨s, hsy⟩
  have hsy' : rightConjugateElem z ((s : X) * t) = y := by
    have h := congrArg
      (fun q : involutionsInSubgroup M => (q : X)) hsy
    change rightConjugateElem z ((s : X) * t) = y at h
    exact h
  have hkt :
      rightConjugateElem ((s : X) * t) t = ((s : X) * t)⁻¹ := by
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    simp [rightConjugateElem, ht.inv_eq_self, s.property.1.inv_eq_self,
      mul_assoc, htt]
  have hkInvConj : ((s : X) * t)⁻¹ ∈ rightConjugate M t := by
    rw [← hkt]
    exact rightConjugateElem_mem_rightConjugate s.property.2
  have hkConj : (s : X) * t ∈ rightConjugate M t := by
    have h := (rightConjugate M t).inv_mem hkInvConj
    simpa using h
  have hkD : (s : X) * t ∈ M ⊓ rightConjugate M t :=
    ⟨s.property.2, hkConj⟩
  exact ⟨(s : X) * t, ⟨hkD, hkt⟩, hsy'⟩

/-- An element inverted by an involution lies in the action commutator when
the ambient subgroup has odd order.  This is the elementary powering step in
Lemma 3.10. -/
public theorem mem_commutator_zpowers_of_mem_peterfalviKSet
    {X : Type u} [Group X] [Finite X] (D : Subgroup X) {t k : X}
    (hDodd : Odd (Nat.card D)) (ht : IsInvolution t)
    (hk : k ∈ peterfalviKSet D t) :
    k ∈ ⁅D, Subgroup.zpowers t⁆ := by
  have htkinv : t * k⁻¹ * t⁻¹ = k := by
    have h := congrArg Inv.inv hk.2
    simpa [rightConjugateElem, ht.inv_eq_self, mul_assoc] using h
  have hcommEq : ⁅k, t⁆ = k ^ 2 := by
    rw [commutatorElement_def]
    calc
      k * t * k⁻¹ * t⁻¹ = k * (t * k⁻¹ * t⁻¹) := by group
      _ = k * k := by rw [htkinv]
      _ = k ^ 2 := by rw [pow_two]
  have hsq : k ^ 2 ∈ ⁅D, Subgroup.zpowers t⁆ := by
    rw [← hcommEq]
    exact Subgroup.commutator_mem_commutator hk.1 (Subgroup.mem_zpowers t)
  let kD : D := ⟨k, hk.1⟩
  have horderOddD : Odd (orderOf kD) :=
    hDodd.of_dvd_nat (orderOf_dvd_natCard kD)
  have horderOdd : Odd (orderOf k) := by
    simpa [kD, Subgroup.orderOf_coe] using horderOddD
  rcases horderOdd with ⟨m, hm⟩
  have hkpow : (k ^ 2) ^ (m + 1) = k := by
    calc
      (k ^ 2) ^ (m + 1) = k ^ (2 * (m + 1)) := by rw [pow_mul]
      _ = k ^ ((2 * m + 1) + 1) := by congr 1 <;> omega
      _ = k ^ (orderOf k + 1) := by rw [hm]
      _ = k := by rw [pow_add, pow_orderOf_eq_one]; simp
  rw [← hkpow]
  exact (⁅D, Subgroup.zpowers t⁆ : Subgroup X).pow_mem hsq (m + 1)

/-- The subgroup occurring in Proposition 6.3.  For a strongly embedded
`M`, the two-point stabilizer `M ⊓ M^t` has odd order, so it is its own
`O_{2'}` and this is exactly `⟨z,t,[t,O_{2'}(D)]⟩`. -/
@[expose] public def theorem4bProposition63Subgroup
    {X : Type u} [Group X] (M : Subgroup X) (z t : X) : Subgroup X :=
  Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
    ⁅M ⊓ rightConjugate M t, Subgroup.zpowers t⁆

/-- Lemma 3.10, conjugacy-class containment part: every involution of the
base strongly embedded subgroup lies in the Proposition 6.3 subgroup. -/
public theorem involution_mem_theorem4bProposition63Subgroup
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t y : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hyM : y ∈ M) (hy : IsInvolution y) :
    y ∈ theorem4bProposition63Subgroup M z t := by
  obtain ⟨k, hkK, hzy⟩ :=
    hM.exists_mem_peterfalviKSet_of_involution_mem
      hzM hz ht htM hyM hy
  have hkComm :
      k ∈ ⁅M ⊓ rightConjugate M t, Subgroup.zpowers t⁆ :=
    mem_commutator_zpowers_of_mem_peterfalviKSet
      (M ⊓ rightConjugate M t)
      (hM.inf_rightConjugate_card_odd htM) ht hkK
  have hzL : z ∈ theorem4bProposition63Subgroup M z t := by
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hkL : k ∈ theorem4bProposition63Subgroup M z t := by
    exact Subgroup.mem_sup_right hkComm
  rw [← hzy]
  dsimp [rightConjugateElem]
  exact (theorem4bProposition63Subgroup M z t).mul_mem
    ((theorem4bProposition63Subgroup M z t).mul_mem
      ((theorem4bProposition63Subgroup M z t).inv_mem hkL) hzL) hkL

/-- Lemma 3.10, involution-generation part: the Proposition 6.3 subgroup is
generated by its own involutions. -/
public theorem theorem4bProposition63Subgroup_eq_involutionCore
    {X : Type u} [Group X] {M : Subgroup X} {z t : X}
    (hz : IsInvolution z) (ht : IsInvolution t) :
    let L := theorem4bProposition63Subgroup M z t
    L = (involutionCore L).map L.subtype := by
  let L : Subgroup X := theorem4bProposition63Subgroup M z t
  let L0 : Subgroup X := (involutionCore L).map L.subtype
  have hsq_mem_L0 {x : X} (hxL : x ∈ L) (hxSq : x ^ 2 = 1) : x ∈ L0 := by
    by_cases hxOne : x = 1
    · simpa [hxOne] using L0.one_mem
    · let xL : L := ⟨x, hxL⟩
      have hxLInv : IsInvolution xL := by
        refine ⟨?_, ?_⟩
        · intro h
          apply hxOne
          exact congrArg Subtype.val h
        · apply Subtype.ext
          exact hxSq
      have hxCore : xL ∈ involutionCore L := by
        rw [involutionCore_eq_closure]
        exact Subgroup.subset_closure hxLInv
      exact Subgroup.mem_map.mpr ⟨xL, hxCore, rfl⟩
  have hzL : z ∈ L := by
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have htL : t ∈ L := by
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hzL0 : z ∈ L0 := hsq_mem_L0 hzL hz.sq_eq_one
  have htL0 : t ∈ L0 := hsq_mem_L0 htL ht.sq_eq_one
  have hcommL0 :
      ⁅M ⊓ rightConjugate M t, Subgroup.zpowers t⁆ ≤ L0 := by
    rw [Subgroup.commutator_le]
    intro d hdD b hbT
    have hbOrder : orderOf b ∣ 2 := by
      have hdiv := orderOf_dvd_of_mem_zpowers hbT
      have htOrder : orderOf t = 2 :=
        (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
      simpa [htOrder] using hdiv
    have hbSq : b ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hbOrder
    have hbL : b ∈ L :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right hbT)
    have hcL : ⁅d, b⁆ ∈ L :=
      Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hdD hbT)
    have hdbdL : d * b * d⁻¹ ∈ L := by
      have h := L.mul_mem hcL hbL
      simpa [commutatorElement_def, mul_assoc] using h
    have hdbdSq : (d * b * d⁻¹) ^ 2 = 1 := by
      have hbMul : b * b = 1 := by simpa [pow_two] using hbSq
      calc
        (d * b * d⁻¹) ^ 2 = d * (b * b) * d⁻¹ := by
          simp only [pow_two]
          group
        _ = 1 := by rw [hbMul]; simp
    have hbInvSq : b⁻¹ ^ 2 = 1 := by
      have h := congrArg Inv.inv hbSq
      simpa [pow_two] using h
    have hdbdL0 : d * b * d⁻¹ ∈ L0 := hsq_mem_L0 hdbdL hdbdSq
    have hbInvL0 : b⁻¹ ∈ L0 := hsq_mem_L0 (L.inv_mem hbL) hbInvSq
    simpa [commutatorElement_def, mul_assoc] using L0.mul_mem hdbdL0 hbInvL0
  change L = L0
  apply le_antisymm
  · change
      Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
        ⁅M ⊓ rightConjugate M t, Subgroup.zpowers t⁆ ≤ L0
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hzL0)
      (Subgroup.zpowers_le.mpr htL0)) hcommL0
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xL, _hxCore, rfl⟩
    exact xL.property

/-- Proposition 3.6(c), in the exact form needed in Lemma 8.3(b): the
involutions of `M` are conjugate by `D = M ⊓ M^t`. -/
public theorem involutions_conjugate_by_inf_rightConjugate
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t a b : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (haM : a ∈ M) (ha : IsInvolution a)
    (hbM : b ∈ M) (hb : IsInvolution b) :
    ∃ d : X, d ∈ M ⊓ rightConjugate M t ∧
      rightConjugateElem a d = b :=
  involutions_conjugate_by_inf_rightConjugate_core
    hM ht htM haM ha hbM hb

private theorem natCard_inf_centralizer_eq_of_rightConjugateElem_eq
    {X : Type u} [Group X] (D : Subgroup X) {a b d : X}
    (hd : d ∈ D) (hab : rightConjugateElem a d = b) :
    Nat.card (D ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) =
      Nat.card (D ⊓ Subgroup.centralizer ({b} : Set X) : Subgroup X) := by
  let Ca : Subgroup X := D ⊓ Subgroup.centralizer ({a} : Set X)
  let Cb : Subgroup X := D ⊓ Subgroup.centralizer ({b} : Set X)
  have hba : rightConjugateElem b d⁻¹ = a := by
    rw [← hab, rightConjugateElem_comp]
    simp [rightConjugateElem]
  have hforward {x : X} (hxD : x ∈ D)
      (hxa : x ∈ Subgroup.centralizer ({a} : Set X)) :
      rightConjugateElem x d ∈ Cb := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa [rightConjugateElem] using
        D.mul_mem (D.mul_mem (D.inv_mem hd) hxD) hd
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hab]
      have hcomm : x * a = a * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxa
      calc
        rightConjugateElem x d * rightConjugateElem a d =
            rightConjugateElem (x * a) d := by
              simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem (a * x) d := by rw [hcomm]
        _ = rightConjugateElem a d * rightConjugateElem x d := by
              simp [rightConjugateElem, mul_assoc]
  have hbackward {x : X} (hxD : x ∈ D)
      (hxb : x ∈ Subgroup.centralizer ({b} : Set X)) :
      rightConjugateElem x d⁻¹ ∈ Ca := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa [rightConjugateElem] using
        D.mul_mem (D.mul_mem hd hxD) (D.inv_mem hd)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hba]
      have hcomm : x * b = b * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxb
      calc
        rightConjugateElem x d⁻¹ * rightConjugateElem b d⁻¹ =
            rightConjugateElem (x * b) d⁻¹ := by
              simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem (b * x) d⁻¹ := by rw [hcomm]
        _ = rightConjugateElem b d⁻¹ * rightConjugateElem x d⁻¹ := by
              simp [rightConjugateElem, mul_assoc]
  let e : Ca ≃ Cb :=
    { toFun := fun x => ⟨rightConjugateElem (x : X) d,
        hforward x.property.1 x.property.2⟩
      invFun := fun x => ⟨rightConjugateElem (x : X) d⁻¹,
        hbackward x.property.1 x.property.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change rightConjugateElem (rightConjugateElem (x : X) d) d⁻¹ = x
        rw [rightConjugateElem_comp]
        simp [rightConjugateElem]
      right_inv := by
        intro x
        apply Subtype.ext
        change rightConjugateElem (rightConjugateElem (x : X) d⁻¹) d = x
        rw [rightConjugateElem_comp]
        simp [rightConjugateElem] }
  exact Nat.card_congr e

/-- Proposition 3.6(c,d), restricted to the centralizer-cardinality equality
between involutions of `M` used in Lemma 8.3(a). -/
public theorem inf_rightConjugate_centralizer_card_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t a b : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (haM : a ∈ M) (ha : IsInvolution a)
    (hbM : b ∈ M) (hb : IsInvolution b) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    Nat.card (D ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) =
      Nat.card (D ⊓ Subgroup.centralizer ({b} : Set X) : Subgroup X) := by
  dsimp only
  obtain ⟨d, hd, hab⟩ :=
    hM.involutions_conjugate_by_inf_rightConjugate
      ht htM haM ha hbM hb
  exact natCard_inf_centralizer_eq_of_rightConjugateElem_eq
    (M ⊓ rightConjugate M t) hd hab

/-- Proposition 3.6(d), in the centralizer-cardinality form used by
Lemma 8.3(a): for `D = M ⊓ M^t`, the centralizer in `D` of the outside
involution `t` has the same cardinality as the centralizer in `D` of any
involution `z ∈ M`.

The proof counts the two `D`-conjugacy orbits.  Proposition `[IG; 17.8(ii)]`
gives a bijection between the involutions in `M * t` and those in `M`, while
oddness of `D` supplies a conjugator in `⟨s * t⟩ ≤ D` for every involution
`s ∈ M * t`. -/
public theorem inf_rightConjugate_outside_inside_centralizer_card_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z t : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    Nat.card (D ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) =
      Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  change
    Nat.card (D ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) =
      Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X)
  let : MulAction D X :=
    { smul := fun d x => (d : X) * x * (d : X)⁻¹
      one_smul := by
        intro x
        change ((1 : D) : X) * x * (((1 : D) : X))⁻¹ = x
        simp
      mul_smul := by
        intro a b x
        change (((a * b : D) : X) * x * (((a * b : D) : X))⁻¹) =
          ((a : X) * (((b : X) * x * (b : X)⁻¹)) * (a : X)⁻¹)
        simp [mul_assoc] }
  have hDodd : Odd (Nat.card D) := hM.inf_rightConjugate_card_odd htM
  have horbitZ :
      MulAction.orbit D z = {y : X | y ∈ M ∧ IsInvolution y} := by
    ext y
    constructor
    · intro hy
      rcases MulAction.mem_orbit_iff.mp hy with ⟨d, rfl⟩
      constructor
      · exact
          M.mul_mem (M.mul_mem d.property.1 hzM) (M.inv_mem d.property.1)
      · change IsInvolution ((d : X) * z * (d : X)⁻¹)
        simpa [rightConjugateElem] using
          (isInvolution_rightConjugateElem
            (x := z) (g := ((d : X)⁻¹)) hz)
    · rintro ⟨hyM, hy⟩
      obtain ⟨d, hdD, hzd⟩ :=
        hM.involutions_conjugate_by_inf_rightConjugate
          ht htM hzM hz hyM hy
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨d⁻¹, D.inv_mem hdD⟩, ?_⟩
      change d⁻¹ * z * (d⁻¹)⁻¹ = y
      simpa [rightConjugateElem] using hzd
  have horbitT :
      MulAction.orbit D t =
        {s : X | IsInvolution s ∧ s * t ∈ M} := by
    ext s
    constructor
    · intro hs
      rcases MulAction.mem_orbit_iff.mp hs with ⟨d, rfl⟩
      constructor
      · change IsInvolution ((d : X) * t * (d : X)⁻¹)
        simpa [rightConjugateElem] using
          (isInvolution_rightConjugateElem
            (x := t) (g := ((d : X)⁻¹)) ht)
      · have hdInvD : (d : X)⁻¹ ∈ D := D.inv_mem d.property
        have hdConj0 :=
          rightConjugateElem_mem_rightConjugate (g := t) hdInvD
        have hdConj : rightConjugateElem (d : X)⁻¹ t ∈ D := by
          have hInv := inf_rightConjugate_invariant_of_isInvolution M ht
          change rightConjugate D t = D at hInv
          rw [hInv] at hdConj0
          exact hdConj0
        have hprodD :
            (d : X) * rightConjugateElem (d : X)⁻¹ t ∈ D :=
          D.mul_mem d.property hdConj
        change ((d : X) * t * (d : X)⁻¹) * t ∈ M
        exact (show D ≤ M from inf_le_left) (by
          simpa [rightConjugateElem, ht.inv_eq_self, mul_assoc] using hprodD)
    · rintro ⟨hs, hstM⟩
      let m : X := s * t
      have hmt : rightConjugateElem m t = m⁻¹ := by
        have htt : t * t = 1 := by
          simpa [pow_two] using ht.sq_eq_one
        simp [m, rightConjugateElem, ht.inv_eq_self, hs.inv_eq_self,
          mul_assoc, htt]
      have hmConjInv : m⁻¹ ∈ rightConjugate M t := by
        rw [← hmt]
        exact rightConjugateElem_mem_rightConjugate hstM
      have hmConj : m ∈ rightConjugate M t := by
        have := (rightConjugate M t).inv_mem hmConjInv
        simpa using this
      have hmD : m ∈ D := ⟨hstM, hmConj⟩
      let mD : D := ⟨m, hmD⟩
      have hmOrderOddSubtype : Odd (orderOf mD) :=
        Odd.of_dvd_nat hDodd (orderOf_dvd_natCard mD)
      have hmOrderOdd : Odd (orderOf m) := by
        simpa [mD, Subgroup.orderOf_coe] using hmOrderOddSubtype
      obtain ⟨g, hgpow, hsg⟩ :=
        exists_zpowers_conjugator_of_odd_product hs ht
          (by simpa [m] using hmOrderOdd)
      have hgD : g ∈ D := (Subgroup.zpowers_le.mpr hmD) hgpow
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨g, hgD⟩, ?_⟩
      change g * t * g⁻¹ = s
      rw [← hsg]
      simp [rightConjugateElem, mul_assoc]
  have hcardOrbits :
      Nat.card (MulAction.orbit D t) = Nat.card (MulAction.orbit D z) := by
    calc
      Nat.card (MulAction.orbit D t) =
          Nat.card (involutionsInRightCoset M t) :=
        Nat.card_congr (Set.equivOfEq horbitT)
      _ = Nat.card (involutionsInSubgroup M) :=
        Nat.card_congr
          (involutionsInRightCosetEquivInvolutionsIn hM hzM hz ht htM)
      _ = Nat.card (MulAction.orbit D z) :=
        (Nat.card_congr (Set.equivOfEq horbitZ)).symm
  have hstabCard (a : X) :
      Nat.card (MulAction.stabilizer D a) =
        Nat.card (D ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) := by
    let e : MulAction.stabilizer D a ≃
        (D ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) :=
      { toFun := fun d => by
          refine ⟨(d : X), d.1.property, ?_⟩
          change (d : X) ∈ Subgroup.centralizer ({a} : Set X)
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hd : (d : X) * a * (d : X)⁻¹ = a := d.property
          calc
            (d : X) * a = ((d : X) * a * (d : X)⁻¹) * (d : X) := by
              group
            _ = a * (d : X) := by rw [hd]
        invFun := fun d => by
          refine ⟨⟨(d : X), d.property.1⟩, ?_⟩
          rw [MulAction.mem_stabilizer_iff]
          have hcomm : (d : X) * a = a * (d : X) :=
            Subgroup.mem_centralizer_singleton_iff.mp d.property.2
          change (d : X) * a * (d : X)⁻¹ = a
          calc
            (d : X) * a * (d : X)⁻¹ =
                (a * (d : X)) * (d : X)⁻¹ := by rw [hcomm]
            _ = a := by group
        left_inv := by intro d; ext; rfl
        right_inv := by intro d; ext; rfl }
    exact Nat.card_congr e
  have htOrbitStabilizer :
      Nat.card (MulAction.orbit D t) *
          Nat.card (MulAction.stabilizer D t) = Nat.card D := by
    simpa [Nat.card_prod] using
      Nat.card_congr
        (MulAction.orbitProdStabilizerEquivGroup D t)
  have hzOrbitStabilizer :
      Nat.card (MulAction.orbit D z) *
          Nat.card (MulAction.stabilizer D z) = Nat.card D := by
    simpa [Nat.card_prod] using
      Nat.card_congr
        (MulAction.orbitProdStabilizerEquivGroup D z)
  have hmul :
      Nat.card (MulAction.orbit D t) *
          Nat.card (D ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) =
        Nat.card (MulAction.orbit D t) *
          Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) := by
    calc
      Nat.card (MulAction.orbit D t) *
          Nat.card (D ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) =
          Nat.card D := by rw [← hstabCard t]; exact htOrbitStabilizer
      _ = Nat.card (MulAction.orbit D z) *
          Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) := by
            rw [← hstabCard z]
            exact hzOrbitStabilizer.symm
      _ = Nat.card (MulAction.orbit D t) *
          Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) := by
            rw [hcardOrbits]
  let : Nonempty (MulAction.orbit D t) :=
    ⟨⟨t, MulAction.mem_orbit_self t⟩⟩
  have hOrbitPos : 0 < Nat.card (MulAction.orbit D t) := Nat.card_pos
  exact Nat.mul_left_cancel hOrbitPos hmul

end IsStronglyEmbedded
end CFSG.BenderSuzuki
