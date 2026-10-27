module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedSetCardSmall
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixFiberSplit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetPairLocal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedElementsLeInfConjugate
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
# Per-coset commuting-pair distribution

For a non-base `Ĥ`-coset containing `n` involutions, the number of ordered
pairs of distinct commuting involutions inside the coset is

* `0` for `n = 0, 1, 3`;
* `2` for `n = 2`;
* `6` for `n = 4`.

The size-two and size-three cases are purely structural.  The size-four
case uses restriction (6): the selected commuting involution `s` and the
order-three inverted odd element `x` give the four fiber elements
`{y, s*y, x*y, x²*y}` (after choosing the representative with a
three-element odd-core fiber), and `s` inverts `x`, so the commuting
graph is the star centered at `s*y`.
-/

/-- The involutions in the right `Ĥ`-coset of `y`. -/
public abbrev cosetFiber {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (y : G) : Type u :=
  {z : G // IsInvolution z ∧
    cosetInvolution_proj c.Hhat z = cosetInvolution_proj c.Hhat y}

/-- Ordered commuting pairs of distinct involutions in the same
non-base coset fiber. -/
public abbrev cosetCommPair {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (y : G) : Type u :=
  {p : cosetFiber c y × cosetFiber c y //
    p.1 ≠ p.2 ∧ Commute (p.1.1 : G) (p.2.1 : G)}

/-- The coset fiber over an outside involution is in bijection with the
inverted set `I_Ĥ(y)`, via `z ↦ z * y⁻¹` / `i ↦ i * y`. -/
public def cosetFiber_equiv_inverted
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) {y : G}
    (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    cosetFiber c y ≃ {x : G // x ∈ invertedElements c.Hhat y} where
  toFun := fun z => ⟨z.1 * y⁻¹, by
    refine ⟨?_, ?_⟩
    · have hcos : cosetInvolution_proj c.Hhat z.1 = cosetInvolution_proj c.Hhat y := z.2.2
      change QuotientGroup.mk (z.1⁻¹) = QuotientGroup.mk (y⁻¹) at hcos
      have hmem := (QuotientGroup.eq (s := c.Hhat)).mp hcos
      simpa using hmem
    · have hzI : IsInvolution ((z.1 * y⁻¹) * y) := by
        convert z.2.1 using 1
        group
      have h14 := (fact_1_4_involution_mul hy).1 hzI
      have hyy : y * y = 1 := by simpa [pow_two] using hy.2
      have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
      simpa [hyInv] using h14.2⟩
  invFun := fun i => ⟨i.1 * y, by
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hiy
      apply hyH
      rw [← hiy]
      exact i.2.1
    · have hyy : y * y = 1 := by simpa [pow_two] using hy.2
      have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
      simpa [hyInv] using i.2.2
    , by
      change QuotientGroup.mk ((i.1 * y)⁻¹) = QuotientGroup.mk (y⁻¹)
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have heq : ((i.1 * y)⁻¹)⁻¹ * y⁻¹ = i.1 := by
        calc
          ((i.1 * y)⁻¹)⁻¹ * y⁻¹ = (i.1 * y) * y⁻¹ := by rw [inv_inv]
          _ = i.1 := by group
      rw [heq]
      exact i.2.1⟩
  left_inv := by
    intro z
    apply Subtype.ext
    group
  right_inv := by
    intro i
    apply Subtype.ext
    group

/-- A size-two coset fiber contributes exactly two ordered commuting
pairs: the two involutions commute with each other. -/
public theorem coset_pair_card_two
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hcard : Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 2) :
    Nat.card (cosetCommPair c y) = 2 := by
  classical
  let I : Type u := {x : G // x ∈ invertedElements c.Hhat y}
  have honeI : (1 : G) ∈ invertedElements c.Hhat y := ⟨c.Hhat.one_mem, by simp⟩
  let a0 : I := ⟨1, honeI⟩
  obtain ⟨tI, htIne, htAll⟩ := (Nat.card_eq_two_iff' a0).1 hcard
  let t : G := tI.1
  have htI : t ∈ invertedElements c.Hhat y := tI.2
  have htne : t ≠ 1 := by
    intro h
    apply htIne
    apply Subtype.ext
    exact h
  have ht2 : t * t = 1 := inverted_card_two_mul_self c.Hhat hy htI hcard
  have hyy : y * y = 1 := by simpa [pow_two] using hy.2
  have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
  have hyt : y * t * y = t⁻¹ := by simpa [hyInv] using htI.2
  have htInv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right ht2).symm
  let yF : cosetFiber c y := ⟨y, hy, rfl⟩
  let tF : cosetFiber c y := ⟨t * y, by
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hty
      apply hyH
      rw [← hty]
      exact htI.1
    · simpa [hyInv] using htI.2
    , by
      rw [cosetInvolution_proj, cosetInvolution_proj]
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have heq : ((t * y)⁻¹)⁻¹ * y⁻¹ = t := by
        calc
          ((t * y)⁻¹)⁻¹ * y⁻¹ = (t * y) * y⁻¹ := by rw [inv_inv]
          _ = t := by group
      rw [heq]
      exact htI.1⟩
  let P : Type u := cosetCommPair c y
  let p0 : P := ⟨(yF, tF), by
    intro h
    apply htne
    have hVal : (y : G) = t * y := congrArg Subtype.val h
    calc
      t = (t * y) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [← hVal]
      _ = 1 := by simp
    , by
      change y * (t * y) = (t * y) * y
      calc
        y * (t * y) = (y * t) * y := by rw [mul_assoc]
        _ = t⁻¹ := hyt
        _ = t := htInv
        _ = (t * y) * y := by
          symm
          calc
            (t * y) * y = t * (y * y) := by rw [mul_assoc]
            _ = t := by rw [hyy]; simp⟩
  let p1 : P := ⟨(tF, yF), by
    intro h
    apply p0.2.1
    exact h.symm
    , by
      change (t * y) * y = y * (t * y)
      exact (p0.2.2.symm.eq)⟩
  let eF : cosetFiber c y ≃ I := cosetFiber_equiv_inverted c hy hyH
  have hclass : ∀ z : cosetFiber c y, z = yF ∨ z = tF := by
    intro z
    have h_yF : eF yF = a0 := by
      simp [eF, cosetFiber_equiv_inverted, yF, a0, I]
    have h_tF : eF tF = tI := by
      simp [eF, cosetFiber_equiv_inverted, tF, t, I]
    by_cases hz0 : eF z = a0
    · left
      exact eF.injective (hz0.trans h_yF.symm)
    · right
      have hzt : eF z = tI := htAll (eF z) hz0
      exact eF.injective (hzt.trans h_tF.symm)
  have hall : ∀ p : P, p = p0 ∨ p = p1 := by
    intro p
    rcases hclass p.1.1 with h1 | h1
    · rcases hclass p.1.2 with h2 | h2
      · -- both `yF`: contradicts `p.1 ≠ p.2`
        exfalso
        apply p.2.1
        rw [h1, h2]
      · left
        -- `(yF, tF)`
        apply Subtype.ext
        apply Prod.ext h1 h2
    · rcases hclass p.1.2 with h2 | h2
      · right
        apply Subtype.ext
        apply Prod.ext h1 h2
      · exfalso
        apply p.2.1
        rw [h1, h2]
  apply (Nat.card_eq_two_iff' p0).2
  refine ⟨p1, ?_, ?_⟩
  intro h
  apply p0.2.1
  have hPair : (p1 : P).1 = p0.1 := congrArg (fun q : P => q.1) h
  exact (Prod.ext_iff.mp hPair).1.symm
  intro y hy
  rcases hall y with h | h
  · exact False.elim (hy h)
  · exact h

/-- A size-three coset fiber contains no commuting pair of distinct
involutions. -/
public theorem coset_pair_card_three_zero
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hcard : Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 3) :
    Nat.card (cosetCommPair c y) = 0 := by
  classical
  let eF : cosetFiber c y ≃ {x : G // x ∈ invertedElements c.Hhat y} :=
    cosetFiber_equiv_inverted c hy hyH
  have : IsEmpty (cosetCommPair c y) := by
    refine ⟨fun p => ?_⟩
    let z1 : cosetFiber c y := p.1.1
    let z2 : cosetFiber c y := p.1.2
    let i1 : G := (eF z1).1
    let i2 : G := (eF z2).1
    have hi1 : i1 ∈ invertedElements c.Hhat y := (eF z1).2
    have hi2 : i2 ∈ invertedElements c.Hhat y := (eF z2).2
    have hz1 : (z1 : G) = i1 * y := by
      simp [i1, eF, cosetFiber_equiv_inverted]
    have hz2 : (z2 : G) = i2 * y := by
      simp [i2, eF, cosetFiber_equiv_inverted]
    have hine : i1 ≠ i2 := by
      intro h
      apply p.2.1
      apply Subtype.ext
      calc
        (z1 : G) = i1 * y := hz1
        _ = i2 * y := by rw [h]
        _ = (z2 : G) := hz2.symm
    have hcomm : Commute (i1 * y) (i2 * y) := by
      simpa [hz1, hz2, z1, z2] using p.2.2
    exact inverted_card_three_no_commuting_fiber_pair
      c.Hhat hy hyH hcard i1 i2 hi1 hi2 hine hcomm
  exact (Nat.card_eq_zero.2 (Or.inl inferInstance))

/-- Transport a commuting-pair count along an equality of coset
projections. -/
public def cosetCommPair_congr {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {y w : G}
    (hcos : cosetInvolution_proj c.Hhat w = cosetInvolution_proj c.Hhat y) :
    cosetCommPair c w ≃ cosetCommPair c y where
  toFun := fun p =>
    ⟨(⟨p.1.1.1, p.1.1.2.1, by rw [← hcos]; exact p.1.1.2.2⟩,
      ⟨p.1.2.1, p.1.2.2.1, by rw [← hcos]; exact p.1.2.2.2⟩),
      ⟨by
        intro h
        apply p.2.1
        apply Subtype.ext
        simpa using congrArg (fun z : cosetFiber c y => (z : G)) h,
        by simpa using p.2.2⟩⟩
  invFun := fun p =>
    ⟨(⟨p.1.1.1, p.1.1.2.1, by rw [hcos]; exact p.1.1.2.2⟩,
      ⟨p.1.2.1, p.1.2.2.1, by rw [hcos]; exact p.1.2.2.2⟩),
      ⟨by
        intro h
        apply p.2.1
        apply Subtype.ext
        simpa using congrArg (fun z : cosetFiber c w => (z : G)) h,
        by simpa using p.2.2⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- The size-four local pair count: with the selected representative `y`
whose odd-core fiber has size three, the four fiber elements are
`{y, s*y, x*y, x²*y}` and `s` inverts `x`, so the commuting graph is a
star centered at `s*y` with six ordered pairs. -/
private theorem coset_pair_card_four_of_odd_fiber
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y s x : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hcard : Nat.card {z : G // z ∈ invertedElements c.Hhat y} = 4)
    (hsI : IsInvolution s) (hsD : s ∈ c.Hhat ⊓ conjugateSubgroup c.Hhat y)
    (hsy : s * y = y * s)
    (hxO : x ∈ oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G))
    (hxne : x ≠ 1) (hxord : orderOf x = 3)
    (hxinv : x ∈ invertedElements
      (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y) :
    Nat.card (cosetCommPair c y) = 6 := by
  classical
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let N : Subgroup G := D ⊓ B
  let O : Subgroup G := oddCoreOf D
  have hOleD : O ≤ D := Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
  have hidx : (N.subgroupOf D).index = 6 := by
    simpa [D, N, B] using firstCase_klein_restrictionSix_index_eq
      hmin c hfirst hklein hy hyH (by omega)
  have hOidx : (O.subgroupOf D).index = 2 := by
    simpa [D, O] using firstCase_klein_intersection_oddCore_index_two_of_index_six
      hmin c hfirst hklein hy hyH hidx
  have hOodd : Nat.Coprime 2 (Nat.card O) := by
    exact Nat.coprime_two_left.mpr (odd_card_oddCoreOf D)
  have hIeqD : Nat.card {z : G // z ∈ invertedElements c.Hhat y} =
      Nat.card {z : G // z ∈ invertedElements D y} := by
    let f : {z : G // z ∈ invertedElements c.Hhat y} →
        {z : G // z ∈ invertedElements D y} := fun z =>
      ⟨z.1, ⟨invertedElements_subset_inf_conjugateSubgroup c.Hhat y z.2, z.2.2⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        have hval : (f a).1 = (f b).1 := congrArg Subtype.val h
        apply Subtype.ext
        simpa [f] using hval
      · intro z
        exact ⟨⟨z.1, ⟨(show z.1 ∈ c.Hhat from (inf_le_left : D ≤ c.Hhat) z.2.1),
          z.2.2⟩⟩, rfl⟩
    exact Nat.card_congr (Equiv.ofBijective f hf)
  have hsplit := firstCase_klein_restrictionSix_fiber_card_split D O hOleD hOidx
    hOodd hy hsI hsD hsy
  have hmemSplit := firstCase_klein_restrictionSix_fiber_mem_split D O hOleD hOidx
    hOodd hy hsI hsD hsy
  have hYne1 : Nat.card {z : G // z ∈ invertedElements O y} ≠ 1 := by
    intro hY1
    obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists).mp hY1
    have honeO : (1 : G) ∈ invertedElements O y := ⟨O.one_mem, by simp⟩
    have h1eq : (⟨1, honeO⟩ : {z : G // z ∈ invertedElements O y}) = z0 := hz0 _
    have hxeq : (⟨x, hxinv⟩ : {z : G // z ∈ invertedElements O y}) = z0 := hz0 _
    exact hxne (congrArg Subtype.val (hxeq.trans h1eq.symm))
  have hYcard : Nat.card {z : G // z ∈ invertedElements O y} = 3 :=
    firstCase_klein_oddCore_inverted_card_three hmin c hfirst hklein hy hyH hidx hYne1
  have hSYcard1 : Nat.card {z : G // z ∈ invertedElements O (s * y)} = 1 := by
    have hD4 : Nat.card {z : G // z ∈ invertedElements D y} = 4 := by
      rw [← hIeqD]
      exact hcard
    have hsum : Nat.card {z : G // z ∈ invertedElements O y} +
        Nat.card {z : G // z ∈ invertedElements O (s * y)} = 4 := by
      rw [← hsplit]
      exact hD4
    omega
  have hSYeq : ∀ z : G, z ∈ invertedElements O (s * y) → z = 1 := by
    intro z hz
    have honeSY : (1 : G) ∈ invertedElements O (s * y) := ⟨O.one_mem, by simp⟩
    obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists).mp hSYcard1
    have hz1 : (⟨z, hz⟩ : {z : G // z ∈ invertedElements O (s * y)}) = z0 := hz0 _
    have h11 : (⟨1, honeSY⟩ : {z : G // z ∈ invertedElements O (s * y)}) = z0 := hz0 _
    exact congrArg Subtype.val (hz1.trans h11.symm)
  have hYset : (invertedElements O y : Set G).ncard = 3 := by
    simpa using hYcard
  have hx2O : x ^ 2 ∈ invertedElements O y := by
    refine ⟨O.pow_mem hxO 2, ?_⟩
    calc
      y * x ^ 2 * y⁻¹ = (y * x * y⁻¹) ^ 2 :=
        (conj_pow (a := y) (b := x) (i := 2)).symm
      _ = (x⁻¹) ^ 2 := by rw [hxinv.2]
      _ = (x ^ 2)⁻¹ := by exact inv_pow (a := x) (n := 2)
  have hxne2 : x ^ 2 ≠ 1 := by
    intro h
    have hord' : orderOf (x ^ 2) = 1 := by rw [h, orderOf_one]
    have hord'' : orderOf (x ^ 2) = 3 := by
      rw [orderOf_pow' (x := x) (n := 2) (by norm_num), hxord]
      norm_num
    omega
  have hx2x : x ^ 2 ≠ x := by
    intro h
    apply hxne
    calc
      x = x ^ 2 * x⁻¹ := by
        group
      _ = x * x⁻¹ := by rw [h]
      _ = 1 := by simp
  have hYcases : ∀ z : G, z ∈ invertedElements O y →
      z = 1 ∨ z = x ∨ z = x ^ 2 :=
    set_ncard_three_forall_mem_cases hYset
      (⟨O.one_mem, by simp⟩) hxinv hx2O
      (Ne.symm hxne) (Ne.symm hxne2) (Ne.symm hx2x)
  have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)
  have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
  have hords : orderOf s = 2 := by
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsI.2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact False.elim (hsI.1 (orderOf_eq_one_iff.mp h1))
    · exact h2
  have hx2ord : orderOf (x ^ 2) = 3 := by
    rw [orderOf_pow' (x := x) (n := 2) (by norm_num), hxord]
    norm_num
  have hsI_D : s ∈ invertedElements D y := by
    refine ⟨hsD, ?_⟩
    calc
      y * s * y⁻¹ = (s * y) * y⁻¹ := by rw [← hsy]
      _ = s := by simp [mul_assoc]
      _ = s⁻¹ := by rw [hss]
  have hIH_cases : ∀ i : G, i ∈ invertedElements c.Hhat y →
      i = 1 ∨ i = x ∨ i = x ^ 2 ∨ i = s := by
    intro i hi
    have hiD : i ∈ invertedElements D y :=
      ⟨invertedElements_subset_inf_conjugateSubgroup c.Hhat y hi, hi.2⟩
    rcases hmemSplit i hiD with hiO | hrest
    · rcases hYcases i hiO with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases hrest with ⟨z, hz, hiz⟩
      have hz1 : z = 1 := hSYeq z hz
      right; right; right
      calc
        i = s * z := hiz
        _ = s * 1 := by rw [hz1]
        _ = s := by simp
  have hys : y * s * y⁻¹ = s := by
    calc
      y * s * y⁻¹ = (s * y) * y⁻¹ := by rw [← hsy]
      _ = s := by simp [mul_assoc]
  have hysInv : y * s⁻¹ * y⁻¹ = s := by
    calc
      y * s⁻¹ * y⁻¹ = (y * s * y⁻¹)⁻¹ := by group
      _ = s⁻¹ := by rw [hys]
      _ = s := hss
  have hOnorm : ∀ d : G, d ∈ D → ∀ o : G, o ∈ O → d * o * d⁻¹ ∈ O := by
    intro d hd o ho
    change o ∈ (pPrimeCore 2 (↥D)).map D.subtype at ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    have hconj := (pPrimeCore_normal (p := 2) (G := ↥D)).conj_mem
      o0 ho0 (⟨d, hd⟩ : ↥D)
    exact Subgroup.mem_map.mpr ⟨⟨d, hd⟩ * o0 * (⟨d, hd⟩ : ↥D)⁻¹, hconj, by
      change d * (o0 : G) * d⁻¹ = d * (o0 : G) * d⁻¹
      rfl⟩
  have sxO : s * x * s⁻¹ ∈ O := hOnorm s hsD x hxO
  have sxInv : s * x * s⁻¹ ∈ invertedElements O y := by
    refine ⟨sxO, ?_⟩
    have hInv : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s := by
      calc
        (s * x * s⁻¹)⁻¹ = (s⁻¹)⁻¹ * (x⁻¹ * s⁻¹) := by
          rw [mul_inv_rev, mul_inv_rev]
        _ = s * (x⁻¹ * s) := by rw [inv_inv, hss]
        _ = s * x⁻¹ * s := by group
    calc
      y * (s * x * s⁻¹) * y⁻¹ =
          (y * s * y⁻¹) * (y * x * y⁻¹) * (y * s⁻¹ * y⁻¹) := by group
      _ = s * x⁻¹ * s := by rw [hxinv.2, hys, hysInv]
      _ = (s * x * s⁻¹)⁻¹ := by rw [hInv]
  have hCase := hYcases (s * x * s⁻¹) sxInv
  have hsInvX : s * x * s⁻¹ = x⁻¹ := by
    rcases hCase with h1 | hx' | hx2'
    · exfalso
      apply hxne
      calc
        x = s * (s * x * s⁻¹) * s := by
          rw [hss]
          have hstep : s * (s * x * s) * s = x := by
            calc
              s * (s * x * s) * s = (s * s) * x * (s * s) := by group
              _ = 1 * x * 1 := by rw [hs2]
              _ = x := by simp
          rw [hstep]
        _ = s * 1 * s := by rw [h1]
        _ = 1 := by simpa using hs2
    · exfalso
      have hComm : s * x = x * s := by
        calc
          s * x = (s * x * s⁻¹) * s := by group
          _ = x * s := by rw [hx']
      have hsxI : s * x ∈ invertedElements D y := by
        refine ⟨D.mul_mem hsD (hOleD hxO), ?_⟩
        calc
          y * (s * x) * y⁻¹ = (y * s * y⁻¹) * (y * x * y⁻¹) := by group
          _ = s * x⁻¹ := by rw [hys, hxinv.2]
          _ = (s * x)⁻¹ := by
            rw [mul_inv_rev]
            have hInvComm : x⁻¹ * s = s * x⁻¹ := by
              have hEqInv := congrArg (fun z : G => z⁻¹) hComm
              simpa [hss] using hEqInv
            rw [hss]
            exact hInvComm.symm
      have hsxIH : s * x ∈ invertedElements c.Hhat y :=
        ⟨(inf_le_left : D ≤ c.Hhat) hsxI.1, hsxI.2⟩
      rcases hIH_cases (s * x) hsxIH with h1' | hx'' | hx2'' | hs''
      · -- `s * x = 1` gives `x = s`, an order mismatch
        have hxs : x = s := by
          calc
            x = s⁻¹ * (s * x) := by group
            _ = s⁻¹ * 1 := by rw [h1']
            _ = s⁻¹ := by simp
            _ = s := hss
        rw [hxs] at hxord
        omega
      · -- `s * x = x` gives `s = 1`
        apply hsI.1
        calc
          s = (s * x) * x⁻¹ := by group
          _ = x * x⁻¹ := by rw [hx'']
          _ = 1 := by simp
      · -- `s * x = x²` gives `x = s`, an order mismatch
        have hxs : x = s := by
          calc
            x = (x ^ 2 * x⁻¹) := by group
            _ = (s * x) * x⁻¹ := by rw [← hx2'']
            _ = s := by group
        rw [hxs] at hxord
        omega
      · -- `s * x = s` gives `x = 1`
        apply hxne
        calc
          x = s⁻¹ * (s * x) := by group
          _ = s⁻¹ * s := by rw [hs'']
          _ = 1 := by simp
    · -- `s * x * s⁻¹ = x² = x⁻¹`: `s` inverts `x`
      have hxInvI : x⁻¹ = x ^ 2 := by
        exact (eq_inv_of_mul_eq_one_right (by
          calc
            x * x ^ 2 = x ^ 3 := by group
            _ = 1 := by
              rw [← hxord]
              exact pow_orderOf_eq_one x)).symm
      rwa [hxInvI]

  -- the four fiber elements
  let yF : cosetFiber c y := ⟨y, hy, rfl⟩
  let xF : cosetFiber c y := ⟨x * y, by
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hxy
      apply hyH
      rw [← hxy]
      exact (inf_le_left : D ≤ c.Hhat) (hOleD hxO)
    · have hyy : y * y = 1 := by simpa [pow_two] using hy.2
      have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
      simpa [hyInv] using hxinv.2
    , by
      change QuotientGroup.mk ((x * y)⁻¹) = QuotientGroup.mk (y⁻¹)
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have heq : ((x * y)⁻¹)⁻¹ * y⁻¹ = x := by
        calc
          ((x * y)⁻¹)⁻¹ * y⁻¹ = (x * y) * y⁻¹ := by rw [inv_inv]
          _ = x := by group
      rw [heq]
      exact (inf_le_left : D ≤ c.Hhat) (hOleD hxO)⟩
  let x2F : cosetFiber c y := ⟨x ^ 2 * y, by
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hx2y
      apply hyH
      rw [← hx2y]
      exact (inf_le_left : D ≤ c.Hhat) (hOleD (O.pow_mem hxO 2))
    · have hyy : y * y = 1 := by simpa [pow_two] using hy.2
      have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
      have hx2inv : x ^ 2 ∈ invertedElements O y := hx2O
      simpa [hyInv] using hx2inv.2
    , by
      change QuotientGroup.mk ((x ^ 2 * y)⁻¹) = QuotientGroup.mk (y⁻¹)
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have heq : ((x ^ 2 * y)⁻¹)⁻¹ * y⁻¹ = x ^ 2 := by
        calc
          ((x ^ 2 * y)⁻¹)⁻¹ * y⁻¹ = (x ^ 2 * y) * y⁻¹ := by rw [inv_inv]
          _ = x ^ 2 := by group
      rw [heq]
      exact (inf_le_left : D ≤ c.Hhat) (hOleD (O.pow_mem hxO 2))⟩
  let sF : cosetFiber c y := ⟨s * y, by
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hsy'
      apply hyH
      rw [← hsy']
      exact hsD.1
    · have hyy : y * y = 1 := by simpa [pow_two] using hy.2
      have hyInv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hyy).symm
      simpa [hyInv] using hsI_D.2
    , by
      change QuotientGroup.mk ((s * y)⁻¹) = QuotientGroup.mk (y⁻¹)
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have heq : ((s * y)⁻¹)⁻¹ * y⁻¹ = s := by
        calc
          ((s * y)⁻¹)⁻¹ * y⁻¹ = (s * y) * y⁻¹ := by rw [inv_inv]
          _ = s := by group
      rw [heq]
      exact hsD.1⟩
  let eF : cosetFiber c y ≃ {z : G // z ∈ invertedElements c.Hhat y} :=
    cosetFiber_equiv_inverted c hy hyH
  let a0 : {z : G // z ∈ invertedElements c.Hhat y} :=
    ⟨1, c.Hhat.one_mem, by simp⟩
  have honeIH : (1 : G) ∈ invertedElements c.Hhat y :=
    ⟨c.Hhat.one_mem, by simp⟩
  have hxIH : x ∈ invertedElements c.Hhat y :=
    ⟨(inf_le_left : D ≤ c.Hhat) (hOleD hxO), hxinv.2⟩
  have hx2IH : x ^ 2 ∈ invertedElements c.Hhat y :=
    ⟨(inf_le_left : D ≤ c.Hhat) (hOleD (O.pow_mem hxO 2)), hx2O.2⟩
  have hsIH : s ∈ invertedElements c.Hhat y :=
    ⟨(inf_le_left : D ≤ c.Hhat) hsD, hsI_D.2⟩
  have h_yF : eF yF = a0 := by
    apply Subtype.ext
    change y * y⁻¹ = (1 : G)
    simp
  have h_xF : eF xF = ⟨x, hxIH⟩ := by
    apply Subtype.ext
    change (x * y) * y⁻¹ = x
    group
  have h_x2F : eF x2F = ⟨x ^ 2, hx2IH⟩ := by
    apply Subtype.ext
    change (x ^ 2 * y) * y⁻¹ = x ^ 2
    group
  have h_sF : eF sF = ⟨s, hsIH⟩ := by
    apply Subtype.ext
    change (s * y) * y⁻¹ = s
    group
  have hfour : ∀ z : cosetFiber c y, z = yF ∨ z = xF ∨ z = x2F ∨ z = sF := by
    intro z
    rcases hIH_cases (eF z).1 (eF z).2 with h | h | h | h
    · left
      exact eF.injective (by
        apply Subtype.ext
        exact h.trans (congrArg Subtype.val h_yF).symm)
    · right; left
      exact eF.injective (by
        apply Subtype.ext
        exact h.trans (congrArg Subtype.val h_xF).symm)
    · right; right; left
      exact eF.injective (by
        apply Subtype.ext
        exact h.trans (congrArg Subtype.val h_x2F).symm)
    · right; right; right
      exact eF.injective (by
        apply Subtype.ext
        exact h.trans (congrArg Subtype.val h_sF).symm)

  -- `s` commutes with every non-`s` fiber element
  have hxInvI : x⁻¹ = x ^ 2 := by
    exact (eq_inv_of_mul_eq_one_right (by
      calc
        x * x ^ 2 = x ^ 3 := by group
        _ = 1 := by
          rw [← hxord]
          exact pow_orderOf_eq_one x)).symm
  have hx2InvI : (x ^ 2)⁻¹ = x := by
    have hEq : x ^ 2 = x⁻¹ := eq_inv_of_mul_eq_one_left (by
      calc
        x ^ 2 * x = x ^ 3 := by group
        _ = 1 := by
          rw [← hxord]
          exact pow_orderOf_eq_one x)
    have h1 : (x ^ 2)⁻¹ = (x⁻¹)⁻¹ := by rw [hEq]
    exact h1.trans (inv_inv x)
  have hsxInvS : s * x * s = x⁻¹ := by
    simpa [hss] using hsInvX
  have hsxInv : s * x⁻¹ * s = x := by
    calc
      s * x⁻¹ * s = (s * x * s)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev]
        rw [hss]
        group
      _ = (x⁻¹)⁻¹ := by rw [hsxInvS]
      _ = x := by simp
  have hsx_sq : (s * x⁻¹) * (s * x⁻¹) = 1 := by
    calc
      (s * x⁻¹) * (s * x⁻¹) = (s * x⁻¹ * s) * x⁻¹ := by group
      _ = x * x⁻¹ := by rw [hsxInv]
      _ = 1 := by simp
  have hsx2_sq : (s * x) * (s * x) = 1 := by
    calc
      (s * x) * (s * x) = (s * x * s) * x := by group
      _ = x⁻¹ * x := by rw [hsxInvS]
      _ = 1 := by simp
  have hcomm_s : ∀ z : cosetFiber c y, z ≠ sF → Commute (sF.1) (z.1) := by
    intro z hz
    rcases hfour z with hzy | hzx | hzx2 | hzs
    · subst z
      -- `sF` and `yF`: `s * 1⁻¹ = s` is an involution
      have hI : IsInvolution (s * 1⁻¹) := by
        refine ⟨?_, ?_⟩
        · simpa using hsI.1
        · simpa using hsI.2
      have hcomm : Commute (s * y) (1 * y) :=
        (@commute_external_involutions_iff_involution_difference G _ c.Hhat y s 1 hy
          hsIH.1 (show (1 : G) ∈ c.Hhat from c.Hhat.one_mem)
          hsIH.2 (by simp) (by
            intro h
            apply hsI.1
            exact h)).2 hI
      simpa using hcomm
    · -- `sF` and `xF`
      subst z
      have hI : IsInvolution (s * x⁻¹) := by
        refine ⟨?_, ?_⟩
        · intro h
          -- `s * x⁻¹ = 1` gives `x = s`, an order mismatch
          have hxs : x = s := by
            calc
              x = 1 * x := by simp
              _ = (s * x⁻¹) * x := by rw [← h]
              _ = s := by rw [mul_assoc]; simp
          rw [hxs] at hxord
          omega
        · rw [pow_two]
          exact hsx_sq
      exact (@commute_external_involutions_iff_involution_difference G _ c.Hhat y s x hy
        hsIH.1 hxIH.1 hsIH.2 hxIH.2 (by
          intro h
          rw [← h] at hxord
          omega)).2 hI
    · -- `sF` and `x2F`
      subst z
      have hI : IsInvolution (s * (x ^ 2)⁻¹) := by
        refine ⟨?_, ?_⟩
        · intro h
          have h' : s * x = 1 := by
            calc
              s * x = s * (x ^ 2)⁻¹ := by rw [hx2InvI]
              _ = 1 := h
          have hxs : x = s := by
            calc
              x = s⁻¹ * (s * x) := by group
              _ = s⁻¹ * 1 := by rw [h']
              _ = s⁻¹ := by simp
              _ = s := hss
          rw [hxs] at hxord
          omega
        · rw [pow_two]
          calc
            (s * (x ^ 2)⁻¹) * (s * (x ^ 2)⁻¹) = (s * x) * (s * x) := by rw [hx2InvI]
            _ = 1 := hsx2_sq
      exact (@commute_external_involutions_iff_involution_difference G _ c.Hhat y s (x ^ 2) hy
        hsIH.1 hx2IH.1 hsIH.2 hx2IH.2 (by
          intro h
          rw [← h] at hx2ord
          omega)).2 hI
    · subst z
      exact False.elim (hz rfl)

  -- no two non-`s` fiber elements commute
  have hdiff3 : ∀ a b : G,
      a = 1 ∨ a = x ∨ a = x ^ 2 →
      b = 1 ∨ b = x ∨ b = x ^ 2 →
      a ≠ b → orderOf (a * b⁻¹) = 3 := by
    intro a b ha hb hab
    rcases ha with ha1 | hax | hax2
    · subst a
      rcases hb with hb1 | hbx | hbx2
      · subst b
        contradiction
      · subst b
        calc
          orderOf (1 * x⁻¹) = orderOf (x ^ 2) := by rw [hxInvI]; simp
          _ = 3 := by
            rw [orderOf_pow' (x := x) (n := 2) (by norm_num), hxord]
            norm_num
      · subst b
        calc
          orderOf (1 * (x ^ 2)⁻¹) = orderOf x := by rw [hx2InvI]; simp
          _ = 3 := hxord
    · subst a
      rcases hb with hb1 | hbx | hbx2
      · subst b
        calc
          orderOf (x * 1⁻¹) = orderOf x := by simp
          _ = 3 := hxord
      · subst b
        contradiction
      · subst b
        calc
          orderOf (x * (x ^ 2)⁻¹) = orderOf (x * x) := by rw [hx2InvI]
          _ = orderOf (x ^ 2) := by
            rw [← pow_two]
          _ = 3 := by
            rw [orderOf_pow' (x := x) (n := 2) (by norm_num), hxord]
            norm_num
    · subst a
      rcases hb with hb1 | hbx | hbx2
      · subst b
        calc
          orderOf ((x ^ 2) * 1⁻¹) = orderOf (x ^ 2) := by simp
          _ = 3 := by
            rw [orderOf_pow' (x := x) (n := 2) (by norm_num), hxord]
            norm_num
      · subst b
        calc
          orderOf ((x ^ 2) * x⁻¹) = orderOf (x ^ 2 * x ^ 2) := by rw [hxInvI]
          _ = orderOf (x ^ 4) := by
            rw [← pow_add (n := 2) (m := 2)]
          _ = orderOf x := by
            rw [show x ^ 4 = x by
              calc
                x ^ 4 = x ^ (3 + 1) := by norm_num
                _ = x ^ 3 * x := by
                  rw [pow_add]
                  simp
                _ = x := by
                  rw [show x ^ 3 = 1 by
                    rw [← hxord]
                    exact pow_orderOf_eq_one x]
                  simp]
          _ = 3 := hxord
      · subst b
        contradiction
  have hnoInv : ∀ a b : G,
      a ∈ invertedElements c.Hhat y → b ∈ invertedElements c.Hhat y →
      a ≠ b →
      a = 1 ∨ a = x ∨ a = x ^ 2 →
      b = 1 ∨ b = x ∨ b = x ^ 2 →
      ¬ Commute (a * y) (b * y) := by
    intro a b ha hb hab ha1 hb1 hcomm
    have hI := (commute_external_involutions_iff_involution_difference c.Hhat hy
      ha.1 hb.1 ha.2 hb.2 hab).1 hcomm
    have hord3 : orderOf (a * b⁻¹) = 3 := hdiff3 a b ha1 hb1 hab
    have hne1 : a * b⁻¹ ≠ 1 := by
      intro h
      apply hab
      calc
        a = (a * b⁻¹) * b := by group
        _ = 1 * b := by rw [h]
        _ = b := by simp
    have hord2 : orderOf (a * b⁻¹) = 2 := by
      have hdvd : orderOf (a * b⁻¹) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hI.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact False.elim (hne1 (orderOf_eq_one_iff.mp h1))
      · exact h2
    omega
  have hno_sF : ∀ z1 z2 : cosetFiber c y,
      z1 ≠ sF → z2 ≠ sF → z1 ≠ z2 → ¬ Commute (z1.1) (z2.1) := by
    intro z1 z2 h1 h2 hne
    rcases hfour z1 with hz1 | hz1 | hz1 | hz1
    · subst z1
      rcases hfour z2 with hz2 | hz2 | hz2 | hz2
      · subst z2
        exact False.elim (hne rfl)
      · subst z2
        simpa using hnoInv 1 x honeIH hxIH (by intro h; exact hxne h.symm)
          (Or.inl rfl) (Or.inr (Or.inl rfl))
      · subst z2
        simpa using hnoInv 1 (x ^ 2) honeIH hx2IH (by intro h; exact hxne2 h.symm)
          (Or.inl rfl) (Or.inr (Or.inr rfl))
      · subst z2
        exact False.elim (h2 rfl)
    · subst z1
      rcases hfour z2 with hz2 | hz2 | hz2 | hz2
      · subst z2
        intro hcomm
        exact (hnoInv x 1 hxIH honeIH (by intro h; exact hxne h)
          (Or.inr (Or.inl rfl)) (Or.inl rfl)) (by simpa using hcomm)
      · subst z2
        exact False.elim (hne rfl)
      · subst z2
        exact hnoInv x (x ^ 2) hxIH hx2IH (by intro h; exact hx2x h.symm)
          (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      · subst z2
        exact False.elim (h2 rfl)
    · subst z1
      rcases hfour z2 with hz2 | hz2 | hz2 | hz2
      · subst z2
        intro hcomm
        exact (hnoInv (x ^ 2) 1 hx2IH honeIH (by intro h; exact hxne2 h)
          (Or.inr (Or.inr rfl)) (Or.inl rfl)) (by simpa using hcomm)
      · subst z2
        exact hnoInv (x ^ 2) x hx2IH hxIH hx2x
          (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      · subst z2
        exact False.elim (hne rfl)
      · subst z2
        exact False.elim (h2 rfl)
    · subst z1
      exact False.elim (h1 rfl)
  have hstar : ∀ p : cosetCommPair c y, p.1.1 = sF ∨ p.1.2 = sF := by
    intro p
    by_cases h1 : p.1.1 = sF
    · exact Or.inl h1
    · right
      by_contra h2
      apply (hno_sF p.1.1 p.1.2 h1 h2 p.2.1) p.2.2

  -- count: pairs are exactly `(sF, leaf)` and `(leaf, sF)`
  let Leaf : Type u := {z : cosetFiber c y // z ≠ sF}
  let E : cosetCommPair c y ≃ (Bool × Leaf) :=
    { toFun := fun p => if h1 : p.1.1 = sF then
          (true, ⟨p.1.2, by
            intro h
            apply p.2.1
            rw [h1, h]⟩)
        else
          (false, ⟨p.1.1, by
            intro h
            apply p.2.1
            rw [(hstar p).resolve_left h1, h]⟩)
      invFun := fun q => if hq : q.1 = true then
          ⟨(sF, q.2.1), ⟨(by intro h; exact q.2.2 h.symm),
            hcomm_s q.2.1 q.2.2⟩⟩
        else
          ⟨(q.2.1, sF), ⟨q.2.2, (hcomm_s q.2.1 q.2.2).symm⟩⟩
      left_inv := by
        intro p
        rcases p with ⟨⟨a, b⟩, hp⟩
        by_cases h1 : a = sF
        · apply Subtype.ext
          simp [h1]
        · have h2 : b = sF := (hstar ⟨⟨a, b⟩, hp⟩).resolve_left h1
          apply Subtype.ext
          simp [h1]
          rw [h2]
      right_inv := by
        intro q
        cases hq : q.1 with
        | true =>
            simp [hq]
            rw [← hq]
        | false =>
            by_cases h : q.2.1 = sF
            · exfalso
              exact q.2.2 h
            · simp [hq, h]
              rw [← hq]
              }
  have hFib : Nat.card (cosetFiber c y) = 4 :=
    (Nat.card_congr eF).trans hcard
  have hOne : Nat.card {z : cosetFiber c y // z = sF} = 1 := by
    let e : {z : cosetFiber c y // z = sF} ≃ PUnit.{u} :=
      { toFun := fun z => PUnit.unit
        invFun := fun _ => ⟨sF, rfl⟩
        left_inv := by
          intro z
          apply Subtype.ext
          exact z.2.symm
        right_inv := by intro z; cases z; rfl }
    simpa using (Nat.card_congr e)
  have hLeaf : Nat.card Leaf = 3 := by
    let : Fintype (cosetFiber c y) := Fintype.ofFinite _
    let : Fintype Leaf := Fintype.ofFinite _
    have hcompl := Fintype.card_subtype_compl (α := cosetFiber c y)
      (p := fun z : cosetFiber c y => z = sF)
    have hnat : Nat.card Leaf = Nat.card (cosetFiber c y) -
        Nat.card {z : cosetFiber c y // z = sF} := by
      simpa [Leaf, Nat.card_eq_fintype_card] using hcompl
    rw [hnat, hFib, hOne]
  calc
    Nat.card (cosetCommPair c y) = Nat.card (Bool × Leaf) := Nat.card_congr E
    _ = Nat.card Bool * Nat.card Leaf := Nat.card_prod _ _
    _ = 2 * 3 := by rw [hLeaf]; norm_num
    _ = 6 := by norm_num

/-- The per-coset commuting-pair distribution: a non-base `Ĥ`-coset
containing `n` involutions contributes `2` ordered commuting pairs when
`n = 2`, `6` when `n = 4`, and none otherwise (fibres are bounded by
restriction (7) through `hbound`). -/
public theorem firstCase_klein_coset_pair_card_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hbound : Nat.card {x : G // x ∈ invertedElements c.Hhat y} ≤ 4) :
    Nat.card (cosetCommPair c y) =
      if Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 2 then 2
      else if Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 4 then 6
      else 0 := by
  classical
  let n : ℕ := Nat.card {x : G // x ∈ invertedElements c.Hhat y}
  have hn : n = Nat.card {x : G // x ∈ invertedElements c.Hhat y} := rfl
  have hbn : n ≤ 4 := by simpa [n] using hbound
  by_cases h2 : n = 2
  · rw [← hn, h2]
    simp [h2]
    exact coset_pair_card_two c hy hyH (by simpa [n] using h2)
  · by_cases h4 : n = 4
    · rw [← hn, h4]
      simp [h2, h4]
      have hge : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
        omega
      obtain ⟨s, x, hsI, hsD, hsy, hfib⟩ :=
        firstCase_klein_restrictionSix_order_three
          hmin c hfirst hklein hy hyH hge
      rcases hfib with
        ⟨hxO, hxne, hxord, hxinv⟩ | ⟨hxO, hxne, hxord, hxinv⟩
      · exact coset_pair_card_four_of_odd_fiber
          hmin c hfirst hklein hy hyH (by simpa [n] using h4)
          hsI hsD hsy hxO hxne hxord hxinv
      · -- the odd-core fibre lies on `s * y`; move the representative there
        let w : G := s * y
        have hconjEq : conjugateSubgroup c.Hhat w =
            conjugateSubgroup c.Hhat y := by
          dsimp [w]
          rw [hsy]
          exact map_conj_mul_right_eq_of_mem_normalizer y
            ⟨s, Subgroup.le_normalizer
              ((inf_le_left : c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat) hsD)⟩
        have hwI : IsInvolution w := by
          dsimp [w]
          refine ⟨?_, ?_⟩
          · intro h
            apply hyH
            have hyeq : y = s⁻¹ * (s * y) := by group
            rw [hyeq]
            exact c.Hhat.mul_mem (c.Hhat.inv_mem
              ((inf_le_left : c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat) hsD))
              (by simpa [h] using c.Hhat.one_mem)
          · rw [pow_two]
            have hs2' : s * s = 1 := by simpa [pow_two] using hsI.2
            have hy2' : y * y = 1 := by simpa [pow_two] using hy.2
            calc
              (s * y) * (s * y) = s * (y * s) * y := by group
              _ = s * (s * y) * y := by rw [hsy]
              _ = (s * s) * (y * y) := by group
              _ = 1 := by rw [hs2', hy2']; simp
        have hwH : w ∉ c.Hhat := by
          intro hw
          apply hyH
          have hyeq : y = s⁻¹ * w := by dsimp [w]; group
          rw [hyeq]
          exact c.Hhat.mul_mem (c.Hhat.inv_mem
            ((inf_le_left : c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat) hsD)) hw
        have hcos : cosetInvolution_proj c.Hhat w =
            cosetInvolution_proj c.Hhat y := by
          dsimp [w]
          change QuotientGroup.mk ((s * y)⁻¹) = QuotientGroup.mk (y⁻¹)
          apply (QuotientGroup.eq (s := c.Hhat)).mpr
          have heq : ((s * y)⁻¹)⁻¹ * y⁻¹ = s := by
            calc
              ((s * y)⁻¹)⁻¹ * y⁻¹ = (s * y) * y⁻¹ := by rw [inv_inv]
              _ = s := by group
          rw [heq]
          exact (inf_le_left : c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat) hsD
        have hyws : (s * y) * s = y := by
          calc
            (s * y) * s = s * (y * s) := by group
            _ = s * (s * y) := by rw [hsy]
            _ = (s * s) * y := by group
            _ = y := by
              rw [show s * s = 1 from (by simpa [pow_two] using hsI.2)]
              simp
        have hsw : s * w = w * s := by
          dsimp [w]
          calc
            s * (s * y) = (s * s) * y := by group
            _ = y := by
              rw [show s * s = 1 from (by simpa [pow_two] using hsI.2)]
              simp
            _ = (s * y) * s := hyws.symm
        have hIw : Nat.card {z : G // z ∈ invertedElements c.Hhat w} = 4 := by
          have hfw : cosetFiber c w ≃ cosetFiber c y := by
            refine {
              toFun := fun z => ⟨z.1, z.2.1, by
                change cosetInvolution_proj c.Hhat (z : G) =
                  cosetInvolution_proj c.Hhat y
                rw [← hcos]
                exact z.2.2⟩
              invFun := fun z => ⟨z.1, z.2.1, by
                change cosetInvolution_proj c.Hhat (z : G) =
                  cosetInvolution_proj c.Hhat w
                rw [hcos]
                exact z.2.2⟩
              left_inv := by intro z; rfl
              right_inv := by intro z; rfl }
          calc
            Nat.card {z : G // z ∈ invertedElements c.Hhat w} =
                Nat.card (cosetFiber c w) :=
                  (Nat.card_congr (cosetFiber_equiv_inverted c hwI hwH)).symm
            _ = Nat.card (cosetFiber c y) := Nat.card_congr hfw
            _ = Nat.card {z : G // z ∈ invertedElements c.Hhat y} :=
                  Nat.card_congr (cosetFiber_equiv_inverted c hy hyH)
            _ = 4 := by simpa [n] using h4
        have hwcard : Nat.card (cosetCommPair c w) = 6 :=
          coset_pair_card_four_of_odd_fiber
            hmin c hfirst hklein hwI hwH hIw hsI (by simpa [hconjEq] using hsD) hsw
            (by simpa [hconjEq] using hxO) hxne hxord
            (by simpa [hconjEq, w] using hxinv)
        exact (Nat.card_congr (cosetCommPair_congr c hcos)).symm.trans hwcard
    · rw [← hn]
      simp [h2, h4]
      have hcases : n = 0 ∨ n = 1 ∨ n = 3 := by omega
      rcases hcases with hn0 | hn1 | hn3
      · -- n = 0
        have hc0 : Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 0 := by
          simpa [n] using hn0
        have hcardFib : Nat.card (cosetFiber c y) = 0 := by
          calc
            Nat.card (cosetFiber c y) =
                Nat.card {x : G // x ∈ invertedElements c.Hhat y} :=
                  Nat.card_congr (cosetFiber_equiv_inverted c hy hyH)
            _ = 0 := hc0
        let : Fintype (cosetFiber c y) := Fintype.ofFinite _
        have : IsEmpty (cosetFiber c y) :=
          Fintype.card_eq_zero_iff.mp (by simpa [Nat.card_eq_fintype_card] using hcardFib)
        have : IsEmpty (cosetCommPair c y) := by
          refine ⟨fun p => ?_⟩
          exact isEmptyElim p.1.1
        exact Nat.card_eq_zero.2 (Or.inl inferInstance)
      · -- n = 1
        have h1card : Nat.card {x : G // x ∈ invertedElements c.Hhat y} = 1 := by
          simpa [n] using hn1
        have h1cardFib : Nat.card (cosetFiber c y) = 1 := by
          calc
            Nat.card (cosetFiber c y) =
                Nat.card {x : G // x ∈ invertedElements c.Hhat y} :=
                  Nat.card_congr (cosetFiber_equiv_inverted c hy hyH)
            _ = 1 := h1card
        have : IsEmpty (cosetCommPair c y) := by
          refine ⟨fun p => ?_⟩
          obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists).mp h1cardFib
          have hz1 : p.1.1 = z0 := hz0 p.1.1
          have hz2 : p.1.2 = z0 := hz0 p.1.2
          exact p.2.1 (hz1.trans hz2.symm)
        exact Nat.card_eq_zero.2 (Or.inl inferInstance)
      · -- n = 3
        exact coset_pair_card_three_zero c hy hyH
          (by simpa [n] using hn3)

end CFSG.GorensteinWalter
