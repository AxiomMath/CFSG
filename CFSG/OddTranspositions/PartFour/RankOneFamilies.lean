module

public import CFSG.OddTranspositions.PartFour.RankOneMeetsSq
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.OddTranspositions.PartFour.RootGroupL2Sz
import CFSG.OddTranspositions.PartFour.UnitaryPlaneSL2
import CFSG.OddTranspositions.PartFour.Fourteen.ModelTwelveOne
import CFSG.OddTranspositions.PartFour.Fourteen.ModelUnitary
import CFSG.OddTranspositions.PartFour.Fourteen.Table
import CFSG.LieType.SuzukiSubgroups.Facts
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem rankOneFamilies_dvd_of_two_pow_sub_one_dvd {f g : ℕ}
    (h : 2 ^ f - 1 ∣ 2 ^ g - 1) : f ∣ g := by
  have hg : Nat.gcd (2 ^ f - 1) (2 ^ g - 1) = 2 ^ f - 1 := Nat.gcd_eq_left h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have h1 : (2 ^ Nat.gcd f g - 1) + 1 = (2 ^ f - 1) + 1 := congrArg (· + 1) hg
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel Nat.one_le_two_pow] at h1
  have hgf : Nat.gcd f g = f := Nat.pow_right_injective le_rfl h1
  exact hgf ▸ Nat.gcd_dvd_right f g

private theorem rankOneFamilies_pow_of_dvd_sq_sub_one {m f j' : ℕ} (hf : Odd f) (hj' : 0 < j')
    (hm : m = 2 ^ (2 * j')) (hdiv : 2 ^ f - 1 ∣ m ^ 2 - 1) :
    ∃ j : ℕ, 0 < j ∧ m = 2 ^ (f * j) := by
  have hcop : Nat.Coprime f 4 := by
    simpa using (Odd.coprime_two_right hf).pow_right 2
  have hdiv' : 2 ^ f - 1 ∣ 2 ^ (4 * j') - 1 := by
    rw [hm] at hdiv
    rwa [show (2 ^ (2 * j')) ^ 2 = 2 ^ (4 * j') by
      rw [← pow_mul]
      congr 1
      ring] at hdiv
  have hfj : f ∣ 4 * j' := rankOneFamilies_dvd_of_two_pow_sub_one_dvd hdiv'
  have hfj' : f ∣ j' := hcop.dvd_of_dvd_mul_left hfj
  obtain ⟨t, ht⟩ := hfj'
  have htpos : 0 < t := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at ht; omega
  refine ⟨2 * t, by omega, ?_⟩
  rw [hm, ht, show 2 * (f * t) = f * (2 * t) by ring]

section SzOrbit


private theorem rankOneFamilies_sz_class_data (hC : HypothesisC D) {f : ℕ}
    (hSz : CFSG.Quasithin.IsSz f
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    {d₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hclass : imageClass hC = {x | IsConj d₀ x}) (hd₀ : orderOf d₀ = 2) :
    (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, y * x * y⁻¹ ∈ imageClass hC) ∧
      (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
        Subgroup.closure (insert y {z | z ∈ imageClass hC ∧ Commute z x}) =
          Subgroup.closure (imageClass hC)) ∧
      (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC,
        ∃ g ∈ Subgroup.closure (imageClass hC), g * x * g⁻¹ = y) ∧
      (∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ 2 + 1) ∧
      (∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC,
        ¬ Commute x y ∧ orderOf (x * y) = 2 ^ f - 1) := by
  have hgenTop : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ imageClass hC ∧ Commute z x}) = ⊤ := by
    intro x hx y hy hxy
    have hx' : IsConj d₀ x := by simpa only [hclass, Set.mem_setOf_eq] using hx
    have hy' : IsConj d₀ y := by simpa only [hclass, Set.mem_setOf_eq] using hy
    rw [hclass]
    exact closure_insert_commute_eq_top_of_isSz hSz hd₀ hx' hy' hxy
  obtain ⟨x₀, hx₀, y₀, hy₀, hnc₀, hord₀⟩ :=
    exists_not_commute_orderOf_mul_eq_two_pow_sub_one_of_isSz hSz hd₀
  have hx₀' : x₀ ∈ imageClass hC := by simpa only [← hclass, Set.mem_setOf_eq] using hx₀
  have hy₀' : y₀ ∈ imageClass hC := by simpa only [← hclass, Set.mem_setOf_eq] using hy₀
  obtain ⟨-, hinv, hgen, hconj⟩ :=
    rootLiftClass_of_closure_insert_eq_top hclass hgenTop ⟨x₀, hx₀', y₀, hy₀', hnc₀⟩
  have hord5 : ∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ 2 + 1 := by
    obtain ⟨x, hx, y, hy, h5⟩ := exists_orderOf_mul_eq_five_of_isSz hSz hd₀
    exact ⟨x, by simpa only [← hclass, Set.mem_setOf_eq] using hx,
      y, by simpa only [← hclass, Set.mem_setOf_eq] using hy, by rw [h5]; norm_num⟩
  exact ⟨hinv, hgen, hconj, hord5, x₀, hx₀', y₀, hy₀', hnc₀, hord₀⟩

theorem exists_ncard_orbit_Malpha_eq_two_pow_mul_of_isSz (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ}
    (hSz : CFSG.Quasithin.IsSz f
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j) := by
  classical
  have hodd : Odd f := by
    obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := hSz
    exact ⟨a, hf⟩
  obtain ⟨d₀, hclass⟩ := imageClass_isClass hC
  have hd₀ : orderOf d₀ = 2 :=
    imageClass_involutions hC hHns d₀ (by rw [hclass]; exact IsConj.refl d₀)
  obtain ⟨hinv, hgen, hconj, hord5, x₀, hx₀, y₀, hy₀, hnc₀, hord₀⟩ :=
    rankOneFamilies_sz_class_data hC hSz hclass hd₀
  obtain ⟨j', hj'pos, hj'⟩ := exists_ncard_orbit_Malpha_eq_two_pow_mul_of_class h89 h113 hC
    hrad hW hn3 hMZ hHns (imageClass hC) subset_rfl (n := 2) (by norm_num) hinv hgen hconj
    hord5 hβ
  have hdiv : 2 ^ f - 1 ∣
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard ^ 2 - 1 := by
    have h := orderOf_mul_dvd_ncard_orbit_sq_sub_one_of_class h89 h113 hC hrad hW hn3 hHns
      (imageClass hC) subset_rfl (n := 2) (by norm_num) hinv hgen hconj hord5 hβ hx₀ hy₀ hnc₀
    rwa [hord₀] at h
  exact rankOneFamilies_pow_of_dvd_sq_sub_one hodd hj'pos hj' hdiv

end SzOrbit

private theorem rankOneFamilies_top_data {X : Type} [Group X]
    (hX : CFSG.BenderSuzuki.IsBenderGroup X) {s : X} {E : Set X}
    (hE : E = {z | IsConj s z}) (hs : orderOf s = 2)
    (hgen : ∀ x ∈ E, ∀ y ∈ E, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ E ∧ Commute z x}) = ⊤)
    {n : ℕ} (hord : ∃ x ∈ E, ∃ y ∈ E, orderOf (x * y) = 2 ^ n + 1) :
    (∀ x ∈ E, ∀ y ∈ E, ¬ Commute x y → Subgroup.closure (insert y (Vmem E x)) = ⊤) ∧
      (∀ x ∈ E, ∀ y ∈ E, ∃ g : X, g * x * g⁻¹ = y) ∧
      (∃ x ∈ E, ∃ y ∈ E, orderOf (x * y) = 2 ^ n + 1) := by
  haveI : Finite X := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hX
  refine ⟨?_, ?_, hord⟩
  · intro x hx y hy hxy
    rw [Vmem_eq_setOf_commute_of_isBenderGroup hX hs hE hx]
    exact hgen x hx y hy hxy
  · intro x hx y hy
    have hx' : IsConj s x := by simpa only [hE, Set.mem_setOf_eq] using hx
    have hy' : IsConj s y := by simpa only [hE, Set.mem_setOf_eq] using hy
    exact isConj_iff.mp (hx'.symm.trans hy')

private theorem rankOneFamilies_top_form {X : Type} [Group X] {E : Set X} {n : ℕ}
    (hgen : ∀ x ∈ E, ∀ y ∈ E, ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = ⊤)
    (hconj : ∀ x ∈ E, ∀ y ∈ E, ∃ g : X, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ E, ∃ y ∈ E, orderOf (x * y) = 2 ^ n + 1) :
    (∀ x ∈ E, x ∈ (⊤ : Subgroup X) → ∀ y ∈ E, y ∈ (⊤ : Subgroup X) → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = ⊤) ∧
      (∀ x ∈ E, x ∈ (⊤ : Subgroup X) → ∀ y ∈ E, y ∈ (⊤ : Subgroup X) →
        ∃ g ∈ (⊤ : Subgroup X), g * x * g⁻¹ = y) ∧
      (∃ x ∈ E, x ∈ (⊤ : Subgroup X) ∧ ∃ y ∈ E, y ∈ (⊤ : Subgroup X) ∧
        orderOf (x * y) = 2 ^ n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx _ y hy _ hxy
    exact hgen x hx y hy hxy
  · intro x hx _ y hy _
    obtain ⟨g, hg⟩ := hconj x hx y hy
    exact ⟨g, trivial, hg⟩
  · obtain ⟨x, hx, y, hy, hord⟩ := hord
    exact ⟨x, hx, trivial, y, hy, trivial, hord⟩

private theorem rankOneFamilies_psl2_top_data
    (hC : HypothesisC D) {f : ℕ} (hf : 2 ≤ f)
    {d₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hclass : imageClass hC = {x | IsConj d₀ x}) (hd₀ : orderOf d₀ = 2)
    (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      CFSG.Theory.Comparator.PSL2Model f) :
    (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = ⊤) ∧
      (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC,
        ∃ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
          g * x * g⁻¹ = y) ∧
      (∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ f + 1) := by
  have hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) := .isPSL2 f hf e
  have hgenIn : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ imageClass hC ∧ Commute z x}) = ⊤ := by
    intro x hx y hy hxy
    have hx' : IsConj d₀ x := by simpa only [hclass, Set.mem_setOf_eq] using hx
    have hy' : IsConj d₀ y := by simpa only [hclass, Set.mem_setOf_eq] using hy
    rw [hclass]
    exact closure_insert_commute_eq_top_of_mulEquiv_psl2Model e hf hd₀ hx' hy' hxy
  have hordIn : ∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ f + 1 := by
    obtain ⟨x, hx, y, hy, h5⟩ :=
      exists_orderOf_mul_eq_two_pow_add_one_of_mulEquiv_psl2Model e hf hd₀
    exact ⟨x, by simpa only [← hclass, Set.mem_setOf_eq] using hx,
      y, by simpa only [← hclass, Set.mem_setOf_eq] using hy, h5⟩
  exact rankOneFamilies_top_data hX hclass hd₀ hgenIn hordIn

private theorem rankOneFamilies_sz_top_data
    (hC : HypothesisC D) {f : ℕ}
    (hSz : CFSG.Quasithin.IsSz f
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    {d₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hclass : imageClass hC = {x | IsConj d₀ x}) (hd₀ : orderOf d₀ = 2) :
    (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = ⊤) ∧
      (∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC,
        ∃ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
          g * x * g⁻¹ = y) ∧
      (∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ 2 + 1) := by
  have hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    isBenderGroup_of_isSz hSz
  have hgenIn : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ imageClass hC ∧ Commute z x}) = ⊤ := by
    intro x hx y hy hxy
    have hx' : IsConj d₀ x := by simpa only [hclass, Set.mem_setOf_eq] using hx
    have hy' : IsConj d₀ y := by simpa only [hclass, Set.mem_setOf_eq] using hy
    rw [hclass]
    exact closure_insert_commute_eq_top_of_isSz hSz hd₀ hx' hy' hxy
  have hordIn : ∃ x ∈ imageClass hC, ∃ y ∈ imageClass hC, orderOf (x * y) = 2 ^ 2 + 1 := by
    obtain ⟨x, hx, y, hy, h5⟩ := exists_orderOf_mul_eq_five_of_isSz hSz hd₀
    exact ⟨x, by simpa only [← hclass, Set.mem_setOf_eq] using hx,
      y, by simpa only [← hclass, Set.mem_setOf_eq] using hy, by rw [h5]; norm_num⟩
  exact rankOneFamilies_top_data (n := 2) hX hclass hd₀ hgenIn hordIn

section Certified


theorem meetsSq_of_mulEquiv_psl2Model_imageClass
    (h87 : PartThree.Theorem8_7) (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (hf : 2 ≤ f)
    (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      CFSG.Theory.Comparator.PSL2Model f) :
    MeetsSq D := by
  classical
  have hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) := .isPSL2 f hf e
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) :=
    not_isSolvable_Halpha_of_isBenderGroup hC hX
  have hn3 : ¬ ∀ d ∈ D, ∀ r ∈ D, orderOf (d * r) ∈ ({1, 2, 3} : Set ℕ) :=
    not_threeTransp_of_meetsSq hC (meetsSq_imageClass_of_isBenderGroup hC hX)
  have hnf : 0 < f := by omega
  obtain ⟨d₀, hclass⟩ := imageClass_isClass hC
  have hd₀ : orderOf d₀ = 2 :=
    imageClass_involutions hC hHns d₀ (by rw [hclass]; exact IsConj.refl d₀)
  obtain ⟨hgenT, hconjT, hordT⟩ := rankOneFamilies_psl2_top_data hC hf hclass hd₀ e
  obtain ⟨hgen, hconj, hord⟩ := rankOneFamilies_top_form hgenT hconjT hordT
  have hpow : ∀ β ∈ Dalpha D hC.alpha, ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j) :=
    fun β hβ => exists_ncard_orbit_Malpha_eq_two_pow_mul h89 h113 hC hrad hW hn3 hMZ hHns ⊤
      (n := f) hnf hgen hconj hord hβ
  exact meetsSq_of_isBenderGroup_imageClass h87 h89 h113 hC hrad hW hMZ hX hf
    (fusionBenderBorel_of_mulEquiv_psl2Model hf e) ⊤ (n := f) hnf hgen hconj hord hpow

theorem meetsSq_of_isSymplecticTransvection_two_imageClass
    (h87 : PartThree.Theorem8_7) (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} {f : ℕ} (hf : 2 ≤ f)
    (hsp : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 f s) :
    MeetsSq D := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_isSymplecticTransvection_two
    (center_eq_bot_quotient_H hC) hf hsp
  exact meetsSq_of_mulEquiv_psl2Model_imageClass h87 h89 h113 hC hrad hW hMZ hf e

theorem meetsSq_of_isUnitaryTransvection_two_imageClass
    (h87 : PartThree.Theorem8_7) (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} {f : ℕ} (hf : 2 ≤ f)
    (hut : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 f s) :
    MeetsSq D := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_isUnitaryTransvection_two
    (center_eq_bot_quotient_H hC) hf hut
  exact meetsSq_of_mulEquiv_psl2Model_imageClass h87 h89 h113 hC hrad hW hMZ hf e

theorem meetsSq_of_isUnitaryTransvection_three_imageClass
    (h87 : PartThree.Theorem8_7) (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {f : ℕ} (hf : 2 ≤ f)
    (hut : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 3 f s) :
    MeetsSq D := by
  classical
  have hZ := center_eq_bot_quotient_H hC
  have hX := isBenderGroup_of_isUnitaryTransvection_three hZ hf hut
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) :=
    not_isSolvable_Halpha_of_isBenderGroup hC hX
  have hn3 : ¬ ∀ d ∈ D, ∀ r ∈ D, orderOf (d * r) ∈ ({1, 2, 3} : Set ℕ) :=
    not_threeTransp_of_meetsSq hC (meetsSq_imageClass_of_isBenderGroup hC hX)
  have hnf : 0 < f := by omega
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3Model_of_isUnitaryTransvection_three hZ hf hut
  have hcl : imageClass hC = {x | IsConj s x} := imageClass_eq_setOf_isConj hC hs
  obtain ⟨K0, hgen, hconj, hord⟩ :=
    exists_subgroup_of_isUnitaryTransvection hZ (le_refl 3) hut
  rw [← hcl] at hgen hconj hord
  refine meetsSq_of_isBenderGroup_imageClass h87 h89 h113 hC hrad hW hMZ hX hf
    (CFSG.CGT.Timmesfeld75.fusionBenderBorel_of_psu3 hf e) K0 (n := f) hnf hgen hconj hord ?_
  intro β hβ
  exact exists_ncard_orbit_Malpha_eq_two_pow_mul h89 h113 hC hrad hW hn3 hMZ hHns K0
    (n := f) hnf hgen hconj hord hβ

theorem meetsSq_of_isSz_imageClass (h87 : PartThree.Theorem8_7)
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (hSz : CFSG.Quasithin.IsSz f
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    MeetsSq D := by
  classical
  have hf2 : 2 ≤ f := by
    obtain ⟨-, a, ha, -, -, -, hf, -, -⟩ := hSz
    omega
  have hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    isBenderGroup_of_isSz hSz
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) :=
    not_isSolvable_Halpha_of_isBenderGroup hC hX
  have hn3 : ¬ ∀ d ∈ D, ∀ r ∈ D, orderOf (d * r) ∈ ({1, 2, 3} : Set ℕ) :=
    not_threeTransp_of_meetsSq hC (meetsSq_imageClass_of_isBenderGroup hC hX)
  obtain ⟨d₀, hclass⟩ := imageClass_isClass hC
  have hd₀ : orderOf d₀ = 2 :=
    imageClass_involutions hC hHns d₀ (by rw [hclass]; exact IsConj.refl d₀)
  obtain ⟨hgenT, hconjT, hordT⟩ := rankOneFamilies_sz_top_data hC hSz hclass hd₀
  obtain ⟨hgen, hconj, hord⟩ := rankOneFamilies_top_form hgenT hconjT hordT
  have hpow : ∀ β ∈ Dalpha D hC.alpha, ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j) :=
    fun β hβ => exists_ncard_orbit_Malpha_eq_two_pow_mul_of_isSz h89 h113 hC hrad hW hn3 hMZ
      hHns hSz hβ
  exact meetsSq_of_isBenderGroup_imageClass h87 h89 h113 hC hrad hW hMZ hX hf2
    (CFSG.LieType.SuzukiSubgroups.fusionBenderBorel_of_isSz hSz) ⊤ (n := 2) (by norm_num) hgen
    hconj hord hpow

end Certified

end CFSG.OddTranspositions.PartFour
