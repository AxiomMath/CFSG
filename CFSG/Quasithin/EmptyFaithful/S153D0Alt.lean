module

public import CFSG.Quasithin.EmptyFaithful.S153D0Two
public import CFSG.Quasithin.EmptyFaithful.S153D0Pair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem star_cube (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : OTwoQuot M}
    (hy : y ∈ imageOTwoQuot M (Y153 Mc M)) : y ^ 3 = 1 := by
  have := (h.Ystar_structure h113).1.2.2 ⟨y, hy⟩
  simpa using congrArg Subtype.val this

theorem Zstar_central (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {c y : OTwoQuot M}
    (hc : c ∈ ZstarOf h) (hy : y ∈ imageOTwoQuot M (Y153 Mc M)) : c * y = y * c :=
  ((h.Ystar_structure h113).2 c hc.2 hc.1 y hy).symm

theorem pCoreOf_Y153_le (Mc M : Subgroup G) : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 M :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Y153_le Mc M))
    (fun _ hm => normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_Y153 Mc M hm))
    (pCoreOf_isPGroup 2 _)

theorem Zstar_le_imageK (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ZstarOf h ≤ imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := by
  intro c hc
  obtain ⟨g, hgM, hgY, rfl⟩ := mem_imageOTwoQuot_iff.mp hc.2
  have hgC : g ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (A4.actionOn_eq_one_iff h.le_normalizer ⟨g, hgM⟩).mp hc.1
  exact mem_imageOTwoQuot_iff.mpr ⟨g, hgM, ⟨hgY, Subgroup.centralizer_le D.le₁ hgC⟩, rfl⟩

theorem Zstar_eq_bot_of_pCore (h : Hyp153 G T Mc M)
    (hP : pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) :
    ZstarOf h = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨g, hgM, hgY, rfl⟩ := mem_imageOTwoQuot_iff.mp hc.2
  have hgC : g ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (A4.actionOn_eq_one_iff h.le_normalizer ⟨g, hgM⟩).mp hc.1
  have : g ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [hP]
    exact ⟨hgY, hgC⟩
  rw [Subgroup.mem_bot]
  exact (mk_eq_one_iff_mem_pCoreOf ⟨g, hgM⟩).2 (pCoreOf_Y153_le Mc M this)

theorem imageOTwoQuot_oTwoUpper_eq (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {X : Subgroup G} (hXY : X ≤ Y153 Mc M) :
    imageOTwoQuot M (oTwoUpper X) = imageOTwoQuot M X := by
  rw [CFSG.Quasithin.imageOTwoQuot_oTwoUpper (hXY.trans (Y153_le Mc M))]
  refine le_antisymm (oTwoUpper_le _) fun u hu => mem_oTwoUpper_of_odd hu ?_
  have h3 := star_cube h113 h (imageOTwoQuot_mono hXY hu)
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)

theorem exists_not_commute_of_isPOnePlusTwo {X : Type*} [Group X] (hp : IsPOnePlusTwo 3 X) :
    ∃ x y : X, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hc : Subgroup.center X = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => hcon y x
  have := hp.1
  have h3 := CFSG.IsExtraspecial.center_order_p 3 X
  have h27 := hp.2.1
  rw [hc, Subgroup.card_top] at h3
  rw [h3] at h27
  norm_num at h27

theorem Zstar_structure (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {A B : OTwoQuot M}
    (hAY : A ∈ imageOTwoQuot M (Y153 Mc M)) (hBY : B ∈ imageOTwoQuot M (Y153 Mc M))
    (hz : ⁅A, B⁆ ∈ ZstarOf h)
    (hgen : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), ∃ (i j : ℤ), ∃ c ∈ ZstarOf h,
      y = B ^ i * A ^ j * c) :
    ZstarOf h = ⊥ ∨ (⁅A, B⁆ ≠ 1 ∧ ZstarOf h ≤ Subgroup.zpowers ⁅A, B⁆) := by
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  rcases h.lemma_15_3_7_cases h113 with ⟨hO, -⟩ | ⟨hP, -⟩
  · exact Or.inl (Zstar_eq_bot_of_pCore h hO)
  · right
    obtain ⟨φ, -⟩ := exists_mulEquiv_imageOTwoQuot (Y153_le Mc M) (le_normalizer_Y153 Mc M)
    have hP' : IsPOnePlusTwo 3 ↥Ys := A36B.isPOnePlusTwo_of_mulEquiv φ hP
    have hZY : ZstarOf h ≤ Ys := fun c hc => hc.2
    have hz1 : ⁅A, B⁆ ≠ 1 := by
      intro hz1
      have hAB : A * B = B * A := by
        rw [commutatorElement_eq_one_iff_mul_comm] at hz1
        exact hz1
      obtain ⟨x, y, hxy⟩ := exists_not_commute_of_isPOnePlusTwo hP'
      exact hxy (Subtype.ext (commute_of_gen hZY hAY hBY hAB
        (fun c hc w hw => Zstar_central h113 h hc hw) hgen x x.2 y y.2))
    refine ⟨hz1, fun c hc => ?_⟩
    have hz' : (⟨⁅A, B⁆, hz.2⟩ : ↥Ys) ∈ Subgroup.center ↥Ys :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Zstar_central h113 h hz g.2).symm
    have hc' : (⟨c, hc.2⟩ : ↥Ys) ∈ Subgroup.center ↥Ys :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Zstar_central h113 h hc g.2).symm
    have hord : orderOf (⟨⁅A, B⁆, hz.2⟩ : ↥Ys) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (by simpa using star_cube h113 h hz.2)
      · intro h1
        exact hz1 (congrArg Subtype.val h1)
    have hcen3 : Nat.card (Subgroup.center ↥Ys) = 3 := by
      have := hP'.1
      exact CFSG.IsExtraspecial.center_order_p 3 ↥Ys
    have hzp : Subgroup.zpowers (⟨⁅A, B⁆, hz.2⟩ : ↥Ys) = Subgroup.center ↥Ys :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz')
        (by rw [Nat.card_zpowers, hord, hcen3])
    have hcm : (⟨c, hc.2⟩ : ↥Ys) ∈ Subgroup.zpowers (⟨⁅A, B⁆, hz.2⟩ : ↥Ys) := by
      rw [hzp]
      exact hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcm
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

end S153D

end CFSG.Quasithin
