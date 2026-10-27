module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTools
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9Gen
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE27
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

structure UCfg {G : Type} [Group G] [Finite G] (L : Subgroup G) (a : G)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) where
  odd : Odd m
  three_le : 3 ≤ m
  center_eq : Subgroup.center (projSU 3 2 m) = ⊥
  ι : projSU 3 2 m →* L ⧸ aschbacherSolvableCore 3 L
  ι_inj : Function.Injective ι
  cube : (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) ^ 3 = 1
  ne_one : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ≠ 1
  fix : ∀ u, thetaQuotMulAut L (compAction L ⟨a, haN⟩) (ι u) = ι u
  comp : IsComponent (ι.range.subgroupOf
    (Item426.fixSub (thetaQuotMulAut L (compAction L ⟨a, haN⟩))))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
  {haN : a ∈ Subgroup.normalizer (L : Set G)} {m : ℕ}

theorem UCfg.exists_of_component (hL : IsComponent L) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : orderOf a = 3) (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) : 3 ≤ m ∧ Nonempty (UCfg L a haN m) := by
  obtain ⟨hm3, hZU, ι, hι, hα3, hα1, hfix, hcomp⟩ := unitary_setup hL haN ha3 haC hKle hKc hm e
  exact ⟨hm3, ⟨⟨hm, hm3, hZU, ι, hι, hα3, hα1, hfix, hcomp⟩⟩⟩

theorem UCfg.false_of_hom (c : UCfg L a haN m) {Y' : Type} [Group Y'] [Finite Y']
    (φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) →* MulAut Y') (hφ : Function.Injective φ)
    (N : Subgroup (MulAut Y'))
    (hinn : ∀ x : L ⧸ aschbacherSolvableCore 3 L, φ (MulAut.conj x) ∈ N)
    (hα : φ (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) ∈ N)
    (hN : ∀ F : Subgroup (MulAut Y'), CFSG.Assembly.IsElemAbelian 3 F → F ≤ N →
      Nat.card F ≤ 9) : False := by
  obtain ⟨E, hE, hE9⟩ : ∃ E : Subgroup (projSU 3 2 m),
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨x, y, hx3, hy3, hx1, hxy, hy⟩ := exists_commuting_order_three_projSU c.odd
    exact exists_elemAbelian_nine_of_commuting x y hx3 hy3 hxy hx1 hy
  obtain ⟨F, hF, hF27, hFle⟩ := exists_E27 c.center_eq c.ι c.ι_inj _ c.cube c.ne_one c.fix E hE hE9
  have hFN : F.map φ ≤ N := by
    rw [Subgroup.map_le_iff_le_comap]
    refine hFle.trans (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      exact hinn x
    · exact Subgroup.zpowers_le.mpr hα
  have hFm : CFSG.Assembly.IsElemAbelian 3 (F.map φ) := Sec4.isElemAbelian_map φ hF
  have h9 := hN _ hFm hFN
  rw [Subgroup.card_map_of_injective hφ, hF27] at h9
  omega

theorem UCfg.card_dvd (c : UCfg L a haN m) :
    Nat.card (projSU 3 2 m) ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
  Subgroup.card_dvd_of_injective c.ι c.ι_inj

theorem UCfg.false_of_two_pow_nine (c : UCfg L a haN m) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (h9 : ¬ 2 ^ 9 ∣ M) : False :=
  h9 ((pow_dvd_pow 2 (by have := c.three_le; omega)).trans
    ((Item419Res3.two_pow_dvd_card_projSU_three_two c.odd).trans (c.card_dvd.trans hM)))

theorem UCfg.false_of_two_pow_fifteen (c : UCfg L a haN m) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (h15 : ¬ 2 ^ 15 ∣ M) (h19 : ¬ 19 ∣ M) :
    False := by
  have hKM : Nat.card (projSU 3 2 m) ∣ M := c.card_dvd.trans hM
  have hm3 := c.three_le
  rcases (show m = 3 ∨ 5 ≤ m by obtain ⟨j, hj⟩ := c.odd; omega) with rfl | h5
  · apply h19
    rw [Item419Res3.card_projSU_three_two_three] at hKM
    exact (show (19 : ℕ) ∣ 5515776 by norm_num).trans hKM
  · exact h15 ((pow_dvd_pow 2 (by omega)).trans
      ((Item419Res3.two_pow_dvd_card_projSU_three_two c.odd).trans hKM))

theorem UCfg.false_of_not_three_dvd (c : UCfg L a haN m)
    (h : ¬ 3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by
    have := c.three_le
    omega
  exact h ((KFacts.three_dvd_card_of_mulEquiv_projSU (p := 2) (f := m) hm0
    (MulEquiv.refl (projSU 3 2 m))).trans c.card_dvd)

theorem UCfg.false_of_inner (c : UCfg L a haN m)
    (hα : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range)
    {S : Type} [Group S] [Finite S]
    (e : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* S)
    (hS : CFSG.pRank 3 S ≤ 2) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine c.false_of_hom (MonoidHom.id _) Function.injective_id
    (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range (fun x => ⟨x, rfl⟩) hα ?_
  intro F hF hFi
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hk2 : k ≤ 2 := (Sec4.le_pRank_of_le_inner e hF hFi hk).trans hS
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
