module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLRank
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLE27
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLLiftP
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Center
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian evenRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private theorem ffCenter_false_of_central_three {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X)) (e : ↥X) (he : e ∈ Subgroup.center ↥X)
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let z : ↥(Subgroup.center ↥X) := ⟨e, he⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext he3
  have hz1 : z ≠ 1 := fun h => he1 (congrArg (fun w : ↥(Subgroup.center ↥X) => (w : ↥X)) h)
  exact hZ3 ((orderOf_eq_prime hz3 hz1) ▸ orderOf_dvd_natCard z)

theorem ffCenterSp6_holds : FFCenterSp6 := by
  intro G _ _ A a X hpt h6 hXq _ _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := hpt.mem_S.1.1
  have ha3 : a ^ 3 = 1 := hAab.2 a hpt.mem
  have ha1 : a ≠ 1 := hpt.ne_one
  have hG : evenRank G = 3 := hpt.standing.evenRank_eq
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta
  have hQ : CFSG.IsQuasisimple (lBar X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have hX : IsL4L5Sp6 X := Or.inr (Or.inr h6)
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X) := ff_not_three_dvd_card_center hXq hX hQ
  have hθ : aschbacherSolvableCore 3 ↥X = Subgroup.center ↥X :=
    ff_aschbacherSolvableCore_eq_center hXq hX hQ
  have eZ : (↥X ⧸ Subgroup.center ↥X) ≃* lBar X := QuotientGroup.quotientMulEquivOfEq hθ.symm
  have hmodC : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ.symm h6
  obtain ⟨eH⟩ := nonempty_mulEquiv_H6_of_stated hmodC
  obtain ⟨E6, hE6, hE627⟩ := CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.exists_e27_H6
  have hE' : IsElemAbelian 3 (E6.map eH.symm.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE6 _
  have hE'27 : Nat.card (E6.map eH.symm.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := eH.symm.toMonoidHom) eH.symm.injective]
    exact hE627
  obtain ⟨E27, hE27, hE27card⟩ :=
    exists_elemAbelian_of_quotient (Subgroup.center ↥X) hZ3 hE'
  rw [hE'27] at hE27card
  set P : Subgroup G := E27.map X.subtype with hPdef
  have hPab : IsElemAbelian 3 P := CFSG.Open.IsElemAbelian.map hE27 X.subtype
  have hPcard : Nat.card P = 27 := by
    rw [hPdef, Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective]
    exact hE27card
  have hPX : P ≤ X := Subgroup.map_subtype_le E27
  have hQab : IsElemAbelian 3 (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha3
  have hQcard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hXa : ∀ y ∈ X, y * a = a * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXC hy)
  have hXzZ : ∀ y ∈ X, ∀ w ∈ Subgroup.zpowers a, y * w = w * y := by
    intro y hy w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((show Commute y a from hXa y hy).zpow_right k).eq
  have hdisj : ∀ x ∈ P, x ∈ Subgroup.zpowers a → x = 1 := by
    intro x hx hxa
    by_contra hx1
    have hxX : x ∈ X := hPX hx
    have hxc : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hXzZ y.1 y.2 x hxa)
    have he3 : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (hQab.2 x hxa)
    have he1 : (⟨x, hxX⟩ : ↥X) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    exact ffCenter_false_of_central_three hZ3 ⟨x, hxX⟩ hxc he3 he1
  have hcomm : ∀ x ∈ P, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy =>
    hXzZ x (hPX hx) y hy
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥X) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥X)) 2 h2
    have hz1 : z ≠ 1 := by
      rintro rfl
      simp at hz
    have hz2 : z ^ 2 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    obtain ⟨g, hg⟩ : ∃ g : G, g = ((z : ↥X) : G) := ⟨_, rfl⟩
    have hg1 : g ≠ 1 := by
      rw [hg]
      intro h
      exact hz1 (Subtype.ext (Subtype.ext h))
    have hg2 : g ^ 2 = 1 := by
      have h := congrArg (fun w : ↥(Subgroup.center ↥X) => ((w : ↥X) : G)) hz2
      simpa [hg] using h
    have hgord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
    have hgX : ∀ y ∈ X, y * g = g * y := by
      intro y hy
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
      rw [hg]
      exact h
    have hgX0 : g ∈ X := by
      rw [hg]
      exact (z : ↥X).2
    have hVne : Subgroup.zpowers g ≠ ⊥ := by
      intro h
      have hm := Subgroup.mem_zpowers g
      rw [h, Subgroup.mem_bot] at hm
      exact hg1 hm
    have hV2 : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgord, pow_one])
    have hcentV : ∀ x : G, Commute g x →
        x ∈ Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hx.zpow_left k).eq
    have hPV : P ≤ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) :=
      fun x hx => Subgroup.centralizer_le_normalizer _ (hcentV x (hgX x (hPX hx)).symm)
    have hQV : Subgroup.zpowers a ≤
        Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ (hcentV a (hXa g hgX0)))
    obtain ⟨K, hKN, hKab, hKcard⟩ :=
      exists_elemAbelian_card_mul hPab hQab hPV hQV hcomm hdisj
    rw [hPcard, hQcard] at hKcard
    have hK := ff_card_le_of_normalizes hVne hV2 hKab hKN
    rw [hG, hKcard] at hK
    norm_num at hK
  have hcenter : Subgroup.center ↥X = ⊥ := center_eq_bot_of_sp6 hXq h2 hZ3 hmodC
  have eX : ↥X ≃* lBar X :=
    (QuotientGroup.quotientBot : ↥X ⧸ (⊥ : Subgroup ↥X) ≃* ↥X).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans eZ)
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eX.symm h6

end CFSG.RankThree.PartTwo.Sec21
