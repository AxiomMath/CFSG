module

public import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.NearModels

@[expose] def fixedSubgroupCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    signalizerFixedSubgroup f ≃* signalizerFixedSubgroup (MulAut.congr e f) where
  toFun x := ⟨e x, by
    change e (f (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, x.2]⟩
  invFun y := ⟨e.symm y, by
    have h : e (f (e.symm y)) = y := y.2
    change f (e.symm y) = e.symm y
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : X) y)

theorem orderOf_mulAutCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    orderOf (MulAut.congr e f) = orderOf f :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective f

theorem isSolvable_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [Group.IsSolvable Y] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_of_natCard {G : Type*} [Group G] [Finite G] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, h])

theorem isSolvable_psl2_zmod_two :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) := by
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
    isSolvable_of_natCard (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [Nat.card_eq_fintype_card]; decide)
  exact inferInstanceAs (Group.IsSolvable (_ ⧸ _))

theorem isSolvable_psl2_zmod_three :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) := by
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    isSolvable_of_natCard (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [Nat.card_eq_fintype_card]; decide)
  exact inferInstanceAs (Group.IsSolvable (_ ⧸ _))

theorem isSolvable_sz_zero : Group.IsSolvable (Sz 0) := by
  obtain ⟨e⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  have : Finite (Sz 0) := Finite.of_equiv _ e.toEquiv
  refine isSolvable_of_natCard (p := 2) (q := 5) (a := 2) (b := 1) Nat.prime_two
    (by norm_num) (by norm_num) ?_
  rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (by simp)]
  norm_num

theorem isSolvable_psu3_two_one : Group.IsSolvable (PSU3 2 1) := by
  have h72 : Nat.card (PSU3 2 1) = 72 :=
    CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one
  have : Finite (PSU3 2 1) := Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
  exact isSolvable_of_natCard (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [h72]; norm_num)

theorem nearSimpleModel_fixedSubgroup_solvable
    {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hX : signalizerNearSimpleModel p X) (hcop : Nat.Coprime p (Nat.card X))
    (f : MulAut X) (hf : orderOf f = p) : Group.IsSolvable (signalizerFixedSubgroup f) := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := isSolvable_psl2_zmod_two
    obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 2 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact isSolvable_of_mulEquiv ((fixedSubgroupCongr e f).trans φ)
  · have := isSolvable_psl2_zmod_three
    obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 3 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact isSolvable_of_mulEquiv ((fixedSubgroupCongr e f).trans φ)
  · have := isSolvable_sz_zero
    obtain ⟨φ⟩ := sz_fixedSubgroup_mulEquiv n hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact isSolvable_of_mulEquiv ((fixedSubgroupCongr e f).trans φ)
  · have := isSolvable_psu3_two_one
    obtain ⟨φ⟩ := psu3_fixedSubgroup_mulEquiv hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact isSolvable_of_mulEquiv ((fixedSubgroupCongr e f).trans φ)

theorem card_pSubgroup_dvd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : ∀ Q : Subgroup (MulAut Y), IsPGroup p Q → Nat.card Q ∣ p)
    (P : Subgroup (MulAut X)) (hP : IsPGroup p P) : Nat.card P ∣ p := by
  have hQ := h (P.map (MulAut.congr e).toMonoidHom) (hP.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hQ

theorem nearSimpleModel_card_pSubgroup_dvd
    {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hX : signalizerNearSimpleModel p X) (hcop : Nat.Coprime p (Nat.card X))
    (P : Subgroup (MulAut X)) (hP : IsPGroup p P) : Nat.card P ∣ p := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact card_pSubgroup_dvd_of_mulEquiv e
      (psl2_card_pSubgroup_dvd 2 hp (by rwa [← Nat.card_congr e.toEquiv])) P hP
  · exact card_pSubgroup_dvd_of_mulEquiv e
      (psl2_card_pSubgroup_dvd 3 hp (by rwa [← Nat.card_congr e.toEquiv])) P hP
  · exact card_pSubgroup_dvd_of_mulEquiv e
      (sz_card_pSubgroup_dvd n hp (by rwa [← Nat.card_congr e.toEquiv])) P hP
  · exact card_pSubgroup_dvd_of_mulEquiv e
      (psu3_card_pSubgroup_dvd hp (by rwa [← Nat.card_congr e.toEquiv])) P hP

end CFSG.SignalizerFunctorTheorem.NearModels
