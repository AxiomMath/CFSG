module

public import CFSG.Quasithin.EmptyFaithful.LRed3A6Ord
public import CFSG.Quasithin.Vol2.Ch10SecQ1SU3
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.Vol2.Ch11SecA02Shape
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Blueprint

structure FactsA6 : Prop where
  su3 : ∀ (K : Type) [Field K] [Finite K] (a : ℕ), Nat.card K = (2 ^ a) ^ 2 →
    ∀ (X : Type) [Group X], IsAlt 6 X → ∀ π : ↥(StatedSU 3 (2 ^ a) K) →* X, ¬ Function.Surjective π
  nineTensor : ∀ (K : Type) [Field K] [Finite K] (a : ℕ), 1 ≤ a → Nat.card K = 2 ^ (2 * a) →
    ∀ (X : Type) [Group X], IsAlt 6 X → ∀ π : ↥(StatedSL 3 K) →* X, ¬ Function.Surjective π
  g2Derived : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (X : Type) [Group X], IsAlt 6 X →
      ∀ π : ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ →* X, ¬ Function.Surjective π
  m12 : ∀ eY : G6.PermMod 24, eY ∈ golayC → hammingNorm (Multiplicative.toAdd eY) = 12 →
    ∀ (X : Type) [Group X], IsAlt 6 X → ∀ π : ↥(m24Fix eY) →* X, ¬ Function.Surjective π
  m22 : ∀ x y : Fin 24, x ≠ y → ∀ (X : Type) [Group X], IsAlt 6 X →
    ∀ π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) →* X, ¬ Function.Surjective π
  m23 : ∀ x : Fin 24, ∀ (X : Type) [Group X], IsAlt 6 X →
    ∀ π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x) →* X,
      ¬ Function.Surjective π
  m24 : ∀ (X : Type) [Group X], IsAlt 6 X → ∀ π : ↥CFSG.Monster.Code.AutPerm →* X,
    ¬ Function.Surjective π
  sp4Twisted : ∀ (K : Type) [Field K] [Finite K] (a : ℕ), 1 ≤ a → Nat.card K = 2 ^ (2 * a) →
    ∀ (X : Type) [Group X], IsAlt 6 X → ∀ π : ↥(StatedSp 2 K) →* X, ¬ Function.Surjective π
  j2 : ∀ (X : Type) [Group X], IsAlt 6 X → ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2)

section Proofs

variable {X : Type} [Group X]

private theorem lred3_exists_quotient {G : Type} [Group G] (hX : A6Target X) (Z : Subgroup G)
    [Z.Normal] (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (π : G →* X) (hπ : Function.Surjective π) :
    ∃ φ : G ⧸ Z →* X, Function.Surjective φ := by
  have hle := le_ker_of_commute hX.isSimple hX.noncomm Z hZ π hπ
  refine ⟨QuotientGroup.lift Z π hle, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hπ x
  exact ⟨QuotientGroup.mk g, rfl⟩

private theorem lred3_quotient_equiv {G : Type} [Group G] (hX : A6Target X) (Z : Subgroup G)
    [Z.Normal] (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hGZ : IsSimpleGroup (G ⧸ Z)) (π : G →* X)
    (hπ : Function.Surjective π) : Nonempty (G ⧸ Z ≃* X) := by
  obtain ⟨φ, hφ⟩ := lred3_exists_quotient hX Z hZ π hπ
  have := hX.nontrivial
  exact nonempty_mulEquiv_of_surjective hGZ φ hφ

private theorem lred3_scalars_comm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) :
    ∀ x ∈ (StatedScalars ι K).subgroupOf H, ∀ y ∈ (StatedScalars ι K).subgroupOf H,
      x * y = y * x :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_mul_comm H

private theorem lred3_two_part_360 {c m k : ℕ} (hc : Odd c) (hm : Odd m)
    (h : c * 360 = 2 ^ k * m) : k = 3 := by
  have h1 : 2 ^ 3 * (c * 45) = 2 ^ k * m := by rw [← h]; ring
  have := two_pow_mul_odd_inj (hc.mul (by decide : Odd 45)) hm h1
  exact this.1.symm

theorem lred3_false_of_surjective_su3 (hX : A6Target X) {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = (2 ^ a) ^ 2) (π : ↥(StatedSU 3 (2 ^ a) K) →* X)
    (hπ : Function.Surjective π) : False := by
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := lred3_scalars_comm (StatedSU 3 (2 ^ a) K)
  have : ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ a) K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    obtain ⟨φ, hφ⟩ := lred3_exists_quotient hX _ hZ π hπ
    have hcard : Nat.card (StatedProj (StatedSU 3 (2 ^ a) K)) = 72 := by
      rw [card_psu3 ha hK, show a = 1 by omega]
      norm_num
    have hdvd : Nat.card X ∣ 72 := by
      rw [← hcard, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    rw [hX.card] at hdvd
    norm_num at hdvd
  ·
    have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ a) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 a hK 3 le_rfl
        (fun h => by
          have h2 : 2 ^ a = 2 := congrArg Prod.snd h
          have h4 : 4 ≤ 2 ^ a :=
            (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) ha2
          omega)
    obtain ⟨e⟩ := lred3_quotient_equiv hX _ hZ hsimple π hπ
    have hc : Nat.card (StatedProj (StatedSU 3 (2 ^ a) K)) = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact hX.card
    rw [card_psu3 ha hK] at hc
    have hd : 2 ^ (a * 3) ∣ 360 := by
      rw [← hc, pow_mul]
      exact dvd_mul_right _ _
    have := lred3_le_three_of_two_pow_dvd hd
    omega

theorem lred3_false_of_surjective_sl3 (hX : A6Target X) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m)) (π : ↥(StatedSL 3 K) →* X)
    (hπ : Function.Surjective π) : False := by
  have hZ := lred3_scalars_comm (StatedSL 3 K)
  have : ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  have := (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := K) (by norm_num)
    (Or.inl le_rfl)).2.1
  have hsimple : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
    (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.isSimpleGroup
  obtain ⟨e⟩ := lred3_quotient_equiv hX _ hZ hsimple π hπ
  have hprod := Vol2.Ch11.SecA.card_statedProj_mul (StatedSL 3 K)
  obtain ⟨t, ht, hSL⟩ := Vol2.Ch11.SecA.card_SL3_eq (n := 2 * m) (by omega) hK
  have hcard : Nat.card ↥(StatedSL 3 K) = 2 ^ (3 * (2 * m)) * t := by
    rw [card_statedSL, hSL]
  have hX360 : Nat.card (StatedProj (StatedSL 3 K)) = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact hX.card
  have hcd : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) ∣ 2 ^ (2 * m) - 1 := by
    have := Vol2.Ch11.SecA.card_scalars_subgroupOf_dvd (K := K) (StatedSL 3 K)
    rwa [hK] at this
  have hcodd : Odd (Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))) :=
    Odd.of_dvd_nat (odd_two_pow_sub_one (by omega)) hcd
  rw [hX360, hcard] at hprod
  have := lred3_two_part_360 hcodd ht (by rw [hprod])
  omega

theorem lred3_false_of_surjective_sp4 (hX : A6Target X) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m)) (π : ↥(StatedSp 2 K) →* X)
    (hπ : Function.Surjective π) : False := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) := (MulEquiv.ofBijective _ hbij).isSimpleGroup
  have := hX.nontrivial
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hsimple' π hπ
  have hcard : Nat.card X =
      2 ^ (4 * (2 * m)) * ((2 ^ (2 * (2 * m)) - 1) * (2 ^ (4 * (2 * m)) - 1)) := by
    rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hK]
  exact lred3_sp4_ne_360 (n := 2 * m) (by omega) (hcard ▸ hX.card)

end Proofs

theorem factsA6_holds :
    FactsA6 where
  su3 K _ _ a hK X _ hX π hπ := lred3_false_of_surjective_su3 (A6Target.of_isAlt hX) hK π hπ
  nineTensor K _ _ a ha hK X _ hX π hπ :=
    lred3_false_of_surjective_sl3 (A6Target.of_isAlt hX) ha hK π hπ
  g2Derived K _ _ hK X _ hX π hπ := by
    have hX' := A6Target.of_isAlt hX
    have hd : Nat.card X ∣ 6048 :=
      (C10P01.card_g2Two_commutator hK) ▸ Subgroup.card_dvd_of_surjective hπ
    rw [hX'.card] at hd
    norm_num at hd
  m12 eY hY hw X _ hX π hπ := by
    have hX' := A6Target.of_isAlt hX
    obtain ⟨p, hp, hpe⟩ := C10P01.exists_permAct_eq hY hw
    have hmap : (m24Fix C10P01.dodecadE).map (MulAut.conj p).toMonoidHom = m24Fix eY := by
      rw [← hpe, C10P01.m24Fix_permAct hp]
    let e1 : ↥(m24Fix C10P01.dodecadE) ≃* ↥(m24Fix eY) :=
      ((m24Fix C10P01.dodecadE).equivMapOfInjective _ (MulAut.conj p).injective).trans
        (MulEquiv.subgroupCongr hmap)
    obtain ⟨⟨e2⟩, -⟩ := C10P01.m24Fix_dodecadE_props
    have hs : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    let e : ↥(m24Fix eY) ≃* NativeSporadic.M12 := e1.symm.trans e2
    exact lred3_false_of_simple hX' hs
      (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
      (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective)
  m22 x y hxy X _ hX π hπ := by
    obtain ⟨hs, hc⟩ := C10P01.stab_props_m22 hxy
    exact lred3_false_of_simple (A6Target.of_isAlt hX) hs (by rw [hc]; norm_num) π hπ
  m23 x X _ hX π hπ := by
    obtain ⟨hs, hc⟩ := C10P01.stab_props_m23 x
    exact lred3_false_of_simple (A6Target.of_isAlt hX) hs (by rw [hc]; norm_num) π hπ
  m24 X _ hX π hπ :=
    lred3_false_of_simple (A6Target.of_isAlt hX) CFSG.Monster.Code.AutPerm_isSimpleGroup
      (by rw [CFSG.Monster.Code.card_AutPerm]; norm_num) π hπ
  sp4Twisted K _ _ a ha hK X _ hX π hπ :=
    lred3_false_of_surjective_sp4 (A6Target.of_isAlt hX) ha hK π hπ
  j2 X _ hX := by
    rintro ⟨e⟩
    have hX' := A6Target.of_isAlt hX
    have hc : Nat.card X = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    rw [hX'.card] at hc
    norm_num at hc

end CFSG.Quasithin
