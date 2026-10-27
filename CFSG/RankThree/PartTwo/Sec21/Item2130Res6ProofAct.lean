module

public import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res6Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSL StatedSU)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev barHom (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) →* MulAut (lBar Y) :=
  (thetaQuotMulAut Y).comp Y.normalizerMonoidHom

theorem mem_thetaQuotCentralizer_iff {Y : Subgroup G} {g : G} :
    g ∈ thetaQuotCentralizer Y ↔
      ∃ hg : g ∈ Subgroup.normalizer (Y : Set G), barHom Y ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨⟨g', hg'⟩, hk, rfl⟩
    exact ⟨hg', hk⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem thetaQuotCentralizer_le_normalizer (Y : Subgroup G) :
    thetaQuotCentralizer Y ≤ Subgroup.normalizer (Y : Set G) := by
  rintro _ ⟨⟨g, hg⟩, -, rfl⟩
  exact hg

theorem barHom_of_mem {Y : Subgroup G} {g : G} (hgY : g ∈ Y) :
    barHom Y ⟨g, Subgroup.le_normalizer hgY⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) :=
  KFacts.thetaQuotMulAut_compAction_of_mem hgY (Subgroup.le_normalizer hgY)

theorem not_le_thetaQuotCentralizer {Y U : Subgroup G} (hq : IsQuasisimple (lBar Y))
    (hYU : ⁅Y, U⁆ = Y) : ¬ U ≤ thetaQuotCentralizer Y := by
  intro hU
  have hle : ⁅Y, U⁆ ≤ (aschbacherSolvableCore 3 Y).map Y.subtype := by
    rw [Subgroup.commutator_le]
    intro y hy u hu
    obtain ⟨huN, h1⟩ := mem_thetaQuotCentralizer_iff.mp (hU hu)
    have h2 := congrArg (fun φ : MulAut (lBar Y) =>
      φ ((⟨y⁻¹, Y.inv_mem hy⟩ : Y) : lBar Y)) h1
    simp only [MulAut.one_apply] at h2
    change ((Y.normalizerMonoidHom ⟨u, huN⟩ ⟨y⁻¹, Y.inv_mem hy⟩ : Y) : lBar Y) =
      ((⟨y⁻¹, Y.inv_mem hy⟩ : Y) : lBar Y) at h2
    rw [QuotientGroup.eq] at h2
    refine ⟨_, (aschbacherSolvableCore 3 Y).inv_mem h2, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      normalizerMonoidHom_apply_coe, commutatorElement_def]
    group
  rw [hYU] at hle
  have htop : aschbacherSolvableCore 3 Y = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨t, ht, hty⟩ := hle y.2
    have : t = y := Subtype.ext hty
    rwa [← this]
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨z, hz⟩ := exists_ne (1 : lBar Y)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  exact hz ((QuotientGroup.eq_one_iff y).mpr (htop ▸ Subgroup.mem_top y))

variable {K : Type} [Field K]

@[expose] def ActsVia (Y : Subgroup G) (ε : lBar Y →* ProjGenLinGroup (Fin 3) K) (g : G)
    (y : GL (Fin 3) K) : Prop :=
  ∃ hg : g ∈ Subgroup.normalizer (Y : Set G), ∀ z : lBar Y,
    ε (barHom Y ⟨g, hg⟩ z) = ProjGenLinGroup.mk y * ε z * (ProjGenLinGroup.mk y)⁻¹

variable {Y : Subgroup G} {ε : lBar Y →* ProjGenLinGroup (Fin 3) K}

theorem ActsVia.mul {g h : G} {y y' : GL (Fin 3) K} (hg : ActsVia Y ε g y)
    (hh : ActsVia Y ε h y') : ActsVia Y ε (g * h) (y * y') := by
  obtain ⟨hgN, hg⟩ := hg
  obtain ⟨hhN, hh⟩ := hh
  refine ⟨Subgroup.mul_mem _ hgN hhN, fun z => ?_⟩
  have : (⟨g * h, Subgroup.mul_mem _ hgN hhN⟩ : Subgroup.normalizer (Y : Set G)) =
      ⟨g, hgN⟩ * ⟨h, hhN⟩ := rfl
  rw [this, map_mul, MulAut.mul_apply, hg, hh, map_mul]
  group

theorem ActsVia.inv {g : G} {y : GL (Fin 3) K} (hg : ActsVia Y ε g y) :
    ActsVia Y ε g⁻¹ y⁻¹ := by
  obtain ⟨hgN, hg⟩ := hg
  refine ⟨Subgroup.inv_mem _ hgN, fun z => ?_⟩
  have : (⟨g⁻¹, Subgroup.inv_mem _ hgN⟩ : Subgroup.normalizer (Y : Set G)) = ⟨g, hgN⟩⁻¹ := rfl
  have h1 := hg ((barHom Y ⟨g, hgN⟩)⁻¹ z)
  rw [MulAut.apply_inv_self] at h1
  rw [this, map_inv, map_inv, inv_inv, h1]
  group

theorem ActsVia.pow {g : G} {y : GL (Fin 3) K} (hg : ActsVia Y ε g y) (n : ℕ) :
    ActsVia Y ε (g ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    refine ⟨Subgroup.one_mem _, fun z => ?_⟩
    have : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (Y : Set G)) = 1 := rfl
    rw [this, map_one, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hg

theorem actsVia_one_of_mem (ε : lBar Y →* ProjGenLinGroup (Fin 3) K) {g : G}
    (hg : g ∈ thetaQuotCentralizer Y) : ActsVia Y ε g 1 := by
  obtain ⟨hgN, h⟩ := mem_thetaQuotCentralizer_iff.mp hg
  exact ⟨hgN, fun z => by rw [h, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]⟩

theorem actsVia_of_mem {g : G} (hgY : g ∈ Y) {l : GL (Fin 3) K}
    (hl : ε (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) = ProjGenLinGroup.mk l) :
    ActsVia Y ε g l := by
  refine ⟨Subgroup.le_normalizer hgY, fun z => ?_⟩
  rw [barHom_of_mem hgY, MulAut.conj_apply, map_mul, map_mul, map_inv, hl]

variable {π : Bool} {p f : ℕ}

theorem exists_actsVia_of_mem (hε : ε.range ≤ projImage (slPi π 3 (p ^ f) K)) {g : G}
    (hgY : g ∈ Y) : ∃ l ∈ slPi π 3 (p ^ f) K, ActsVia Y ε g l := by
  obtain ⟨l, hl, hle⟩ := hε ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩, rfl⟩
  exact ⟨l, hl, actsVia_of_mem hgY hle.symm⟩

theorem exists_actsVia_of_mem_sup (hε : ε.range ≤ projImage (slPi π 3 (p ^ f) K)) {g : G}
    (hg : g ∈ Y ⊔ thetaQuotCentralizer Y) : ∃ l ∈ slPi π 3 (p ^ f) K, ActsVia Y ε g l := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Y _
    (thetaQuotCentralizer_le_normalizer Y)] at hg
  obtain ⟨y, hy, k, hk, rfl⟩ := hg
  obtain ⟨l, hl, hyl⟩ := exists_actsVia_of_mem hε hy
  exact ⟨l, hl, by simpa using hyl.mul (actsVia_one_of_mem ε hk)⟩

theorem ActsVia.inv_mul_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (hε : projImage (slPi π 3 (p ^ f) K) ≤ ε.range) {g : G} {y y' : GL (Fin 3) K}
    (hy : ActsVia Y ε g y) (hy' : ActsVia Y ε g y') : y⁻¹ * y' ∈ StatedScalars (Fin 3) K := by
  obtain ⟨hgN, h1⟩ := hy
  obtain ⟨hgN', h2⟩ := hy'
  refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
  rw [← mk_eq_one_iff_mem_statedScalars]
  obtain ⟨z, hz⟩ := hε ⟨s, hs, rfl⟩
  have h3 := (h1 z).symm.trans (h2 z)
  rw [hz] at h3
  simp only [map_mul, map_inv]
  calc (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s *
        ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y')⁻¹ * (ProjGenLinGroup.mk s)⁻¹ =
      (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s *
        (ProjGenLinGroup.mk y')⁻¹) * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s)⁻¹ := by group
    _ = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s *
        (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s)⁻¹ := by
          rw [h3]
    _ = 1 := by group

theorem commMod_of_commute (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (hε : projImage (slPi π 3 (p ^ f) K) ≤ ε.range) {g h : G} {y y' : GL (Fin 3) K}
    (hg : ActsVia Y ε g y) (hh : ActsVia Y ε h y') (hgh : g * h = h * g) :
    y * y' * y⁻¹ * y'⁻¹ ∈ StatedScalars (Fin 3) K := by
  have h1 := hg.mul hh
  rw [hgh] at h1
  have h2 := ActsVia.inv_mul_mem hK hq hε (hh.mul hg) h1
  have h3 := (StatedScalars.normal (Fin 3) K).conj_mem _ h2 (y' * y)
  have e : y' * y * ((y' * y)⁻¹ * (y * y')) * (y' * y)⁻¹ = y * y' * y⁻¹ * y'⁻¹ := by group
  rwa [e] at h3

theorem pow_mem_of_actsVia (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (hε : projImage (slPi π 3 (p ^ f) K) ≤ ε.range) {g : G} {y : GL (Fin 3) K}
    (hg : ActsVia Y ε g y) {n : ℕ} (hn : g ^ n = 1) : y ^ n ∈ StatedScalars (Fin 3) K := by
  have h1 := hg.pow n
  rw [hn] at h1
  have h2 := ActsVia.inv_mul_mem hK hq hε (actsVia_one_of_mem ε (Subgroup.one_mem _)) h1
  rwa [inv_one, one_mul] at h2

theorem ActsVia.mem_thetaQuotCentralizer
    (hfaith : ∀ φ : MulAut (lBar Y), (∀ z, ε (φ z) = ε z) → φ = 1) {g : G} {y : GL (Fin 3) K}
    (hy : ActsVia Y ε g y) (hys : y ∈ StatedScalars (Fin 3) K) : g ∈ thetaQuotCentralizer Y := by
  obtain ⟨hgN, h⟩ := hy
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hgN, hfaith _ fun z => ?_⟩
  rw [h, mk_eq_one_iff_mem_statedScalars.mpr hys, one_mul, inv_one, mul_one]

theorem mem_sup_of_actsVia (hε : projImage (slPi π 3 (p ^ f) K) ≤ ε.range)
    (hfaith : ∀ φ : MulAut (lBar Y), (∀ z, ε (φ z) = ε z) → φ = 1) {g : G} {y l : GL (Fin 3) K}
    (hy : ActsVia Y ε g y) (hl : l ∈ slPi π 3 (p ^ f) K)
    (hyl : y⁻¹ * l ∈ StatedScalars (Fin 3) K) : g ∈ Y ⊔ thetaQuotCentralizer Y := by
  obtain ⟨z, hz⟩ := hε ⟨l, hl, rfl⟩
  obtain ⟨⟨y₀, hy₀⟩, rfl⟩ := QuotientGroup.mk_surjective z
  have h0 : ActsVia Y ε y₀ l := actsVia_of_mem hy₀ hz
  have h1 := hy.mul h0.inv
  have hsc : y * l⁻¹ ∈ StatedScalars (Fin 3) K := by
    have h2 := inv_mem hyl
    rw [mul_inv_rev, inv_inv] at h2
    have h3 := (StatedScalars.normal (Fin 3) K).conj_mem _ h2 y
    rwa [show y * (l⁻¹ * y) * y⁻¹ = y * l⁻¹ by group] at h3
  have hk := h1.mem_thetaQuotCentralizer hfaith hsc
  have e : g = (g * y₀⁻¹) * y₀ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hy₀)

structure IsBarModel (Y : Subgroup G) (π : Bool) (p f : ℕ) (K : Type) [Field K]
    (ε : lBar Y →* ProjGenLinGroup (Fin 3) K) : Prop where
  field : PiField π p f K
  modThree : ModThree π (p ^ f)
  two_lt : 2 < p ^ f
  range_eq : ε.range = projImage (slPi π 3 (p ^ f) K)
  faithful : ∀ φ : MulAut (lBar Y), (∀ z, ε (φ z) = ε z) → φ = 1

omit [Finite G] in
theorem IsBarModel.isPerfect (h : IsBarModel Y π p f K ε) [Group.IsPerfect (lBar Y)] :
    Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
  h.range_eq ▸ Group.IsPerfect.range ε

theorem mulAut_eq_one_of_central {Q : Type*} [Group Q] [hQ : Group.IsPerfect Q] (φ : MulAut Q)
    (h : ∀ x, x⁻¹ * φ x ∈ Subgroup.center Q) : φ = 1 := by
  let δ : Q →* Subgroup.center Q :=
    { toFun := fun x => ⟨x⁻¹ * φ x, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        change (x * y)⁻¹ * φ (x * y) = x⁻¹ * φ x * (y⁻¹ * φ y)
        calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by simp [mul_assoc]
          _ = x⁻¹ * φ x * y⁻¹ * φ y := by rw [hc]
          _ = x⁻¹ * φ x * (y⁻¹ * φ y) := by simp [mul_assoc] }
  have hker : commutator Q ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hQ.commutator_eq_top] at hker
  ext x
  have hx : δ x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have := congrArg Subtype.val hx
  simp only [OneMemClass.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

omit [Finite G] in
theorem isBarModel_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f)
    (e : lBar Y ≃* projImage (slPi π 3 (p ^ f) K)) :
    IsBarModel Y π p f K ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom) where
  field := hK
  modThree := hq
  two_lt := h2
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ e.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  faithful := fun φ hφ => by
    ext z
    have h1 := hφ z
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom] at h1
    rw [MulAut.one_apply]
    exact e.injective (Subtype.ext h1)

omit [Finite G] in
theorem isBarModel_slPi [Group.IsPerfect (lBar Y)] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f) (e : lBar Y ≃* slPi π 3 (p ^ f) K) :
    IsBarModel Y π p f K
      ((ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
        ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) where
  field := hK
  modThree := hq
  two_lt := h2
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    rfl
  faithful := fun φ hφ => by
    refine mulAut_eq_one_of_central φ fun z => ?_
    have h1 := hφ z
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom] at h1
    have hs : ((e z : GL (Fin 3) K))⁻¹ * (e (φ z) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h1, inv_mul_cancel]
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (commute_of_mem_statedScalars hs (e w : GL (Fin 3) K))

theorem isSolvable_slPi_false_of_eq_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable (slPi false 3 (p ^ f) K) := by
  have hp : p.Prime := hK.prime
  have hp2 : p = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd p ⟨p ^ (f - 1), by
      rw [← pow_succ', Nat.sub_add_cancel hK.one_le, h2]⟩ with h | h
    · exact absurd h hp.one_lt.ne'
    · exact h
  have hf1 : f = 1 := by
    rw [hp2] at h2
    exact Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 1 by rw [h2, pow_one])
  subst hp2 hf1
  have hU := hK.unitary
  have := hK.finite
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  exact hsolv

theorem two_lt_of_ne (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h : ¬ (π = false ∧ p ^ f = 2)) : 2 < p ^ f := by
  have h2 : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
  rcases Nat.lt_or_ge 2 (p ^ f) with h3 | h3
  · exact h3
  · exfalso
    have hq2 : p ^ f = 2 := by omega
    cases π
    · exact h ⟨rfl, hq2⟩
    · change p ^ f % 3 = 1 at hq
      omega

theorem two_lt_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {X : Type} [Group X]
    (hX : IsQuasisimple X) (e : X ≃* slPi π 3 (p ^ f) K) : 2 < p ^ f := by
  refine two_lt_of_ne hK hq fun ⟨hπ, h2⟩ => ?_
  subst hπ
  have hsolv := isSolvable_slPi_false_of_eq_two hK h2
  have : Group.IsPerfect X := hX.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hX
  exact Group.IsPerfect.not_isSolvable X
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem two_lt_of_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {X : Type}
    [Group X] (hX : IsQuasisimple X) (e : X ≃* projImage (slPi π 3 (p ^ f) K)) :
    2 < p ^ f := by
  refine two_lt_of_ne hK hq fun ⟨hπ, h2⟩ => ?_
  subst hπ
  have hsolv := isSolvable_slPi_false_of_eq_two hK h2
  have h1 : Group.IsSolvable (projImage (slPi false 3 (p ^ f) K)) :=
    Group.isSolvable_of_surjective (projOf_surjective (slPi false 3 (p ^ f) K))
  have : Group.IsPerfect X := hX.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hX
  exact Group.IsPerfect.not_isSolvable X
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem odd_oThreePrime_of_projImage (hK : PiField π p f K) (h2 : 2 < p ^ f) {X : Type}
    [Group X] [Finite X] (e : X ≃* projImage (slPi π 3 (p ^ f) K)) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have := hK.finite
  cases π
  · exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv
      (e.trans (psuEquivUnitary hK.unitary))
      (Item49OddChar.odd_card_oThreePrime_outer_unitaryPSU_three hK.unitary h2)
  · exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv (e.trans (pslEquivProjective _ K))
      (Item49OddChar.odd_card_oThreePrime_outer_projectiveSL_three K)

theorem odd_oThreePrime_of_slPi (hK : PiField π p f K) (h2 : 2 < p ^ f) {X : Type} [Group X]
    [Finite X] [Group.IsPerfect X] (e : X ≃* slPi π 3 (p ^ f) K) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have := hK.finite
  cases π
  · exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv_unitarySU hK.unitary h2
      (e.trans (slPiFalseEquiv p f K))
  · exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv_statedSL (K := K) e

theorem le_sup_thetaQuotCentralizer_of_odd
    (hodd : Odd (Nat.card (oThreePrime (Outer (lBar Y))))) {X U : Subgroup G}
    (hX3 : IsPGroup 3 X) (hXN : X ≤ Subgroup.normalizer (Y : Set G))
    (hUN : U ≤ Subgroup.normalizer (Y : Set G)) (hU2 : IsPGroup 2 U) (hXU : ⁅X, U⁆ = U) :
    U ≤ Y ⊔ thetaQuotCentralizer Y := by
  set N := Subgroup.normalizer (Y : Set G) with hN
  set φ : N →* Outer (lBar Y) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (lBar Y))).comp
      (barHom Y) with hφ
  set O := oThreePrime (Outer (lBar Y))
  have hUO : U ≤ (O.comap φ).map N.subtype := by
    rw [← hXU, Subgroup.commutator_le]
    intro x hx u hu
    have hxN : x ∈ N := hXN hx
    have huN : u ∈ N := hUN hu
    refine ⟨⁅(⟨x, hxN⟩ : N), ⟨u, huN⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX3) ⟨x, hx⟩
    have hx3 : φ ⟨x, hxN⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : N) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have h := congrArg Subtype.val (pow_orderOf_eq_one (⟨x, hx⟩ : X))
        rw [hk] at h
        simpa using h
      rw [this, map_one]
    set a := φ ⟨x, hxN⟩
    set b := φ ⟨u, huN⟩
    have hconj : (b * a⁻¹ * b⁻¹) ^ 3 ^ k = 1 := by
      rw [conj_pow, inv_pow, hx3, inv_one, mul_one, mul_inv_cancel]
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact Subgroup.mul_mem _ (mem_oThreePrime_of_pow hx3) (mem_oThreePrime_of_pow hconj)
  intro u hu
  obtain ⟨⟨u', hu'N⟩, hmem₀, rfl⟩ := hUO hu
  have hmem : φ ⟨u', hu'N⟩ ∈ O := Subgroup.mem_comap.mp hmem₀
  have : Finite (Outer (lBar Y)) := Item49OddChar.finite_outer _
  have hcop : Nat.Coprime (Nat.card O) (Nat.card U) := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have hord : orderOf (⟨φ ⟨u', hu'N⟩, hmem⟩ : O) = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hcop.gcd_eq_one]
    refine Nat.dvd_gcd (orderOf_dvd_natCard _) ?_
    rw [Subgroup.orderOf_mk]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    have hu' : u' ∈ U := hu
    have h1 : orderOf (⟨u', hu'⟩ : U) ∣ Nat.card U := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h1
  have h1 : φ ⟨u', hu'N⟩ = 1 := by
    have := orderOf_eq_one_iff.mp hord
    exact congrArg Subtype.val this
  have hinn : barHom Y ⟨u', hu'N⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (lBar Y) :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨z, hz⟩ := hinn
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
  have hℓN : ((ℓ : Y) : G)⁻¹ ∈ N := Subgroup.inv_mem _ (Subgroup.le_normalizer ℓ.2)
  have hcN : u' * ((ℓ : Y) : G)⁻¹ ∈ N := Subgroup.mul_mem _ hu'N hℓN
  have hcC : u' * ((ℓ : Y) : G)⁻¹ ∈ thetaQuotCentralizer Y := by
    refine mem_thetaQuotCentralizer_iff.mpr ⟨hcN, ?_⟩
    have hsplit : (⟨u' * ((ℓ : Y) : G)⁻¹, hcN⟩ : N) = ⟨u', hu'N⟩ * ⟨((ℓ : Y) : G)⁻¹, hℓN⟩ := rfl
    rw [hsplit, map_mul, ← hz, barHom_of_mem (Subgroup.inv_mem _ ℓ.2)]
    have hinvℓ : QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
        ⟨((ℓ : Y) : G)⁻¹, Subgroup.inv_mem _ ℓ.2⟩ =
        (QuotientGroup.mk ℓ : lBar Y)⁻¹ := by
      rw [show (⟨((ℓ : Y) : G)⁻¹, Subgroup.inv_mem _ ℓ.2⟩ : Y) = ℓ⁻¹ from rfl, map_inv]
      rfl
    rw [hinvℓ, map_inv, mul_inv_cancel]
  have heq : u' = (u' * ((ℓ : Y) : G)⁻¹) * ((ℓ : Y) : G) := by group
  change u' ∈ Y ⊔ thetaQuotCentralizer Y
  rw [heq, sup_comm]
  exact Subgroup.mul_mem_sup hcC ℓ.2

end CFSG.RankThree.PartTwo.Sec21.Item2130Res6Proof
