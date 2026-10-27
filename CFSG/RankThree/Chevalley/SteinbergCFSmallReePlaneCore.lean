module

public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.RankThree.SteinbergR3ESmallReeRadical
public import CFSG.RankThree.SteinbergR3ELinearTwoPrimeCentralizer
public import CFSG.RankThree.GroupTheory.SteinbergBKSmallSylowTwoCommutatorOdd
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.Walter.Ree.Model.Fusion
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innerAut
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (coordinatePSLAction
  coordinatePSLAction_injective coordinatePSLAction_range_eq_G coordinateG_le_D coordinateD)
open CFSG.Walter.Ree.Model (smallReeH smallReeInvCentralizer)
open scoped commutatorElement MatrixGroups Pointwise

theorem isCyclic_centralizer_PSL2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpK : p ≠ ringChar K) {y : PSL(2, K)} (hy : orderOf y = p) :
    IsCyclic (Subgroup.centralizer ({y} : Set (PSL(2, K)))) := by
  set f := coordinatePSLAction K with hf
  have hfinj := coordinatePSLAction_injective K
  have hyD : f y ∈ coordinateD K :=
    coordinateG_le_D K (coordinatePSLAction_range_eq_G K ▸ ⟨y, rfl⟩)
  have hfy : orderOf (f y) = p := by rw [orderOf_injective f hfinj y, hy]
  have hcyc := (CFSG.RankThree.LinearTwo.linear_two_inner_prime_centralizer_alternatives K hp hp3
    hyD hfy).1 hpK
  refine isCyclic_of_injective (((f.comp (Subgroup.centralizer {y}).subtype).codRestrict
    (coordinateD K ⊓ Subgroup.centralizer {f y}) fun g => ⟨coordinateG_le_D K
      (coordinatePSLAction_range_eq_G K ▸ ⟨g, rfl⟩), ?_⟩)) ?_
  · change f (g : PSL(2, K)) ∈ Subgroup.centralizer {f y}
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 g.2]
  · intro g g' h
    exact Subtype.ext (hfinj (congrArg Subtype.val h))

theorem mem_right_of_pow_eq_one_of_odd {X : Type*} [Group X] {t : X} (ht : t ^ 2 = 1)
    {L C : Subgroup X} (hd : CFSG.Walter.JT.IsInternalDirectProduct (Subgroup.zpowers t) L C)
    {y : X} (hy : y ∈ C) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : y ∈ L := by
  obtain ⟨u, hu, l, hl, rfl⟩ := hd.exists_mul hy
  have h1 := (hd.pow_eq_one_of_mul hu hl hym).1
  have h2 : u ^ 2 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  have hu1 : u = 1 := by
    have h3 : orderOf u ∣ Nat.gcd m 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.coprime_two_right.2 hm] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  rw [hu1, one_mul]
  exact hl

theorem eq_bot_of_normal_solvable_of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : ∀ R : Subgroup H', R.Normal → Group.IsSolvable R → R = ⊥) :
    ∀ R : Subgroup H, R.Normal → Group.IsSolvable R → R = ⊥ := by
  intro R hRn hRs
  have h1 := h (R.map e.toMonoidHom) (hRn.map _ e.surjective)
    (Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective R e.toMonoidHom
      e.injective).toMonoidHom) (MulEquiv.surjective _))
  exact (Subgroup.map_eq_bot_iff_of_injective R e.injective).1 h1

theorem isElementaryAbelian_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) [IsElementaryAbelian p H] : IsElementaryAbelian p G :=
  { is_comm := ⟨fun x y => hf (by rw [map_mul, map_mul]; exact IsMulCommutative.is_comm.comm _ _)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hf (by
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p H)
        _) }

theorem smallReeH_neg_one_sq {a : ℕ} {K : Type} [Field K] : smallReeH a K (-1) ^ 2 = 1 := by
  rw [sq, ← CFSG.Walter.Ree.Model.smallReeH_mul, show ((-1 : Kˣ) * -1) = 1 by simp,
    CFSG.Walter.Ree.Model.smallReeH_one]

section SmallRee

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem exists_smallRee_involution_centralizer_factor (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ L : Subgroup (ModGL ReeTag.G2.tag K),
      CFSG.Walter.JT.IsInternalDirectProduct (Subgroup.zpowers (smallReeH a K (-1))) L
        (smallReeInvCentralizer a K) ∧
      ∀ {p : ℕ}, p.Prime → 3 < p → ∀ y ∈ L, orderOf y = p →
        IsCyclic ↥(L ⊓ Subgroup.centralizer {y}) := by
  classical
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, -, -, -, -, -, -, hdp, e, -⟩ :=
    CFSG.Walter.Ree.Model.small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  refine ⟨ψ.range, hdp, fun {p} hp hp3 y hy hyp => ?_⟩
  set y' := e.symm ⟨y, hy⟩ with hy'
  have hy'p : orderOf y' = p := by
    rw [hy', MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyp]
  have hcyc := isCyclic_centralizer_PSL2 hp hp3 (by rw [ringChar.eq K 3]; omega) hy'p
  refine isCyclic_of_injective (G' := ↥(Subgroup.centralizer ({y'} : Set (PSL(2, K)))))
    { toFun := fun l => ⟨e.symm ⟨l, l.2.1⟩, ?_⟩
      map_one' := Subtype.ext (show e.symm 1 = 1 from map_one _)
      map_mul' := fun l l' => Subtype.ext (by
        change e.symm ⟨_, _⟩ = e.symm ⟨_, _⟩ * e.symm ⟨_, _⟩
        rw [← map_mul]
        rfl) } ?_
  · rw [Subgroup.mem_centralizer_singleton_iff, hy', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 l.2.2)
  · intro l l' h
    have h1 : e.symm ⟨l, l.2.1⟩ = e.symm ⟨l', l'.2.1⟩ := congrArg Subtype.val h
    have h2 := e.symm.injective h1
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3

theorem smallRee_false_of_plane_le_centralizer_involution (hK : Nat.card K = 3 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {z : ModGL ReeTag.G2.tag K}
    (hzΓ : z ∈ ReeTag.G2.reeGamma K a) (hz : orderOf z = 2)
    (E : Subgroup (ModGL ReeTag.G2.tag K)) (hEΓ : E ≤ ReeTag.G2.reeGamma K a)
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEz : E ≤ Subgroup.centralizer {z}) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hgΓ, hgz⟩ := (CFSG.Walter.Ree.Model.small_Ree_prime_field_involution_fusion a K hK
    w₀ hw₀).2.2.2.2.2 z hzΓ hz
  obtain ⟨L, hdp, hLcyc⟩ := exists_smallRee_involution_centralizer_factor (a := a) hK
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'el : IsElementaryAbelian p E' := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hE'C : E' ≤ smallReeInvCentralizer a K := by
    rintro _ ⟨e, he, rfl⟩
    show _ ∈ ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {smallReeH a K (-1)}
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgΓ (hEΓ he)) (inv_mem hgΓ), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgz]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hEz he)
    change g * e * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * e * g⁻¹)
    calc g * e * g⁻¹ * (g * z * g⁻¹) = g * (e * z) * g⁻¹ := by group
      _ = g * (z * e) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * (g * e * g⁻¹) := by group
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hE'L : E' ≤ L := fun y hy => mem_right_of_pow_eq_one_of_odd smallReeH_neg_one_sq hdp
    (hE'C hy) hpodd (elemPow_eq_one_of_isElementaryAbelian (A := E') y hy)
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  have : Finite E' := Nat.finite_of_card_ne_zero (by rw [hE'card]; positivity)
  have h1p : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := E')).1 fun h => by
    rw [h, Subgroup.card_bot] at hE'card
    omega
  have hy1' : y ≠ 1 := by
    rintro rfl
    exact hy1 rfl
  have hyp : orderOf y = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := E') y hy) hy1'
  have hcyc := hLcyc hp hp3 y (hE'L hy) hyp
  have hE'le : E' ≤ L ⊓ Subgroup.centralizer {y} := fun u hu => ⟨hE'L hu,
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hE'el.is_comm.comm ⟨u, hu⟩ ⟨y, hy⟩))⟩
  have : IsCyclic E' :=
    isCyclic_of_injective (Subgroup.inclusion hE'le) (Subgroup.inclusion_injective hE'le)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hE'card this

theorem smallRee_false_of_eight_le_centralizer_prime (hK : Nat.card K = 3 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {x : ModGL ReeTag.G2.tag K}
    (hxΓ : x ∈ ReeTag.G2.reeGamma K a) (hx : orderOf x = p)
    (T : Subgroup (ModGL ReeTag.G2.tag K)) (hTΓ : T ≤ ReeTag.G2.reeGamma K a)
    (hT2 : ∀ u ∈ T, u ^ 2 = 1) (hTcard : Nat.card T = 8)
    (hTx : T ≤ Subgroup.centralizer {x}) : False := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hTcomm : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := by
    intro u hu v hv
    have h1 := hT2 _ (mul_mem hu hv)
    have h2 := hT2 u hu
    have h3 := hT2 v hv
    rw [sq] at h1 h2 h3
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right h2,
      inv_eq_of_mul_eq_one_right h3]
  obtain ⟨⟨z, hzT⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T)).1 fun h => by
    rw [h, Subgroup.card_bot] at hTcard
    omega
  have hz1' : z ≠ 1 := by
    rintro rfl
    exact hz1 rfl
  have hz : orderOf z = 2 := orderOf_eq_prime (hT2 z hzT) hz1'
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hgΓ, hgz⟩ := (CFSG.Walter.Ree.Model.small_Ree_prime_field_involution_fusion a K hK
    w₀ hw₀).2.2.2.2.2 z (hTΓ hzT) hz
  obtain ⟨L, hdp, hLcyc⟩ := exists_smallRee_involution_centralizer_factor (a := a) hK
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  set x' := g * x * g⁻¹ with hx'
  have hconj : ∀ u v : ModGL ReeTag.G2.tag K, u * v = v * u →
      g * u * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * u * g⁻¹) := fun u v h => by
    calc g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * (v * u) * g⁻¹ := by rw [h]
      _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group
  have hT'C : T' ≤ smallReeInvCentralizer a K := by
    rintro _ ⟨u, hu, rfl⟩
    show _ ∈ ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {smallReeH a K (-1)}
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgΓ (hTΓ hu)) (inv_mem hgΓ), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgz]
    exact hconj u z (hTcomm u hu z hzT)
  have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 (hTx hzT)
  have hx'C : x' ∈ smallReeInvCentralizer a K := by
    show _ ∈ ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {smallReeH a K (-1)}
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgΓ hxΓ) (inv_mem hgΓ), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgz]
    exact hconj x z hzx.symm
  have hT'x : ∀ u ∈ T', u * x' = x' * u := by
    rintro _ ⟨u, hu, rfl⟩
    exact hconj u x (Subgroup.mem_centralizer_singleton_iff.1 (hTx hu))
  have hT'2 : ∀ u ∈ T', u ^ 2 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    change (g * u * g⁻¹) ^ 2 = 1
    rw [conj_pow, hT2 u hu, mul_one, mul_inv_cancel]
  have hx'p : orderOf x' = p := by
    rw [hx', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hx'L : x' ∈ L := mem_right_of_pow_eq_one_of_odd smallReeH_neg_one_sq hdp hx'C hpodd
    (by rw [← hx'p]; exact pow_orderOf_eq_one x')
  have hcyc := hLcyc hp hp3 x' hx'L hx'p
  set Z := Subgroup.zpowers (smallReeH a K (-1)) with hZ
  set D := L ⊓ Subgroup.centralizer {x'} with hD
  have hdec : ∀ u : T', ∃ c : Z × {l : D // l ^ 2 = 1},
      (c.1 : ModGL ReeTag.G2.tag K) * ((c.2 : D) : ModGL ReeTag.G2.tag K) = u := by
    intro u
    obtain ⟨c, hc, l, hl, hcl⟩ := hdp.exists_mul (hT'C u.2)
    have hl2 : l ^ 2 = 1 := (hdp.pow_eq_one_of_mul hc hl (by rw [hcl]; exact hT'2 u u.2)).2
    have hcx : c * x' = x' * c := hdp.commute hc hx'L
    have hlx : l * x' = x' * l := by
      have hu := hT'x u u.2
      rw [← hcl] at hu
      refine mul_left_cancel (a := c) ?_
      calc c * (l * x') = c * l * x' := by group
        _ = x' * (c * l) := hu
        _ = x' * c * l := by group
        _ = c * x' * l := by rw [← hcx]
        _ = c * (x' * l) := by group
    exact ⟨(⟨c, hc⟩, ⟨⟨l, hl, Subgroup.mem_centralizer_singleton_iff.2 hlx⟩,
      Subtype.ext (by simpa using hl2)⟩), hcl⟩
  choose F hF using hdec
  have hFinj : Function.Injective F := fun u v h => Subtype.ext (by rw [← hF u, ← hF v, h])
  have hle := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_prod] at hle
  have hZc : Nat.card Z ≤ 2 := by
    rw [hZ, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos smallReeH_neg_one_sq
  have hDc : Nat.card {l : D // l ^ 2 = 1} ≤ 2 := by
    have : Fintype D := Fintype.ofFinite D
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le two_pos
  have hT'card : Nat.card T' = 8 := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj g).injective, hTcard]
  rw [hT'card] at hle
  nlinarith

theorem smallRee_mem_inner_of_pow_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (β : MulAut (ReeTag.G2.reeGamma K a)) (k : ℕ) (hβ : β ^ 2 ^ k = 1) :
    β ∈ innerAut (ReeTag.G2.reeGamma K a) := by
  obtain ⟨-, -, -, -, hOutodd, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  have h1 : orderOf (QuotientGroup.mk' (innerAut (ReeTag.G2.reeGamma K a)) β) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ, map_one])
  have h2 : orderOf (QuotientGroup.mk' (innerAut (ReeTag.G2.reeGamma K a)) β) ∣
      Nat.card (Outer (ReeTag.G2.reeGamma K a)) := orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj0 : j = 0 := by
    by_contra hj0
    have h3 : 2 ∣ Nat.card (Outer (ReeTag.G2.reeGamma K a)) :=
      (dvd_pow_self 2 hj0).trans (by rw [← hj]; exact h2)
    exact (Nat.not_even_iff_odd.2 hOutodd) (even_iff_two_dvd.2 h3)
  rw [hj0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj
  exact hj

theorem odd_card_core_of_fixed_radical {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥)
    (hOut : Odd (Nat.card (Outer G))) {p : ℕ} (hp : p.Prime) (B : Subgroup (MulAut G))
    (hB : innerAut G ≤ B) (x : B) [Finite B]
    (hrad : ∀ R : Subgroup ((x : MulAut G).toMonoidHom.eqLocus (MonoidHom.id G)), R.Normal →
      Group.IsSolvable R → R = ⊥) :
    Odd (Nat.card (aschbacherSolvableCore p (Subgroup.centralizer ({x} : Set B)))) := by
  classical
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨-, hRchar, -⟩ :=
    solvable_prime_complement_core_characterization (H := Subgroup.centralizer ({x} : Set B)) hp
  have hRn : (aschbacherSolvableCore p (Subgroup.centralizer ({x} : Set B))).Normal :=
    Subgroup.normal_of_characteristic _
  have hRsolv := (solvable_prime_complement_core_characterization
    (H := Subgroup.centralizer ({x} : Set B)) hp).1
  let Rm : Subgroup (MulAut G) := ((aschbacherSolvableCore p
    (Subgroup.centralizer ({x} : Set B))).map (Subgroup.centralizer ({x} : Set B)).subtype).map
      B.subtype
  let Fx : Subgroup G := (x : MulAut G).toMonoidHom.eqLocus (MonoidHom.id G)
  let P : Subgroup G := Rm.comap MulAut.conj
  have hcomm_iff : ∀ g : G,
      g ∈ Fx ↔ MulAut.conj g * (x : MulAut G) = (x : MulAut G) * MulAut.conj g := by
    intro g
    have h1 := CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv (x : MulAut G) g
    constructor
    · intro hg
      have hg' : (x : MulAut G) g = g := hg
      rw [hg'] at h1
      calc MulAut.conj g * (x : MulAut G) =
          (x : MulAut G) * MulAut.conj g * (x : MulAut G)⁻¹ * (x : MulAut G) := by rw [h1]
        _ = (x : MulAut G) * MulAut.conj g := by group
    · intro hg
      change (x : MulAut G) g = g
      apply hinj
      rw [← h1, ← hg, mul_inv_cancel_right]
  have hPFx : P ≤ Fx := by
    intro g hg
    obtain ⟨_, ⟨r, -, rfl⟩, hrg⟩ := hg
    have hr : (r : B) ∈ Subgroup.centralizer ({x} : Set B) := r.2
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hr)
    rw [hcomm_iff]
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
    rw [← hrg]
    exact h1
  have hPnormal : (P.subgroupOf Fx).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, ⟨r, hr, rfl⟩, hrn⟩ := hn
    have hgB : MulAut.conj (g : G) ∈ B := hB ⟨g, rfl⟩
    have hgC : (⟨MulAut.conj (g : G), hgB⟩ : B) ∈ Subgroup.centralizer ({x} : Set B) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ((hcomm_iff g).1 g.2))
    let c : Subgroup.centralizer ({x} : Set B) := ⟨⟨MulAut.conj (g : G), hgB⟩, hgC⟩
    refine ⟨(Subgroup.centralizer ({x} : Set B)).subtype (c * r * c⁻¹),
      ⟨c * r * c⁻¹, hRn.conj_mem r hr c, rfl⟩, ?_⟩
    change MulAut.conj (g : G) * ((r : B) : MulAut G) * (MulAut.conj (g : G))⁻¹ =
      MulAut.conj ((g * n * g⁻¹ : Fx) : G)
    have hrn' : ((r : B) : MulAut G) = MulAut.conj (n : G) := hrn
    rw [hrn', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  have hPsolv : Group.IsSolvable (P.subgroupOf Fx) := by
    have hle : P.map MulAut.conj ≤ Rm := Subgroup.map_comap_le _ _
    have hRm : Group.IsSolvable Rm := by
      have e1 := Subgroup.equivMapOfInjective (aschbacherSolvableCore p
        (Subgroup.centralizer ({x} : Set B))) _
          (Subgroup.centralizer ({x} : Set B)).subtype_injective
      have e2 := Subgroup.equivMapOfInjective ((aschbacherSolvableCore p
        (Subgroup.centralizer ({x} : Set B))).map (Subgroup.centralizer ({x} : Set B)).subtype)
          B.subtype B.subtype_injective
      exact Group.isSolvable_of_surjective (f := (e1.trans e2).toMonoidHom)
        (e1.trans e2).surjective
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hle).comp ((Subgroup.equivMapOfInjective P _ hinj).toMonoidHom.comp
        (Subgroup.subgroupOfEquivOfLe hPFx).toMonoidHom))
      ((Subgroup.inclusion_injective hle).comp
        ((Subgroup.equivMapOfInjective P _ hinj).injective.comp
          (Subgroup.subgroupOfEquivOfLe hPFx).injective))
  have hPbot : P = ⊥ := by
    have h1 := hrad (P.subgroupOf Fx) hPnormal hPsolv
    rw [Subgroup.subgroupOf_eq_bot] at h1
    exact eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Subgroup.disjoint_def.1 h1 hg (hPFx hg))
  have hRmOut : Function.Injective ((QuotientGroup.mk' (innerAut G)).comp Rm.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨g, hg⟩ : (y : MulAut G) ∈ (MulAut.conj : G →* MulAut G).range := hy
    have hgP : g ∈ P := by
      change MulAut.conj g ∈ Rm
      rw [hg]
      exact y.2
    have hg1 : g = 1 := by
      rw [hPbot] at hgP
      exact hgP
    exact Subtype.ext (by rw [← hg, hg1, map_one]; rfl)
  have hcardR : Nat.card (aschbacherSolvableCore p (Subgroup.centralizer ({x} : Set B))) =
      Nat.card Rm := by
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set B)).subtype_injective]
  rw [hcardR]
  exact hOut.of_dvd_nat (Subgroup.card_dvd_of_injective _ hRmOut)

theorem smallRee_fixed_radical_of_not_inner (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (x : MulAut (ReeTag.G2.reeGamma K a))
    (hxp : orderOf x = p) (hxinn : x ∉ innerAut (ReeTag.G2.reeGamma K a)) :
    ∀ R : Subgroup (x.toMonoidHom.eqLocus (MonoidHom.id (ReeTag.G2.reeGamma K a))), R.Normal →
      Group.IsSolvable R → R = ⊥ := by
  classical
  obtain ⟨hpf, δ, σ, -, hδ, hkcard, hfix⟩ :=
    CFSG.RankThree.small_Ree_large_prime_field_coset_descent a ha K hK hp hp3 x hxp hxinn
  have hdp : (2 * a + 1) / p * p = 2 * a + 1 := Nat.div_mul_cancel hpf
  have hodd : Odd ((2 * a + 1) / p * p) := by
    rw [hdp]
    exact odd_two_mul_add_one a
  have hdodd : Odd ((2 * a + 1) / p) := (Nat.odd_mul.1 hodd).1
  have hkcard' : Nat.card (fixSubfield σ) = 3 ^ (2 * (((2 * a + 1) / p - 1) / 2) + 1) := by
    rw [hkcard]
    obtain ⟨c, hc⟩ := hdodd
    congr 1
    omega
  have hrad := (small_Ree_native_fixed_groups_solvable_radical_trivial
    (((2 * a + 1) / p - 1) / 2) (fixSubfield σ) hkcard').1
  have eσ : ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2) :=
    ((Subgroup.equivMapOfInjective _ (ReeTag.G2.reeGamma K a).subtype
      (ReeTag.G2.reeGamma K a).subtype_injective).trans (MulEquiv.subgroupCongr hfix)).trans
      (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm
  have hxδ : x = δ⁻¹ * ReeTag.G2.reeGammaFieldAut K a σ * δ := by
    rw [← hδ]
    group
  have hFxσ : (x.toMonoidHom.eqLocus (MonoidHom.id _)).map δ.toMonoidHom =
      (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : x g = g := hg
      change ReeTag.G2.reeGammaFieldAut K a σ (δ g) = δ g
      rw [← hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hg']
    · intro hh
      have hh' : ReeTag.G2.reeGammaFieldAut K a σ h = h := hh
      refine ⟨δ⁻¹ h, ?_, by simp⟩
      change x (δ⁻¹ h) = δ⁻¹ h
      rw [hxδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hh']
  have ex := (Subgroup.equivMapOfInjective (x.toMonoidHom.eqLocus (MonoidHom.id _))
    δ.toMonoidHom δ.injective).trans (MulEquiv.subgroupCongr hFxσ)
  exact eq_bot_of_normal_solvable_of_mulEquiv (ex.trans eσ) hrad

theorem smallRee_commutator_le_pPrimeCore (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (ReeTag.G2.reeGamma K a)))
    (A : Subgroup B) [IsElementaryAbelian p A] (t : B) (htA : t ∈ A) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (ReeTag.G2.reeGamma K a)) ∈ innerAut (ReeTag.G2.reeGamma K a))
    (S : Subgroup B) (hSC : S ≤ Subgroup.centralizer ({t} : Set B))
    (hAN : A ≤ Subgroup.normalizer (S : Set B)) (hSsolv : Group.IsSolvable S)
    (hpS : ¬p ∣ Nat.card S) :
    ⁅S, A⁆ ≤ inSubgroup (pPrimeCore 2) S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hZ := (small_Ree_fixed_group_center_trivial a K hK).1
  have hinj : Function.Injective (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)) := mulAut_conj_injective_of_center_eq_bot hZ
  have htp : orderOf t = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := A) t htA) ht1
  obtain ⟨x₀, hx₀⟩ : (t : MulAut (ReeTag.G2.reeGamma K a)) ∈
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range := htinn
  have hx₀p : orderOf x₀ = p := by
    rw [← orderOf_injective _ hinj x₀, hx₀, Subgroup.orderOf_coe, htp]
  have hT : ∃ T : Sylow 2 S, Nat.card (T : Subgroup S) ≤ 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T⟩ : Nonempty (Sylow 2 S) := inferInstance
    refine ⟨T, ?_⟩
    by_contra hT4
    push Not at hT4
    let Tm : Subgroup (MulAut (ReeTag.G2.reeGamma K a)) :=
      ((T : Subgroup S).map S.subtype).map B.subtype
    have hTmcard : Nat.card Tm = Nat.card (T : Subgroup S) := by
      rw [Subgroup.card_map_of_injective B.subtype_injective,
        Subgroup.card_map_of_injective S.subtype_injective]
    have hTm2 : IsPGroup 2 Tm := (T.isPGroup'.map S.subtype).map B.subtype
    have hTminn : Tm ≤
        (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range :=
      fun y hy => by
        obtain ⟨k, hk⟩ := hTm2 ⟨y, hy⟩
        exact smallRee_mem_inner_of_pow_eq_one ha hK y k (by simpa using congrArg Subtype.val hk)
    let T₀ : Subgroup (ReeTag.G2.reeGamma K a) := Tm.comap MulAut.conj
    have hT₀map : T₀.map MulAut.conj = Tm := Subgroup.map_comap_eq_self hTminn
    have eT : T₀ ≃* Tm :=
      (Subgroup.equivMapOfInjective T₀ _ hinj).trans (MulEquiv.subgroupCongr hT₀map)
    have hT₀card : Nat.card T₀ = Nat.card (T : Subgroup S) := by
      rw [Nat.card_congr eT.toEquiv, hTmcard]
    have hT₀2 : IsPGroup 2 T₀ := hTm2.of_equiv eT.symm
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
    obtain ⟨-, hE8el, hE8card, ⟨P₁, hP₁⟩, -, -⟩ :=
      CFSG.Walter.Ree.Model.small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
    obtain ⟨P₀, hP₀⟩ := hT₀2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ReeTag.G2.reeGamma K a) P₁ P₀
    have hT₀sq : ∀ u ∈ T₀, u ^ 2 = 1 := by
      intro u hu
      have hu0 : u ∈ (P₀ : Subgroup (ReeTag.G2.reeGamma K a)) := hP₀ hu
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hu0
      have hu1 : g⁻¹ * u * g ∈ (P₁ : Subgroup (ReeTag.G2.reeGamma K a)) := by
        rw [← MulAut.conj_inv_apply]
        exact hu0
      have h1 : ((g⁻¹ * u * g : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
          CFSG.Walter.Ree.Model.smallReeE8 a K w₀ := by
        rw [← hP₁]
        exact ⟨_, hu1, rfl⟩
      have := hE8el
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := CFSG.Walter.Ree.Model.smallReeE8 a K w₀) _ h1
      have h3 : (g⁻¹ * u * g) ^ 2 = 1 := Subtype.ext (by simpa using h2)
      have h4 : u ^ 2 = g * (g⁻¹ * u * g) ^ 2 * g⁻¹ := by
        rw [sq, sq]
        group
      rw [h4, h3, mul_one, mul_inv_cancel]
    have hT₀dvd : Nat.card T₀ ∣ 8 := by
      have h1 : Nat.card T₀ ∣ Nat.card (P₀ : Subgroup (ReeTag.G2.reeGamma K a)) :=
        Subgroup.card_dvd_of_le hP₀
      have h2 : Nat.card (P₀ : Subgroup (ReeTag.G2.reeGamma K a)) =
          Nat.card (P₁ : Subgroup (ReeTag.G2.reeGamma K a)) := by
        rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
      have h3 : Nat.card (P₁ : Subgroup (ReeTag.G2.reeGamma K a)) = 8 := by
        rw [← Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective, hP₁,
          hE8card]
      rwa [h2, h3] at h1
    have hT₀8 : Nat.card T₀ = 8 := by
      obtain ⟨n, hn⟩ : ∃ n, Nat.card T₀ = n := ⟨_, rfl⟩
      rw [hn] at hT₀dvd ⊢
      have h1 := Nat.le_of_dvd (by norm_num) hT₀dvd
      have h2 : 4 < n := by rw [← hn, hT₀card]; exact hT4
      rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with h | h | h | h
      · subst h
        norm_num at hT₀dvd
      · subst h
        norm_num at hT₀dvd
      · subst h
        norm_num at hT₀dvd
      · exact h
    have hT₀x : ∀ u ∈ T₀, u * x₀ = x₀ * u := by
      intro u hu
      obtain ⟨_, ⟨s', -, rfl⟩, hs'⟩ := hu
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hSC s'.2))
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      apply hinj
      rw [map_mul, map_mul, ← hs', hx₀]
      exact h1
    refine smallRee_false_of_eight_le_centralizer_prime hK hp hp3 (x := (x₀ : ModGL _ K)) x₀.2
      (by rw [Subgroup.orderOf_coe, hx₀p]) (T₀.map (ReeTag.G2.reeGamma K a).subtype)
      (Subgroup.map_subtype_le _) ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hT₀sq u hu, OneMemClass.coe_one]
    · rw [Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective, hT₀8]
    · rintro _ ⟨u, hu, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hT₀x u hu]
  let ψ : A →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  let _ : MulDistribMulAction A S := MulDistribMulAction.compHom S ψ
  have hψ : ∀ (c : A) (h : S), ((c • h : S) : B) = c * h * (c : B)⁻¹ := fun c h => rfl
  obtain ⟨hle, -⟩ := GroupTheory.SteinbergBK.solvable_large_prime_small_sylow_two_commutator_odd
    hp hp3 hSsolv hpS (IsElementaryAbelian.isPGroup p A) hT
  rw [Subgroup.commutator_le]
  intro s hs b hb
  refine ⟨(⟨s, hs⟩⁻¹ : S)⁻¹ * ((⟨b, hb⟩ : A) • (⟨s, hs⟩⁻¹ : S)),
    hle (Subgroup.subset_closure ⟨⟨b, hb⟩, ⟨s, hs⟩⁻¹, Subgroup.mem_top _, rfl⟩), ?_⟩
  rw [Subgroup.coe_subtype, Subgroup.coe_mul, hψ, commutatorElement_def]
  simp only [Subgroup.coe_inv, inv_inv]
  group

end SmallRee

theorem small_Ree_plane_local_core_product_odd (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (ReeTag.G2.reeGamma K a)))
    (hB : innerAut (ReeTag.G2.reeGamma K a) ≤ B) (A : Subgroup B) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) :
    Odd (Nat.card (thetaT p A)) ∧
    (∀ x ∈ A, (x : MulAut (ReeTag.G2.reeGamma K a)) ∉ innerAut (ReeTag.G2.reeGamma K a) →
      Odd (Nat.card (aschbacherSolvableCore p (Subgroup.centralizer ({x} : Set B))))) ∧
    (∀ t ∈ A, t ≠ 1 → (t : MulAut (ReeTag.G2.reeGamma K a)) ∈ innerAut (ReeTag.G2.reeGamma K a) →
      ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), A⁆ ≤
        inSubgroup (pPrimeCore 2)
          (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)))) ∧
    ∀ t ∈ A, t ≠ 1 →
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), A⁆ :
          Subgroup B) : Set B) * (thetaT p A : Set B) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), A⁆ ⊔
          thetaT p A : Subgroup B) : Set B) ∧
      Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({t} : Set B)), A⁆ ⊔ thetaT p A)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hZ := (small_Ree_fixed_group_center_trivial a K hK).1
  have hinj : Function.Injective (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)) := mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨-, -, -, -, hOutodd, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  have hApow : ∀ b ∈ A, b ^ p = 1 := fun b hb => elemPow_eq_one_of_isElementaryAbelian b hb
  have hcore : ∀ x ∈ A, (x : MulAut (ReeTag.G2.reeGamma K a)) ∉ innerAut (ReeTag.G2.reeGamma K a) →
      Odd (Nat.card (aschbacherSolvableCore p (Subgroup.centralizer ({x} : Set B)))) := by
    intro x hxA hxinn
    have hx1 : x ≠ 1 := fun h => hxinn (by rw [h]; exact one_mem _)
    have hxp : orderOf x = p := orderOf_eq_prime (hApow x hxA) hx1
    have hxp' : orderOf (x : MulAut (ReeTag.G2.reeGamma K a)) = p := by
      rw [Subgroup.orderOf_coe, hxp]
    exact odd_card_core_of_fixed_radical hZ hOutodd hp B hB x
      (smallRee_fixed_radical_of_not_inner ha hK hp hp3 _ hxp' hxinn)
  have hI : Odd (Nat.card (thetaT p A)) := by
    by_cases hout : ∃ x ∈ A,
        (x : MulAut (ReeTag.G2.reeGamma K a)) ∉ innerAut (ReeTag.G2.reeGamma K a)
    · obtain ⟨x, hxA, hxinn⟩ := hout
      have hx1 : x ≠ 1 := fun h => hxinn (by rw [h]; exact one_mem _)
      have hle : thetaT p A ≤
          inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set B)) :=
        iInf_le_of_le x (iInf_le_of_le hxA (iInf_le_of_le hx1 le_rfl))
      refine (hcore x hxA hxinn).of_dvd_nat ?_
      rw [← Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set B)).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    · push Not at hout
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
      have hzM : orderOf ((z : B) : MulAut (ReeTag.G2.reeGamma K a)) = 2 := by
        simpa [Subgroup.orderOf_coe] using hz
      have hzinn := smallRee_mem_inner_of_pow_eq_one ha hK ((z : B) : MulAut _) 1
        (by rw [pow_one, ← hzM]; exact pow_orderOf_eq_one _)
      obtain ⟨g₀, hg₀⟩ : ((z : B) : MulAut (ReeTag.G2.reeGamma K a)) ∈
          (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range :=
        hzinn
      have hg₀ord : orderOf g₀ = 2 := by rw [← orderOf_injective _ hinj g₀, hg₀, hzM]
      have hzcent : (z : B) ∈ Subgroup.centralizer (A : Set B) :=
        GroupTheory.SteinbergBY.thetaT_le_centralizer p A z.2
      have hAinn : A.map B.subtype ≤
          (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range := by
        rintro _ ⟨b, hb, rfl⟩
        exact hout b hb
      set A₀ : Subgroup (ReeTag.G2.reeGamma K a) := (A.map B.subtype).comap MulAut.conj
        with hA₀
      have hA₀map : A₀.map MulAut.conj = A.map B.subtype := Subgroup.map_comap_eq_self hAinn
      set E := A₀.map (ReeTag.G2.reeGamma K a).subtype with hE
      have hEΓ : E ≤ ReeTag.G2.reeGamma K a := Subgroup.map_subtype_le _
      have hEcard : Nat.card E = p ^ 2 := by
        rw [hE, Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective,
          ← Subgroup.card_map_of_injective hinj, hA₀map,
          Subgroup.card_map_of_injective B.subtype_injective, hAcard]
      have : IsElementaryAbelian p (A.map B.subtype) := IsElementaryAbelian.map B.subtype
      have hEmem : ∀ e : E, MulAut.conj (Subgroup.inclusion hEΓ e) ∈ A.map B.subtype := by
        rintro ⟨_, ⟨g, hg, rfl⟩⟩
        exact hg
      have hEel : IsElementaryAbelian p E := isElementaryAbelian_of_injective
        ((MulAut.conj.comp (Subgroup.inclusion hEΓ)).codRestrict _ hEmem)
        (fun u v h => Subgroup.inclusion_injective hEΓ (hinj (congrArg Subtype.val h)))
      have hEz : E ≤ Subgroup.centralizer {(g₀ : ModGL ReeTag.G2.tag K)} := by
        rintro _ ⟨g, hg, rfl⟩
        obtain ⟨b, hb, hbg⟩ := hg
        have h1 := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hzcent) b hb)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
        have h2 : g * g₀ = g₀ * g := by
          apply hinj
          rw [map_mul, map_mul, hg₀, ← hbg]
          exact h1
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype, ← Subgroup.coe_mul,
          ← Subgroup.coe_mul, h2]
      exact smallRee_false_of_plane_le_centralizer_involution hK hp hp3 g₀.2
        (by rw [Subgroup.orderOf_coe, hg₀ord]) E hEΓ hEel hEcard hEz
  have hAN : ∀ t ∈ A, A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({t} : Set B)) : Subgroup B) : Set B) := fun t htA b hb =>
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨t, htA⟩))))
  have hScore : ∀ t : B, Group.IsSolvable (inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({t} : Set B))) ∧
      ¬p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({t} : Set B))) := by
    intro t
    obtain ⟨hsolv, -, hpdvd, -⟩ :=
      solvable_prime_complement_core_characterization (H := Subgroup.centralizer ({t} : Set B)) hp
    have e := Subgroup.equivMapOfInjective (aschbacherSolvableCore p
      (Subgroup.centralizer ({t} : Set B))) _ (Subgroup.centralizer ({t} : Set B)).subtype_injective
    exact ⟨Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
      by rw [inSubgroup, ← Nat.card_congr e.toEquiv]; exact hpdvd⟩
  have hO2 : ∀ t ∈ A, t ≠ 1 →
      (t : MulAut (ReeTag.G2.reeGamma K a)) ∈ innerAut (ReeTag.G2.reeGamma K a) →
      ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), A⁆ ≤
        inSubgroup (pPrimeCore 2)
          (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B))) :=
    fun t htA ht1 htinn => smallRee_commutator_le_pPrimeCore ha hK hp hp3 B A t htA ht1 htinn _
      (Subgroup.map_subtype_le _) (hAN t htA) (hScore t).1 (hScore t).2
  refine ⟨hI, hcore, hO2, fun t htA ht1 =>
    ⟨((GroupTheory.SteinbergBY.section_nine_residual_to_intersection hp (by omega) A).1 t htA
      ht1).symm, ?_⟩⟩
  have hIS : thetaT p A ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) :=
    iInf_le_of_le t (iInf_le_of_le htA (iInf_le_of_le ht1 le_rfl))
  by_cases htinn : (t : MulAut (ReeTag.G2.reeGamma K a)) ∈ innerAut (ReeTag.G2.reeGamma K a)
  ·
    set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) with hS
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hOodd : Odd (Nat.card (inSubgroup (pPrimeCore 2) S)) := by
      rw [inSubgroup, Subgroup.card_map_of_injective S.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hON : S ≤ Subgroup.normalizer ((inSubgroup (pPrimeCore 2) S : Subgroup B) : Set B) := by
      have : ((inSubgroup (pPrimeCore 2) S).subgroupOf S).Normal := by
        rw [inSubgroup, ← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
        infer_instance
      exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)
    have hsup := CFSG.OddSolvableUnitary.odd_card_sup_of_le_normalizer (hIS.trans hON) hI hOodd
    exact hsup.of_dvd_nat (Subgroup.card_dvd_of_le
      (sup_le ((hO2 t htA ht1 htinn).trans le_sup_right) le_sup_left))
  ·
    have hSodd : Odd (Nat.card
        (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)))) := by
      rw [inSubgroup, Subgroup.card_map_of_injective
        (Subgroup.centralizer ({t} : Set B)).subtype_injective]
      exact hcore t htA htinn
    have hcomm : ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) := by
      rw [Subgroup.commutator_le]
      intro s hs b hb
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine mul_mem hs ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.1 (hAN t htA hb) s⁻¹).1 (inv_mem hs)
    exact hSodd.of_dvd_nat (Subgroup.card_dvd_of_le (sup_le hcomm hIS))

end CFSG.RankThree.Chevalley
