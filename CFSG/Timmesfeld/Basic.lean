module

public import CFSG.Timmesfeld.Defs
public import CFSG.GroupTheory.BaerSuzuki

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G]

section IsClass

variable {D : Set G}

theorem conj_mem_of_isClass (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g : G) {x : G}
    (hx : x ∈ D) : g * x * g⁻¹ ∈ D := by
  obtain ⟨d₀, rfl⟩ := hclass
  exact IsConj.trans hx (isConj_iff.mpr ⟨g, rfl⟩)

theorem isConj_of_isClass (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {x y : G} (hx : x ∈ D)
    (hy : y ∈ D) : IsConj x y := by
  obtain ⟨d₀, rfl⟩ := hclass
  exact (isConj_comm.mp hx).trans hy

theorem image_conj_of_isClass (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g : G) :
    (fun x => g * x * g⁻¹) '' D = D := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_of_isClass hclass g hx
  · intro hy
    exact ⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_of_isClass hclass g⁻¹ hy, by group⟩

end IsClass

namespace IsRootInvolutionSet

variable {D : Set G} {d e : G}

theorem orderOf_eq_two (hD : IsRootInvolutionSet D) (hd : d ∈ D) : orderOf d = 2 :=
  hD.1 d hd

theorem mul_self_eq_one (hD : IsRootInvolutionSet D) (hd : d ∈ D) : d * d = 1 := by
  rw [← pow_two, ← hD.orderOf_eq_two hd, pow_orderOf_eq_one]

theorem inv_eq (hD : IsRootInvolutionSet D) (hd : d ∈ D) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (hD.mul_self_eq_one hd)

theorem ne_one (hD : IsRootInvolutionSet D) (hd : d ∈ D) : d ≠ 1 := by
  rintro rfl
  have h := hD.orderOf_eq_two hd
  rw [orderOf_one] at h
  exact absurd h (by decide)

theorem orderOf_mul (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D) :
    orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)) :=
  hD.2.1 d hd e he

theorem sq_mem (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : (d * e) ^ 2 ∈ D :=
  hD.2.2 d hd e he h4

end IsRootInvolutionSet

theorem sq_mem_of_orderOf_eq_four {D : Set G} (hD : IsRootInvolutionSet D) {d e : G}
    (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    (d * e) ^ 2 ∈ D ∧ Commute d ((d * e) ^ 2) ∧ Commute e ((d * e) ^ 2) ∧
      e * d * e = d * (d * e) ^ 2 := by
  have hd2 := hD.mul_self_eq_one hd
  have he2 := hD.mul_self_eq_one he
  have hdd : ∀ y : G, d * (d * y) = y := fun y => by rw [← mul_assoc, hd2, one_mul]
  have hee : ∀ y : G, e * (e * y) = y := fun y => by rw [← mul_assoc, he2, one_mul]
  have hinv : (d * e)⁻¹ = e * d := by rw [mul_inv_rev, hD.inv_eq hd, hD.inv_eq he]
  have hx4 : (d * e) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one (d * e)
  have hsq : (d * e) ^ 2 = (e * d) ^ 2 := by
    rw [← hinv, inv_pow, eq_inv_iff_mul_eq_one, ← pow_add]
    exact hx4
  refine ⟨hD.sq_mem hd he h4, ?_, ?_, ?_⟩
  · change d * (d * e) ^ 2 = (d * e) ^ 2 * d
    conv_rhs => rw [hsq]
    simp only [pow_two, mul_assoc, hdd, hd2, mul_one]
  · change e * (d * e) ^ 2 = (d * e) ^ 2 * e
    conv_lhs => rw [hsq]
    simp only [pow_two, mul_assoc, hee, he2, mul_one]
  · simp only [pow_two, mul_assoc, hdd]

theorem mul_sq_mem_of_orderOf_eq_four {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : d * (d * e) ^ 2 ∈ D := by
  rw [← (sq_mem_of_orderOf_eq_four hD hd he h4).2.2.2]
  simpa [hD.inv_eq he] using conj_mem_of_isClass hclass e hd

section Dihedral

variable {d e : G}

theorem commute_iff_mul_sq_eq_one (hd : d * d = 1) (he : e * e = 1) :
    Commute d e ↔ (d * e) ^ 2 = 1 := by
  rw [pow_two, ← eq_inv_iff_mul_eq_one, mul_inv_rev, inv_eq_of_mul_eq_one_right hd,
    inv_eq_of_mul_eq_one_right he]
  rfl

theorem mul_zpow_mul_eq_zpow_neg_mul (hd : d * d = 1) (he : e * e = 1) (i : ℤ) :
    d * (d * e) ^ i = (d * e) ^ (-i) * d := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have h1 : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [hdi, mul_inv_rev, hdi, hei, ← mul_assoc, hd, one_mul]
  have h2 : d * (d * e) ^ i * d⁻¹ = (d * e) ^ (-i) := by
    rw [← conj_zpow, h1, zpow_neg, inv_zpow]
  calc d * (d * e) ^ i = d * (d * e) ^ i * d⁻¹ * d := by group
    _ = (d * e) ^ (-i) * d := by rw [h2]

theorem exists_zpow_of_mem_closure_pair (hd : d * d = 1) (he : e * e = 1) {g : G}
    (hg : g ∈ Subgroup.closure ({d, e} : Set G)) :
    ∃ i : ℤ, g = (d * e) ^ i ∨ g = (d * e) ^ i * d := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hc := mul_zpow_mul_eq_zpow_neg_mul hd he
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, hdi, hei, mul_assoc, hd, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨j, rfl | rfl⟩ := hy
    · exact ⟨i + j, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨i - j, Or.inr ?_⟩
      rw [mul_assoc, hc, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨i - j, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc d, hc, mul_assoc, hd, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv x _ hx =>
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact ⟨-i, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [mul_inv_rev, hdi, ← zpow_neg, hc, neg_neg]

theorem isPGroup_two_closure_pair (hd : d * d = 1) (he : e * e = 1) {k : ℕ}
    (hk : (d * e) ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.closure ({d, e} : Set G)) := by
  rintro ⟨g, hg⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  obtain ⟨i, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair hd he hg
  · have h1 : ((d * e) ^ i) ^ 2 ^ k = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, hk, one_zpow]
    rw [pow_succ, pow_mul, h1, one_pow]
  · have h2 : ((d * e) ^ i * d) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc d, mul_zpow_mul_eq_zpow_neg_mul hd he, mul_assoc, hd,
        mul_one, ← zpow_add, add_neg_cancel, zpow_zero]
    rw [pow_succ', pow_mul, h2, one_pow]

theorem exists_conj_of_odd_orderOf_mul (hd : d * d = 1) (he : e * e = 1)
    (hodd : Odd (orderOf (d * e))) :
    ∃ g ∈ Subgroup.closure ({d, e} : Set G), g * d * g⁻¹ = e := by
  obtain ⟨k, hk⟩ := hodd
  have hdmem : d ∈ Subgroup.closure ({d, e} : Set G) := Subgroup.subset_closure (by simp)
  have hemem : e ∈ Subgroup.closure ({d, e} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨(d * e) ^ k, Subgroup.pow_mem _ (Subgroup.mul_mem _ hdmem hemem) k, ?_⟩
  have hpow : (d * e) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one _
  have hc := mul_zpow_mul_eq_zpow_neg_mul hd he (-(k : ℤ))
  rw [neg_neg, zpow_natCast, zpow_neg, zpow_natCast] at hc
  calc (d * e) ^ k * d * ((d * e) ^ k)⁻¹ = (d * e) ^ k * (d * e) ^ k * d := by
        rw [mul_assoc, hc, mul_assoc]
    _ = (d * e) ^ (2 * k + 1) * (d * e)⁻¹ * d := by
        rw [← pow_add, pow_succ, mul_inv_cancel_right, two_mul]
    _ = e := by
        rw [hpow, one_mul, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right he]

end Dihedral

theorem commutator_eq_top {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hgen : Subgroup.closure D = ⊤)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) : commutator G = ⊤ := by
  obtain ⟨d, hd, e, he, h4⟩ := hnondeg
  have himg : ∀ x ∈ D, Abelianization.of x = Abelianization.of d := by
    intro x hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd hx)
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hone : Abelianization.of d = 1 := by
    have h1 := himg _ (hD.sq_mem hd he h4)
    have h2 : Abelianization.of d ^ 2 = 1 := by
      rw [← map_pow, pow_two, hD.mul_self_eq_one hd, map_one]
    rw [map_pow, map_mul, himg e he, ← pow_two, ← pow_mul] at h1
    rw [← h1, pow_mul, h2, one_pow]
  rw [eq_top_iff, ← hgen, Subgroup.closure_le, ← Abelianization.ker_of]
  intro x hx
  rw [SetLike.mem_coe, MonoidHom.mem_ker, himg x hx, hone]

theorem exists_opposite [Finite G] {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {d : G} (hd : d ∈ D) :
    ∃ e ∈ D, 1 < orderOf (d * e) ∧ Odd (orderOf (d * e)) := by
  by_contra hne
  push Not at hne
  have h4 : ∀ e ∈ D, (d * e) ^ 2 ^ 2 = 1 := by
    intro e he
    rcases hD.orderOf_mul hd he with h | h | h
    · rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, ← h, pow_orderOf_eq_one, one_pow]
    · rw [show 2 ^ 2 = 4 by norm_num, ← h, pow_orderOf_eq_one]
    · have h1 : orderOf (d * e) = 1 := by
        have := orderOf_pos (d * e)
        by_contra h1
        exact hne e he (by omega) h
      rw [orderOf_eq_one_iff.mp h1, one_pow]
  have hmem : d ∈ CFSG.pCore 2 G := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hg := conj_mem_of_isClass hclass g hd
    exact isPGroup_two_closure_pair (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hg) (h4 _ hg)
  rw [hO2 _ (CFSG.BaerSuzuki.Helpers.pCore_normal 2) (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2),
    Subgroup.mem_bot] at hmem
  exact hD.ne_one hd hmem

section RootSet

variable {D : Set G} {d e : G}

theorem rootSet_subset (D : Set G) (d : G) : rootSet D d ⊆ D := fun _ he => he.1

theorem mem_rootSet_self (hd : d ∈ D) : d ∈ rootSet D d := ⟨hd, fun _ _ => Iff.rfl⟩

theorem rootSet_eq_of_mem (he : e ∈ rootSet D d) : rootSet D e = rootSet D d := by
  ext x
  exact and_congr_right fun _ => forall₂_congr fun f hf => by rw [he.2 f hf]

theorem mem_rootSet_comm (hd : d ∈ D) (he : e ∈ rootSet D d) : d ∈ rootSet D e := by
  rw [rootSet_eq_of_mem he]
  exact mem_rootSet_self hd

theorem commute_of_mem_rootSet (hd : d ∈ D) {a b : G} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) : Commute a b :=
  (ha.2 b hb.1).2 ((hb.2 d hd).2 (Commute.refl d)).symm

theorem mem_rootSet_iff [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hd : d ∈ D) :
    e ∈ rootSet D d ↔ e ∈ D ∧ Commute d e ∧ ∀ f ∈ D, Commute d f → Commute e f := by
  constructor
  · rintro ⟨he, h⟩
    exact ⟨he, (h e he).1 (Commute.refl e), fun f hf hdf => (h f hf).2 hdf⟩
  rintro ⟨he, -, hsub⟩
  refine ⟨he, fun f hf => ⟨fun hef => ?_, hsub f hf⟩⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd he)
  let C : G → Set G := fun x => {f | f ∈ D ∧ Commute x f}
  have hsub' : C d ⊆ C (g * d * g⁻¹) := fun f hf => ⟨hf.1, hsub f hf.1 hf.2⟩
  have himage : C (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' C d := by
    ext y
    constructor
    · rintro ⟨hy, hgy⟩
      refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_of_isClass hclass g⁻¹ hy, ?_⟩, by group⟩
      rw [← Commute.conj_iff g]
      simpa [mul_assoc] using hgy
    · rintro ⟨x, ⟨hx, hdx⟩, rfl⟩
      exact ⟨conj_mem_of_isClass hclass g hx, (Commute.conj_iff g).2 hdx⟩
  have hinj : Function.Injective (fun x => g * x * g⁻¹) := fun x y hxy => by simpa using hxy
  have heq : C d = C (g * d * g⁻¹) := Set.eq_of_subset_of_ncard_le hsub'
    (by rw [himage, Set.ncard_image_of_injective _ hinj]) (Set.toFinite _)
  have hmem : f ∈ C (g * d * g⁻¹) := ⟨hf, hef⟩
  rw [← heq] at hmem
  exact hmem.2

theorem rootSet_map {H : Type*} [Group H] (φ : G ≃* H) {E : Set H} (hDE : φ '' D = E) (d : G) :
    rootSet E (φ d) = φ '' rootSet D d := by
  subst hDE
  have hcomm : ∀ a b : G, Commute (φ a) (φ b) ↔ Commute a b := fun a b =>
    ⟨fun h => by simpa using h.map φ.symm, fun h => h.map φ⟩
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  simp only [rootSet, Set.mem_ofPred_eq, φ.injective.mem_set_image, Set.forall_mem_image, hcomm]

theorem rootSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g d : G) :
    rootSet D (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' rootSet D d := by
  have hfun : ⇑(MulAut.conj g) = fun x => g * x * g⁻¹ := funext (MulAut.conj_apply g)
  have h := rootSet_map (MulAut.conj g) (E := D)
    (by rw [hfun]; exact image_conj_of_isClass hclass g) d
  rwa [hfun] at h

end RootSet

namespace Hyp

variable {D : Set G}

theorem conj_mem (h : Hyp G D) (g : G) {x : G} (hx : x ∈ D) : g * x * g⁻¹ ∈ D :=
  conj_mem_of_isClass h.isClass g hx

theorem isConj (h : Hyp G D) {x y : G} (hx : x ∈ D) (hy : y ∈ D) : IsConj x y :=
  isConj_of_isClass h.isClass hx hy

theorem nonempty (h : Hyp G D) : D.Nonempty :=
  let ⟨d, hd, _⟩ := h.nondeg
  ⟨d, hd⟩

theorem commutator_eq_top (h : Hyp G D) : commutator G = ⊤ :=
  Timmesfeld.commutator_eq_top h.isClass h.root h.gen h.nondeg

theorem exists_opposite (h : Hyp G D) {d : G} (hd : d ∈ D) :
    ∃ e ∈ D, 1 < orderOf (d * e) ∧ Odd (orderOf (d * e)) :=
  have := h.finite
  Timmesfeld.exists_opposite h.isClass h.root h.twoCore hd

theorem mem_rootSet_iff (h : Hyp G D) {d e : G} (hd : d ∈ D) :
    e ∈ rootSet D d ↔ e ∈ D ∧ Commute d e ∧ ∀ f ∈ D, Commute d f → Commute e f :=
  have := h.finite
  Timmesfeld.mem_rootSet_iff h.isClass hd

theorem rootSet_conj (h : Hyp G D) (g d : G) :
    rootSet D (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' rootSet D d :=
  Timmesfeld.rootSet_conj h.isClass g d

theorem center_eq_bot (h : Hyp G D) : Subgroup.center G = ⊥ := by
  have := h.finite
  refine h.oddCore _ inferInstance ?_
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz' : orderOf (z : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hnormal : (Subgroup.zpowers (z : G)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i) g, mul_inv_cancel_right]
    exact hx
  have hp : IsPGroup 2 (Subgroup.zpowers (z : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hbot := h.twoCore _ hnormal hp
  rw [Subgroup.zpowers_eq_bot] at hbot
  rw [hbot, orderOf_one] at hz'
  exact absurd hz' (by decide)

end Hyp

end CFSG.Timmesfeld
