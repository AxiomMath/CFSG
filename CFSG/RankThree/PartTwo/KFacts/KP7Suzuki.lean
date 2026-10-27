module

public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Model
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP7

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq := two_pow_odd_mod_three a
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

variable {H : Type} [Group H] {p f : ℕ}

theorem three_not_dvd_card (h : SuzukiModel H p f) : ¬ 3 ∣ Nat.card H := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact not_three_dvd_order a

theorem finite_of_suzukiModel (h : SuzukiModel H p f) : Finite H := by
  obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := h
  exact Finite.of_equiv _ e.symm.toEquiv

theorem finite_mulAut (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α.toEquiv : Equiv.Perm X)) fun _ _ hαβ =>
    MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm X => e x) hαβ

theorem commutatorElement_mem_inner (h : SuzukiModel H p f) (α β : MulAut H) :
    ⁅α, β⁆ ∈ inner H := by
  have hcyc := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} H p f h).1.1
  rw [← QuotientGroup.eq_one_iff (N := inner H), ← QuotientGroup.mk'_apply,
    map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (IsCyclic.commGroup (α := Outer H)).mul_comm _ _

theorem commutator_le_inner (h : SuzukiModel H p f) : commutator (MulAut H) ≤ inner H := by
  rw [commutator_def, Subgroup.commutator_le]
  exact fun α _ β _ => commutatorElement_mem_inner h α β

theorem map_commutator_le_inner (h : SuzukiModel H p f) {G : Type*} [Group G]
    (ρ : G →* MulAut H) (E A : Subgroup G) : (⁅E, A⁆).map ρ ≤ inner H := by
  rw [Subgroup.map_commutator]
  exact (Subgroup.commutator_mono le_top le_top).trans (commutator_def (MulAut H) ▸
    commutator_le_inner h)

theorem inf_inner_eq_bot (h : SuzukiModel H p f) {P : Subgroup (MulAut H)} (hP : IsPGroup 3 P) :
    P ⊓ inner H = ⊥ := by
  have := finite_of_suzukiModel h
  have hI : Nat.card (inner H) ∣ Nat.card H :=
    Subgroup.card_dvd_of_surjective (f := (MulAut.conj : H →* MulAut H).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hPI : IsPGroup 3 (P ⊓ inner H : Subgroup (MulAut H)) := hP.to_le inf_le_left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPI
  have hdvd : Nat.card (P ⊓ inner H : Subgroup (MulAut H)) ∣ Nat.card H :=
    (Subgroup.card_dvd_of_le inf_le_right).trans hI
  rw [hk] at hdvd
  rcases k with _ | k
  · rwa [pow_zero, Subgroup.card_eq_one] at hk
  · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd) (three_not_dvd_card h)

theorem isCyclic_of_isPGroup_three (h : SuzukiModel H p f) {P : Subgroup (MulAut H)}
    (hP : IsPGroup 3 P) : IsCyclic P := by
  have hcyc := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} H p f h).1.1
  refine isCyclic_of_injective ((QuotientGroup.mk' (inner H)).comp P.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : MulAut H) ∈ P ⊓ inner H :=
    ⟨x.2, (QuotientGroup.eq_one_iff _).1 hx⟩
  rw [inf_inner_eq_bot h hP] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem card_dvd_three_of_pow_three (h : SuzukiModel H p f) {E : Subgroup (MulAut H)}
    (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ∣ 3 := by
  have hP : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE x x.2)⟩
  have := isCyclic_of_isPGroup_three h hP
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE x x.2)

theorem pRank_three_mulAut_le_one (h : SuzukiModel H p f) : CFSG.pRank 3 (MulAut H) ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hdvd := card_dvd_three_of_pow_three h (E := A) fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := A) x hx
  rw [hcard] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 (by rwa [pow_one])

theorem card_map_dvd_three (h : SuzukiModel H p f) {G : Type*} [Group G] (ρ : G →* MulAut H)
    {E : Subgroup G} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card (E.map ρ) ∣ 3 := by
  refine card_dvd_three_of_pow_three h fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  rw [← map_pow, hE x hx, map_one]

section Involution

open CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiModel

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem mem_suzukiU_and_orderOf_eq_two_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} :
    g ∈ suzukiU a K ∧ orderOf g = 2 ↔ g ∈ suzukiB a K ∧ orderOf g = 2 := by
  refine ⟨fun hg => ⟨suzukiU_le_suzukiB a K hg.1, hg.2⟩, fun hg => ?_⟩
  obtain ⟨v, -, hv⟩ := (mem_suzukiB_and_orderOf_eq_two_iff hK).1 hg
  exact ⟨hv ▸ suzukiSElt_mem_suzukiU a K 0 v, hg.2⟩

theorem card_involutions_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card {g : suzukiGroup a K // g ∈ suzukiU a K ∧ orderOf g = 2} = 2 ^ (2 * a + 1) - 1 := by
  rw [← ncard_involutions_suzukiB hK, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_suzukiU_and_orderOf_eq_two_iff hK)

omit [Finite K] in
theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (x : G) (U : Sylow p G) (g : G) :
    g ∈ ((x • U : Sylow p G) : Subgroup G) ↔ x⁻¹ * g * x ∈ (U : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem card_involutions_sylow (hK : Nat.card K = 2 ^ (2 * a + 1)) (Q : Sylow 2 (suzukiGroup a K)) :
    Nat.card {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2} =
      2 ^ (2 * a + 1) - 1 := by
  obtain ⟨U, hU⟩ := exists_sylow_eq_suzukiU hK
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) U Q
  rw [← card_involutions_suzukiU hK]
  have hord : ∀ y g : suzukiGroup a K, orderOf (y * g * y⁻¹) = orderOf g := fun y g => by
    have h := (MulAut.conj y).orderOf_eq g
    rwa [MulAut.conj_apply] at h
  refine Nat.card_congr
    { toFun := fun g => ⟨x⁻¹ * g * x, hU ▸ (mem_smul_sylow_iff x U g).1 g.2.1, ?_⟩
      invFun := fun g => ⟨x * g * x⁻¹, (mem_smul_sylow_iff x U _).2 ?_, ?_⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc]) }
  · have h := hord x⁻¹ g
    rw [inv_inv] at h
    rw [h, g.2.2]
  · simpa [mul_assoc, hU] using g.2.1
  · rw [hord x g, g.2.2]

theorem exists_involution_fixed (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (P : Subgroup (MulAut (suzukiGroup a K))) (hP : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ t : suzukiGroup a K, orderOf t = 2 ∧ ∀ α ∈ P, α t = t := by
  classical
  have hmodel : SuzukiModel (suzukiGroup a K) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  have hPp : IsPGroup 3 P := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hP x x.2)⟩
  have := isCyclic_of_isPGroup_three hmodel hPp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 P :=
    { is_comm := ⟨fun x y => (IsCyclic.commGroup (α := P)).mul_comm x y⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hP x x.2) }
  have := finite_of_suzukiModel hmodel
  obtain ⟨Q, hQ⟩ := CFSG.SolvableHall.exists_invariant_sylow (A := P) (p := 3)
    (three_not_dvd_card hmodel) 2
  let X := {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2}
  let _ : MulAction P X :=
    { smul := fun α g => ⟨(α : MulAut (suzukiGroup a K)) g, hQ α g g.2.1, by
        rw [MulEquiv.orderOf_eq, g.2.2]⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  have hcard := hPp.card_modEq_card_fixedPoints X
  rw [card_involutions_sylow hK Q] at hcard
  have hq : (2 ^ (2 * a + 1) - 1) % 3 = 1 := by
    have h1 := two_pow_odd_mod_three a
    have h2 := Nat.one_le_two_pow (n := 2 * a + 1)
    omega
  have hne : Nat.card (MulAction.fixedPoints P X) ≠ 0 := by
    intro h0
    rw [h0] at hcard
    unfold Nat.ModEq at hcard
    omega
  obtain ⟨⟨t, ht⟩⟩ := (Nat.card_ne_zero.1 hne).1
  exact ⟨t, t.2.2, fun α hα => congrArg Subtype.val (ht ⟨α, hα⟩)⟩

theorem exists_involution_fixed_of_suzukiModel {H : Type} [Group H] {p f : ℕ}
    (h : SuzukiModel H p f) {G : Type*} [Group G] (ρ : G →* MulAut H) {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ 3 = 1) : ∃ t : H, orderOf t = 2 ∧ ∀ x ∈ E, ρ x t = t := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  obtain ⟨t, ht, hfix⟩ := exists_involution_fixed ha hK
    ((E.map ρ).map (MulAut.congr e).toMonoidHom) (by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [← map_pow, ← map_pow, hE x hx, map_one, map_one])
  refine ⟨e.symm t, by rw [MulEquiv.orderOf_eq, ht], fun x hx => ?_⟩
  have hx' := hfix _ ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
  apply e.injective
  rw [e.apply_symm_apply]
  exact hx'

end Involution

section SzEight

variable {K : Type} [Field K] [Finite K]

theorem card_suzukiGroup_eight (hK : Nat.card K = 8) : Nat.card (suzukiGroup 1 K) = 29120 := by
  rw [CFSG.LieType.Ree.suzuki_order (a := 1) (by rw [hK]; norm_num)]
  norm_num

theorem card_suzukiGroup_two : Nat.card (suzukiGroup 0 (ZMod 2)) = 20 := by
  rw [CFSG.LieType.Ree.suzuki_order (a := 0) (K := ZMod 2) (by simp)]
  norm_num

theorem exists_orderOf_eq_thirteen (hK : Nat.card K = 8) :
    ∃ x : suzukiGroup 1 K, orderOf x = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Finite (suzukiGroup 1 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_suzukiGroup_eight hK]; norm_num)
  exact exists_prime_orderOf_dvd_card' 13 (by rw [card_suzukiGroup_eight hK]; norm_num)

theorem exists_thirteen_fixedPointFree (hK : Nat.card K = 8) (α : MulAut (suzukiGroup 1 K))
    (hα : orderOf α = 3) :
    ∃ X : Subgroup (suzukiGroup 1 K), Nat.card X = 13 ∧ (∀ x ∈ X, α x ∈ X) ∧
      ∀ x ∈ X, α x = x → x = 1 := by
  classical
  have hcard := card_suzukiGroup_eight hK
  have : Finite (suzukiGroup 1 K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hα3 : α ^ 3 = 1 := hα ▸ pow_orderOf_eq_one α
  have hA3 : ∀ x ∈ Subgroup.zpowers α, x ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3, one_zpow]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 (Subgroup.zpowers α) :=
    { is_comm := ⟨fun x y => (IsCyclic.commGroup (α := Subgroup.zpowers α)).mul_comm x y⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA3 x x.2) }
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := CFSG.SolvableHall.exists_invariant_sylow (A := Subgroup.zpowers α) (p := 3)
    (by rw [hcard]; norm_num) 13
  have hQcard : Nat.card (Q : Subgroup (suzukiGroup 1 K)) = 13 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have hdvd : 13 ^ k ∣ 29120 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra h
      exact absurd ((Nat.pow_dvd_pow 13 (show 2 ≤ k by omega)).trans hdvd) (by norm_num)
    have hidx := Q.not_dvd_index
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
    · exfalso
      apply hidx
      have h := (Q : Subgroup (suzukiGroup 1 K)).card_mul_index
      rw [hk, hcard, pow_zero, one_mul] at h
      rw [h]
      norm_num
    · rw [hk, pow_one]
  refine ⟨Q, hQcard, fun x hx => hQ ⟨α, Subgroup.mem_zpowers α⟩ x hx, fun x hx hfix => ?_⟩
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_fixedSubgroup_suzukiGroup
    (a := 1) le_rfl (by rw [hK]; norm_num) (by norm_num) (by rw [hcard]; norm_num) α hα
  have h20 : Nat.card (CFSG.Open.signalizerFixedSubgroup α) = 20 := by
    rw [Nat.card_congr e.toEquiv, card_suzukiGroup_two]
  have hx20 : orderOf x ∣ 20 := by
    have h := orderOf_dvd_natCard (⟨x, hfix⟩ : CFSG.Open.signalizerFixedSubgroup α)
    rw [← Subgroup.orderOf_coe, h20] at h
    exact h
  have hx13 : orderOf x ∣ 13 := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : (Q : Subgroup (suzukiGroup 1 K)))
    rw [← Subgroup.orderOf_coe, hQcard] at h
    exact h
  have h1 : orderOf x ∣ Nat.gcd 13 20 := Nat.dvd_gcd hx13 hx20
  rwa [show Nat.gcd 13 20 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1

end SzEight

section Transport

variable {H : Type} [Group H] {p f : ℕ}

theorem exists_orderOf_eq_thirteen_of_suzukiModel (h : SuzukiModel H p 3) :
    ∃ x : H, orderOf x = 13 := by
  obtain ⟨-, a, -, K, _, _, ha, hK, ⟨e⟩⟩ := h
  obtain rfl : a = 1 := by omega
  obtain ⟨x, hx⟩ := exists_orderOf_eq_thirteen (K := K) (by rw [hK]; norm_num)
  exact ⟨e.symm x, by rw [MulEquiv.orderOf_eq, hx]⟩

theorem exists_thirteen_fixedPointFree_of_suzukiModel (h : SuzukiModel H p 3) (α : MulAut H)
    (hα : orderOf α = 3) :
    ∃ X : Subgroup H, Nat.card X = 13 ∧ (∀ x ∈ X, α x ∈ X) ∧ ∀ x ∈ X, α x = x → x = 1 := by
  obtain ⟨-, a, -, K, _, _, ha, hK, ⟨e⟩⟩ := h
  obtain rfl : a = 1 := by omega
  obtain ⟨X, hX, hinv, hfree⟩ := exists_thirteen_fixedPointFree (K := K) (by rw [hK]; norm_num)
    (MulAut.congr e α) (by rw [MulEquiv.orderOf_eq, hα])
  refine ⟨X.comap e.toMonoidHom, ?_, fun x hx => ?_, fun x hx hfix => ?_⟩
  · rw [← hX]
    exact Nat.card_congr ((X.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (MulEquiv.subgroupCongr (by
        rw [← Subgroup.comap_equiv_eq_map_symm']))).symm.toEquiv
  · have := hinv (e x) hx
    simpa [MulAut.congr_apply] using this
  · have h1 := hfree (e x) hx (by simp [MulAut.congr_apply, hfix])
    exact e.injective (by rw [h1, map_one])

theorem thirteen_dvd_or_two_pow_ten_dvd_card (h : SuzukiModel H p f) :
    13 ∣ Nat.card H ∨ 2 ^ 10 ∣ Nat.card H := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  rcases Nat.lt_or_ge a 2 with h2 | h2
  · obtain rfl : a = 1 := by omega
    left
    norm_num
  · right
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)

theorem not_suzukiModel_section {T : Type} [Group T] [Finite T] (h13 : ¬ 13 ∣ Nat.card T)
    (h2 : ¬ 2 ^ 10 ∣ Nat.card T) (X : Subgroup T) (N : Subgroup X) [N.Normal] :
    ¬ SuzukiModel (X ⧸ N) p f := by
  intro h
  have hdvd : Nat.card (X ⧸ N) ∣ Nat.card T :=
    (Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (Subgroup.card_subgroup_dvd_card X)
  rcases thirteen_dvd_or_two_pow_ten_dvd_card h with h' | h'
  · exact h13 (h'.trans hdvd)
  · exact h2 (h'.trans hdvd)

end Transport

end CFSG.RankThree.PartTwo.KFacts.KP7
