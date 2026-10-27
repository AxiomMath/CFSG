module

public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LocalAnalysis.SectionRank.SmallRee

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped commutatorElement

section SL2

variable {K : Type} [Field K]

@[expose] def slThree (K : Type) [Field K] : SL2 K :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem slThree_pow_three : slThree K ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [slThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem slThree_mul_uSL_ne : slThree K * uSL 1 ≠ uSL 1 * slThree K := by
  intro h
  have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simp [slThree, uSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem slThree_ne_one : slThree K ≠ 1 := by
  intro h
  apply slThree_mul_uSL_ne (K := K)
  rw [h, one_mul, mul_one]

theorem orderOf_slThree : orderOf (slThree K) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime slThree_pow_three slThree_ne_one

theorem commutatorElement_uSL_WSL [CharP K 2] : ⁅uSL (1 : K), WSL⁆ = slThree K := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hn : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  ext i j
  simp only [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [slThree, uSL, WSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hn]
  linear_combination h2

end SL2

section LargeRee

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

theorem largeReeA1Hom_mem_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL2 K) :
    largeReeA1Hom K a g ∈ F4.reeGamma K a := by
  have h : largeReeA1Hom K a g ∈ (largeReeA1Hom K a).range := ⟨g, rfl⟩
  rw [largeReeA1Hom_range hK, largeReeA1M] at h
  exact (sup_le inf_le_right inf_le_right : _ ≤ F4.reeGamma K a) h

@[expose] noncomputable def a1Fixed (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SL2 K →* reeFixed F4 K a :=
  ((largeReeA1Hom K a).codRestrict (adjointGroup F4.tag K) fun g =>
      (mem_reeGamma.1 (largeReeA1Hom_mem_reeGamma a hK g)).1).codRestrict (reeFixed F4 K a)
    fun g => by
      rw [mem_reeFixed, ← finiteReeAut_eq_reeAut]
      exact (mem_reeGamma.1 (largeReeA1Hom_mem_reeGamma a hK g)).2

theorem coe_a1Fixed (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL2 K) :
    ((a1Fixed a hK g : adjointGroup F4.tag K) : ModGL F4.tag K) = largeReeA1Hom K a g :=
  rfl

theorem a1Fixed_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (a1Fixed a hK) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply eq_one_of_largeReeA1Hom_eq_one a
  rw [← coe_a1Fixed a hK, hg]
  rfl

theorem a1Fixed_slThree (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    orderOf (a1Fixed a hK (slThree K)) = 3 ∧
      a1Fixed a hK (slThree K) * a1Fixed a hK (uSL 1) ≠
        a1Fixed a hK (uSL 1) * a1Fixed a hK (slThree K) := by
  refine ⟨by rw [orderOf_injective _ (a1Fixed_injective a hK), orderOf_slThree], fun h => ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact slThree_mul_uSL_ne (a1Fixed_injective a hK h)

end LargeRee

section Tits

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem center_commutator_reeFixed_tits_eq_bot (hK : Nat.card K = 2) :
    Subgroup.center (commutator (reeFixed F4 K 0)) = ⊥ := by
  set D := commutator (reeFixed F4 K 0)
  set N : Subgroup (reeFixed F4 K 0) := (Subgroup.center D).map D.subtype
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hn
    have hgz : g * (z : reeFixed F4 K 0) * g⁻¹ ∈ D :=
      (Subgroup.commutator_normal ⊤ ⊤).conj_mem _ z.2 g
    refine ⟨⟨_, hgz⟩, Subgroup.mem_center_iff.2 fun d => ?_, rfl⟩
    have hd : g⁻¹ * (d : reeFixed F4 K 0) * g ∈ D := by
      have := (Subgroup.commutator_normal ⊤ ⊤).conj_mem _ d.2 g⁻¹
      rwa [inv_inv] at this
    have hc' := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hd⟩)
    simp only [Subgroup.coe_mul] at hc'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (d : reeFixed F4 K 0) * (g * z * g⁻¹) = g * ((g⁻¹ * d * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * d * g)) * g⁻¹ := by rw [hc']
      _ = g * z * g⁻¹ * d := by group
  rcases (CFSG.LieType.Simplicity.titsData K hK).le_of_normal hK N with h | h
  · rw [eq_bot_iff]
    intro z hz
    have : (z : reeFixed F4 K 0) ∈ N := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := (CFSG.LieType.Simplicity.titsData K hK).nonabelian
    obtain ⟨z, hz, hzx⟩ := h hx
    apply hxy
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at this
    rw [← hzx]
    exact this.symm

end Tits

theorem orderOf_mk_center_eq_three {Γ : Type*} [Group Γ] {y : Γ} (hy : orderOf y = 3) {x : Γ}
    (hxy : y * x ≠ x * y) : orderOf (QuotientGroup.mk y : Γ ⧸ Subgroup.center Γ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => hxy (Subgroup.mem_center_iff.1 h x).symm

theorem three_dvd_card_of_reeTitsModel_twistedF4 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) : 3 ∣ Nat.card S := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have hK2 : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := hK2
  have ha : 1 ≤ a := by omega
  have hperf := CFSG.LieType.Simplicity.commutator_reeFixed_F4 a ha hK'
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  let e' := (e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm))).trans
    (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))
  obtain ⟨hy3, hyc⟩ := a1Fixed_slThree a hK2
  have hz := orderOf_mk_center_eq_three hy3 hyc
  rw [← hz, ← MulEquiv.orderOf_eq e'.symm]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_of_reeTitsModel_tits {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have hK1 : Nat.card K = 2 ^ (2 * 0 + 1) := hK2
  let e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  set R := a1Fixed 0 hK1
  have hmem : R (slThree K) ∈ commutator (reeFixed ReeTag.F4 K 0) := by
    rw [← commutatorElement_uSL_WSL, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hy : orderOf (⟨R (slThree K), hmem⟩ : commutator (reeFixed ReeTag.F4 K 0)) = 3 := by
    rw [← Subgroup.orderOf_coe, (a1Fixed_slThree 0 hK1).1]
  have hz : orderOf (QuotientGroup.mk ⟨R (slThree K), hmem⟩ :
      commutator (reeFixed ReeTag.F4 K 0) ⧸
        Subgroup.center (commutator (reeFixed ReeTag.F4 K 0))) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff, center_commutator_reeFixed_tits_eq_bot hK2,
        Subgroup.mem_bot]
      intro h1
      rw [h1, orderOf_one] at hy
      omega
  rw [← hz, ← MulEquiv.orderOf_eq e'.symm]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_of_reeTitsModel_twistedG2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) : 3 ∣ Nat.card S := by
  obtain ⟨-, hf3, hrk⟩ := CFSG.SectionRank.smallReeModel_rank h
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup S)
  have h3E : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  exact h3E.trans (Subgroup.card_subgroup_dvd_card E)

theorem three_dvd_card_of_reeTitsModel {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {p f : ℕ} (h : ReeTitsModel S t p f) : 3 ∣ Nat.card S := by
  cases t with
  | twistedG2 => exact three_dvd_card_of_reeTitsModel_twistedG2 h
  | twistedF4 => exact three_dvd_card_of_reeTitsModel_twistedF4 h
  | Tits => exact three_dvd_card_of_reeTitsModel_tits h
  | _ => exact (h.2.choose_spec.2 : False).elim

end CFSG.RankThree.PartTwo.KFacts.KS14
