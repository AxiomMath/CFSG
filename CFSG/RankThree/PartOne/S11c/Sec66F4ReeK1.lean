module

public import CFSG.RankThree.PartOne.S11c.Sec66F4Ree
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.S11c.Sec66Degen
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem reeF4_model_data
    {T : Type} [Group T] {f : ℕ}
    (hR : ReeTitsModel T .twistedF4 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧ Nonempty (T ≃* F4.reeGamma K a) := by
  obtain ⟨-, hf3, -, -, -, -, hmain⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions T 2 f hR
  obtain ⟨hadm, a, hfa, K, _, _, hKcard, he⟩ := hR
  have : CharP K F4.prime := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
      rw [← Nat.card_eq_fintype_card, hKcard])
  obtain ⟨⟨e⟩, -⟩ := hmain a K hfa hKcard he
  exact ⟨a, K, inferInstance, inferInstance, this, by omega, hfa, hKcard, ⟨e⟩⟩

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley SteinbergBT in
theorem reeF4_fixed_data_odd
    {a : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β : K ≃+* K} (hβ : orderOf β = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield β) = 2 ^ (2 * b + 1) ∧
      ∃ _ : CharP (fixSubfield β) F4.prime,
        Nonempty (↥(fixSub (F4.reeGammaFieldAut K a β)) ≃* F4.reeGamma (fixSubfield β) b) := by
  classical
  obtain ⟨b, hbp, hbcard, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield β) F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hbcard])
  refine ⟨b, hbp, hbcard, hchar, ?_⟩
  have hFix : fixSub (F4.reeGammaFieldAut K a β) =
      (F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  exact ⟨(((fixSub (F4.reeGammaFieldAut K a β)).equivMapOfInjective
      (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfix))).trans
    ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm⟩

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley SteinbergBT in
theorem reeF4_fixed_data
    {a : ℕ} (_ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {β : K ≃+* K} (hβ : orderOf β = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield β) = 2 ^ (2 * b + 1) ∧
      ∃ _ : CharP (fixSubfield β) F4.prime,
        Nonempty (↥(fixSub (F4.reeGammaFieldAut K a β)) ≃* F4.reeGamma (fixSubfield β) b) :=
  reeF4_fixed_data_odd hK hp (by omega) hβ

open CFSG.LieType.Simplicity (isSimpleGroup_quotient_center_reeFixed_F4) in
theorem isSimpleGroup_reeGamma_F4'
    {b : ℕ} (hb : 1 ≤ b) {k : Type}
    [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsSimpleGroup (ReeTag.F4.reeGamma k b) := by
  set e := ReeTag.reeFixedEquivReeGamma k b
  have hZ : Subgroup.center (reeFixed ReeTag.F4 k b) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (ReeTag.F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [ReeTag.large_Ree_fixed_group_center_trivial b k hk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
    isSimpleGroup_quotient_center_reeFixed_F4 b hb hk
  have hs : IsSimpleGroup (reeFixed ReeTag.F4 k b) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact e.symm.isSimpleGroup

theorem reeF4_fixRes_model_pos
    {C : Type} [Group C] [Finite C]
    {α : MulAut C} {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (e : ↥(fixSub α) ≃* ReeTag.F4.reeGamma k b) :
    LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .twistedF4 0 2 (2 * b + 1) := by
  obtain ⟨-, hcomm, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 b hb k hk
  have hsimple := isSimpleGroup_reeGamma_F4' hb hk
  have hnab : ∃ x y : ReeTag.F4.reeGamma k b, x * y ≠ y * x := exists_noncomm_of_perfect hcomm
  obtain ⟨iso⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := k) (a := b) hb hk
  have hfx : reeFixedGroup .F4 k reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ b else 2 ^ (b + 1)) = ReeTag.F4.reeGamma k b :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := k) (a := b)).symm
  have hR : ReeTitsModel (ReeTag.F4.reeGamma k b) .twistedF4 2 (2 * b + 1) := by
    refine ⟨⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one b, by omega⟩, b, rfl, k,
      inferInstance, inferInstance, hk, ?_⟩
    let iso' : DerivedCentralQuotient (reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ b else 2 ^ (b + 1))) ≃*
        DerivedCentralQuotient (ReeTag.F4.reeGamma k b) :=
      centerQuotientCongr (MulEquiv.subgroupCongr (by rw [hfx]; rfl))
    exact ⟨iso.symm.trans iso'.symm⟩
  exact lieModel_fixRes_of_simple hnab e (lieModel_twistedF4_iff.mpr ⟨rfl, hR⟩)

open CFSG.LieType.Simplicity (titsData) in
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv) in
theorem reeF4_fixRes_model_zero
    {C : Type} [Group C] [Finite C]
    {α : MulAut C} {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]
    (hk : Nat.card k = 2) (e : ↥(fixSub α) ≃* ReeTag.F4.reeGamma k 0) :
    LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .Tits 0 2 1 := by
  classical
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  set W₂ : Subgroup ↥(adjointGroup ReeTag.F4.tag k) := reeFixed ReeTag.F4 k 0 with hW₂
  have : Finite ↥(adjointGroup ReeTag.F4.tag k) := Subtype.finite
  let eR : ↥W₂ ≃* ReeTag.F4.reeGamma k 0 := ReeTag.reeFixedEquivReeGamma k 0
  let θ : ↥(fixSub α) →* ↥W₂ := eR.symm.toMonoidHom.comp e.toMonoidHom
  have hsurj : Function.Surjective θ := eR.symm.surjective.comp e.surjective
  have hker : θ.ker ≤ Subgroup.center ↥(fixSub α) := by
    intro x hx
    have hx1 : θ x = 1 := hx
    have hinj : Function.Injective θ := eR.symm.injective.comp e.injective
    have : x = 1 := hinj (by rw [hx1, map_one])
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨e1⟩ := nonempty_centerQuotient_perfectResidual_equiv (fixSub α) W₂ θ hsurj hker
  set N₂ : Subgroup ↥(adjointGroup ReeTag.F4.tag k) := ⁅W₂, W₂⁆ with hN₂
  have hNsub : N₂.subgroupOf W₂ = commutator ↥W₂ := by
    rw [hN₂, ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective W₂.subtype_injective _
  have hNW : N₂ ≤ W₂ := Subgroup.commutator_le_self W₂
  have hNnormal : (N₂.subgroupOf W₂).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥W₂ ⧸ N₂.subgroupOf W₂) := by
    have : (N₂.subgroupOf W₂).Normal := hNnormal
    have : CommGroup (↥W₂ ⧸ commutator ↥W₂) := inferInstanceAs (CommGroup (Abelianization ↥W₂))
    have : Group.IsSolvable (↥W₂ ⧸ commutator ↥W₂) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hq : IsQuasisimple (commutator (reeFixed ReeTag.F4 k 0)) :=
    (titsData k hk).isQuasisimple hk
  have hperf : Group.IsPerfect ↥N₂ := by
    have h1 : Group.IsPerfect ↥(commutator ↥W₂) := hq.1
    have h2 : (commutator ↥W₂).map W₂.subtype = N₂ := Subgroup.map_subtype_commutator W₂
    rw [← h2]
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.equivMapOfInjective _ W₂.subtype
      W₂.subtype_injective).toMonoidHom) (Subgroup.equivMapOfInjective _ W₂.subtype
      W₂.subtype_injective).surjective
  have hres : inSubgroup perfectResidual W₂ = N₂ :=
    inSubgroup_perfectResidual_eq_of_normal hNW hNnormal hperf hsolv
  have hH := reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0
  have hHc : ⁅reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)),
      reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))⁆ =
      N₂.map (adjointGroup ReeTag.F4.tag k).subtype := by
    rw [hN₂, Subgroup.map_commutator]
    exact congrArg₂ (fun A B => ⁅A, B⁆) hH hH
  let eN : ↥N₂ ≃* ↥⁅reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)),
      reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))⁆ :=
    (Subgroup.equivMapOfInjective N₂ (adjointGroup ReeTag.F4.tag k).subtype
      (adjointGroup ReeTag.F4.tag k).subtype_injective).trans (MulEquiv.subgroupCongr hHc.symm)
  have hTits : ReeTitsModel (DerivedCentralQuotient (reeFixedGroup .F4 k reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)))) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_refl 1, rfl, rfl, rfl⟩, 0, rfl, k, inferInstance, inferInstance, hk,
      ⟨MulEquiv.refl _⟩⟩
  have e2 : ↥(inSubgroup perfectResidual W₂) ⧸ Subgroup.center ↥(inSubgroup perfectResidual W₂) ≃*
      DerivedCentralQuotient (reeFixedGroup .F4 k reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))) :=
    centerQuotientCongr ((MulEquiv.subgroupCongr hres).trans eN)
  exact lieModel_of_mulEquiv (e1.trans e2).symm (lieModel_Tits_iff.mpr ⟨rfl, hTits⟩)

theorem fieldAutT_of_conj_fix_tits {T C : Type} [Group T] [Group C] [Finite T] [Finite C]
    {p f : ℕ} (e : T ≃* C) (hM : LieModel T .twistedF4 0 2 f) (hff' : f = p * 1)
    (α : MulAut T) (β ψ : MulAut C) (hψ : ψ * MulAut.congr e α * ψ⁻¹ = β)
    (hfix : LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) .Tits 0 2 1) :
    FieldAutT p α := by
  have hψ' : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β := by rw [hψ]
  have e12 : ↥(fixSub α) ≃* ↥(fixSub β) :=
    ((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ')
  refine ⟨.twistedF4, 0, 1, le_refl 1, ?_, Or.inr ⟨rfl, rfl, rfl, lieModel_fixRes_congr e12 hfix⟩⟩
  rw [← hff']
  exact hM

theorem sec66T_K1_twistedF4
    (hLang : LargeReeFieldAutCoset) :
    Sec66T_K1 .twistedF4 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨hn0, hR⟩ := lieModel_twistedF4_iff.mp hM
  subst hn0
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := reeF4_model_data hR
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Finite (F4.reeGamma K a) := Finite.of_equiv T e.toEquiv
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'p : α' ^ p = 1 := by rw [← hα'ord]; exact pow_orderOf_eq_one α'
  have hα'inn : α' ∉ (MulAut.conj : ↥(F4.reeGamma K a) →* MulAut ↥(F4.reeGamma K a)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := hLang a ha K hK p hp hp5 β hβord α' hα'p ⟨x, hxβ⟩
  have hψ : (MulAut.conj g)⁻¹ * MulAut.congr e α * ((MulAut.conj g)⁻¹)⁻¹ =
      F4.reeGammaFieldAut K a β := by
    have : MulAut.congr e α = MulAut.conj g * F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ :=
      hg
    rw [this]
    group
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeF4_fixed_data ha hK hp (by omega) hβord
  have hff' : f = p * (2 * b + 1) := by rw [mul_comm, hbp, hfa]
  by_cases hb : 1 ≤ b
  · have hfix := reeF4_fixRes_model_pos hb hbcard eC
    exact fieldAutT_of_conj_fix e hM hff' (by omega) α (F4.reeGammaFieldAut K a β)
      (MulAut.conj g)⁻¹ hψ hfix
  · have hb0 : b = 0 := by omega
    subst hb0
    have hfix := reeF4_fixRes_model_zero hbcard eC
    exact fieldAutT_of_conj_fix_tits e hM hff' α (F4.reeGammaFieldAut K a β)
      (MulAut.conj g)⁻¹ hψ hfix

end CFSG.RankThree.PartOne.Sec66T
