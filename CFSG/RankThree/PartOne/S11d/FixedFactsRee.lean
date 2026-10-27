module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalReeFinal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeBZero

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.LieType.Simplicity (titsData)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

@[expose] def LargeReeTitsNonLocalized :
    Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → p = 2 * a + 1 →
      ∀ σ : K ≃+* K, orderOf σ = p →
        NonLocalized (fixRes (ReeTag.F4.reeGammaFieldAut K a σ))

theorem mem_of_odd_pow_of_sup_zpowers {G : Type*} [Group G] {D : Subgroup G} [D.Normal] {g : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) (hg2 : g ^ 2 ∈ D) {x : G} {m : ℕ} (hm : Odd m)
    (hx : x ^ m = 1) : x ∈ D := by
  have hsq : ∀ y : G ⧸ D, y ^ 2 = 1 := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      have hy : y ∈ D ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top y
      obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hd1 : QuotientGroup.mk' D d = 1 := (QuotientGroup.eq_one_iff d).2 hd
      have hg1 : (QuotientGroup.mk' D g) ^ 2 = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).2 hg2
      have hcomm : ((QuotientGroup.mk' D g) ^ i) ^ 2 = ((QuotientGroup.mk' D g) ^ 2) ^ i := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      show (QuotientGroup.mk' D (d * g ^ i)) ^ 2 = 1
      rw [map_mul, hd1, one_mul, map_zpow, hcomm, hg1, one_zpow]
  obtain ⟨j, hj⟩ := hm
  have hy : (QuotientGroup.mk' D x) = 1 := by
    have h1 : (QuotientGroup.mk' D x) ^ m = 1 := by rw [← map_pow, hx, map_one]
    have h2 : (QuotientGroup.mk' D x) ^ m = (QuotientGroup.mk' D x) := by
      rw [hj, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← h2, h1]
  exact (QuotientGroup.eq_one_iff x).1 hy


theorem reeF4_pElements_zero {C : Type} [Group C] [Finite C] {α : MulAut C} {k : Type} [Field k]
    [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2)
    (e : ↥(fixSub α) ≃* ReeTag.F4.reeGamma k 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ x ∈ fixSub α, (∃ j : ℕ, orderOf x = p ^ j) → x ∈ fixRes α := by
  classical
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag k) := Subtype.finite
  set W₂ : Subgroup ↥(adjointGroup ReeTag.F4.tag k) := reeFixed ReeTag.F4 k 0 with hW₂
  have : Finite ↥W₂ := Subtype.finite
  let eW : ↥(fixSub α) ≃* ↥W₂ := e.trans (reeFixedEquivReeGamma k 0).symm
  have hT := titsData k hk
  have hsup := hT.commutator_sup_zpowers_eq_top hk
  have hg2 := hT.g₁_sq_mem
  have : (commutator ↥W₂).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hperfW : Group.IsPerfect ↥(commutator ↥W₂) := hT.isPerfect hk
  have hcomm : (commutator ↥(fixSub α)).map eW.toMonoidHom = commutator ↥W₂ := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eW.surjective]
  have hperf : Group.IsPerfect ↥(commutator ↥(fixSub α)) := by
    have e' : ↥(commutator ↥(fixSub α)) ≃* ↥(commutator ↥W₂) :=
      (Subgroup.equivMapOfInjective _ eW.toMonoidHom eW.injective).trans
        (MulEquiv.subgroupCongr hcomm)
    exact Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  have hsub : commutator ↥(fixSub α) ≤ perfectResidual ↥(fixSub α) :=
    (perfect_residual_transport (MonoidHom.id ↥(fixSub α))).2.2 _ hperf
  intro x hx ⟨j, hj⟩
  have hxo : (⟨x, hx⟩ : ↥(fixSub α)) ^ (p ^ j) = 1 := by
    apply Subtype.ext
    show x ^ (p ^ j) = 1
    rw [← hj]
    exact pow_orderOf_eq_one x
  have hw : (eW ⟨x, hx⟩) ^ (p ^ j) = 1 := by rw [← map_pow, hxo, map_one]
  have hmem : eW ⟨x, hx⟩ ∈ commutator ↥W₂ :=
    mem_of_odd_pow_of_sup_zpowers hsup hg2 (hp.odd_of_ne_two hp2 |>.pow) hw
  have hmem' : (⟨x, hx⟩ : ↥(fixSub α)) ∈ commutator ↥(fixSub α) := by
    rw [← hcomm] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    exact (eW.injective hyx) ▸ hy
  exact ⟨⟨x, hx⟩, hsub hmem', rfl⟩

theorem tagFixedFacts_twistedF4 (hTits : LargeReeTitsNonLocalized) :
    TagFixedFacts .twistedF4 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn0, hR⟩ := lieModel_twistedF4_iff.mp hM
  subst hn0
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := reeF4_model_data hR
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (ReeTag.F4.reeGamma K a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [← hα'ord]; exact pow_orderOf_eq_one α'
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK p hp hp5 β hβord α' hα'p ⟨x, hxβ⟩
  set ψ : MulAut (ReeTag.F4.reeGamma K a) := (MulAut.conj g)⁻¹ with hψdef
  have hψ : ψ * MulAut.congr e α * ψ⁻¹ = ReeTag.F4.reeGammaFieldAut K a β := by
    have : MulAut.congr e α =
        MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ := hg
    rw [hψdef, this]
    group
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeF4_fixed_data ha hK hp (by omega) hβord
  have hff' : p * f₀ = p * (2 * b + 1) := by rw [hfa, ← hbp]; ring
  have hf₀b : f₀ = 2 * b + 1 := Nat.eq_of_mul_eq_mul_left hp.pos hff'
  set φ : T ≃* ReeTag.F4.reeGamma K a := e.trans ψ with hφ
  have hφα : MulAut.congr φ α = ReeTag.F4.reeGammaFieldAut K a β := hψ
  have : Finite (fixSubfield β) := Subtype.finite
  by_cases hb : 1 ≤ b
  · have hfix := reeF4_fixRes_model_pos hb hbcard eC
    have hF : FieldAutT p α :=
      fieldAutT_of_conj_fix e hM hff' (by omega) α (ReeTag.F4.reeGammaFieldAut K a β) ψ hψ hfix
    obtain ⟨-, hcommu, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 b hb
      (fixSubfield β) hbcard
    have hsimple := isSimpleGroup_reeGamma_F4' hb hbcard
    have hnab : ∃ x y : ReeTag.F4.reeGamma (fixSubfield β) b, x * y ≠ y * x :=
      exists_noncomm_of_perfect hcommu
    have hperfG : Group.IsPerfect ↥(ReeTag.F4.reeGamma (fixSubfield β) b) :=
      isPerfect_of_simple_nonabelian hnab
    have hperf : Group.IsPerfect ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a β)) :=
      Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
    have hres := fixRes_eq_fixSub_of_perfect hperf
    have hNL := SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedLargeRee_of
      SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedLargeReeBZero a ha K hK p hp
      (by omega) β hβord
    have hP : ∀ x ∈ fixSub (MulAut.congr φ α), x ∈ fixRes (MulAut.congr φ α) := by
      intro x hx
      rw [hφα] at hx
      rw [hφα, hres]
      exact hx
    refine fixedFacts_of_transfer φ α hF ?_ (fun x hx _ => hP x hx)
      (Or.inl fun x hx _ => hP x hx)
    rw [hφα, hres]
    exact hNL
  · have hb0 : b = 0 := by omega
    subst hb0
    have hf₀1 : f₀ = 1 := hf₀b
    have hfix := reeF4_fixRes_model_zero hbcard eC
    have hF : FieldAutT p α :=
      fieldAutT_of_conj_fix_tits e hM (by rw [hff']) α (ReeTag.F4.reeGammaFieldAut K a β) ψ hψ
        hfix
    have hpa : p = 2 * a + 1 := by omega
    have hNL := hTits a ha K hK p hp (by omega) hpa β hβord
    have hMp : LieModel T .twistedF4 0 2 p := by
      rw [hf₀1, mul_one] at hM
      exact hM
    refine fixedFacts_of_transfer φ α hF ?_ ?_ (Or.inr hMp)
    · rw [hφα]
      exact hNL
    · rw [hφα]
      exact reeF4_pElements_zero hbcard eC hp (by omega)

end CFSG.RankThree.PartOne.FieldFix
