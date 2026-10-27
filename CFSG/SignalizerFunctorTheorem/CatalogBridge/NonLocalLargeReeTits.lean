module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeBZero
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsDerived
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsRegular
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.GroupTheory.PerfectResidualNodes

public noncomputable section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)
open CFSG.RankThree.PartOne.Sec66T (fixSub fixRes)
open CFSG.LieType.Simplicity (titsData)
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped IsMulCommutative commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge


section TwoGroup

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
  {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem largeRee_twoGroup_eq_bot_tits (f : k →+* K)
    (ι : reeFixed ReeTag.F4 k 0 →* ↥(ReeTag.F4.reeGamma K a))
    (hι : ∀ t : reeFixed ReeTag.F4 k 0,
      ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        baseChangeGL f (((t : adjointGroup ReeTag.F4.tag k)) : ModGL ReeTag.F4.tag k)) :
    ∀ E : Subgroup ↥(ReeTag.F4.reeGamma K a), IsPGroup ReeTag.F4.prime E →
      (∀ d ∈ commutator (reeFixed ReeTag.F4 k 0), ∀ e ∈ E, ι d * e * (ι d)⁻¹ ∈ E) → E = ⊥ := by
  classical
  have hp2 : Nat.Prime ReeTag.F4.prime := Nat.prime_two
  have : Fact ReeTag.F4.prime.Prime := ⟨hp2⟩
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    simpa using CharP.cast_eq_zero K 2
  have hXC : ReeTag.F4.reeGamma K a ≤ adjointGroup ReeTag.F4.tag K := fun g hg =>
    (ReeTag.mem_reeGamma.1 hg).1
  let θ : reeFixed ReeTag.F4 k 0 →* ModGL ReeTag.F4.tag K :=
    (baseChangeGL f).comp (((adjointGroup ReeTag.F4.tag k).subtype).comp
      (reeFixed ReeTag.F4 k 0).subtype)
  have hθ : ∀ t, θ t = ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) :=
    fun t => (hι t).symm
  have hθw : ∀ w : List ℤ, θ (gWordG k w) =
      (((gWordG K w : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) := fun w => baseChangeGL_gWordG f w
  let Jt : Subgroup (ModGL ReeTag.F4.tag K) := (commutator (reeFixed ReeTag.F4 k 0)).map θ
  have hJΓ : Jt ≤ ReeTag.F4.reeGamma K a := by
    rintro _ ⟨t, -, rfl⟩
    rw [hθ]
    exact (ι t).2
  have hJC : Jt ≤ adjointGroup ReeTag.F4.tag K := hJΓ.trans hXC
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.F4.tag
  have hgood : ∀ w ∈ [[1], [2, 3, 2, -3], [3, 4, 3, 4, 3, 4, 3, 4]], ∀ l ∈ w, GoodLetter l := by
    decide
  have hyJ : ∀ i, titsRegular K i ∈ Jt := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [titsRegular, hi, ↓reduceIte]
      refine ⟨gWordG k [1], gWordG_mem_commutator_of_even _ (hgood _ (by simp)) (by decide)
        (by decide) (by decide), ?_⟩
      rw [hθw, gWordG_g0_eq]
    · simp only [titsRegular, hi, ↓reduceIte]
      refine ⟨gWordG k [2, 3, 2, -3], gWordG_mem_commutator_of_even _ (hgood _ (by simp))
        (by decide) (by decide) (by decide), ?_⟩
      rw [hθw, gWordG_y_eq h2]
  have hn : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ Jt :=
    ⟨gWordG k [3, 4, 3, 4, 3, 4, 3, 4], gWordG_mem_commutator_of_even _ (hgood _ (by simp))
      (by decide) (by decide) (by decide), by rw [hθw, canonicalRep_longest_eq hw₀]⟩
  intro E hE hnorm
  have hWr : IsPGroup ReeTag.F4.prime (E.map (ReeTag.F4.reeGamma K a).subtype) := hE.map _
  have hWC : E.map (ReeTag.F4.reeGamma K a).subtype ≤ adjointGroup ReeTag.F4.tag K := by
    rintro _ ⟨e, -, rfl⟩
    exact hXC e.2
  have hbot := eq_bot_of_isPGroup_of_normalized_regular (τ := ReeTag.F4.tag) ReeTag.F4.prime
    hJC hWC hWr (y := titsRegular K) hyJ (titsRegular_mem_posUnipotent h2) (c := fun _ => 1)
    (fun _ => one_ne_zero) (hasCoord_titsRegular h2) hw₀ hn
    (fun j hj w hw => by
      obtain ⟨t, ht, rfl⟩ := hj
      obtain ⟨e, he, rfl⟩ := hw
      rw [hθ]
      exact ⟨_, hnorm t ht e he, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ (ReeTag.F4.reeGamma K a).subtype_injective).1 hbot

end TwoGroup

section OddGroup

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
  {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem largeRee_oddGroup_eq_bot_tits (hK : Nat.card K = 2 ^ (2 * a + 1)) (hk : Nat.card k = 2)
    (f : k →+* K) (ι : reeFixed ReeTag.F4 k 0 →* ↥(ReeTag.F4.reeGamma K a))
    (hι : ∀ t : reeFixed ReeTag.F4 k 0,
      ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        baseChangeGL f (((t : adjointGroup ReeTag.F4.tag k)) : ModGL ReeTag.F4.tag k))
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) :
    ∀ E : Subgroup ↥(ReeTag.F4.reeGamma K a), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ s = 1) →
      (∀ d ∈ commutator (reeFixed ReeTag.F4 k 0), ∀ e ∈ E, ι d * e * (ι d)⁻¹ ∈ E) → E = ⊥ := by
  classical
  intro E hEcomm hEexp hnorm
  have hXC : ReeTag.F4.reeGamma K a ≤ adjointGroup ReeTag.F4.tag K := fun g hg =>
    (ReeTag.mem_reeGamma.1 hg).1
  let F := AlgebraicClosure K
  have hFr : CharP F ReeTag.F4.prime :=
    charP_of_injective_algebraMap (algebraMap K F).injective _
  have : Fintype ↥(ReeTag.F4.shortLabels) := Fintype.ofFinite _
  have hp0 : ((ReeTag.F4.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K ReeTag.F4.prime
  let ρ₀ : ↥(ReeTag.F4.reeGamma K a) →* Module.End K (ReeTag.F4.shortModule K) :=
    (ReeTag.shortRestrictHom ReeTag.F4 K hp0).comp (Subgroup.inclusion hXC)
  have hρ₀ : Function.Injective ρ₀ :=
    (shortRestrictHom_injective ReeTag.F4).comp (Subgroup.inclusion_injective hXC)
  let ρ : ↥(ReeTag.F4.reeGamma K a) →* Module.End F (↥ReeTag.F4.shortLabels → F) :=
    matrixRep F (ReeTag.F4.shortBasis K) ρ₀
  have hρ : Function.Injective ρ := matrixRep_injective F _ hρ₀
  have hdim : Module.finrank F (↥ReeTag.F4.shortLabels → F) = 26 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, ReeTag.card_shortLabels]
    rfl
  have hEc : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext (hEcomm _ x.2 _ y.2)⟩⟩
  have : Finite E := Subtype.finite
  have hinv : (Nat.card E : F) ≠ 0 :=
    cast_card_ne_zero_of_exponent (r := ReeTag.F4.prime) Nat.prime_two hs hs2 hEexp
  obtain ⟨hfinE, hcardE⟩ := finite_card_weights ρ E hEc
  have := hfinE
  let ι' : ↥(commutator (reeFixed ReeTag.F4 k 0)) →* ↥(ReeTag.F4.reeGamma K a) :=
    ι.comp (commutator (reeFixed ReeTag.F4 k 0)).subtype
  have hnormι : ∀ g : ↥(commutator (reeFixed ReeTag.F4 k 0)), ∀ v ∈ E,
      ι' g * v * (ι' g)⁻¹ ∈ E := fun g v hv => hnorm g.1 g.2 v hv
  have hπcard : Nat.card (Wt ρ E) < 32 := by
    have h26 : Nat.card (Wt ρ E) ≤ 26 := by
      rw [hdim] at hcardE
      exact hcardE
    omega
  have hker := titsD_action_trivial hk hπcard (weightAction ρ E ι' hnormι)
  have hcommElt : ∀ pr ∈ modStab ++ modSpan, ∀ v : ↥(ReeTag.F4.reeGamma K a), v ∈ E →
      cElt K pr * (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ : adjointGroup ReeTag.F4.tag K) =
        (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ : adjointGroup ReeTag.F4.tag K) * cElt K pr := by
    intro pr hpr v hv
    have htc : (⁅gWordG k pr.1, gWordG k pr.2⁆ : reeFixed ReeTag.F4 k 0) ∈
        commutator (reeFixed ReeTag.F4 k 0) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hπt := hker ⟨_, htc⟩
    have hc := centralizes_of_weightAction_eq_one ρ hρ E hEc hinv ι' hnormι ⟨_, htc⟩ hπt v hv
    have h1 : ((ι' ⟨⁅gWordG k pr.1, gWordG k pr.2⁆, htc⟩ : ↥(ReeTag.F4.reeGamma K a)) :
        ModGL ReeTag.F4.tag K) =
        ((cElt K pr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
      show ((ι ⁅gWordG k pr.1, gWordG k pr.2⁆ : ↥(ReeTag.F4.reeGamma K a)) :
        ModGL ReeTag.F4.tag K) = _
      rw [hι, baseChangeGL_cElt]
    have h2 := congrArg (fun z : ↥(ReeTag.F4.reeGamma K a) => (z : ModGL ReeTag.F4.tag K)) hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h1] at h2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hscal : ∀ v : ↥(ReeTag.F4.reeGamma K a), v ∈ E →
      ∃ c : K, ∀ u ∈ ReeTag.F4.shortModule K,
        ((v : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) u = c • u :=
    fun v hv => scalar_of_commutes (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ :
      adjointGroup ReeTag.F4.tag K) (fun pr hpr => hcommElt pr hpr v hv)
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  obtain ⟨c, hc⟩ := hscal v hv
  have hvZ : v ∈ Subgroup.center ↥(ReeTag.F4.reeGamma K a) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have key : (⟨(y : ModGL ReeTag.F4.tag K), hXC y.2⟩ : adjointGroup ReeTag.F4.tag K) *
        ⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ =
        ⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ *
          ⟨(y : ModGL ReeTag.F4.tag K), hXC y.2⟩ := by
      apply shortRestrictHom_injective ReeTag.F4 (K := K)
      refine LinearMap.ext fun u => Subtype.ext ?_
      simp only [map_mul, Module.End.mul_apply, ReeTag.coe_shortRestrictHom_apply]
      have hyu : ((y : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K))
          (u : RootModule ReeTag.F4.tag K) ∈ ReeTag.F4.shortModule K :=
        ReeTag.mem_shortModule_of_mem hp0 (hXC y.2) u.2
      rw [hc _ hyu, hc _ u.2, map_smul]
    have h3 := congrArg Subtype.val key
    simp only [Subgroup.coe_mul] at h3 ⊢
    exact h3
  rw [hZ] at hvZ
  exact hvZ

end OddGroup

theorem subfieldNonLocalizedLargeReeTits :
    ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → p = 2 * a + 1 →
        ∀ σ : K ≃+* K, orderOf σ = p →
          NonLocalized (fixRes (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  intro a ha K _ _ _ hK p hp hp3 hpa σ hσ
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨hpf, hcard⟩ := card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ] at hpf hcard
  have hk2 : Nat.card (fixSubfield σ) = 2 := by
    rw [hcard, hpa, Nat.div_self (by omega), pow_one]
  obtain ⟨b, hkcard, hfixed⟩ := largeRee_fixed_data ha hK hp hp3 σ hσ
  have hb : b = 0 := by
    have h1 : 2 ^ (2 * b + 1) = 2 ^ 1 := by rw [← hkcard, hk2, pow_one]
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * 0 + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinj : Function.Injective (baseChangeGL (τ := ReeTag.F4.tag) (fixSubfield σ).subtype) :=
    baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype
  let eC : fixSub (ReeTag.F4.reeGammaFieldAut K a σ) ≃* ReeTag.F4.reeGamma (fixSubfield σ) 0 :=
    isoOfMapEq (ReeTag.F4.reeGamma K a) _ (ReeTag.F4.reeGamma (fixSubfield σ) 0)
      (baseChangeGL (fixSubfield σ).subtype) hinj hfixed
  have heC : ∀ x : fixSub (ReeTag.F4.reeGammaFieldAut K a σ),
      baseChangeGL (fixSubfield σ).subtype
        ((eC x : ReeTag.F4.reeGamma (fixSubfield σ) 0) : ModGL ReeTag.F4.tag (fixSubfield σ)) =
        (((x : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K)) := fun x =>
    isoOfMapEq_val _ _ _ _ hinj _ x
  let Φ : reeFixed ReeTag.F4 (fixSubfield σ) 0 ≃*
      fixSub (ReeTag.F4.reeGammaFieldAut K a σ) :=
    (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).trans eC.symm
  let ι : reeFixed ReeTag.F4 (fixSubfield σ) 0 →* ↥(ReeTag.F4.reeGamma K a) :=
    (fixSub (ReeTag.F4.reeGammaFieldAut K a σ)).subtype.comp Φ.toMonoidHom
  have hιval : ∀ t : reeFixed ReeTag.F4 (fixSubfield σ) 0,
      ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        baseChangeGL (fixSubfield σ).subtype
          ((t : adjointGroup ReeTag.F4.tag (fixSubfield σ)) :
            ModGL ReeTag.F4.tag (fixSubfield σ)) := by
    intro t
    have h := heC (eC.symm (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0 t))
    rw [MulEquiv.apply_symm_apply, ReeTag.coe_reeFixedEquivReeGamma] at h
    exact h.symm
  have hperf : Group.IsPerfect ↥(commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)) :=
    (titsData (fixSubfield σ) hk2).isPerfect hk2
  have : Finite ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ)) := Subtype.finite
  have hcomm : (commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))).map
      Φ.symm.toMonoidHom = commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Φ.symm.surjective]
  have hperfJ : Group.IsPerfect ↥(commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))) := by
    have e' : ↥(commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))) ≃*
        ↥(commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)) :=
      (Subgroup.equivMapOfInjective _ Φ.symm.toMonoidHom Φ.symm.injective).trans
        (MulEquiv.subgroupCongr hcomm)
    exact Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  have hsub : commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ)) ≤
      perfectResidual ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ)) :=
    (perfect_residual_transport (MonoidHom.id ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ)))).2.2 _
      hperfJ
  have hfixι : ∀ d ∈ commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0),
      ι d ∈ fixRes (ReeTag.F4.reeGammaFieldAut K a σ) := by
    intro d hd
    have hmem : Φ d ∈ commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ)) := by
      have hd' : d ∈ (commutator ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))).map
          Φ.symm.toMonoidHom := by
        rw [hcomm]
        exact hd
      obtain ⟨x, hx, hxd⟩ := hd'
      have hΦx : Φ d = x := by
        rw [← hxd]
        exact Φ.apply_symm_apply x
      rw [hΦx]
      exact hx
    exact ⟨Φ d, hsub hmem, rfl⟩
  refine nonLocalized_of_elemAbelian (fun s E hs hE0 hEcomm hEexp hle => hE0 ?_)
  have hnorm : ∀ d ∈ commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0), ∀ e ∈ E,
      ι d * e * (ι d)⁻¹ ∈ E := fun d hd e he =>
    (Subgroup.mem_normalizer_iff.1 (hle (hfixι d hd)) e).1 he
  by_cases hs2 : s = 2
  · subst hs2
    have : Fact (Nat.Prime 2) := ⟨hs⟩
    have hEp : IsPGroup 2 E := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact largeRee_twoGroup_eq_bot_tits (fixSubfield σ).subtype ι hιval E hEp hnorm
  · exact largeRee_oddGroup_eq_bot_tits hK hk2 (fixSubfield σ).subtype ι hιval hs hs2 E hEcomm
      hEexp hnorm

end CFSG.SignalizerFunctorTheorem.CatalogBridge
