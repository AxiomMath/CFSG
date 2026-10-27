module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h2
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowCases
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open TauCeti (PrimePower LieTypeIndex)
open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (commutator_reeGamma_F4_zero_data tits_valid
  reeF4_inner_or_field exists_fixSubgroup_fieldAut_equiv')

set_option linter.unusedSectionVars false


theorem exists_conj_of_g2_small {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    (hq2 : q.p = 2) (hq8 : q.card < 8) {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) {x : MulAut L} (hx3 : x ^ 3 = 1) :
    ∃ c : L, x = MulAut.conj c := by
  obtain ⟨K, _, _, hK, -, ⟨e'⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let eA : ↥(adjointGroup .G2 K) ≃* AdjointQuotient .G2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hr : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard := TauCeti.PrimePower.card_def q
  have hq3 : 3 ≤ q.p ^ q.exponent := by rw [← hcard]; exact hr
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 q.p q.exponent :=
    ⟨q.prime_p, q.exponent_pos, rfl, hq3⟩
  have hM : LieModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, hadm, K, inferInstance, inferInstance,
      by rw [hK, hcard], ⟨e'.trans eA⟩⟩)
  have hML := hM.of_mulEquiv e.symm
  have he2 : q.exponent = 2 := by
    rw [hq2] at hcard
    have h1 : q.exponent < 3 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : q.exponent ≠ 1 := by
      intro h
      rw [h] at hcard
      omega
    have := q.exponent_pos
    omega
  by_contra hno
  push Not at hno
  have hxin : x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner L := by
    rintro ⟨c, hc⟩
    exact hno c hc.symm
  obtain ⟨f₀, hf, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds L .G2 0
    q.p q.exponent hadm hML (by decide) 3 Nat.prime_three (by norm_num)
    (by simp [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor]) (by simp) (by simp) x hx3 hxin
  omega

theorem noA5_triD4_two_outer (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq2 : q.p = 2) {S : Type} [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)) (α : MulAut S)
    (hα : α ^ 3 = 1) (hout : ∀ a : S, MulAut.conj a ≠ α) (J : Subgroup S)
    (hJ : IsComponentOf J (fixSubgroup α)) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := he
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  have hβ' : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hout' : MulAut.congr e' α ∉
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨x, hx⟩
    apply hout (e'.symm x)
    apply (MulAut.congr e').injective
    rw [InputsL33c.congr_conj_apply, MulEquiv.apply_symm_apply]
    exact hx
  have hN := noA5Comps_triality_outer (f := q.exponent) q.exponent_pos (K₃ := K)
    (by rw [hK, hq2]) σ (by rw [← hq2]; exact hσ) _ hβ' hout'
  have hJ' := InputsL33.isComponentOf_map_congr e' hJ
  intro hL
  exact noA5_of_noA5Comps hN hJ' (Claims1110h.a5Center_map e' hL)

theorem isQuasisimple_of_simple_nonab' {J : Type*} [Group J] (hs : IsSimpleGroup J)
    (hn : ∃ a b : J, a * b ≠ b * a) : CFSG.IsQuasisimple J := by
  have hc : Subgroup.center J = ⊥ := by
    rcases (inferInstance : (Subgroup.center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator J).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have hmem : ⁅a, b⁆ ∈ commutator J := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem noA5Comps_of_comm {H : Type} [Group H] (h : ∀ a b : H, a * b = b * a) : NoA5Comps H := by
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := h }
  haveI : Group.IsSolvable H := Group.isSolvable_of_comm h
  exact noA5Comps_of_isSolvable

theorem noA5Comps_reeGamma_F4 {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) : NoA5Comps ↥(ReeTag.F4.reeGamma k b) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma k b) := Subtype.finite
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    obtain ⟨hs, hnc, -⟩ := commutator_reeGamma_F4_zero_data hk2
    obtain ⟨e₃⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv
      (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group 2 1
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨tits_valid, ⟨MulEquiv.refl _⟩⟩)
    obtain ⟨-, -, ⟨eT⟩⟩ := commutator_reeGamma_F4_zero_data hk2
    have hM60 : Nat.card ↥(commutator ↥(ReeTag.F4.reeGamma k 0)) ≠ 60 := by
      rw [Nat.card_congr (eT.trans e₃).toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
      norm_num
    haveI := hs
    refine noA5Comps_of_normal (commutator ↥(ReeTag.F4.reeGamma k 0))
      (isQuasisimple_of_simple_nonab' hs hnc) ?_ ?_
    · exact Group.isSolvable_of_comm fun a b => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hxy : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [hxy, commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · exact not_a5_of_center_eq_bot
        (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc) hM60
  · by_cases hnc : ∃ x y : ↥(ReeTag.F4.reeGamma k b), x * y ≠ y * x
    · haveI : IsSimpleGroup ↥(ReeTag.F4.reeGamma k b) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
      refine noA5Comps_of_simple hnc ?_
      have hord :=
        (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b
          k hk).1
      set q := 2 ^ (2 * b + 1) with hq
      have h12 : 2 ^ 12 ∣ Nat.card ↥(ReeTag.F4.reeGamma k b) := by
        rw [hord]
        have : 2 ^ 12 ∣ q ^ 12 := pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 12
        exact this.trans (Dvd.intro ((q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
          (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)) (by ring))
      intro h60
      rw [h60] at h12
      norm_num at h12
    · push Not at hnc
      exact noA5Comps_of_comm hnc

theorem noA5_reeF4_outer (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) {S : Type} [Group S]
    [Finite S] (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) (x : MulAut S)
    (hx3 : x ^ 3 = 1) (hout : ∀ c : S, x ≠ MulAut.conj c) (J : Subgroup S)
    (hJ : IsComponentOf J (fixSubgroup x)) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  classical
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hβ : MulAut.congr e x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hβ1 : MulAut.congr e x ≠ 1 := by
    intro h
    apply hout 1
    rw [map_one]
    exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  rcases reeF4_inner_or_field ha hK Nat.prime_three hβ hβ1 with ⟨y, hy, -, -⟩ |
    ⟨σ, g, hσ, hβeq⟩
  · exfalso
    apply hout (e.symm y)
    apply (MulAut.congr e).injective
    rw [hy, InputsL33c.congr_conj_apply, MulEquiv.apply_symm_apply]
  · obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
      exists_fixSubgroup_fieldAut_equiv' hK Nat.prime_three (by norm_num) σ hσ
    haveI := hchar
    haveI : Finite (fixSubfield σ) := Subtype.finite
    have hF : NoA5Comps ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) :=
      NoA5Comps.of_mulEquiv eC (noA5Comps_reeGamma_F4 hkcard)
    have hN : NoA5Comps ↥(fixSubgroup (MulAut.congr e x)) :=
      NoA5Comps.of_conj_eq (ψ := (MulAut.conj g)⁻¹) (by rw [hβeq]; group) hF
    have hJ' := InputsL33.isComponentOf_map_congr e hJ
    intro hL
    exact noA5_of_noA5Comps hN hJ' (Claims1110h.a5Center_map e hL)

theorem exists_conj_of_tits (hv : LieTypeIndex.tits.Valid) {L : Type} [Group L] [Finite L]
    (he : Nonempty (L ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) {x : MulAut L}
    (hx3 : x ^ 3 = 1) : ∃ c : L, x = MulAut.conj c := by
  have hR := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, he⟩
  have h2 := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier L 2 1 hR).1
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  obtain ⟨c, hc⟩ := CFSG.AGLEmbedding.OuterSylow.mem_inner_of_not_dvd_card_outer Nat.prime_three
    (fun hd => by
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)) hx3
  exact ⟨c, hc.symm⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
