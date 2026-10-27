module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.GroupTheory.PStability.Solvable
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.LocalAnalysis.SolvableSignalizer.Factorization.Criterion
import CFSG.LocalAnalysis.SolvableSignalizer.Transitivity
import CFSG.LocalAnalysis.SolvableZJ.NormalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

section

variable {A G : Type*} [CommGroup A] [Group G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

private theorem map_embeddedThompsonCenter_of_injective {H K : Type*} [Group H] [Finite H]
    [Group K] [Finite K] (P : Subgroup H) (f : H →* K) (hf : Function.Injective f) :
    (embeddedThompsonCenter P).map f = embeddedThompsonCenter (P.map f) :=
  map_embeddedThompsonCenter P f (by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf, bot_inf_eq])

private theorem coe_eq_map_mul_map_of_subgroupProduct {U : Subgroup G} {R N : Subgroup U}
    (h : subgroupProduct R N = Set.univ) :
    (U : Set G) = (R.map U.subtype : Set G) * (N.map U.subtype : Set G) := by
  refine Set.Subset.antisymm (fun g hg => ?_) ?_
  · have hmem : (⟨g, hg⟩ : U) ∈ subgroupProduct R N := by rw [h]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := hmem
    exact ⟨x, Subgroup.mem_map_of_mem _ hx, y, Subgroup.mem_map_of_mem _ hy,
      by simpa using congrArg Subtype.val hxy⟩
  · rintro g ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x', -, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', -, rfl⟩ := Subgroup.mem_map.mp hy
    exact U.mul_mem x'.2 y'.2

end

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

omit [Finite A] in
private theorem isInvariant_embeddedThompsonCenter {T : Subgroup G} (hT : IsInvariant α T) :
    IsInvariant α (embeddedThompsonCenter T) := by
  intro a
  rw [map_embeddedThompsonCenter_of_injective T (α a).toMonoidHom (α a).injective, hT a]

private lemma embeddedThompsonCenter_ne_bot_and_compatibleAt (d : Datum p α θ)
    (hq : q.Prime) {T : Subgroup G} (hT : CompatibleAt p α θ {q} T) (hne : T ≠ ⊥) :
    embeddedThompsonCenter T ≠ ⊥ ∧ CompatibleAt p α θ {q} (embeddedThompsonCenter T) := by
  obtain ⟨hz, hzq⟩ := SignalizerFunctor.Helpers.embedded_order_thompson_center_pgroup q hq T
    ((CFSG.primeSupported_singleton_iff_isPGroup q hq).mp hT.2) hne
  exact ⟨hz, Compatible.of_le_of_isInvariant d hT.1 (Subgroup.map_subtype_le _)
    (isInvariant_embeddedThompsonCenter hT.1.1),
    (CFSG.primeSupported_singleton_iff_isPGroup q hq).mpr hzq⟩

private lemma conjugate_completionIn_normalizer (d : Datum p α θ)
    {T : Subgroup G} (hT : IsInvariant α T) {c : G} (hc : c ∈ commonSignalizerWhole θ) :
    conjugate (completionIn θ (Subgroup.normalizer
      (embeddedThompsonCenter T : Set G))) c =
    completionIn θ (Subgroup.normalizer
      (embeddedThompsonCenter (conjugate T c) : Set G)) := by
  rw [conjugate, (map_conj_completionIn d
      (isInvariant_embeddedThompsonCenter hT).normalizer hc).2,
    Subgroup.map_equiv_normalizer_eq, conjugate,
    map_embeddedThompsonCenter_of_injective T _ (MulAut.conj c⁻¹).injective]

private lemma exists_sylow_isInvariant_le_of_compatible (d : Datum p α θ) (hq : q.Prime)
    {U R : Subgroup G} (hU : Compatible p α θ U) (hR : IsInvariant α R)
    (hRq : primeSupported {q} (Nat.card R)) (hRU : R ≤ U) :
    ∃ T : Subgroup G, (∃ Q : Sylow q U, (Q : Subgroup U).map U.subtype = T) ∧
      IsInvariant α T ∧ R ≤ T := by
  have := d.isElementaryAbelian
  let β := restrictAction α U hU.1
  have hcomp : ∀ a, (α a).toMonoidHom.comp U.subtype = U.subtype.comp (β a).toMonoidHom :=
    fun a => by
      ext x
      exact (restrictAction_apply α U hU.1 a x).symm
  have hRinv : IsInvariant β (R.subgroupOf U) := by
    intro a
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRU,
      hR a]
  obtain ⟨Q, hQ, hRQ⟩ := exists_sylow_isInvariant_le p d.prime
    (CFSG.IsElementaryAbelian.isPGroup p A) β q hq
    (d.prime.coprime_iff_not_dvd.mp hU.2.2.1) (R.subgroupOf U) hRinv
    (((CFSG.primeSupported_singleton_iff_isPGroup q hq).mp hRq).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRU).symm)
  refine ⟨(Q : Subgroup U).map U.subtype, ⟨Q, rfl⟩, fun a => ?_, ?_⟩
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ a]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hRU]
    exact Subgroup.map_mono hRQ

omit [Finite A] in
private lemma exists_maxCompatible_le {T : Subgroup G} (hT : CompatibleAt p α θ {q} T) :
    ∃ S : Subgroup G, MaxCompatible p α θ {q} S ∧ T ≤ S := by
  obtain ⟨S, hTS, hmax⟩ := Finite.exists_le_maximal (p := CompatibleAt p α θ {q}) hT
  exact ⟨S, ⟨hmax.prop, fun K hK hSK => hmax.le_of_ge hK hSK⟩, hTS⟩

private theorem factorization_completionIn_normalizer_embeddedThompsonCenter
    (d : Datum p α θ) (hloc : LocallyComplete p α θ) (hq : q.Prime) (hq5 : 5 ≤ q)
    {W U T : Subgroup G} (hW : CompatibleAt p α θ {q} W) (hWne : W ≠ ⊥)
    (hU : U = completionIn θ (Subgroup.normalizer (W : Set G)))
    (hSylow : ∃ Q : Sylow q U, (Q : Subgroup U).map U.subtype = T)
    (hTinv : IsInvariant α T) :
    T ≠ ⊥ ∧ CompatibleAt p α θ {q} T ∧ embeddedThompsonCenter T ≠ ⊥ ∧
      CompatibleAt p α θ {q} (embeddedThompsonCenter T) ∧
      Compatible p α θ (completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G))) ∧
      (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G)) :
          Subgroup G) : Set G) ∧
      W ≤ completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G)) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQT⟩ := hSylow
  obtain ⟨hUcomp, hWU, hWnorm, -, -⟩ := compatible_completionIn_normalizer d hloc hW.1 hWne
  rw [← hU] at hUcomp hWU hWnorm
  have hWq : IsPGroup q W := (CFSG.primeSupported_singleton_iff_isPGroup q hq).mp hW.2
  have hqU : q ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hWq.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hWne ((Subgroup.eq_bot_iff_card W).mpr (by rwa [pow_zero] at hn))
    exact (show q ∣ Nat.card W by rw [hn]; exact dvd_pow_self q hn0).trans
      (Subgroup.card_dvd_of_le hWU)
  have hTne : T ≠ ⊥ := by
    intro hbot
    refine Sylow.ne_bot_of_dvd_card Q hqU
      ((Subgroup.map_eq_bot_iff_of_injective (H := (Q : Subgroup U)) U.subtype_injective).mp ?_)
    rw [hQT, hbot]
  have hTU : T ≤ U := hQT ▸ Subgroup.map_subtype_le _
  have hTCA : CompatibleAt p α θ {q} T :=
    ⟨Compatible.of_le_of_isInvariant d hUcomp hTU hTinv,
      (CFSG.primeSupported_singleton_iff_isPGroup q hq).mpr (hQT ▸ Q.isPGroup'.map U.subtype)⟩
  obtain ⟨hZne, hZCA⟩ := embeddedThompsonCenter_ne_bot_and_compatibleAt d hq hTCA hTne
  let NQ : Subgroup U := Subgroup.normalizer (embeddedThompsonCenter (Q : Subgroup U) : Set U)
  have hprodU : subgroupProduct (pPrimeCore q U) NQ = Set.univ :=
    solvable_zj_normalizer_factorization (p := q) (G := U) hq5 hUcomp.2.1 Q
  have hZQ :
      (embeddedThompsonCenter (Q : Subgroup U)).map U.subtype = embeddedThompsonCenter T := by
    rw [map_embeddedThompsonCenter_of_injective (Q : Subgroup U) U.subtype U.subtype_injective, hQT]
  have hZU : embeddedThompsonCenter T ≤ U := (Subgroup.map_subtype_le _).trans hTU
  have hcomap : (embeddedThompsonCenter T).comap U.subtype =
      embeddedThompsonCenter (Q : Subgroup U) := by
    rw [← hZQ]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  have hNQmap : NQ.map U.subtype = U ⊓ Subgroup.normalizer (embeddedThompsonCenter T : Set G) := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (f := U.subtype)
      (H := embeddedThompsonCenter T) (by simpa using hZU)
    rw [hcomap] at h
    rw [show NQ = (Subgroup.normalizer (embeddedThompsonCenter T : Set G)).subgroupOf U from
      h.symm, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hNL : U ⊓ Subgroup.normalizer (embeddedThompsonCenter T : Set G) =
      U ⊓ completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G)) := by
    refine le_antisymm (le_inf inf_le_left ?_)
      (inf_le_inf_left _ (completionIn_le θ _))
    have hNcomp := Compatible.of_le_of_isInvariant d hUcomp inf_le_left
      (hUcomp.1.inf (isInvariant_embeddedThompsonCenter hTinv).normalizer)
    rw [(eq_completionIn_and_le_completion d hNcomp).1]
    exact completionIn_mono θ inf_le_right
  have hprod := coe_eq_map_mul_map_of_subgroupProduct hprodU
  rw [hNQmap, hNL] at hprod
  have hsub : W.subgroupOf U ≤ NQ :=
    (pCore_le_of_coprime_normal_mul_eq_univ q hq (pPrimeCore q U) NQ pPrimeCore_coprime_card
      (by
        ext x
        exact ⟨fun _ => trivial, fun _ => by
          change x ∈ subgroupProduct (pPrimeCore q U) NQ
          rw [hprodU]; trivial⟩)).1
      (W.subgroupOf U) hWnorm (hWq.of_equiv (Subgroup.subgroupOfEquivOfLe hWU).symm)
  have hWL : W ≤ completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G)) := by
    have h1 : W ≤ NQ.map U.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hWU]
      exact Subgroup.map_mono hsub
    rw [hNQmap] at h1
    rw [(eq_completionIn_and_le_completion d hW.1).1]
    exact completionIn_mono θ (h1.trans inf_le_right)
  exact ⟨hTne, hTCA, hZne, hZCA, hloc.1 _ hZCA.1 hZne, hprod, hWL⟩

private theorem exists_isInvariant_card_lt (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) (hq : q.Prime) {T S : Subgroup G}
    (hT : CompatibleAt p α θ {q} T) (hS : CompatibleAt p α θ {q} S) (hTne : T ≠ ⊥)
    (hTS : T < S) :
    ∃ R : Subgroup G, IsInvariant α R ∧ primeSupported {q} (Nat.card R) ∧
      R ≤ completionIn θ (Subgroup.normalizer (embeddedThompsonCenter T : Set G)) ∧
      Nat.card T < Nat.card R := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hZne, hZ⟩ := embeddedThompsonCenter_ne_bot_and_compatibleAt d hq hT hTne
  have := (thompsonOrder_isomorphism (MulEquiv.refl T)).2.2.2.2.2
  have hNTZ : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (embeddedThompsonCenter T : Set G) :=
    SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic T (centerThompsonOrder T)
  let R : Subgroup G := S ⊓ Subgroup.normalizer (T : Set G)
  have hRinv : IsInvariant α R := hS.1.1.inf hT.1.1.normalizer
  have hTR : T < R := by
    have hU : T.subgroupOf S < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hTS.2 (Subgroup.subgroupOf_eq_top.mp h)
    have h1 := (Subgroup.map_subtype_lt_map_subtype (G' := S)).mpr
      (lt_normalizer_of_isPGroup q S ((CFSG.primeSupported_singleton_iff_isPGroup q hq).mp hS.2)
        (T.subgroupOf S) hU)
    rwa [Subgroup.map_subgroupOf_eq_of_le hTS.1,
      SignalizerFunctor.Helpers.normalizer_subgroupOf_map S T hTS.1] at h1
  refine ⟨R, hRinv, fun r hr hd => hS.2 r hr (hd.trans (Subgroup.card_dvd_of_le inf_le_left)),
    ?_, Subgroup.card_lt_of_lt hTR⟩
  exact (compatible_completionIn_normalizer d hloc hZ.1 hZne).2.2.2.1 R
    (Compatible.of_le_of_isInvariant d hS.1 inf_le_left hRinv) (inf_le_right.trans hNTZ)

private theorem normalizer_control_of_maxCompatible (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) (hA : p ^ 3 ≤ Nat.card A) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hqθ : q ∈ spectrum θ) {S : Subgroup G} (hS : MaxCompatible p α θ {q} S) (hSne : S ≠ ⊥) :
    let M : Subgroup G := completionIn θ (Subgroup.normalizer (embeddedThompsonCenter S : Set G))
    Compatible p α θ M ∧
      ∀ W : Subgroup G, CompatibleAt p α θ {q} W → W ≠ ⊥ →
        ∃ c : G, c ∈ commonSignalizerWhole θ ∧
          let U := completionIn θ (Subgroup.normalizer (W : Set G))
          (U : Set G) = (factorizationComplementCore q U : Set G) *
            ((U ⊓ conjugate M c : Subgroup G) : Set G) := by
  classical
  intro M
  obtain ⟨hZSne, hZS⟩ := embeddedThompsonCenter_ne_bot_and_compatibleAt d hq hS.1 hSne
  have hM : Compatible p α θ M := hloc.1 _ hZS.1 hZSne
  refine ⟨hM, ?_⟩
  let Uof := fun W : Subgroup G => completionIn θ (Subgroup.normalizer (W : Set G))
  let control := fun W : Subgroup G => ∃ c : G, c ∈ commonSignalizerWhole θ ∧
    (Uof W : Set G) = (factorizationComplementCore q (Uof W) : Set G) *
      ((Uof W ⊓ conjugate M c : Subgroup G) : Set G)
  change ∀ W, CompatibleAt p α θ {q} W → W ≠ ⊥ → control W
  by_contra hfail
  push Not at hfail
  obtain ⟨W₀, hW₀, hW₀ne, hW₀bad⟩ := hfail
  obtain ⟨T₀, hT₀syl, hT₀inv, -⟩ := exists_sylow_isInvariant_le_of_compatible d hq
    (hloc.1 W₀ hW₀.1 hW₀ne) (fun a => by simp) (fun r hr hd => by simp [hr.not_dvd_one] at hd)
    bot_le
  let bad := fun v : Subgroup G × Subgroup G =>
    CompatibleAt p α θ {q} v.1 ∧ v.1 ≠ ⊥ ∧
    (∃ Q : Sylow q (Uof v.1), (Q : Subgroup (Uof v.1)).map (Uof v.1).subtype = v.2) ∧
    IsInvariant α v.2 ∧ ¬ control v.1
  have : Nonempty {v // bad v} := ⟨⟨(W₀, T₀), hW₀, hW₀ne, hT₀syl, hT₀inv, hW₀bad⟩⟩
  obtain ⟨⟨⟨W, T⟩, hW, hWne, hTsyl, hTinv, hbad⟩, hvmax⟩ :=
    Finite.exists_max (fun v : {v // bad v} => Nat.card v.val.2)
  set L := Uof (embeddedThompsonCenter T)
  obtain ⟨hTne, hT, hZne, hZ, hL, hUL, hWL⟩ :=
    factorization_completionIn_normalizer_embeddedThompsonCenter d hloc hq hq5 hW hWne rfl
      hTsyl hTinv
  obtain ⟨S', hS', hTS'⟩ := exists_maxCompatible_le hT
  by_cases heq : T = S'
  ·
    obtain ⟨c, hc, hST⟩ := exists_conj_eq_of_maxCompatible d hA hqθ hS (heq ▸ hS')
    have hML : conjugate M c = L := by
      rw [conjugate_completionIn_normalizer d hS.1.1.1 hc]
      exact congrArg (fun X => Uof (embeddedThompsonCenter X)) hST
    exact hbad ⟨c, hc, by rw [hML]; exact hUL⟩
  ·
    obtain ⟨R, hRinv, hRq, hRL, hTR⟩ :=
      exists_isInvariant_card_lt d hloc hq hT hS'.1 hTne (lt_of_le_of_ne hTS' heq)
    obtain ⟨T', hT'syl, hT'inv, hRT'⟩ :=
      exists_sylow_isInvariant_le_of_compatible d hq hL hRinv hRq hRL
    have hcontrolZ : control (embeddedThompsonCenter T) := by
      by_contra hZbad
      exact (not_le_of_gt (hTR.trans_le (Subgroup.card_le_of_le hRT')))
        (hvmax ⟨(_, T'), hZ, hZne, hT'syl, hT'inv, hZbad⟩)
    obtain ⟨c, hc, hLc⟩ := hcontrolZ
    obtain ⟨b, hb, hUb⟩ := exists_conj_factorization_completionIn d hloc hqθ
      (conjugate M c) L W (((map_conj_of_mem_commonSignalizerWhole d hc).2.1 M).mpr hM)
      hL hW hWne hWL
      (by simpa only [inf_comm] using hLc) hUL
    refine hbad ⟨c * b, (commonSignalizerWhole θ).mul_mem hc hb.1, ?_⟩
    simpa only [conjugate_conjugate] using hUb

private theorem isComplete_of_spectrum_ne (d : Datum p α θ)
    (hA : p ^ 3 ≤ Nat.card A) (hloc : LocallyComplete p α θ)
    (hπ : spectrum θ ≠ ({2, 3} : Set ℕ)) : IsComplete p α θ := by
  classical
  by_cases hsmall : (spectrum θ).ncard ≤ 1
  · exact isComplete_of_ncard_spectrum_le_one d hA hsmall
  obtain ⟨q, hqθ, hq5⟩ : ∃ q ∈ spectrum θ, 5 ≤ q := by
    by_contra hcon
    push Not at hcon
    have hsub : spectrum θ ⊆ ({2, 3} : Set ℕ) := by
      intro q hq
      have hprime : q.Prime := hq.1
      have hlt5 : q < 5 := hcon q hq
      interval_cases q <;> simp_all <;> norm_num at hprime
    refine hπ (Set.eq_of_subset_of_ncard_le hsub ?_)
    rw [show ({2, 3} : Set ℕ).ncard = 2 by norm_num]
    omega
  obtain ⟨W, hW, hWne⟩ := exists_compatibleAt_singleton_ne_bot d hqθ
  obtain ⟨S, hSmax, hWS⟩ := exists_maxCompatible_le hW
  have hSne : S ≠ ⊥ := fun h => hWne (le_bot_iff.mp (h ▸ hWS))
  obtain ⟨hM, hcontrol⟩ :=
    normalizer_control_of_maxCompatible d hloc hA hqθ.1 hq5 hqθ hSmax hSne
  exact isComplete_of_normalizer_factorization d hloc hA hqθ hM hcontrol

theorem isComplete_of_locallyComplete_of_two {A G : Type*} [CommGroup A] [Finite A]
    [Group G] [Finite G] (α : A →* MulAut G) (θ : A → Subgroup G)
    (d : Datum 2 α θ) (hA : 8 ≤ Nat.card A)
    (hloc : LocallyComplete 2 α θ) : IsComplete 2 α θ :=
  isComplete_of_spectrum_ne d hA hloc fun hπ => d.notMem_spectrum (by simp [hπ])

end CFSG.SolvableSignalizer
