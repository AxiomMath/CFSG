module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Adapter
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.PrimeSubfunctor
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerLocalValueFactorization

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise
open Internal CFSG.SignalizerFunctor

@[expose]
def twoStageCore (q : ℕ) (H : Type*) [Group H] : Subgroup H :=
  Subgroup.comap (QuotientGroup.mk' (pPrimeCore q H))
    (pCore q (H ⧸ pPrimeCore q H))

theorem pCore_ne_bot_and_twoStageCore_sylow_ne_bot (q : ℕ) (H : Type*) [Group H] [Finite H]
    (hq : q.Prime) (hsolv : Group.IsSolvable H) (hqH : q ∣ Nat.card H) :
    pCore q (H ⧸ pPrimeCore q H) ≠ ⊥ ∧
      ∀ Q : Sylow q (twoStageCore q H), (Q : Subgroup (twoStageCore q H)) ≠ ⊥ := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set R := pPrimeCore q H
  have : Group.IsSolvable (H ⧸ R) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective R)
  have hqG : q ∣ Nat.card (H ⧸ R) := by
    rw [← Subgroup.card_mul_index R, Subgroup.index_eq_card] at hqH
    exact ((pPrimeCore_coprime_card (p := q) (G := H)).dvd_mul_left).mp hqH
  have hpcore : pCore q (H ⧸ R) ≠ ⊥ := by
    intro hbot
    have hfit : fittingSubgroup (H ⧸ R) = ⊥ := by
      rw [Fitting_eq_pcore (H ⧸ R) q
        (pPrimeCore_quotient_eq_bot hq)]
      exact hbot
    have hcard1 : Nat.card (H ⧸ R) = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable (H ⧸ R)).mp hfit
    exact hq.not_dvd_one (hcard1 ▸ hqG)
  refine ⟨hpcore, fun Q => Sylow.ne_bot_of_dvd_card Q ?_⟩
  have hNq : q ∣ Nat.card (pCore q (H ⧸ R)) := by
    rcases (pCore_isPGroup (p := q) (G := H ⧸ R)).card_eq_or_dvd with h1 | h
    · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h1) hpcore
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pCore q (H ⧸ R)) q hNq
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective R (x : H ⧸ R)
  have hyX : y ∈ twoStageCore q H := by
    change QuotientGroup.mk' R y ∈ pCore q (H ⧸ R)
    rw [hy]
    exact x.2
  have hdivq : q ∣ orderOf y := by
    have h := orderOf_map_dvd (QuotientGroup.mk' R) y
    rwa [hy, Subgroup.orderOf_coe, hx] at h
  exact hdivq.trans (Subgroup.orderOf_dvd_natCard (twoStageCore q H) hyX)

private theorem map_twoStageCore {H J : Type*} [Group H] [Group J] [Finite H] [Finite J]
    (q : ℕ) (e : H ≃* J) :
    (twoStageCore q H).map e.toMonoidHom = twoStageCore q J := by
  let C := pPrimeCore q H
  let C' := pPrimeCore q J
  have hC : C.map e.toMonoidHom = C' := pPrimeCore_map_iso q e
  let eQ := QuotientGroup.congr C C' e hC
  have hQ : (pCore q (H ⧸ C)).map eQ.toMonoidHom =
      pCore q (J ⧸ C') := pCore_map_iso q eQ
  ext j
  constructor
  · rintro ⟨h, hh, rfl⟩
    change QuotientGroup.mk' C' (e h) ∈ pCore q (J ⧸ C')
    rw [← hQ]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' C h, hh, QuotientGroup.congr_mk C C' e hC h⟩
  · intro hj
    refine Subgroup.mem_map.mpr ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    change QuotientGroup.mk' C (e.symm j) ∈ pCore q (H ⧸ C)
    change QuotientGroup.mk' C' j ∈ pCore q (J ⧸ C') at hj
    rw [← hQ] at hj
    obtain ⟨x, hx, hxe⟩ := hj
    have heq : eQ x = eQ (QuotientGroup.mk' C (e.symm j)) := by
      change eQ x = QuotientGroup.congr C C' e hC (QuotientGroup.mk (e.symm j))
      rw [QuotientGroup.congr_mk C C' e hC]
      exact hxe.trans (congrArg (QuotientGroup.mk' C') (e.apply_symm_apply j)).symm
    exact eQ.injective heq ▸ hx

section

variable {A G : Type*} [CommGroup A] [Group G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G} {M Q₀ : Subgroup G}

private theorem le_normalizer_iSup_of_le {ι : Sort*} {X : Subgroup G} {H : ι → Subgroup G}
    (h : ∀ i, X ≤ Subgroup.normalizer (H i)) :
    X ≤ Subgroup.normalizer ((⨆ i, H i : Subgroup G) : Set G) :=
  (le_iInf h).trans (Subgroup.iInf_normalizer_le_normalizer_iSup H)

private theorem eq_sup_of_coe_eq_mul {N H K : Subgroup G}
    (h : (N : Set G) = (H : Set G) * (K : Set G)) : N = H ⊔ K := by
  apply le_antisymm
  · intro x hx
    rw [← SetLike.mem_coe, h] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [← SetLike.mem_coe, h]
      exact ⟨x, hx, 1, K.one_mem, mul_one x⟩
    · rw [← SetLike.mem_coe, h]
      exact ⟨1, H.one_mem, x, hx, one_mul x⟩

@[expose]
def factorizationComplementCore (q : ℕ) (H : Subgroup G) : Subgroup G :=
  (pPrimeCore q H).map H.subtype

private theorem le_normalizer_factorizationComplementCore (q : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (factorizationComplementCore q H : Set G) := by
  have hmap := Subgroup.le_normalizer_map (H := pPrimeCore q H) H.subtype
  rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap

def factorizationQ (Q₀ : Subgroup G) : Subgroup G :=
  (Subgroup.center Q₀).map Q₀.subtype

@[expose]
def factorizationL (θ : A → Subgroup G) (Q₀ : Subgroup G) : Subgroup G :=
  completionIn θ (Subgroup.normalizer (factorizationQ Q₀ : Set G))

@[expose]
def factorizationK (α : A →* MulAut G) (θ : A → Subgroup G) (q : ℕ) :
    Subgroup G :=
  completion (primeSubfunctor α θ (spectrum θ \ {q}))

@[expose]
def factorizationG₀ (α : A →* MulAut G) (θ : A → Subgroup G)
    (q : ℕ) (Q₀ : Subgroup G) : Subgroup G :=
  factorizationK α θ q ⊔ factorizationQ Q₀

@[expose]
def factorizationD (α : A →* MulAut G) (θ : A → Subgroup G)
    (q : ℕ) (Q₀ : Subgroup G) : Subgroup G :=
  ⨆ g : factorizationG₀ α θ q Q₀, conjugate (factorizationQ Q₀) (g : G)

@[expose]
def factorizationHyperplanes (p : ℕ) : Set (Subgroup A) :=
  {B | B.index = p}

@[expose]
def factorizationHyperplaneCore (θ : A → Subgroup G) (q : ℕ)
    (B : Subgroup A) : Subgroup G :=
  ⨆ (a : A) (_ : a ∈ B) (_ : a ≠ 1), factorizationComplementCore q (θ a)

end

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G} {M Q₀ : Subgroup G}

structure FactorizationDatum (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (q : ℕ) (M Q₀ : Subgroup G) : Prop where
  solvable : Datum p α θ
  locally_complete : LocallyComplete p α θ
  rank_three : p ^ 3 ≤ Nat.card A
  selected_prime : q ∈ spectrum θ
  compatible_M : Compatible p α θ M
  sylow_Q₀ : ∃ S : Sylow q (twoStageCore q M),
    Q₀ = ((S : Subgroup (twoStageCore q M)).map (twoStageCore q M).subtype).map M.subtype
  nontrivial_Q₀ : Q₀ ≠ ⊥
  invariant_Q₀ : IsInvariant α Q₀
  normalizer_control :
    ∀ W : Subgroup G, CompatibleAt p α θ {q} W → W ≠ ⊥ →
      ∃ c : G, c ∈ commonSignalizerWhole θ ∧
        let U := completionIn θ (Subgroup.normalizer (W : Set G))
        (U : Set G) = (factorizationComplementCore q U : Set G) *
          ((U ⊓ conjugate M c : Subgroup G) : Set G)

theorem FactorizationDatum.basic_subgroups (f : FactorizationDatum p α θ q M Q₀) :
    factorizationQ Q₀ ≠ ⊥ ∧ IsMulCommutative (factorizationQ Q₀) ∧
      CompatibleAt p α θ {q} (factorizationQ Q₀) ∧
      Compatible p α θ (factorizationL θ Q₀) ∧
      CompatibleAt p α θ (spectrum θ \ {q}) (factorizationK α θ q) ∧
      commonSignalizerWhole θ ≤ Subgroup.normalizer (factorizationK α θ q : Set G) ∧
      ∀ a : A, a ≠ 1 → factorizationComplementCore q (θ a) ≤ factorizationK α θ q := by
  have hq : q ∈ spectrum θ := f.selected_prime
  have : Fact q.Prime := ⟨hq.1⟩
  obtain ⟨S, hS⟩ := f.sylow_Q₀
  have hQ₀pg : IsPGroup q Q₀ := by
    rw [hS]
    exact (S.isPGroup'.map (twoStageCore q M).subtype).map M.subtype
  have : Nontrivial Q₀ := (Subgroup.nontrivial_iff_ne_bot Q₀).mpr f.nontrivial_Q₀
  have hQne : factorizationQ Q₀ ≠ ⊥ := fun h => hQ₀pg.bot_lt_center.ne'
    ((Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center Q₀)
      Q₀.subtype_injective).mp h)
  have hQ₀leM : Q₀ ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hQcomp : Compatible p α θ (factorizationQ Q₀) :=
    Compatible.of_le_of_isInvariant f.solvable f.compatible_M
      ((Subgroup.map_subtype_le (Subgroup.center Q₀)).trans hQ₀leM)
      (f.invariant_Q₀.map_subtype_of_characteristic Subgroup.centerCharacteristic)
  have hQsupp : primeSupported {q} (Nat.card (factorizationQ Q₀)) := by
    have hQpg : IsPGroup q (factorizationQ Q₀) :=
      (hQ₀pg.to_subgroup (Subgroup.center Q₀)).map Q₀.subtype
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    intro r hr hd
    rw [hn] at hd
    exact (Nat.prime_dvd_prime_iff_eq hr hq.1).mp (hr.dvd_of_dvd_pow hd)
  obtain ⟨hKcompAt, hKnorm, _, hKcore⟩ :=
    LocallyComplete.completion_primeSubfunctor_spec f.solvable f.locally_complete q hq
  exact ⟨hQne, Subgroup.map_isMulCommutative (Subgroup.center Q₀) Q₀.subtype,
    ⟨hQcomp, hQsupp⟩, f.locally_complete.1 _ hQcomp hQne, hKcompAt, hKnorm, hKcore⟩

theorem FactorizationDatum.hyperplaneCore_spec (f : FactorizationDatum p α θ q M Q₀)
    (B : Subgroup A) (_hB : B ∈ factorizationHyperplanes p) :
    factorizationHyperplaneCore θ q B ≤ factorizationK α θ q ∧
      IsInvariant α (factorizationHyperplaneCore θ q B) ∧
      commonSignalizer θ B ≤ Subgroup.normalizer (factorizationHyperplaneCore θ q B : Set G) ∧
      fixedInBySubgroup α (factorizationQ Q₀) B ≤
        Subgroup.normalizer (factorizationHyperplaneCore θ q B : Set G) := by
  obtain ⟨-, -, ⟨hQcompat, -⟩, -, -, -, hleK⟩ := FactorizationDatum.basic_subgroups f
  have hinv : ∀ a : A, a ≠ 1 → IsInvariant α (factorizationComplementCore q (θ a)) :=
    fun a ha => (f.solvable.invariant a ha).map_subtype_of_characteristic inferInstance
  have h3 : commonSignalizer θ B ≤
      Subgroup.normalizer (factorizationHyperplaneCore θ q B : Set G) :=
    le_normalizer_iSup_of_le fun a => le_normalizer_iSup_of_le fun ha =>
      le_normalizer_iSup_of_le fun ha1 =>
        (iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le ha1 le_rfl))).trans
          (le_normalizer_factorizationComplementCore q (θ a))
  have hsub : fixedInBySubgroup α (factorizationQ Q₀) B ≤ commonSignalizer θ B := by
    intro g hg
    rw [mem_fixedInBySubgroup] at hg
    simp only [commonSignalizer, Subgroup.mem_iInf]
    exact fun b hb hb1 => hQcompat.2.2.2 b hb1 ⟨hg.1, hg.2 b hb⟩
  exact ⟨iSup_le fun a => iSup_le fun _ => iSup_le fun ha => hleK a ha,
    IsInvariant.iSup fun a => IsInvariant.iSup fun _ => IsInvariant.iSup fun ha => hinv a ha,
    h3, hsub.trans h3⟩

private theorem pow_le_card_actor (d : Datum p α θ) :
    p ^ (1 + 1) ≤ Nat.card (actor α) := by
  rw [card_actor]
  exact d.rank_two

omit [Finite A] [Finite G] in
private theorem lift_sup (H K : Subgroup G) : lift α (H ⊔ K) = lift α H ⊔ lift α K :=
  Subgroup.map_sup H K (embed α)

private theorem lift_factorizationComplementCore (hq : q.Prime) (H : Subgroup G) :
    lift α (factorizationComplementCore q H) =
      (Helpers.primeSetCore (GroupType := lift α H) ({q}ᶜ)).map (lift α H).subtype := by
  rw [factorizationComplementCore, pPrimeCore_eq_helpersPrimeSetCore hq]
  have hm := congrArg (Subgroup.map (lift α H).subtype)
    (Helpers.prime_set_core_map_isomorphism ({q}ᶜ) (liftEquiv α H))
  rw [Subgroup.map_map] at hm
  change Subgroup.map (embed α) (Subgroup.map H.subtype _) = _
  rw [Subgroup.map_map]
  convert hm using 1
  congr 1

omit [Finite A] [Finite G] in
private theorem lift_conjugate (H : Subgroup G) (c : G) :
    lift α (conjugate H c) = Helpers.conjugateSubgroup (embed α c⁻¹) (lift α H) :=
  Helpers.conjugate_subgroup_map (embed α) c⁻¹ H

omit [Finite A] [Finite G] in
private theorem lift_factorizationQ (Q₀ : Subgroup G) :
    lift α (factorizationQ Q₀) = factorizationQ (lift α Q₀) :=
  Helpers.subgroup_center_map_injective (embed α) (embed_injective α) Q₀

private theorem lift_factorizationL (d : Datum p α θ) (Q₀ : Subgroup G) :
    lift α (factorizationL θ Q₀) =
      Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ)
        (factorizationQ (lift α Q₀)) := by
  rw [factorizationL, ← lift_factorizationQ, Helpers.signalizerNormalizerCompletion,
    iSup_signalizerRestriction_values d]

private theorem helpers_twoStageCore_eq {H : Type*} [Group H] [Finite H]
    (q : ℕ) (hq : q.Prime) :
    Helpers.twoStageCore (GroupType := H) q = twoStageCore q H := by
  have hc : Helpers.primeSetCore (GroupType := H) ({q}ᶜ) = pPrimeCore q H :=
    (pPrimeCore_eq_helpersPrimeSetCore hq).symm
  have hp : Helpers.primeSetCore (GroupType := H ⧸ pPrimeCore q H) {q} =
      pCore q (H ⧸ pPrimeCore q H) :=
    (pCore_eq_helpersPrimeSetCore hq).symm
  let t : {C : Subgroup H // C.Normal} → Subgroup H := fun C =>
    have : C.val.Normal := C.property
    (Helpers.primeSetCore (GroupType := H ⧸ C.val) {q}).comap (QuotientGroup.mk' C.val)
  have hbundled : (⟨Helpers.primeSetCore ({q}ᶜ), Helpers.prime_set_core_normal ({q}ᶜ)⟩ :
      {C : Subgroup H // C.Normal}) = ⟨pPrimeCore q H, inferInstance⟩ :=
    Subtype.ext hc
  exact (congrArg t hbundled).trans
    (congrArg (Subgroup.comap (QuotientGroup.mk' (pPrimeCore q H))) hp)

private theorem exists_helpers_sylow (f : FactorizationDatum p α θ q M Q₀) :
    ∃ P : Sylow q ((Helpers.twoStageCore (GroupType := lift α M) q).map (lift α M).subtype),
      (P : Subgroup ((Helpers.twoStageCore (GroupType := lift α M) q).map
        (lift α M).subtype)).map
          ((Helpers.twoStageCore (GroupType := lift α M) q).map
            (lift α M).subtype).subtype = lift α Q₀ ∧
      actor α ≤ Subgroup.normalizer (lift α Q₀ : Set (Ambient α)) ∧ lift α Q₀ ≠ ⊥ := by
  obtain ⟨S, hS⟩ := f.sylow_Q₀
  have : Fact q.Prime := ⟨f.selected_prime.1⟩
  let eM := liftEquiv α M
  let C := Helpers.twoStageCore (GroupType := lift α M) q
  have hC : (twoStageCore q M).map eM.toMonoidHom = C :=
    (map_twoStageCore q eM).trans (helpers_twoStageCore_eq q f.selected_prime.1).symm
  let eC : twoStageCore q M ≃* C :=
    ((twoStageCore q M).equivMapOfInjective eM.toMonoidHom eM.injective).trans
      (MulEquiv.subgroupCongr hC)
  let e : twoStageCore q M ≃* C.map (lift α M).subtype :=
    eC.trans (C.equivMapOfInjective (lift α M).subtype (lift α M).subtype_injective)
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨P, ?_, (isInvariant_iff_actor_le_normalizer α Q₀).mp f.invariant_Q₀, ?_⟩
  · rw [hS]
    change (P : Subgroup (C.map (lift α M).subtype)).map _ =
      (((S : Subgroup (twoStageCore q M)).map _).map _).map (embed α)
    dsimp only [P]
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S,
      Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
  · intro hb
    apply f.nontrivial_Q₀
    apply lift_injective α
    simpa only [lift, Subgroup.map_bot] using hb

private theorem helpers_normalizerFactorization (f : FactorizationDatum p α θ q M Q₀) :
    Helpers.signalizerNormalizerFactorization p 1 q (actor α) (values α θ) (lift α M) := by
  intro T hTne hT hTq
  obtain ⟨hW, heq⟩ := compatible_lower f.solvable T hT
  let W := lower α T
  have hWne : W ≠ ⊥ := by
    intro hb
    apply hTne
    rw [← heq]
    change lift α W = ⊥
    rw [hb]
    exact Subgroup.map_bot _
  have hWq : IsPGroup q W := by
    have hTq' : IsPGroup q (lift α W) := heq.symm ▸ hTq
    simpa only [heq] using
      hTq'.of_injective (liftEquiv α W).toMonoidHom (liftEquiv α W).injective
  have hWAt : CompatibleAt p α θ {q} W :=
    ⟨hW, (primeSupported_singleton_iff_isPGroup q f.selected_prime.1).mpr hWq⟩
  obtain ⟨c, hc, hprod⟩ := f.normalizer_control W hWAt hWne
  refine ⟨⟨embed α c⁻¹, ?_⟩, ?_⟩
  · rw [signalizerCommonFixed_values f.solvable]
    exact Subgroup.mem_map.mpr ⟨c⁻¹, (commonSignalizerWhole θ).inv_mem hc, rfl⟩
  · change Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ) T = _
    unfold Helpers.signalizerNormalizerCompletion
    rw [← heq, iSup_signalizerRestriction_values f.solvable]
    have hm := congrArg (lift α) (eq_sup_of_coe_eq_mul hprod)
    rw [lift_sup, lift_factorizationComplementCore f.selected_prime.1, lift_inf,
      lift_conjugate] at hm
    exact hm

private theorem theta_factorization_transfer_aux
    (d : Datum p α θ) (hloc : LocallyComplete p α θ) (hq : q ∈ spectrum θ)
    (L M W U : Subgroup G) (hL : Compatible p α θ L) (hM : Compatible p α θ M)
    (hW : CompatibleAt p α θ {q} W) (hne : W ≠ ⊥) (hWM : W ≤ M)
    (hU : U = completionIn θ (Subgroup.normalizer (W : Set G)))
    (hfactorM : (M : Set G) = (factorizationComplementCore q M : Set G) *
      ((L ⊓ M : Subgroup G) : Set G))
    (hfactorU : (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ M : Subgroup G) : Set G)) :
    ∃ c : G, c ∈ commonSignalizerWhole θ ⊓ M ∧
      (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ conjugate L c : Subgroup G) : Set G) := by
  have hWne : lift α W ≠ ⊥ := fun h =>
    hne (lift_injective α (h.trans (Subgroup.map_bot (embed α)).symm))
  have hWpg : IsPGroup q (lift α W) :=
    (Helpers.prime_supported_singleton_iff_pgroup q hq.1 (lift α W)).mp
      (by rw [card_lift]; exact hW.2)
  have hMfac : lift α M =
      (Helpers.primeSetCore (GroupType := lift α M) ({q}ᶜ)).map (lift α M).subtype ⊔
        (lift α L ⊓ lift α M) := by
    conv_lhs => rw [eq_sup_of_coe_eq_mul hfactorM]
    rw [lift_sup, lift_inf, lift_factorizationComplementCore hq.1]
  have hCU : Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ) (lift α W) =
      lift α U := by
    rw [hU]
    exact iSup_signalizerRestriction_values d W
  have hUfac : Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ) (lift α W) =
      (Helpers.primeSetCore (GroupType :=
          Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ) (lift α W))
          ({q}ᶜ)).map
        (Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ)
          (lift α W)).subtype ⊔
      (Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ) (lift α W) ⊓
        lift α M) := by
    rw [hCU]
    conv_lhs => rw [eq_sup_of_coe_eq_mul hfactorU]
    rw [lift_sup, lift_inf, lift_factorizationComplementCore hq.1]
  obtain ⟨x, hxM, hconcl⟩ :=
    Helpers.signalizer_normalizer_factorization_transfer
      p 1 q d.prime hq.1 (actor α) (lift α L) (lift α M) (lift α W)
      (isElemAbelian_actor d) (pow_le_card_actor d) (values α θ)
      (solvableSignalizerConditions_values d) ((locallyComplete_iff d).mp hloc)
      ((compatible_iff_lift d L).mp hL)
      ((compatible_iff_lift d M).mp hM) ((compatible_iff_lift d W).mp hW.1) hWne hWpg
      (Subgroup.map_mono hWM) hMfac hUfac
  obtain ⟨m, hmM, hme⟩ := Subgroup.mem_map.mp (show x.val ∈ M.map (embed α) from hxM)
  have hmcommon : m ∈ commonSignalizerWhole θ := by
    have hx : x.val ∈ lift α (commonSignalizerWhole θ) := by
      rw [← signalizerCommonFixed_values d]
      exact x.2
    exact (mem_lift α (commonSignalizerWhole θ) m).mp (hme ▸ hx)
  have hconj : Helpers.conjugateSubgroup (embed α m) (lift α L) =
      lift α (conjugate L m⁻¹) := by
    rw [lift_conjugate, inv_inv]
  refine ⟨m⁻¹, ⟨Subgroup.inv_mem _ hmcommon, Subgroup.inv_mem _ hmM⟩, ?_⟩
  rw [hCU, ← hme, hconj, ← lift_inf, ← lift_factorizationComplementCore hq.1, ← lift_sup]
    at hconcl
  refine (congrArg (fun H : Subgroup G => (H : Set G)) (lift_injective α hconcl)).trans ?_
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (inf_le_left.trans (le_normalizer_factorizationComplementCore q U))

theorem exists_conj_factorization_completionIn (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) (hq : q ∈ spectrum θ)
    (L M W : Subgroup G) (hL : Compatible p α θ L) (hM : Compatible p α θ M)
    (hW : CompatibleAt p α θ {q} W) (hne : W ≠ ⊥) (hWM : W ≤ M)
    (hfactorM : (M : Set G) = (factorizationComplementCore q M : Set G) *
      ((L ⊓ M : Subgroup G) : Set G))
    (hfactorU :
      let U := completionIn θ (Subgroup.normalizer (W : Set G))
      (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ M : Subgroup G) : Set G)) :
    ∃ c : G, c ∈ commonSignalizerWhole θ ⊓ M ∧
      let U := completionIn θ (Subgroup.normalizer (W : Set G))
      (U : Set G) = (factorizationComplementCore q U : Set G) *
        ((U ⊓ conjugate L c : Subgroup G) : Set G) :=
  theta_factorization_transfer_aux d hloc hq L M W
    (completionIn θ (Subgroup.normalizer (W : Set G))) hL hM hW hne hWM rfl hfactorM hfactorU

private theorem factorization_M_normalizer (f : FactorizationDatum p α θ q M Q₀) :
    (M : Set G) = (factorizationComplementCore q M : Set G) *
        ((M ⊓ factorizationL θ Q₀ : Subgroup G) : Set G) ∧
      ∀ a : A, a ≠ 1 →
        ((M ⊓ θ a : Subgroup G) : Set G) =
          ((factorizationComplementCore q M ⊓ θ a : Subgroup G) : Set G) *
          ((M ⊓ factorizationL θ Q₀ ⊓ θ a : Subgroup G) : Set G) := by
  classical
  have hq : q.Prime := f.selected_prime.1
  obtain ⟨P, hPimage, hPnorm, hPne⟩ := exists_helpers_sylow f
  obtain ⟨hmain, hsecond⟩ :=
    Helpers.signalizer_model_center_factorization p 1 q f.solvable.prime hq
      (actor α) (lift α M) (isElemAbelian_actor f.solvable) (pow_le_card_actor f.solvable)
      (values α θ) (solvableSignalizerConditions_values f.solvable)
      ((compatible_iff_lift f.solvable M).mp f.compatible_M)
      ((locallyComplete_iff f.solvable).mp f.locally_complete) P
      (by rw [hPimage]; exact hPnorm) (by rw [hPimage]; exact hPne)
  have hcore : (Helpers.primeSetCore (GroupType := lift α M) ({q}ᶜ)).map (lift α M).subtype =
      lift α (factorizationComplementCore q M) :=
    (lift_factorizationComplementCore hq M).symm
  have hLC : Helpers.signalizerNormalizerCompletion p 1 (actor α) (values α θ)
      (factorizationQ (lift α Q₀)) = lift α (factorizationL θ Q₀) :=
    (lift_factorizationL f.solvable Q₀).symm
  simp only [factorizationQ] at hmain hLC
  have hRnorm : M ≤ Subgroup.normalizer (factorizationComplementCore q M : Set G) :=
    le_normalizer_factorizationComplementCore q M
  refine ⟨?_, fun a ha => ?_⟩
  · rw [hPimage, hLC, hcore, ← lift_inf, ← lift_sup] at hmain
    rw [inf_comm M, ← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans hRnorm), ← lift_injective α hmain]
  · have hmem : cyclicActor α a ∈ Open.signalizerFunctorEk p 1 (actor α) :=
      ⟨cyclicActor_le α a, by simpa using card_cyclicActor f.solvable ha⟩
    have h2 := hsecond (cyclicActor α a) hmem
    rw [values_cyclicActor f.solvable ha, hPimage, hLC, hcore] at h2
    simp only [← lift_inf] at h2
    rw [← lift_sup] at h2
    have hN : factorizationL θ Q₀ ⊓ M ⊓ θ a ≤
        Subgroup.normalizer ((factorizationComplementCore q M ⊓ θ a : Subgroup G) : Set G) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hRnorm hx.1.2, Subgroup.le_normalizer hx.2⟩
    rw [lift_injective α h2, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN, inf_comm M]

theorem FactorizationDatum.coe_value_eq_mul (f : FactorizationDatum p α θ q M Q₀)
    (a : A) (ha : a ≠ 1) :
    (θ a : Set G) = (factorizationComplementCore q (θ a) : Set G) *
      ((θ a ⊓ factorizationL θ Q₀ : Subgroup G) : Set G) := by
  classical
  have hq : q.Prime := f.selected_prime.1
  have d : Datum p α θ := f.solvable
  have hmember : cyclicActor α a ∈ Open.signalizerFunctorEk p 1 (actor α) :=
    ⟨cyclicActor_le α a, by rw [pow_one]; exact card_cyclicActor d ha⟩
  have hMfac : lift α M =
      (Helpers.primeSetCore (GroupType := lift α M) ({q}ᶜ)).map
        (lift α M).subtype ⊔ (lift α (factorizationL θ Q₀) ⊓ lift α M) := by
    conv_lhs => rw [eq_sup_of_coe_eq_mul (factorization_M_normalizer f).1]
    rw [lift_sup, lift_factorizationComplementCore hq, lift_inf, inf_comm (lift α M)]
  have hres := Helpers.signalizer_local_value_factorization
    p 1 q d.prime hq (actor α) (lift α (factorizationL θ Q₀)) (lift α M) (isElemAbelian_actor d)
    (pow_le_card_actor d) (values α θ) (solvableSignalizerConditions_values d)
    ((locallyComplete_iff d).mp f.locally_complete)
    ((compatible_iff_lift d _).mp (FactorizationDatum.basic_subgroups f).2.2.2.1)
    ((compatible_iff_lift d M).mp f.compatible_M) hMfac (helpers_normalizerFactorization f)
    (cyclicActor α a) hmember
  rw [values_cyclicActor d ha, ← lift_factorizationComplementCore hq, ← lift_inf,
    ← lift_sup] at hres
  refine (congrArg (fun H : Subgroup G => (H : Set G)) (lift_injective α hres)).trans ?_
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (inf_le_left.trans (le_normalizer_factorizationComplementCore q (θ a)))

end CFSG.SolvableSignalizer
