module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

@[expose] def UnitarySwapPairExclusion {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (n : ℕ) : Prop :=
  ∀ θ θ' : MulAut (unitaryPSU h n), θ * θ = 1 → θ ≠ 1 → θ' * θ' = 1 → θ' ≠ 1 →
    (Nat.card (fixedSubgroup θ)).factorization 2 + (Nat.card (fixedSubgroup θ')).factorization 2 ≤
      (2 * Nat.card (MulAut (unitaryPSU h n))).factorization 2 →
    Nat.card (perfectCore (fixedSubgroup θ)) * Nat.card (perfectCore (fixedSubgroup θ')) ∣
      Nat.card (unitaryPSU h n) → False

section Orders

theorem card_dvd_card_range_of_ker_le {X N Q : Type*} [Group X] [Group N] [Group Q] [Finite X]
    (μ : X →* N) (ν : X →* Q) (hν : Function.Surjective ν) (hker : μ.ker ≤ ν.ker) :
    Nat.card Q ∣ Nat.card μ.range := by
  have h1 := card_ker_mul_card_range μ
  have h2 := card_ker_mul_card_range ν
  rw [MonoidHom.range_eq_top.2 hν, Subgroup.card_top] at h2
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hker
  refine ⟨d, ?_⟩
  have hpos : 0 < Nat.card μ.ker := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h2, hd]
  ring

theorem factorization_two_le_of_odd_ker {X G : Type*} [Group X] [Group G] [Finite X] [Finite G]
    (μ : X →* G) {M : Subgroup G} (hM : μ.range ≤ M) (hodd : Odd (Nat.card μ.ker)) :
    (Nat.card X).factorization 2 ≤ (Nat.card M).factorization 2 := by
  have h1 := card_ker_mul_card_range μ
  have hk : (Nat.card μ.ker).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.1 hodd; omega)
  have hr0 : Nat.card μ.range ≠ 0 := Nat.card_pos.ne'
  have hk0 : Nat.card μ.ker ≠ 0 := Nat.card_pos.ne'
  rw [← h1, Nat.factorization_mul hk0 hr0, Finsupp.add_apply, hk, zero_add]
  exact LinearPilot.factorization_two_le_of_dvd (Subgroup.card_dvd_of_le hM) Nat.card_pos.ne'

end Orders

section Induced

theorem ker_eq_center_of_surjective {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (hs : Function.Surjective φ) (hker : φ.ker ≤ center X) (hZ : center Y = ⊥) :
    φ.ker = center X := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hc : φ z ∈ center Y := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hs y
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz x)]
  rw [hZ, mem_bot] at hc
  exact hc

@[expose] noncomputable def quotientCenterEquivOfSurjective {X Y : Type*} [Group X] [Group Y]
    (φ : X →* Y) (hs : Function.Surjective φ) (hker : φ.ker ≤ center X) (hZ : center Y = ⊥) :
    X ⧸ center X ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_center_of_surjective φ hs hker hZ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hs)

variable {G : Type} [Group G] {P : Type} [Group P]

@[expose] noncomputable def inducedAut (X : Subgroup G) (ψ : X ⧸ center X ≃* P) {t : G}
    (htX : t ∈ normalizer (X : Set G)) : MulAut P :=
  MulAut.congr ψ (centerQuotientAut (X.normalizerMonoidHom ⟨t, htX⟩))

variable {X : Subgroup G} (ψ : X ⧸ center X ≃* P) {t : G} (htX : t ∈ normalizer (X : Set G))

theorem inducedAut_mul_self (ht : orderOf t = 2) :
    inducedAut X ψ htX * inducedAut X ψ htX = 1 := by
  have hτ2 : X.normalizerMonoidHom ⟨t, htX⟩ * X.normalizerMonoidHom ⟨t, htX⟩ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one X htX (by rw [← ht]; exact pow_orderOf_eq_one t)
  rw [inducedAut, ← map_mul, ← LinearPilot.centerQuotientAut_mul, hτ2,
    LinearPilot.centerQuotientAut_one, map_one]

theorem inducedAut_ne_one [Group.IsPerfect X] (hnX : t ∉ centralizer (X : Set G)) :
    inducedAut X ψ htX ≠ 1 := by
  intro h1
  have h2 : centerQuotientAut (X.normalizerMonoidHom ⟨t, htX⟩) = 1 := by
    have h3 := congrArg (MulAut.congr ψ).symm h1
    rwa [inducedAut, MulEquiv.symm_apply_apply, map_one] at h3
  have h3 := F4Pilot.eq_one_of_centerQuotientAut_eq_one h2
  apply hnX
  rw [mem_centralizer_iff]
  intro x hx
  have h4 := congrArg (fun φ : MulAut X => ((φ ⟨x, hx⟩ : X) : G)) h3
  simp only [MulAut.one_apply] at h4
  rw [F4Pilot.coe_normalizerMonoidHom_mk_apply X htX] at h4
  calc x * t = (t * x * t⁻¹) * t := by rw [h4]
    _ = t * x := by group

variable [Finite G]

theorem card_fixedSubgroup_inducedAut_dvd :
    Nat.card (fixedSubgroup (inducedAut X ψ htX)) ∣
      Nat.card (X ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  rw [inducedAut, LinearPilot.card_fixedSubgroup_congr]
  refine (LinearPilot.card_fixedSubgroup_centerQuotientAut_dvd _).trans ?_
  rw [← F4Pilot.map_fixedSubgroup_normalizerMonoidHom X htX,
    card_map_of_injective X.subtype_injective]

theorem card_perfectCore_fixedSubgroup_inducedAut [Finite P] :
    Nat.card (perfectCore (fixedSubgroup (inducedAut X ψ htX))) =
      Nat.card ((perfectCore (fixedSubgroup (X.normalizerMonoidHom ⟨t, htX⟩))).map
        (QuotientGroup.mk' (center X))) := by
  rw [inducedAut, LinearPilot.card_perfectCore_fixedSubgroup_congr,
    LinearPilot.perfectCore_fixedSubgroup_centerQuotientAut]

omit [Finite G] in
theorem map_perfectCore_fixedSubgroup_le_centralizer :
    (perfectCore (fixedSubgroup (X.normalizerMonoidHom ⟨t, htX⟩))).map X.subtype ≤
      centralizer ({t} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  have h2 : (y : G) ∈ (fixedSubgroup (X.normalizerMonoidHom ⟨t, htX⟩)).map X.subtype :=
    ⟨y, CFSG.Quasithin.perfectCore_le _ hy, rfl⟩
  rw [F4Pilot.map_fixedSubgroup_normalizerMonoidHom] at h2
  exact h2.2

end Induced

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem exists_pair_of_factorNormal (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A B : Subgroup G} (hqA : CFSG.Open.IsQuasisimple A) (hqB : CFSG.Open.IsQuasisimple B)
    (hAB : B ≤ centralizer (A : Set G)) (hodd : Odd (Nat.card (A ⊓ B : Subgroup G)))
    (ψA : A ⧸ center A ≃* unitaryPSU h n) (ψB : B ⧸ center B ≃* unitaryPSU h n)
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G))
    (hnA : t ∉ centralizer (A : Set G)) (hnB : t ∉ centralizer (B : Set G)) :
    ∃ θ θ' : MulAut (unitaryPSU h n), θ * θ = 1 ∧ θ ≠ 1 ∧ θ' * θ' = 1 ∧ θ' ≠ 1 ∧
      (Nat.card (fixedSubgroup θ)).factorization 2 +
          (Nat.card (fixedSubgroup θ')).factorization 2 ≤
        (2 * Nat.card (MulAut (unitaryPSU h n))).factorization 2 ∧
      Nat.card (perfectCore (fixedSubgroup θ)) * Nat.card (perfectCore (fixedSubgroup θ')) ∣
        Nat.card (unitaryPSU h n) := by
  have := h.finite
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv h hn hnq e
  have : Group.IsPerfect A := ⟨hqA.1⟩
  have : Group.IsPerfect B := ⟨hqB.1⟩
  refine ⟨inducedAut A ψA htA, inducedAut B ψB htB, inducedAut_mul_self ψA htA ht,
    inducedAut_ne_one ψA htA hnA, inducedAut_mul_self ψB htB ht, inducedAut_ne_one ψB htB hnB,
    ?_, ?_⟩
  ·
    set CA := A ⊓ centralizer ({t} : Set G) with hCA
    set CB := B ⊓ centralizer ({t} : Set G) with hCB
    have hcomm : ∀ (x : CA) (y : CB), Commute (CA.subtype x) (CB.subtype y) := fun x y =>
      mem_centralizer_iff.1 (hAB y.2.1) x x.2.1
    set μ := MonoidHom.noncommCoprod CA.subtype CB.subtype hcomm with hμ
    have hrange : μ.range ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, rfl⟩
      rw [hμ, MonoidHom.noncommCoprod_apply]
      exact mul_mem p.1.2.2 p.2.2.2
    have hrel : ∀ p : μ.ker, ((p : CA × CB).1 : G) = ((p : CA × CB).2 : G)⁻¹ := by
      intro p
      have h0 := (MonoidHom.noncommCoprod_apply CA.subtype CB.subtype hcomm
        (p : CA × CB)).symm.trans (MonoidHom.mem_ker.1 p.2)
      exact eq_inv_of_mul_eq_one_left h0
    have hmem : ∀ p : μ.ker, ((p : CA × CB).1 : G) ∈ A ⊓ B := fun p =>
      mem_inf.2 ⟨(p : CA × CB).1.2.1, by rw [hrel p]; exact inv_mem (p : CA × CB).2.2.1⟩
    let ι : μ.ker →* (A ⊓ B : Subgroup G) :=
      { toFun := fun p => ⟨_, hmem p⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro p q hpq
      have h1 : ((p : CA × CB).1 : G) = ((q : CA × CB).1 : G) :=
        congrArg (fun z : (A ⊓ B : Subgroup G) => (z : G)) hpq
      have h2 : ((p : CA × CB).2 : G) = ((q : CA × CB).2 : G) := by
        have hp := hrel p
        have hq := hrel q
        rw [h1] at hp
        exact inv_injective (hp.symm.trans hq)
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    have hkerodd : Odd (Nat.card μ.ker) := Odd.of_dvd_nat hodd (card_dvd_of_injective ι hι)
    have h1 := factorization_two_le_of_odd_ker μ hrange hkerodd
    have hCt := F4Pilot.card_centralizer_dvd_two_mul_card_mulAut e ht
      (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC
        ht) hKt
    have h2 := LinearPilot.factorization_two_le_of_dvd hCt
      (mul_ne_zero two_ne_zero Nat.card_pos.ne')
    have hdA := LinearPilot.factorization_two_le_of_dvd (card_fixedSubgroup_inducedAut_dvd ψA htA)
      Nat.card_pos.ne'
    have hdB := LinearPilot.factorization_two_le_of_dvd (card_fixedSubgroup_inducedAut_dvd ψB htB)
      Nat.card_pos.ne'
    rw [Nat.card_prod, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply] at h1
    rw [← hCA] at hdA
    rw [← hCB] at hdB
    omega
  ·
    set PA := perfectCore (fixedSubgroup (A.normalizerMonoidHom ⟨t, htA⟩)) with hPA
    set PB := perfectCore (fixedSubgroup (B.normalizerMonoidHom ⟨t, htB⟩)) with hPB
    have hcomm : ∀ (x : PA) (y : PB),
        Commute ((A.subtype.comp PA.subtype) x) ((B.subtype.comp PB.subtype) y) := fun x y =>
      mem_centralizer_iff.1 (hAB (y : B).2) _ (x : A).2
    set μ := MonoidHom.noncommCoprod (A.subtype.comp PA.subtype) (B.subtype.comp PB.subtype)
      hcomm with hμ
    set ν := MonoidHom.prodMap ((QuotientGroup.mk' (center A)).comp PA.subtype)
      ((QuotientGroup.mk' (center B)).comp PB.subtype) with hν
    have hker : μ.ker ≤ ν.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro p hp
      rw [MonoidHom.mem_ker, hμ, MonoidHom.noncommCoprod_apply] at hp
      have hx : (((p.1 : PA) : A) : G) = (((p.2 : PB) : B) : G)⁻¹ := eq_inv_of_mul_eq_one_left hp
      have hy : (((p.2 : PB) : B) : G) = (((p.1 : PA) : A) : G)⁻¹ := eq_inv_of_mul_eq_one_right hp
      have hxZ : ((p.1 : PA) : A) ∈ center A := by
        rw [mem_center_iff]
        intro a
        apply Subtype.ext
        have hxB : (((p.1 : PA) : A) : G) ∈ B := by rw [hx]; exact inv_mem ((p.2 : PB) : B).2
        exact mem_centralizer_iff.1 (hAB hxB) a a.2
      have hyZ : ((p.2 : PB) : B) ∈ center B := by
        rw [mem_center_iff]
        intro b
        apply Subtype.ext
        have hyA : (((p.2 : PB) : B) : G) ∈ A := by rw [hy]; exact inv_mem ((p.1 : PA) : A).2
        exact (mem_centralizer_iff.1 (hAB b.2) _ hyA).symm
      rw [MonoidHom.mem_ker]
      refine Prod.ext ?_ ?_
      · change QuotientGroup.mk' (center A) ((p.1 : PA) : A) = 1
        exact (QuotientGroup.eq_one_iff _).2 hxZ
      · change QuotientGroup.mk' (center B) ((p.2 : PB) : B) = 1
        exact (QuotientGroup.eq_one_iff _).2 hyZ
    have hdvd := card_dvd_card_range_of_ker_le μ ν.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ν) hker
    have hνr : Nat.card ν.range = Nat.card (PA.map (QuotientGroup.mk' (center A))) *
        Nat.card (PB.map (QuotientGroup.mk' (center B))) := by
      rw [hν, MonoidHom.range_prodMap, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype,
        range_subtype, ← Nat.card_prod]
      exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
    have hpA : Group.IsPerfect PA := Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
    have hpB : Group.IsPerfect PB := Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
    have htop : ⁅(⊤ : Subgroup (PA × PB)), (⊤ : Subgroup (PA × PB))⁆ =
        (⊤ : Subgroup (PA × PB)) := by
      rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, ← commutator_def,
        ← commutator_def, Group.IsPerfect.commutator_eq_top, Group.IsPerfect.commutator_eq_top]
    have hperf : ⁅μ.range, μ.range⁆ = μ.range := by
      rw [MonoidHom.range_eq_map, ← map_commutator, htop]
    have hμt : μ.range ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, rfl⟩
      rw [hμ, MonoidHom.noncommCoprod_apply]
      exact mul_mem (map_perfectCore_fixedSubgroup_le_centralizer htA ⟨_, p.1.2, rfl⟩)
        (map_perfectCore_fixedSubgroup_le_centralizer htB ⟨_, p.2.2, rfl⟩)
    have hμL : μ.range ≤ L :=
      CFSG.SeitzReduction.std_perfect_le hset.standardSetting hOut htC ht hperf hμt
    have hLdvd : Nat.card μ.range ∣ Nat.card (unitaryPSU h n) := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_le hμL
    rw [card_perfectCore_fixedSubgroup_inducedAut, card_perfectCore_fixedSubgroup_inducedAut,
      ← hPA, ← hPB, ← hνr]
    exact hdvd.trans hLdvd

end Core

theorem false_of_factorNormal_of_pairExclusion {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {n : ℕ}
    (hP : UnitarySwapPairExclusion h n) (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (A : Subgroup G)
    (hq : CFSG.Open.IsQuasisimple A) (hoddZ : Odd (Nat.card (center A)))
    (hφ : ∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) (g : G)
    (hAB : A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G))
    (htA : t ∈ normalizer (A : Set G))
    (htB : t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (hnA : t ∉ centralizer (A : Set G))
    (hnB : t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    False := by
  obtain ⟨φ, hφs, hφk⟩ := hφ
  have hZL := hset.center_eq_bot
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  have hqB : CFSG.Open.IsQuasisimple B := LinearPilot.isQuasisimple_map_conj hq g
  set σ : B ≃* A := (A.equivMapOfInjective _ (MulAut.conj g).injective).symm with hσ
  have hφBs : Function.Surjective (φ.comp σ.toMonoidHom) := hφs.comp σ.surjective
  have hφBk : (φ.comp σ.toMonoidHom).ker ≤ center B := by
    intro z hz
    have hz' : σ z ∈ center A := hφk hz
    rw [mem_center_iff] at hz' ⊢
    intro w
    apply σ.injective
    rw [map_mul, map_mul]
    exact hz' (σ w)
  set ψA := (quotientCenterEquivOfSurjective φ hφs hφk hZL).trans e with hψA
  set ψB := (quotientCenterEquivOfSurjective (φ.comp σ.toMonoidHom) hφBs hφBk hZL).trans e
    with hψB
  have hodd : Odd (Nat.card (A ⊓ B : Subgroup G)) := by
    have hle : (A ⊓ B).subgroupOf A ≤ center A := by
      intro x hx
      rw [mem_subgroupOf] at hx
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      exact mem_centralizer_iff.1 (hAB (mem_inf.1 hx).2) a a.2
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
    exact Odd.of_dvd_nat hoddZ (Subgroup.card_dvd_of_le hle)
  obtain ⟨θ, θ', h1, h2, h3, h4, h5, h6⟩ := exists_pair_of_factorNormal hset e hn hnq ht
    hKt hq hqB hAB hodd ψA ψB htA htB hnA hnB
  exact hP θ θ' h1 h2 h3 h4 h5 h6

end CFSG.SeitzReduction.UnitaryPilot
