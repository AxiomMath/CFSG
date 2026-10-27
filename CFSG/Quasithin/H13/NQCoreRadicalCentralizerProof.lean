module

public import CFSG.Quasithin.H13.NQCoreRadicalCentralizer
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.H13.NQCorePrimeResidualWitness
public import CFSG.Quasithin.H13.NQSetupCcomponent
public import CFSG.Quasithin.H13.NQBlockOddResidual
public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open scoped commutatorElement

theorem chief_central_of_odd_index {W : Type*} [Group W] (h : Odd (CFSG.pCore 2 W).index) :
    ∀ B A : Subgroup W, CFSG.IsChiefFactor B A → CFSG.pCore 2 W ≤ B →
      (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B := by
  intro B A hBA hB hn
  obtain ⟨n, hn⟩ := hn
  exfalso
  have hlt : B < A := hBA.lt
  have hdvd : B.relIndex A ∣ (CFSG.pCore 2 W).index := by
    have e1 := relIndex_mul_relIndex (CFSG.pCore 2 W) B ⊤ hB le_top
    have e2 := relIndex_mul_relIndex B A ⊤ hlt.le le_top
    simp only [relIndex_top_right] at e1 e2
    rw [← e1, ← e2]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero, relIndex_eq_one] at hn
    exact absurd hn (not_le_of_gt hlt)
  · have h2 : 2 ∣ (CFSG.pCore 2 W).index := (dvd_pow_self 2 hpos.ne').trans (hn ▸ hdvd)
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

theorem commutator_top_le_of_relIndex_eq_two {W : Type*} [Group W] {B A : Subgroup W}
    (hB : B.Normal) (hA : A.Normal) (h2 : B.relIndex A = 2) : ⁅A, ⊤⁆ ≤ B := by
  rw [commutator_le]
  intro a ha w _
  rw [commutatorElement_def]
  by_cases haB : a ∈ B
  · have h1 : w * a⁻¹ * w⁻¹ ∈ B := hB.conj_mem _ (B.inv_mem haB) w
    simpa [mul_assoc] using B.mul_mem haB h1
  · have hc : w * a⁻¹ * w⁻¹ ∈ A := hA.conj_mem _ (A.inv_mem ha) w
    have hcB : w * a⁻¹ * w⁻¹ ∉ B := fun h => haB (by
      have h1 := hB.conj_mem _ h w⁻¹
      have e : w⁻¹ * (w * a⁻¹ * w⁻¹) * w⁻¹⁻¹ = a⁻¹ := by group
      rw [e] at h1
      exact inv_mem_iff.mp h1)
    have hi : (B.subgroupOf A).index = 2 := h2
    have key := (mul_mem_iff_of_index_two hi (a := ⟨a, ha⟩) (b := ⟨w * a⁻¹ * w⁻¹, hc⟩)).mpr
      (iff_of_false (fun h => haB (mem_subgroupOf.mp h)) (fun h => hcB (mem_subgroupOf.mp h)))
    rw [mem_subgroupOf] at key
    simpa [mul_assoc] using key

theorem chief_central_of_radical {W : Type*} [Group W] [Finite W]
    (hW : CFSG.IsCComponent (⊤ : Subgroup W))
    (h4 : ¬ 4 ∣ (CFSG.pCore 2 W).relIndex (CFSG.solvableRadical W)) :
    ∀ B A : Subgroup W, CFSG.IsChiefFactor B A → CFSG.pCore 2 W ≤ B →
      (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B := by
  intro B A hBA hB hn
  obtain ⟨n, hn⟩ := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBn : B.Normal := hBA.normal_K
  have hAn : A.Normal := hBA.normal_H
  have hlt : B < A := hBA.lt
  have hperf : Group.IsPerfect W :=
    Group.isPerfect_def.mpr (by rw [commutator_def]; exact hW.2.1)
  have hAtop : A ≠ ⊤ := by
    rintro rfl
    have hcard : Nat.card (W ⧸ B) = 2 ^ n := by rw [← hn, relIndex_top_right, index_eq_card]
    have hBt : B = ⊤ := NoPQuotient.of_isPerfect hperf B (IsPGroup.of_card hcard)
    exact (ne_of_lt hlt) hBt
  have hAR : A ≤ CFSG.solvableRadical W := NQSetup.le_solvableRadical_of_normal_ne_top hW hAtop
  have hBR : B ≤ CFSG.solvableRadical W := hlt.le.trans hAR
  have hdvd : B.relIndex A ∣ (CFSG.pCore 2 W).relIndex (CFSG.solvableRadical W) := by
    rw [← relIndex_mul_relIndex _ _ _ hB hBR, ← relIndex_mul_relIndex _ _ _ hlt.le hAR]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hn1 : n = 1 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [pow_zero, relIndex_eq_one] at hn
        exact absurd hn (not_le_of_gt hlt)
      · rfl
    · exact absurd ((pow_dvd_pow 2 h).trans (hn ▸ hdvd)) h4
  rw [hn1, pow_one] at hn
  exact commutator_top_le_of_relIndex_eq_two hBn hAn hn

theorem chief_central_of_mulEquiv {W W' : Type*} [Group W] [Group W'] (e : W ≃* W')
    (h : ∀ B A : Subgroup W, CFSG.IsChiefFactor B A → CFSG.pCore 2 W ≤ B →
      (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B) :
    ∀ B A : Subgroup W', CFSG.IsChiefFactor B A → CFSG.pCore 2 W' ≤ B →
      (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B := by
  intro B A hBA hB hn
  set f : W →* W' := e.toMonoidHom with hf
  have hfs : Function.Surjective f := e.surjective
  have hfi : Function.Injective f := e.injective
  have hBA' : CFSG.IsChiefFactor (B.comap f) (A.comap f) := by
    obtain ⟨hBn, hAn, hlt, hmax⟩ := hBA
    refine ⟨hBn.comap f, hAn.comap f, (comap_lt_comap_of_surjective hfs).mpr hlt,
      fun N hN hBN hNA => ?_⟩
    have hN' : (N.map f).Normal := hN.map f hfs
    have h1 : B ≤ N.map f := by
      calc B = (B.comap f).map f := (map_comap_eq_self_of_surjective hfs B).symm
        _ ≤ N.map f := map_mono hBN
    have h2 : N.map f ≤ A := by
      calc N.map f ≤ (A.comap f).map f := map_mono hNA
        _ = A := map_comap_eq_self_of_surjective hfs A
    rcases hmax _ hN' h1 h2 with h | h
    · left
      rw [← h, comap_map_eq_self_of_injective hfi]
    · right
      rw [← h, comap_map_eq_self_of_injective hfi]
  have hcore : CFSG.pCore 2 W ≤ B.comap f := by
    have h1 : (CFSG.pCore 2 W).map f = CFSG.pCore 2 W' := CFSG.pCore_map_iso 2 e
    intro x hx
    exact hB (h1 ▸ ⟨x, hx, rfl⟩)
  have hrel : (B.comap f).relIndex (A.comap f) = B.relIndex A := by
    rw [relIndex_comap, map_comap_eq_self_of_surjective hfs]
  have hc := h _ _ hBA' hcore (hrel ▸ hn)
  calc ⁅A, ⊤⁆ = (⁅A.comap f, (⊤ : Subgroup W)⁆ : Subgroup W).map f := by
        rw [map_commutator, map_comap_eq_self_of_surjective hfs, map_top_of_surjective f hfs]
    _ ≤ (B.comap f).map f := map_mono hc
    _ = B := map_comap_eq_self_of_surjective hfs B

theorem omegaOneCenterOf_map {E F : Type*} [Group E] [Group F] (p : ℕ) (f : E →* F)
    (hf : Function.Injective f) (Q : Subgroup E) :
    (NQBlock.omegaOneCenterOf p Q).map f = NQBlock.omegaOneCenterOf p (Q.map f) := by
  unfold NQBlock.omegaOneCenterOf
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨z, ⟨hzQC, hzp⟩, rfl⟩
    obtain ⟨hzQ, hzC⟩ := mem_inf.mp hzQC
    refine ⟨mem_inf.mpr ⟨⟨z, hzQ, rfl⟩, mem_centralizer_iff.mpr ?_⟩, by
      rw [← map_pow, hzp, map_one]⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hzC q hq]
  · rintro ⟨hwQC, hwp⟩
    obtain ⟨⟨z, hzQ, rfl⟩, hwC⟩ := mem_inf.mp hwQC
    refine ⟨z, ⟨mem_inf.mpr ⟨hzQ, mem_centralizer_iff.mpr fun q hq => hf ?_⟩,
      hf (by rw [map_pow, hwp, map_one])⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hwC (f q) ⟨q, hq, rfl⟩

theorem map_map_pCore_subgroupOf {G : Type*} [Group G] (p : ℕ) {E X : Subgroup G}
    (hXE : X ≤ E) :
    ((CFSG.pCore p ↥(X.subgroupOf E)).map (X.subgroupOf E).subtype).map E.subtype =
      pCoreOf p X := by
  set e : ↥(X.subgroupOf E) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXE
  have h1 : (CFSG.pCore p ↥(X.subgroupOf E)).map e.toMonoidHom = CFSG.pCore p ↥X :=
    CFSG.pCore_map_iso p e
  have h2 : E.subtype.comp (X.subgroupOf E).subtype = X.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [map_map, h2, ← map_map, h1, pCoreOf]

theorem reduced_witness_of_le {G : Type*} [Group G] [Finite G] {E X : Subgroup G} (hXE : X ≤ E)
    (hn : (X.subgroupOf E).Normal) (hno : NoPQuotient 2 ↥X) :
    (⁅(primeReducedAggregate ↥E 2).map E.subtype, X⁆ ≠ ⊥ →
        ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 X), X⁆ ≠ ⊥) ∧
      ((∀ B A : Subgroup ↥X, CFSG.IsChiefFactor B A → CFSG.pCore 2 ↥X ≤ B →
          (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B) →
        ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 X), X⁆ ≠ ⊥ →
        ⁅(primeReducedAggregate ↥E 2).map E.subtype, X⁆ ≠ ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X' : Subgroup ↥E := X.subgroupOf E with hX'
  set e : ↥X' ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXE with he
  have hno' : NoPQuotient 2 ↥X' :=
    NoPQuotient.of_surjective e.symm.toMonoidHom e.symm.surjective hno
  obtain ⟨-, -, h3, h4⟩ := prime_residual_subnormal_reduced_witness hn.isSubnormal hno'
  have hXmap : X'.map E.subtype = X := by
    rw [hX', subgroupOf_map_subtype, inf_eq_left.mpr hXE]
  have ha : (⁅NQBlock.omegaOneCenterOf 2 ((CFSG.pCore 2 ↥X').map X'.subtype), X'⁆).map
      E.subtype = ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 X), X⁆ := by
    rw [map_commutator, omegaOneCenterOf_map 2 E.subtype E.subtype_injective,
      map_map_pCore_subgroupOf 2 hXE, hXmap]
  have hc : (⁅primeReducedAggregate ↥E 2, X'⁆).map E.subtype =
      ⁅(primeReducedAggregate ↥E 2).map E.subtype, X⁆ := by
    rw [map_commutator, hXmap]
  have hne : ∀ K : Subgroup ↥E, K.map E.subtype ≠ ⊥ ↔ K ≠ ⊥ := fun K =>
    not_congr (map_eq_bot_iff_of_injective K E.subtype_injective)
  refine ⟨fun h => ?_, fun hchief h => ?_⟩
  · rw [← hc, hne] at h
    rw [← ha, hne]
    exact h3 h
  · rw [← ha, hne] at h
    rw [← hc, hne]
    exact ((h4 (chief_central_of_mulEquiv e.symm hchief)).2).mp h

theorem relIndex_eq_card_map_mk {W : Type*} [Group W] (N K : Subgroup W) [N.Normal] :
    N.relIndex K = Nat.card (K.map (QuotientGroup.mk' N)) := by
  have h1 : ((QuotientGroup.mk' N).comp K.subtype).ker = N.subgroupOf K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have h2 : ((QuotientGroup.mk' N).comp K.subtype).range = K.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [relIndex, ← h1, index_ker, h2]

theorem closure_odd_le {W : Type*} [Group W] (R : Subgroup W) :
    closure {x | x ∈ R ∧ Odd (orderOf x)} ≤ R :=
  (closure_le _).mpr fun _ hx => hx.1

theorem noPQuotient_closure_odd {W : Type*} [Group W] [Finite W] (R : Subgroup W) :
    NoPQuotient 2 ↥(closure {x | x ∈ R ∧ Odd (orderOf x)}) := by
  intro N _ hN
  have key : closure {x | x ∈ R ∧ Odd (orderOf x)} ≤
      N.map (closure {x | x ∈ R ∧ Odd (orderOf x)}).subtype := by
    refine (closure_le _).mpr fun x hx => ?_
    have hxY : x ∈ closure {x | x ∈ R ∧ Odd (orderOf x)} := subset_closure hx
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    obtain ⟨k, hk⟩ := hN (QuotientGroup.mk ⟨x, hxY⟩)
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 := orderOf_map_dvd (QuotientGroup.mk' N) ⟨x, hxY⟩
    rw [← Subgroup.orderOf_coe] at h2
    have hcop : Nat.gcd (2 ^ k) (orderOf x) = 1 := Nat.Coprime.pow_left k
      (Nat.coprime_two_left.mpr hx.2)
    have h3 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
    rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  ext y
  simp only [mem_top, iff_true]
  obtain ⟨n, hn, hny⟩ := key y.2
  rwa [show n = y from Subtype.ext hny] at hn

theorem pow_two_pow_mem_closure_odd {W : Type*} [Group W] [Finite W] (R : Subgroup W) {r : W}
    (hr : r ∈ R) : ∃ k : ℕ, r ^ 2 ^ k ∈ closure {x | x ∈ R ∧ Odd (orderOf x)} := by
  obtain ⟨k, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos r).ne' 2 (by norm_num)
  refine ⟨k, subset_closure ⟨R.pow_mem hr _, ?_⟩⟩
  rw [orderOf_pow' r (pow_ne_zero k two_ne_zero), hord, Nat.gcd_mul_right_left,
    Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)

theorem closure_odd_characteristic {W : Type*} [Group W] (R : Subgroup W) [hR : R.Characteristic] :
    (closure {x | x ∈ R ∧ Odd (orderOf x)}).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, ⟨hx, hxo⟩, rfl⟩
  refine subset_closure ⟨characteristic_iff_map_le.mp hR φ ⟨x, hx, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  exact hxo

theorem radical_two_part (h36 : Vol2Native.A36CoreForSQTKCat)
    {W : Type} [Group W] [Finite W] (hW : CFSG.SectionRank.IsSQTKCat W)
    (hWC : CFSG.IsCComponent (⊤ : Subgroup W))
    (hq : ¬ CFSG.IsQuasisimple (W ⧸ CFSG.pCore 2 W)) :
    ¬ 4 ∣ (CFSG.pCore 2 W).relIndex (CFSG.solvableRadical W) ∧
      Odd (CFSG.pCore 2
        ↥(closure {x | x ∈ CFSG.solvableRadical W ∧ Odd (orderOf x)})).index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 W) with hπ
  obtain ⟨hSQT', hO2', hLC'⟩ := NQBlock.quotient_two_core_setup hW.1 hWC
  obtain ⟨-, -, hFodd, -, -, -⟩ := NQBlock.odd_Fitting_cores_self hSQT' hO2' hLC' hq
  have hQ' : Vol2Native.SQTKHypCat (W ⧸ CFSG.pCore 2 W) := Vol2Native.SQTKHypCat.quotient_pCore W hW
  have htop : (⊤ : Subgroup (W ⧸ CFSG.pCore 2 W)) ∈ cComp (⊤ : Subgroup (W ⧸ CFSG.pCore 2 W)) :=
    mem_cComp_top_iff_isCComponent.mpr hLC'
  obtain ⟨-, hcom, -⟩ := h36 _ hQ' ⊤ htop
  set τ : ↥(⊤ : Subgroup (W ⧸ CFSG.pCore 2 W)) ≃* (W ⧸ CFSG.pCore 2 W) := Subgroup.topEquiv
  have hFτ : (CFSG.fittingSubgroup ↥(⊤ : Subgroup (W ⧸ CFSG.pCore 2 W))).map τ.toMonoidHom =
      CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) := C1Pack.fittingSubgroup_map_mulEquiv τ
  have hRτ : (CFSG.solvableRadical ↥(⊤ : Subgroup (W ⧸ CFSG.pCore 2 W))).map τ.toMonoidHom =
      CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W) := E1.solvableRadical_map_mulEquiv τ
  have hcardF : Nat.card (CFSG.fittingSubgroup ↥(⊤ : Subgroup (W ⧸ CFSG.pCore 2 W))) =
      Nat.card (CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W)) := by
    rw [← hFτ, card_map_of_injective τ.injective]
  have hF25 : 25 ≤ Nat.card (CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W)) := by
    obtain ⟨p, hp, hp5, D₀, -, hD₀, hshape, -⟩ :=
      NQBlock.nq_characteristic_radical_odd_residual_witness hW.1 hWC hq
    have : Fact p.Prime := ⟨hp⟩
    have hle : D₀ ≤ CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) :=
      hD₀.trans (CFSG.pCore_le_fitting _ p)
    have hdvd := card_dvd_of_le hle
    have h25 : 25 ≤ Nat.card D₀ := by
      have hp2 : 25 ≤ p ^ 2 := by nlinarith
      rcases hshape with ⟨-, h2⟩ | ⟨-, h3, -⟩
      · omega
      · have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
        omega
    exact h25.trans (Nat.le_of_dvd Nat.card_pos hdvd)
  have hrel : (CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W)).relIndex
      (CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) = 2 := by
    obtain ⟨-, -, hcases, -, -⟩ := hcom
    rcases hcases with ⟨-, h2⟩ | ⟨-, -, h13⟩
    · rw [← hFτ, ← hRτ, relIndex_map_map_of_injective _ _ τ.injective]
      exact h2
    · exfalso
      rw [hcardF] at h13
      omega
  have hodd : Odd (Nat.card ↥(CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) ⊓
      CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W))) :=
    Odd.of_dvd_nat hFodd (card_dvd_of_le inf_le_left)
  have hcardR : Nat.card (CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) =
      2 * Nat.card ↥(CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) ⊓
        CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) := by
    rw [← relIndex_mul_card, hrel]
  have hRmap : (CFSG.solvableRadical W).map π ≤ CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W) := by
    obtain ⟨hc, hs, -⟩ := Setup.Offender.solvableRadical_characterization W
    refine (Setup.Offender.solvableRadical_characterization _).2.2.1 _
      ((inferInstance : (CFSG.solvableRadical W).Normal).map π (QuotientGroup.mk'_surjective _))
      ?_
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (CFSG.solvableRadical W))
      (MonoidHom.subgroupMap_surjective _ _)
  refine ⟨fun h4 => ?_, ?_⟩
  · have h1 : (CFSG.pCore 2 W).relIndex (CFSG.solvableRadical W) ∣
        Nat.card (CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) := by
      rw [relIndex_eq_card_map_mk]
      exact card_dvd_of_le hRmap
    rw [hcardR] at h1
    obtain ⟨m, hm⟩ := hodd
    have := h4.trans h1
    omega
  · set Y : Subgroup W := closure {x | x ∈ CFSG.solvableRadical W ∧ Odd (orderOf x)} with hY
    have hmemF : ∀ x ∈ CFSG.solvableRadical W, Odd (orderOf x) →
        π x ∈ CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) := by
      intro x hx hxo
      set y : ↥(CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) := ⟨π x, hRmap ⟨x, hx, rfl⟩⟩
      have hyo : Odd (orderOf y) := by
        have h1 : orderOf y = orderOf (π x) := (Subgroup.orderOf_coe y).symm
        exact Odd.of_dvd_nat hxo (h1 ▸ orderOf_map_dvd π x)
      have hy2 := sq_mem_of_index_two hrel y
      obtain ⟨k, hk⟩ := hyo
      have hy1 : y * (y ^ 2) ^ k = 1 := by
        rw [← pow_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
      have hyF : y ∈ (CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W)).subgroupOf
          (CFSG.solvableRadical (W ⧸ CFSG.pCore 2 W)) := by
        rw [eq_inv_of_mul_eq_one_left hy1]
        exact inv_mem (pow_mem hy2 k)
      exact mem_subgroupOf.mp hyF
    have hYF : Y.map π ≤ CFSG.fittingSubgroup (W ⧸ CFSG.pCore 2 W) := by
      rw [hY, MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, ⟨hx, hxo⟩, rfl⟩
      exact hmemF x hx hxo
    have hk : (CFSG.pCore 2 W).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
      have hp : IsPGroup 2 ((CFSG.pCore 2 W).subgroupOf Y) :=
        (CFSG.pCore_isPGroup (p := 2) (G := W)).comap_of_injective Y.subtype Y.subtype_injective
      exact le_sSup ⟨inferInstance, hp⟩
    have h1 : (CFSG.pCore 2 ↥Y).index ∣ ((CFSG.pCore 2 W).subgroupOf Y).index := index_dvd_of_le hk
    have h2 : ((CFSG.pCore 2 W).subgroupOf Y).index = Nat.card (Y.map π) :=
      relIndex_eq_card_map_mk _ _
    exact Odd.of_dvd_nat (Odd.of_dvd_nat hFodd (card_dvd_of_le hYF)) (h2 ▸ h1)

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_qtnqVc (M : Subgroup G) : IsTwoReducedIn M (qtnqVc M) := by
  refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨map_subtype_le _, ?_⟩
  have hsub : (qtnqVc M).subgroupOf M = primeReducedAggregate (↥M) 2 :=
    comap_map_eq_self_of_injective M.subtype_injective _
  rw [hsub]
  exact isPrimeReduced_primeReducedAggregate 2

theorem snRadicalCentralizer (h36 : Vol2Native.A36CoreForSQTKCat)
    (h3214 : Stmt3_2_14) : StmtSNRadicalCentralizer := by
  intro G _ _ T D hs hnab hQ hT hDf hTD hDq
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hs
  have hK : LocalSQTK G := (qtkeCore_of_cat hnab hQ).1
  have hDl := hDf.1
  have hO2D : pCoreOf 2 D ≠ ⊥ := U3.pCoreOf_ne_bot_of_isFaithfulLocal hDf
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥D := hK D hO2D
  have hDc : D ∈ cComp (D ⊔ T) := cComp_of_isLocal hDl
  have hDtop : CFSG.IsCComponent (⊤ : Subgroup ↥D) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp
      (subgroupOf_mem_cComp (cComp_mem_of_le hDc le_rfl le_sup_left))
    rwa [subgroupOf_self] at h3
  obtain ⟨h4, hYodd⟩ := radical_two_part h36 hsqtk hDtop hDq
  set J := normalizer (D : Set G) with hJ
  set V := qtnqVc J with hV
  set R : Subgroup ↥D := CFSG.solvableRadical ↥D with hR
  set Y : Subgroup ↥D := closure {x | x ∈ R ∧ Odd (orderOf x)} with hY
  have hRc : R.Characteristic := (Setup.Offender.solvableRadical_characterization ↥D).1
  have hYc : Y.Characteristic := closure_odd_characteristic R
  have hDJ : D ≤ J := le_normalizer
  have hDTJ : D ⊔ T ≤ J := sup_le hDJ hTD
  have hNR : J ≤ normalizer (R.map D.subtype : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic R
  have hNY : J ≤ normalizer (Y.map D.subtype : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Y
  have hRGD : R.map D.subtype ≤ D := map_subtype_le R
  have hYGR : Y.map D.subtype ≤ R.map D.subtype := map_mono (closure_odd_le R)
  have hYGD : Y.map D.subtype ≤ D := hYGR.trans hRGD
  have hVred : IsTwoReducedIn J V := isTwoReducedIn_qtnqVc J
  have h314 : R.map D.subtype ≤ centralizer (reducedAggregate (D ⊔ T) : Set G) :=
    h3214 G T D hs hnab hQ hT hDl hDq
  set eY : ↥Y ≃* ↥(Y.map D.subtype) := Y.equivMapOfInjective D.subtype D.subtype_injective
  have hnoY : NoPQuotient 2 ↥(Y.map D.subtype) :=
    NoPQuotient.of_surjective eY.toMonoidHom eY.surjective (noPQuotient_closure_odd R)
  have hperfD : Group.IsPerfect ↥D :=
    Group.isPerfect_def.mpr (by rw [commutator_def]; exact hDtop.2.1)
  have hnoD : NoPQuotient 2 ↥D := NoPQuotient.of_isPerfect hperfD
  have hchD := chief_central_of_radical hDtop h4
  have hchY := chief_central_of_mulEquiv eY (chief_central_of_odd_index hYodd)
  have hYJn : ((Y.map D.subtype).subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hYGD.trans hDJ)).mpr hNY
  have hYDTn : ((Y.map D.subtype).subgroupOf (D ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hYGD.trans le_sup_left)).mpr (hDTJ.trans hNY)
  have hDJn : (D.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hDJ).mpr le_rfl
  have hYV : Y.map D.subtype ≤ centralizer (V : Set G) := by
    by_contra hne
    have h1 : ⁅(primeReducedAggregate ↥J 2).map J.subtype, Y.map D.subtype⁆ ≠ ⊥ := by
      rw [commutator_comm]
      exact fun h => hne (commutator_eq_bot_iff_le_centralizer.mp h)
    have ha := (reduced_witness_of_le (hYGD.trans hDJ) hYJn hnoY).1 h1
    have hc := (reduced_witness_of_le (hYGD.trans le_sup_left) hYDTn hnoY).2 hchY ha
    apply hc
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hYGR.trans h314)
  have hRV : R.map D.subtype ≤ centralizer (V : Set G) := by
    refine hVred.2.2.2 _ (hRGD.trans hDJ) hNR fun d hd => ?_
    obtain ⟨r, hr, rfl⟩ := hd
    obtain ⟨k, hk⟩ := pow_two_pow_mem_closure_odd R hr
    exact ⟨k, hYV ⟨r ^ 2 ^ k, hk, by simp⟩⟩
  refine le_antisymm ?_ (le_inf hRGD hRV)
  set C : Subgroup ↥D := (D ⊓ centralizer (V : Set G)).subgroupOf D with hC
  have hCn : C.Normal := by
    have hle : D ≤ normalizer ((D ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
      (le_inf le_normalizer (hDJ.trans (hVred.2.1.trans
        (normalizer_le_normalizer_centralizer V)))).trans inf_normalizer_le_normalizer_inf
    have h1 := (normal_subgroupOf_iff_le_normalizer (inf_le_left : D ⊓ _ ≤ D)).mpr hle
    exact h1
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hDV : D ≤ centralizer (V : Set G) := fun x hx => by
      have hx' : (⟨x, hx⟩ : ↥D) ∈ C := htop ▸ mem_top _
      exact (mem_inf.mp (mem_subgroupOf.mp hx')).2
    have hV2 : ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 D), D⁆ ≠ ⊥ := hDf.2.2.2
    have hc := (reduced_witness_of_le hDJ hDJn hnoD).2 hchD hV2
    apply hc
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hDV
  have hCR : C ≤ R := NQSetup.le_solvableRadical_of_normal_ne_top hDtop hCtop
  intro x hx
  exact ⟨⟨x, (mem_inf.mp hx).1⟩, hCR (mem_subgroupOf.mpr hx), rfl⟩

end CFSG.Quasithin.H13.NQCore
