module

public import CFSG.Quasithin.H13.NQRigidSylow
public import CFSG.Quasithin.SteinbergCCSylowNormalizerBootstrap
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralizerPushing

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.QuasithinUnique.Setup.Offender (fixGL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_map_subtype_iff)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCore_map_le_of_le_normalizer {K H : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) :
    (CFSG.pCore 2 K).map K.subtype ≤ (CFSG.pCore 2 H).map H.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (CFSG.pCore 2 K).map K.subtype with hA
  have hAH : A ≤ H := (map_subtype_le _).trans hKH
  have hHA : H ≤ normalizer (A : Set G) := hHK.trans (normalizer_le_normalizer_map_pCore 2 K)
  have hn : (A.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  have h2 : IsPGroup 2 (A.subgroupOf H) := (CFSG.pCore_isPGroup.map _).comap_subtype
  have hle := SteinbergCC.le_pCore_of_normal_of_isPGroup hn h2
  intro a ha
  exact ⟨⟨a, hAH ha⟩, hle ha, rfl⟩

omit [Finite G] in
theorem le_pCore_map_of_le_normalizer {R H : Subgroup G} (hRH : R ≤ H)
    (hHR : H ≤ normalizer (R : Set G)) (hR : IsPGroup 2 R) :
    R ≤ (CFSG.pCore 2 H).map H.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (R.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hRH).mpr hHR
  have hle := SteinbergCC.le_pCore_of_normal_of_isPGroup hn hR.comap_subtype
  intro r hr
  exact ⟨⟨r, hRH hr⟩, hle hr, rfl⟩

omit [Finite G] in
theorem le_normalizer_pCore_map (H : Subgroup G) :
    H ≤ normalizer (((CFSG.pCore 2 H).map H.subtype : Subgroup G) : Set G) :=
  le_normalizer.trans (normalizer_le_normalizer_map_pCore 2 H)

theorem centralizer_pushing_core {M T X : Subgroup G} (hXM : X ≤ M)
    (hXn : (X.subgroupOf M).Normal) (hX : NoPQuotient 2 X)
    (hMG : CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) = {M}) {v : G}
    (hvX : X ≤ centralizer ({v} : Set G)) {R : Subgroup G}
    (hR : R = (CFSG.pCore 2 (X ⊔ (T ⊓ centralizer {v}) : Subgroup G)).map
      (X ⊔ (T ⊓ centralizer {v})).subtype)
    (hQA : IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v})) (hR1 : R ≠ ⊥)
    (hRn : X ⊔ T ≤ normalizer (R : Set G)) :
    normalizer (R : Set G) ≤ M ∧
      R = (CFSG.pCore 2 (centralizer {v} ⊓ normalizer (R : Set G) : Subgroup G)).map
        (centralizer {v} ⊓ normalizer (R : Set G)).subtype ∧
      IsSylowOf 2 R (⨆ a ∈ M ⊓ centralizer {v}, CFSG.conjugate R a) := by
  classical
  have := Fact.mk Nat.prime_two
  set H := centralizer ({v} : Set G) with hHdef
  have hR2 : IsPGroup 2 R := by rw [hR]; exact CFSG.pCore_isPGroup.map _
  have hNR : normalizer (R : Set G) ≤ M := by
    obtain ⟨B, ⟨hBloc, hNB⟩, hBmax⟩ := (Set.toFinite
      {Y : Subgroup G | CFSG.IsPLocal 2 Y ∧ normalizer (R : Set G) ≤ Y}).exists_maximal
        ⟨_, ⟨R, hR1, hR2, rfl⟩, le_rfl⟩
    have hBM : B ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) := by
      refine ⟨⟨hBloc, fun Y hBY hY => ?_⟩, fun g hg => hNB (hRn hg)⟩
      exact absurd (hBmax ⟨hY, hNB.trans hBY.le⟩ hBY.le) (not_le_of_gt hBY)
    rw [hMG, Set.mem_singleton_iff] at hBM
    exact hBM ▸ hNB
  have hNHR : H ⊓ normalizer (R : Set G) ≤ M ⊓ H := le_inf (inf_le_right.trans hNR) inf_le_left
  have hRXQ : R ≤ X ⊔ (T ⊓ H) := by rw [hR]; exact map_subtype_le _
  have hXH : X ≤ H := hvX
  have hQH : T ⊓ H ≤ H := inf_le_right
  have hAH : M ⊓ H ≤ H := inf_le_right
  have hRH : R ≤ H := hRXQ.trans (sup_le hXH hQH)
  set X' := X.subgroupOf H with hX'def
  set Q' := (T ⊓ H).subgroupOf H with hQ'def
  set A' := (M ⊓ H).subgroupOf H with hA'def
  have hXA' : X' ≤ A' := fun x hx => ⟨hXM hx, hXH hx⟩
  have hXn' : (X'.subgroupOf A').Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hXA').mpr ?_
    have hMX : M ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer hXM).mp hXn
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp (hMX (mem_subgroupOf.mp ha).1) x
  have hX' : ∀ (N : Subgroup X') [N.Normal], IsPGroup 2 (X' ⧸ N) → N = ⊤ := by
    intro N _ hN
    let e : X' ≃* X := subgroupOfEquivOfLe hXH
    have hNe : (N.map e.toMonoidHom).Normal := Normal.map inferInstance _ e.surjective
    have h1 : IsPGroup 2 (X ⧸ N.map e.toMonoidHom) :=
      hN.of_equiv (QuotientGroup.congr N _ e rfl)
    have h2 := hX _ h1
    have h3 : N.map e.toMonoidHom = (⊤ : Subgroup X').map e.toMonoidHom := by
      rw [h2, map_top_of_surjective _ e.surjective]
    exact map_injective e.injective h3
  have hQA' : IsSylowOf 2 Q' A' := by
    rw [← isSylowOf_map_subtype_iff H, hQ'def, hA'def, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hQH, inf_of_le_left hAH]
    exact hQA
  have hXQ' : (X' ⊔ Q').map H.subtype = X ⊔ (T ⊓ H) := by
    rw [Subgroup.map_sup, hX'def, hQ'def, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left hXH, inf_of_le_left hQH]
  have hR' : (CFSG.pCore 2 (X' ⊔ Q' : Subgroup H)).map (X' ⊔ Q').subtype = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hXQ', subgroupOf_map_subtype,
      inf_of_le_left hRH, hR]
  have hconf : normalizer (((CFSG.pCore 2 (X' ⊔ Q' : Subgroup H)).map
      (X' ⊔ Q').subtype : Subgroup H) : Set H) ≤ A' := by
    rw [hR', ← subgroupOf_normalizer_eq hRH]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact hNHR ⟨y.2, hy⟩
  obtain ⟨-, -, -, -, -, hRO, hRsyl, -, -⟩ :=
    SteinbergCC.prime_residual_sylow_normalizer_core_bootstrap Nat.prime_two hXA' hXn' hX'
      hQA' hconf
  rw [hR'] at hRO hRsyl
  have hNR' : (normalizer ((R.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      H ⊓ normalizer (R : Set G) := by
    rw [← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype, inf_comm]
  have hRO' : R = (CFSG.pCore 2 (H ⊓ normalizer (R : Set G) : Subgroup G)).map
      (H ⊓ normalizer (R : Set G)).subtype := by
    have h := congrArg (Subgroup.map H.subtype) hRO
    rw [subgroupOf_map_subtype, inf_of_le_left hRH,
      CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hNR'] at h
    exact h
  have hRsyl' : IsSylowOf 2 R (⨆ a ∈ M ⊓ H, CFSG.conjugate R a) := by
    rw [← isSylowOf_map_subtype_iff H] at hRsyl
    rwa [subgroupOf_map_subtype, inf_of_le_left hRH,
      CFSG.LocalAnalysis.GorensteinLyons.map_subtype_iSup_conjugate H (M ⊓ H) R hAH hRH] at hRsyl
  exact ⟨hNR, hRO', hRsyl'⟩

section RX

variable {T L M : Subgroup G}

theorem rx_action_of_witness (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hXL : X ≤ L) (hNX : normalizer (X : Set G) = M)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) :
    (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) ∧
      ⁅L, (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype⁆ ≤
        (CFSG.solvableRadical L).map L.subtype ∧
      ∀ l ∈ L, ∀ r ∈ (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype,
        ∀ x ∈ qtnqU L M, l * (r * x * r⁻¹) * l⁻¹ = r * (l * x * l⁻¹) * r⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set RX := (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype with hRX
  have hMX : M ≤ normalizer (X : Set G) := hNX.ge
  have hLN : L ≤ normalizer (X : Set G) := h.l_le.trans hMX
  have hXTM : X ⊔ T ≤ M := sup_le (hXL.trans h.l_le) h.t_le
  have hRXXT : RX ≤ X ⊔ T := map_subtype_le _
  have hRXM : RX ≤ M := hRXXT.trans hXTM
  have hXTRX : X ⊔ T ≤ normalizer (RX : Set G) := le_normalizer_pCore_map _
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have hβ := frattiniConj_comp_ne_one hp hLN hW hirrL
  have hnt : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hβ
    ext l w
    have h1 := hno (inclusion hLN l) l.2
    rw [MonoidHom.comp_apply, h1]
    rfl
  have hRXtriv : ∀ r ∈ RX, ∀ hr : r ∈ normalizer (X : Set G),
      normalizerFrattiniConj X ⟨r, hr⟩ = 1 := by
    intro r hrR hr
    have hXRX : RX.subgroupOf X ≤ CFSG.pCore 2 X := by
      refine SteinbergCC.le_pCore_of_normal_of_isPGroup ?_ ?_
      · refine ⟨fun a ha b => ?_⟩
        simp only [mem_subgroupOf, coe_mul, coe_inv] at ha ⊢
        exact (mem_normalizer_iff.mp (hXTRX ((le_sup_left : X ≤ X ⊔ T) (b : X).2)) _).mp ha
      · exact (CFSG.pCore_isPGroup.map _).comap_subtype
    ext w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    change ((((X.normalizerMonoidHom ⟨r, hr⟩ x : X) : X ⧸ CFSG.pCore 2 X)) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
      (((x : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))
    have h1 : (X.normalizerMonoidHom ⟨r, hr⟩ x : X ⧸ CFSG.pCore 2 X) =
        (x : X ⧸ CFSG.pCore 2 X) := by
      rw [QuotientGroup.eq]
      apply hXRX
      rw [mem_subgroupOf]
      change (r * x * r⁻¹)⁻¹ * (x : G) ∈ RX
      have h4 : (x : G)⁻¹ * r⁻¹ * (x : G)⁻¹⁻¹ ∈ RX :=
        (mem_normalizer_iff.mp (hXTRX ((le_sup_left : X ≤ X ⊔ T) (X.inv_mem x.2))) r⁻¹).mp
          (RX.inv_mem hrR)
      rw [inv_inv] at h4
      rw [show (r * x * r⁻¹)⁻¹ * (x : G) = r * ((x : G)⁻¹ * r⁻¹ * x) by group]
      exact RX.mul_mem hrR h4
    rw [h1]
  set φ := (normalizerFrattiniConj X).comp (inclusion hLN) with hφ
  have hker : φ.ker ≤ CFSG.solvableRadical L := by
    refine NQSetup.le_solvableRadical_of_normal_ne_top hLC fun htop => hβ ?_
    ext l w
    have hl : l ∈ φ.ker := htop ▸ mem_top l
    rw [MonoidHom.mem_ker] at hl
    rw [hl]
    rfl
  have hcomm : ∀ l ∈ L, ∀ r ∈ RX, ⁅l, r⁆ ∈ L ∧ ∀ hc : ⁅l, r⁆ ∈ L,
      (⟨⁅l, r⁆, hc⟩ : L) ∈ CFSG.solvableRadical L := by
    intro l hl r hr
    have hrL : r * l⁻¹ * r⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (h.eq_normalizer ▸ hRXM hr) l⁻¹).mp (L.inv_mem hl)
    have hcL : ⁅l, r⁆ ∈ L := by
      rw [commutatorElement_def, show l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) by group]
      exact L.mul_mem hl hrL
    refine ⟨hcL, fun hc => hker ?_⟩
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply]
    have hrN : r ∈ normalizer (X : Set G) := hMX (hRXM hr)
    have hlN : l ∈ normalizer (X : Set G) := hLN hl
    have he : inclusion hLN ⟨⁅l, r⁆, hc⟩ = ⟨l, hlN⟩ * ⟨r, hrN⟩ * ⟨l, hlN⟩⁻¹ * ⟨r, hrN⟩⁻¹ :=
      Subtype.ext rfl
    rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hRXtriv r hr hrN]
    group
  refine ⟨hnt, ?_, ?_⟩
  · rw [commutator_le]
    intro l hl r hr
    obtain ⟨hcL, hc⟩ := hcomm l hl r hr
    exact ⟨⟨_, hcL⟩, hc hcL, rfl⟩
  · intro l hl r hr x hx
    obtain ⟨hcL, hc⟩ := hcomm l hl r hr
    have hUM := le_normalizer_qtnqU h
    have hy : r * (l * x * l⁻¹) * r⁻¹ ∈ qtnqU L M := by
      have h1 := (mem_normalizer_iff.mp (hUM (h.l_le hl)) x).mp hx
      exact (mem_normalizer_iff.mp (hUM (hRXM hr)) _).mp h1
    have hcy := NQSetup.radical_commute_qtnqVc h (hc hcL) (NQSetup.qtnqU_le_qtnqVc h hy)
    change ⁅l, r⁆ * (r * (l * x * l⁻¹) * r⁻¹) = r * (l * x * l⁻¹) * r⁻¹ * ⁅l, r⁆ at hcy
    calc l * (r * x * r⁻¹) * l⁻¹
        = ⁅l, r⁆ * (r * (l * x * l⁻¹) * r⁻¹) * ⁅l, r⁆⁻¹ := by
          rw [commutatorElement_def]; group
      _ = r * (l * x * l⁻¹) * r⁻¹ := by rw [hcy, mul_inv_cancel_right]

end RX

section Escaping

variable {T L M : Subgroup G}

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (U : Subgroup G) :
    normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  simp only [mem_centralizer_iff]
  constructor
  · intro hy x hx
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ U := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rw [inv_inv] at h1
    have h2 := hy _ h1
    calc x * (g * y * g⁻¹) = g * (g⁻¹ * x * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * x := by group
  · intro hy x hx
    have h1 : g * x * g⁻¹ ∈ U := (mem_normalizer_iff.mp hg x).mp hx
    have h2 := hy _ h1
    have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := h2
        _ = g * (y * x) * g⁻¹ := by group
    simpa using h3

theorem pushing_core_of_witness
    (h : QTNQ T L M) (hmod : QTNQExplicitModule L M) {p : ℕ}
    (hp : p.Prime) {X : Subgroup G} (hXL : X ≤ L)
    (hXRad : X ≤ (CFSG.solvableRadical L).map L.subtype) (hX2 : NoPQuotient 2 X)
    (hO2 : CFSG.pCore 2 X ≠ ⊥) (hNX : normalizer (X : Set G) = M)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) {u : G} (hu : u ∈ qtnqU L M) (hu1 : u ≠ 1)
    (hCu : ¬ centralizer {u} ≤ M) :
    ∃ m ∈ M,
      IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (M ⊓ centralizer {m⁻¹ * u * m}) ∧
      IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (centralizer {m⁻¹ * u * m}) ∧
      (T ⊓ centralizer {m⁻¹ * u * m}).relIndex T = 2 ∧
      (CFSG.pCore 2 X).map X.subtype ≠ ⊥ ∧
      (CFSG.pCore 2 X).map X.subtype ≤
        (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} ∧
      (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} =
        (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
          centralizer (qtnqU L M : Set G) ∧
      (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} =
        (CFSG.pCore 2 (X ⊔ (T ⊓ centralizer {m⁻¹ * u * m}) : Subgroup G)).map
          (X ⊔ (T ⊓ centralizer {m⁻¹ * u * m})).subtype ∧
      X ⊔ T ≤ normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
        centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) ∧
      (CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) = {M} →
        normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
          centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) ≤ M ∧
        (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} =
          (CFSG.pCore 2 (centralizer {m⁻¹ * u * m} ⊓ normalizer
            (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
              centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) : Subgroup G)).map
            (centralizer {m⁻¹ * u * m} ⊓ normalizer
              (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
                centralizer {m⁻¹ * u * m} : Subgroup G) : Set G)).subtype ∧
        IsSylowOf 2 ((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
            centralizer {m⁻¹ * u * m})
          (⨆ a ∈ M ⊓ centralizer {m⁻¹ * u * m}, CFSG.conjugate
            ((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
              centralizer {m⁻¹ * u * m}) a)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hpos⟩ := explicit_module_ambient_centralizer_Sylow_position h hmod
  obtain ⟨m, hm, hQA, -, hQG, -, htwo⟩ := hpos u hu hu1
  have hTQ := htwo hCu
  refine ⟨m, hm, ?_⟩
  set v := m⁻¹ * u * m with hv
  set RX := (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype with hRX
  set Q := T ⊓ centralizer {v} with hQ
  have hUel := qtnqU_isElementaryAbelian h
  have hUM : M ≤ normalizer (qtnqU L M : Set G) := le_normalizer_qtnqU h
  have hvU : v ∈ qtnqU L M := by
    have := (mem_normalizer_iff.mp (hUM (M.inv_mem hm)) u).mp hu
    simpa [hv] using this
  have hMX : M ≤ normalizer (X : Set G) := hNX.ge
  have hXM : X ≤ M := hXL.trans h.l_le
  have hXTM : X ⊔ T ≤ M := sup_le hXM h.t_le
  have hXTN : X ⊔ T ≤ normalizer (X : Set G) := hXTM.trans hMX
  have hRX2 : IsPGroup 2 RX := CFSG.pCore_isPGroup.map _
  have hRXXT : RX ≤ X ⊔ T := map_subtype_le _
  have hRXM : RX ≤ M := hRXXT.trans hXTM
  have hXTRX : X ⊔ T ≤ normalizer (RX : Set G) := le_normalizer_pCore_map _
  obtain ⟨-, -, hcommU⟩ := rx_action_of_witness (T := T) h hp hXL hNX hexp hW hirrL
  have hXCU : ∀ x ∈ X, ∀ y ∈ qtnqU L M, x * y = y * x := by
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := hXRad hx
    exact NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h hy)
  have hXCv : X ≤ centralizer {v} := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hXCU x hx v hvU)
  have hRXT : RX ≤ T := by
    set T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2 with hT'
    have hT'T : (T' : Subgroup G) = T := IsPGroup.toSylow_coe h.sylow.1 h.sylow.2
    have hTRX : (T' : Subgroup G) ≤ normalizer (RX : Set G) := by
      rw [hT'T]
      exact (le_sup_right : T ≤ X ⊔ T).trans hXTRX
    have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hRX2 hTRX) le_sup_left
    rw [← hT'T, ← h1]
    exact le_sup_right
  have hfin : Finite (Additive (qtnqU L M)) := inferInstanceAs (Finite (qtnqU L M))
  have : FiniteDimensional (ZMod 2) (Additive (qtnqU L M)) := Module.Finite.of_finite
  set ρ := qtnqAction h with hρ
  set B := (RX.subgroupOf M).map ρ with hB
  set P := (T.subgroupOf M).map ρ with hP
  have hρapply : ∀ (g : M) (x : qtnqU L M), ρ g (Additive.ofMul x) =
      Additive.ofMul ⟨g * x * (g : G)⁻¹, (mem_normalizer_iff.mp (hUM g.2) x).mp x.2⟩ :=
    fun _ _ => rfl
  have hBS : B ≤ centralizer (qtnqS h : Set (Additive (qtnqU L M) ≃ₗ[ZMod 2]
      Additive (qtnqU L M))) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    obtain ⟨l, rfl⟩ := (mem_qtnqS h).mp hs
    refine LinearEquiv.ext fun e => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * ((r : G) * ((e.toMul : qtnqU L M) : G) * (r : G)⁻¹) * (l : G)⁻¹ =
      (r : G) * ((l : G) * ((e.toMul : qtnqU L M) : G) * (l : G)⁻¹) * (r : G)⁻¹
    exact hcommU l l.2 r hr _ (e.toMul).2
  have hB2 : IsPGroup 2 B := hRX2.comap_subtype.map _
  have hP2 : IsPGroup 2 P := h.sylow.1.comap_subtype.map _
  have hPS : P ≤ normalizer (qtnqS h : Set (Additive (qtnqU L M) ≃ₗ[ZMod 2]
      Additive (qtnqU L M))) ⊓ normalizer (B : Set (Additive (qtnqU L M) ≃ₗ[ZMod 2]
      Additive (qtnqU L M))) := by
    refine le_inf ((map_mono ?_).trans (le_normalizer_map ρ))
      ((map_mono ?_).trans (le_normalizer_map ρ))
    · intro t ht
      rw [mem_normalizer_iff]
      intro k
      simp only [mem_subgroupOf, coe_mul, coe_inv]
      have htN : (t : G) ∈ normalizer (L : Set G) := by
        rw [← h.eq_normalizer]
        exact h.t_le ht
      exact mem_normalizer_iff.mp htN k
    · intro t ht
      rw [mem_normalizer_iff]
      intro k
      simp only [mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp (hXTRX ((le_sup_right : T ≤ X ⊔ T) ht)) k
  obtain ⟨hcol, -⟩ := NQSetup.nq_explicit_module_two_stabilizer_collapse (qtnqS h)
    (commGL_qtnqS_eq_top h) (explicitModule_of_qtnqExplicitModule h hmod) B hBS hB2 P hPS hP2
  have hnofix : ∀ s ∈ qtnqS h, s (Additive.ofMul ⟨v, hvU⟩) ∉ fixGL P := by
    intro s hs hfix
    obtain ⟨l, rfl⟩ := (mem_qtnqS h).mp hs
    set z := (l : G) * v * (l : G)⁻¹ with hz
    have hzU : z ∈ qtnqU L M := (mem_normalizer_iff.mp (hUM (h.l_le l.2)) v).mp hvU
    have hzT : z ∈ T := NQSetup.qtnqU_le_t h hzU
    have hzc : ∀ t ∈ T, t * z = z * t := by
      intro t ht
      have h1 := hfix (ρ ⟨t, h.t_le ht⟩) ⟨⟨t, h.t_le ht⟩, ht, rfl⟩
      have h2 : t * z * t⁻¹ = z := congrArg (fun x : Additive (qtnqU L M) =>
        ((x.toMul : qtnqU L M) : G)) h1
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h2]
    have hz2 : z ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian z hzU
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      QuasithinUnique.mem_quasithinOmegaOneCenter_iff.mpr
        ⟨hzT, mem_centralizer_iff.mpr fun t ht => hzc t ht, hz2⟩
    have hz1 : z ≠ 1 := by
      intro h1
      apply hu1
      have h2 : v = 1 := by
        have : v = (l : G)⁻¹ * z * l := by rw [hz]; group
        rw [this, h1]
        group
      have : u = m * v * m⁻¹ := by rw [hv]; group
      rw [this, h2]
      group
    have hCz := centralizer_le_of_mem_omegaOneCenter h hzZ hz1
    apply hCu
    intro x hx
    have h1 : (l : G) * (m⁻¹ * x * m) * (l : G)⁻¹ ∈ centralizer {z} := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [hz, hv]
      calc (l : G) * (m⁻¹ * x * m) * (l : G)⁻¹ * ((l : G) * (m⁻¹ * u * m) * (l : G)⁻¹)
          = (l : G) * (m⁻¹ * (x * u) * m) * (l : G)⁻¹ := by group
        _ = (l : G) * (m⁻¹ * (u * x) * m) * (l : G)⁻¹ := by rw [hx]
        _ = (l : G) * (m⁻¹ * u * m) * (l : G)⁻¹ * ((l : G) * (m⁻¹ * x * m) * (l : G)⁻¹) := by
          group
    have h2 := hCz h1
    have hlM := h.l_le l.2
    have : x = m * ((l : G)⁻¹ * ((l : G) * (m⁻¹ * x * m) * (l : G)⁻¹) * l) * m⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem hm (M.mul_mem (M.mul_mem (M.inv_mem hlM) h2) hlM)) (M.inv_mem hm)
  have hReq : RX ⊓ centralizer {v} = RX ⊓ centralizer (qtnqU L M : Set G) := by
    apply le_antisymm
    · intro r hr
      obtain ⟨hrRX, hrv⟩ := mem_inf.mp hr
      have hρr : ρ ⟨r, hRXM hrRX⟩ = 1 := by
        refine hcol _ hnofix _ ⟨⟨r, hRXM hrRX⟩, hrRX, rfl⟩ ?_
        rw [hρapply]
        apply Additive.toMul.injective
        apply Subtype.ext
        change r * v * r⁻¹ = v
        rw [mem_centralizer_singleton_iff.mp hrv, mul_inv_cancel_right]
      refine mem_inf.mpr ⟨hrRX, mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 := LinearEquiv.congr_fun hρr (Additive.ofMul ⟨x, hx⟩)
      have h2 : r * x * r⁻¹ = x := congrArg (fun y : Additive (qtnqU L M) =>
        ((y.toMul : qtnqU L M) : G)) h1
      calc x * r = r * x * r⁻¹ * r := by rw [h2]
        _ = r * x := by group
    · exact inf_le_inf_left _ (fun r hr => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hr v hvU).symm))
  have hRn : X ⊔ T ≤ normalizer ((RX ⊓ centralizer {v} : Subgroup G) : Set G) := by
    rw [hReq]
    exact le_trans (le_inf hXTRX (hXTM.trans (hUM.trans
      (normalizer_le_normalizer_centralizer _)))) (inf_normalizer_le_normalizer_inf)
  have hO2map : (CFSG.pCore 2 X).map X.subtype ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ X.subtype_injective]
    exact hO2
  have hO2R : (CFSG.pCore 2 X).map X.subtype ≤ RX ⊓ centralizer {v} :=
    le_inf (pCore_map_le_of_le_normalizer le_sup_left hXTN)
      ((map_subtype_le _).trans hXCv)
  have hQT : Q ≤ T := inf_le_left
  have hQn : T ≤ normalizer (Q : Set G) := by
    have hidx : (Q.subgroupOf T).index = 2 := hTQ
    have hn : (Q.subgroupOf T).Normal := normal_of_index_eq_two hidx
    exact (normal_subgroupOf_iff_le_normalizer hQT).mp hn
  have hXQN : X ⊔ T ≤ normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    refine sup_le ((le_sup_left : X ≤ X ⊔ Q).trans le_normalizer) ?_
    exact (le_inf (hXTN.trans' le_sup_right) hQn).trans (inf_normalizer_le_normalizer_sup X Q)
  have hRO : RX ⊓ centralizer {v} =
      (CFSG.pCore 2 (X ⊔ Q : Subgroup G)).map (X ⊔ Q).subtype := by
    apply le_antisymm
    · refine le_pCore_map_of_le_normalizer ?_ ?_ (hRX2.to_le inf_le_left)
      · exact (inf_le_inf_right _ hRXT).trans le_sup_right
      · exact (sup_le_sup_left hQT X).trans hRn
    · refine le_inf (pCore_map_le_of_le_normalizer (sup_le_sup_left hQT X) hXQN) ?_
      exact (map_subtype_le _).trans (sup_le hXCv inf_le_right)
  have hR1 : RX ⊓ centralizer {v} ≠ ⊥ := fun h1 => hO2map (le_bot_iff.mp (h1 ▸ hO2R))
  refine ⟨hQA, hQG, hTQ, hO2map, hO2R, hReq, hRO, hRn, fun hMG => ?_⟩
  have hXn : (X.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hXM).mpr hMX
  exact centralizer_pushing_core hXM hXn hX2 hMG hXCv hRO hQA hR1 hRn

end Escaping

variable {T L M : Subgroup G}

theorem explicit_module_pushing_core_witness
    (h : QTNQ T L M) (hmod : QTNQExplicitModule L M) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ X : Subgroup G, X ≤ L ∧ (X.subgroupOf L).Characteristic ∧
      X ≤ (CFSG.solvableRadical L).map L.subtype ∧ CFSG.pCore 2 X ≠ ⊥ ∧
      normalizer (X : Set G) = M ∧ NoPQuotient 2 X ∧
      Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p ∧ CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 ∧
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 ∧
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) ∧
      IsFrattiniIrreducible X L ∧
      ⁅L, (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype⁆ ≤
        (CFSG.solvableRadical L).map L.subtype ∧
      (∀ l ∈ L, ∀ r ∈ (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype,
        ∀ x ∈ qtnqU L M, l * (r * x * r⁻¹) * l⁻¹ = r * (l * x * l⁻¹) * r⁻¹) ∧
      ∀ u ∈ qtnqU L M, u ≠ 1 → ¬ centralizer {u} ≤ M → ∃ m ∈ M,
        IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (M ⊓ centralizer {m⁻¹ * u * m}) ∧
        IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (centralizer {m⁻¹ * u * m}) ∧
        (T ⊓ centralizer {m⁻¹ * u * m}).relIndex T = 2 ∧
        (CFSG.pCore 2 X).map X.subtype ≠ ⊥ ∧
        (CFSG.pCore 2 X).map X.subtype ≤
          (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} ∧
        (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} =
          (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
            centralizer (qtnqU L M : Set G) ∧
        (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {m⁻¹ * u * m} =
          (CFSG.pCore 2 (X ⊔ (T ⊓ centralizer {m⁻¹ * u * m}) : Subgroup G)).map
            (X ⊔ (T ⊓ centralizer {m⁻¹ * u * m})).subtype ∧
        X ⊔ T ≤ normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
          centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) ∧
        (CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) = {M} →
          normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
            centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) ≤ M ∧
          (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
              centralizer {m⁻¹ * u * m} =
            (CFSG.pCore 2 (centralizer {m⁻¹ * u * m} ⊓ normalizer
              (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
                centralizer {m⁻¹ * u * m} : Subgroup G) : Set G) : Subgroup G)).map
              (centralizer {m⁻¹ * u * m} ⊓ normalizer
                (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
                  centralizer {m⁻¹ * u * m} : Subgroup G) : Set G)).subtype ∧
          IsSylowOf 2 ((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
              centralizer {m⁻¹ * u * m})
            (⨆ a ∈ M ⊓ centralizer {m⁻¹ * u * m}, CFSG.conjugate
              ((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
                centralizer {m⁻¹ * u * m}) a)) := by
  obtain ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hX2, hexp, hrk, hO2, hNX, hW, hirrL, -, -⟩ :=
    configuration_centralizer_conjugate_rigidity_witness h
  obtain ⟨hnt, hcomm, hU⟩ := rx_action_of_witness (T := T) h hp hXL hNX hexp hW hirrL
  exact ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hO2, hNX, hX2, hexp, hrk, hW, hnt, hirrL, hcomm, hU,
    fun u hu hu1 hCu => pushing_core_of_witness h hmod hp hXL hXRad hX2 hO2 hNX hexp hW hirrL hu
      hu1 hCu⟩

end CFSG.Quasithin.H13.NQRigid
