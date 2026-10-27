module

public import CFSG.Quasithin.H13.NQRigidAsmBasic
public import CFSG.Quasithin.H13.NQRigidCoreQuot
public import CFSG.Quasithin.H13.NQRigidCore
public import CFSG.Quasithin.H13.NQRigidFacts
public import CFSG.Quasithin.H13.NQRigidInputs

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

structure RigidEscape (T L M : Subgroup G) (p : ℕ) (X : Subgroup G) (v : G)
    (K : Subgroup (centralizer ({v} : Set G))) : Prop where
  qtnq : QTNQ T L M
  module : QTNQExplicitModule L M
  prime : p.Prime
  five_le : 5 ≤ p
  le_l : X ≤ L
  char_l : (X.subgroupOf L).Characteristic
  le_rad : X ≤ (CFSG.solvableRadical L).map L.subtype
  core_ne : CFSG.pCore 2 X ≠ ⊥
  normalizer_eq : normalizer (X : Set G) = M
  no_quot : NoPQuotient 2 X
  exponent_eq : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p
  rank_eq : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2
  card_w : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2
  acts_l : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1
  irr_l : IsFrattiniIrreducible X L
  mem_u : v ∈ qtnqU L M
  ne_one : v ≠ 1
  not_le : ¬ centralizer ({v} : Set G) ≤ M
  le_h : X ≤ centralizer ({v} : Set G)
  core_le_q : (CFSG.pCore 2 X).map X.subtype ≤ T ⊓ centralizer {v}
  sylow_a : IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v})
  sylow_h : IsSylowOf 2 (T ⊓ centralizer {v}) (centralizer {v})
  singleton : CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) = {M}
  core_le_r : (CFSG.pCore 2 X).map X.subtype ≤
    (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {v}
  r_eq : (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {v} =
    (CFSG.pCore 2 (X ⊔ (T ⊓ centralizer {v}) : Subgroup G)).map
      (X ⊔ (T ⊓ centralizer {v})).subtype
  r_normalizer : X ⊔ T ≤ normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
    centralizer {v} : Subgroup G) : Set G)
  r_pushing : (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {v} =
    (CFSG.pCore 2 (centralizer {v} ⊓ normalizer
      (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
        centralizer {v} : Subgroup G) : Set G) : Subgroup G)).map
      (centralizer {v} ⊓ normalizer
        (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓
          centralizer {v} : Subgroup G) : Set G)).subtype
  irr_a : IsFrattiniIrreducible X (M ⊓ centralizer {v})
  odd_core : CFSG.pPrimeCore 2 (centralizer ({v} : Set G)) = ⊥
  fitting_le : (CFSG.fittingSubgroup (centralizer ({v} : Set G) ⧸
      CFSG.pCore 2 (centralizer ({v} : Set G)))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))) ≤
    (M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G))
  ccomp : CFSG.IsCComponent K
  quasi : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)
  escapes : ¬ K ≤ normalizer ((X.subgroupOf (centralizer ({v} : Set G)) :
    Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G)))
  comp_e : CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))))
  escapes_e : ¬ K.map (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))) ≤
    normalizer (((X.subgroupOf (centralizer ({v} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))) :
      Subgroup (centralizer ({v} : Set G) ⧸ CFSG.pCore 2 (centralizer ({v} : Set G)))) :
      Set (centralizer ({v} : Set G) ⧸ CFSG.pCore 2 (centralizer ({v} : Set G))))
  core_inf : K ⊓ CFSG.pCore 2 (centralizer ({v} : Set G)) = (CFSG.pCore 2 K).map K.subtype
  x_normalizes : X.subgroupOf (centralizer ({v} : Set G)) ≤
    normalizer (K : Set (centralizer ({v} : Set G)))
  comm_eq : ⁅K, X.subgroupOf (centralizer ({v} : Set G))⁆ = K

theorem two_le_pRank_map_mk {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup H} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (C : Subgroup H) [C.Normal]
    (hC : IsPGroup 2 C) : 2 ≤ CFSG.pRank p (X.map (QuotientGroup.mk' C)) := by
  classical
  have hp := (Fact.out : p.Prime)
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p X))
  let e₀ : (P₀ : Subgroup X) ≃* X ⧸ CFSG.pCore 2 X :=
    MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hXA P₀)
  have hmem : ∀ y : (P₀ : Subgroup X),
      (QuotientGroup.mk' C) ((y : X) : H) ∈ X.map (QuotientGroup.mk' C) :=
    fun y => ⟨(y : X), (y : X).2, rfl⟩
  let ψ : (P₀ : Subgroup X) →* X.map (QuotientGroup.mk' C) :=
    ((QuotientGroup.mk' C).comp (X.subtype.comp (P₀ : Subgroup X).subtype)).codRestrict _ hmem
  have hCp : ¬ p ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := hC.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : ((y : X) : H) ∈ C := by
      have h1 : (QuotientGroup.mk' C) ((y : X) : H) = 1 := congrArg Subtype.val hy
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P₀.isPGroup') y
    have hk' : orderOf ((y : X) : H) = p ^ k := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hk]
    exact Subtype.ext (Subtype.ext (NQTerm.eq_one_of_orderOf_dvd_prime_pow hp hCp hy' hk'.dvd))
  have h1 : CFSG.pRank p (P₀ : Subgroup X) = 2 := by rw [pRank_congr hp.one_lt e₀, hrk]
  have h2 : CFSG.pRank p (P₀ : Subgroup X) ≤ CFSG.pRank p (X.map (QuotientGroup.mk' C)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt ψ hψ
  omega

theorem pCore_map_le_of_sylowTwo {T Y : Subgroup G} (hT : quasithinIsSylowTwo T) (hTY : T ≤ Y) :
    (CFSG.pCore 2 Y).map Y.subtype ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set RY := (CFSG.pCore 2 Y).map Y.subtype with hRY
  have hR2 : IsPGroup 2 RY := CFSG.pCore_isPGroup.map _
  have hYR : Y ≤ normalizer (RY : Set G) := le_normalizer_pCore_map Y
  set T' : Sylow 2 G := hT.1.toSylow hT.2 with hT'
  have hT'T : (T' : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  have hTR : (T' : Subgroup G) ≤ normalizer (RY : Set G) := by
    rw [hT'T]
    exact hTY.trans hYR
  have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hR2 hTR) le_sup_left
  rw [← hT'T, ← h1]
  exact le_sup_right

theorem exists_rigidEscape (hsing : FactWitnessSingleton)
    (hB1 : StmtEscapingComponentAction) {T L M : Subgroup G} (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) {u : G} (hu : u ∈ qtnqU L M) (hu1 : u ≠ 1)
    (hCu : ¬ centralizer ({u} : Set G) ≤ M) :
    ∃ (p : ℕ) (X : Subgroup G) (m : G), m ∈ M ∧
      ∃ K : Subgroup (centralizer ({m⁻¹ * u * m} : Set G)),
        RigidEscape T L M p X (m⁻¹ * u * m) K := by
  classical
  obtain ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hO2, hNX, hX2, hexp, hrk, hW, hLW, hirrL, -, -,
    hpush⟩ := explicit_module_pushing_core_witness h hmod
  obtain ⟨m, hm, hQA, hQH, -, -, hO2R, -, hRXQ, hRn, hsingR⟩ := hpush u hu hu1 hCu
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set v := m⁻¹ * u * m with hv
  have hvU : v ∈ qtnqU L M := conj_mem_qtnqU h hm hu
  have hv1 : v ≠ 1 := by
    intro h1
    apply hu1
    have h2 : u = m * v * m⁻¹ := by rw [hv]; group
    rw [h2, h1, mul_one, mul_inv_cancel]
  have hCv : ¬ centralizer ({v} : Set G) ≤ M := fun hle => hCu (centralizer_le_of_conj hm hle)
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent hexp
  have hS := hsing G T L M h p hp hp5 X hXRad hXchar hO2 hX2 hXA hexp hrk hW hLW hirrL
  obtain ⟨-, hRO, -⟩ := hsingR hS
  obtain ⟨hirrA, hfit⟩ := explicit_module_selected_witness_Fitting_containment h hmod hp hp5 hXL
    hXchar hXRad hNX hX2 hexp hrk hW hLW
  obtain ⟨S₀, hS₀⟩ := hQH.exists_sylow_eq_subgroupOf
  have hSA : (S₀ : Subgroup (centralizer ({v} : Set G))) ≤
      (M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G)) := by
    rw [hS₀]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨h.t_le hx.1, hx.2⟩
  obtain ⟨hFA, hpart⟩ := hfit v hvU hv1 ⟨S₀, hSA⟩
  obtain ⟨hcomm, hcyc⟩ := hpart hCv
  have hodd := NQSetup.internal_centralizer_Fitting_containment_kills_odd_core h hvU hv1 hFA
  set H := centralizer ({v} : Set G) with hH
  have hXH : X ≤ H := by
    intro x hx
    rw [hH, mem_centralizer_singleton_iff]
    obtain ⟨l, hl, rfl⟩ := hXRad hx
    exact NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h hvU)
  set X' := X.subgroupOf H with hX'
  have hXs : Group.IsSolvable X' :=
    isSolvable_of_isPGroup_quotient_pCore (isPGroup_coreQuot_subgroupOf hXH hXA)
  have hC2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hCn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hrk' : CFSG.pRank p (X' ⧸ CFSG.pCore 2 X') = 2 := by
    rw [pRank_congr hp.one_lt (coreQuotEquivSubgroupOf hXH), hrk]
  have hrank2 := two_le_pRank_map_mk hp2 (isPGroup_coreQuot_subgroupOf hXH hXA) hrk'
    (CFSG.pCore 2 H) hC2
  obtain ⟨K, hKc, hKq, hKX, hJc, hJX, hKC⟩ :=
    NQBlock.cyclic_prime_core_Fitting_centralization_produces_escaping_Ccomponent hXs hrank2 hcyc
      hcomm
  have hSQT := isStronglyQuasithin_centralizer h hvU hv1
  have hCsolv : Group.IsSolvable (CFSG.pCore 2 H) := by
    have : Group.IsNilpotent (CFSG.pCore 2 H) := hC2.isNilpotent
    infer_instance
  have hrkE : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ CFSG.pCore 2 H) ≤ 2 := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    have h1 := CFSG.SectionRank.pRank_quotient_two_group _ hC2 hr hr2
    have h2 := hSQT r hr hr2
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2 ⊢
    exact h1.trans_le h2
  have hX'no : NoPQuotient 2 X' :=
    NoPQuotient.of_surjective (subgroupOfEquivOfLe hXH).symm.toMonoidHom
      (subgroupOfEquivOfLe hXH).symm.surjective hX2
  have hidx : ∀ D : Subgroup X', D.Normal → D.index ≠ 2 :=
    fun D hD => index_ne_two_of_noPQuotient hX'no D hD
  obtain ⟨hXK, hKXc⟩ := hB1 H (CFSG.pCore 2 H) hCsolv X' hidx hrkE K hKc hJc
  have hcoreQ : (CFSG.pCore 2 X).map X.subtype ≤ T ⊓ centralizer {v} := by
    refine le_inf ?_ ((map_subtype_le _).trans hXH)
    exact (hO2R.trans inf_le_left).trans (pCore_map_le_of_sylowTwo h.sylow le_sup_right)
  exact ⟨p, X, m, hm, K, ⟨h, hmod, hp, hp5, hXL, hXchar, hXRad, hO2, hNX, hX2, hexp, hrk, hW,
    hLW, hirrL, hvU, hv1, hCv, hXH, hcoreQ, hQA, hQH, hS, hO2R, hRXQ, hRn, hRO, hirrA v hvU,
    hodd, hFA, hKc, hKq, hKX, hJc, hJX, hKC, hXK, hKXc hJX⟩⟩

end CFSG.Quasithin.H13.NQRigid
