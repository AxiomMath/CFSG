module

public import CFSG.Quasithin.H13.NQRigidAsmSubgroupOf
public import CFSG.Quasithin.SteinbergCCRankOneSplitting
public import CFSG.Quasithin.SteinbergCDCorePlaneFactorPair
public import CFSG.Quasithin.SteinbergCDSwappedFactorsCoreSupports
public import CFSG.Quasithin.H13.NQRigidAsmPairData
public import CFSG.Quasithin.H13.NQRigidAsmSingleData
public import CFSG.Quasithin.H13.NQRigidAsmTransport
public import CFSG.Quasithin.H13.NQRigidSporadic
public import CFSG.Quasithin.H13.NQTermComponentOrbits
public import CFSG.Quasithin.H13.NQTermShortCcomponent
public import CFSG.Quasithin.SteinbergCDPermutableIntersection

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj coreQuotConj frattiniQuotConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isElementaryAbelian_coreQuot {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p) :
    CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X) :=
  { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
    exponent_dvd_p := by rw [hexp] }

theorem coreQuotConj_irreducible_of {L' : Type*} [Group L'] [Finite L'] {X : Subgroup L'}
    [X.Normal] (hΦ : frattini (X ⧸ CFSG.pCore 2 X) = ⊥)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : L', ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ U : Subgroup (X ⧸ CFSG.pCore 2 X), (∀ l : L', ∀ u ∈ U, coreQuotConj X l u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  set q := QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X)) with hq
  have hqi : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, hq, QuotientGroup.ker_mk', hΦ]
  rcases hirr (U.map q) (by
    rintro l _ ⟨u, hu, rfl⟩
    exact ⟨coreQuotConj X l u, hU l u hu, rfl⟩) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : q u ∈ U.map q := ⟨u, hu, rfl⟩
    rw [h0, mem_bot] at h1
    exact (mem_bot).mpr (hqi (h1.trans (map_one q).symm))
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : q u ∈ U.map q := ht ▸ mem_top _
    obtain ⟨u', hu', huu⟩ := h1
    rwa [← hqi huu]

theorem rigidPair_false (hcen : FactCenterOddPart)
    (hsect : FactSimpleQuotientSQT) (hthin : FactThinCentralQuotient)
    (hquad : FactQuadraticOffender) (hOD : StmtOuterDerivedCoprime) (hB3 : StmtPairContainment)
    (hB8 : StmtCPUOffenderSection) (hB9 : StmtCPUShortBlock)
    {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (E : RigidEscape T L M p X v K)
    (hred : ¬ IsFrattiniIrreducible (X.subgroupOf (centralizer ({v} : Set G)))
      ((M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G)) ⊓
        normalizer (K : Set (centralizer ({v} : Set G))))) : False := by
  classical
  have h := E.qtnq
  have hp := E.prime
  have hp5 := E.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hXH : X ≤ centralizer ({v} : Set G) := E.le_h
  let H := centralizer ({v} : Set G)
  have hH : H = centralizer ({v} : Set G) := rfl
  set A := (M ⊓ H).subgroupOf H with hA
  set X' := X.subgroupOf H with hX'
  set C := CFSG.pCore 2 H with hC
  set π := QuotientGroup.mk' C with hπ
  have hC2 : IsPGroup 2 C := CFSG.pCore_isPGroup
  have hCn : C.Normal := CFSG.pCore_normal
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent C := hC2.isNilpotent
    infer_instance
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent E.exponent_eq
  have hX'A : IsPGroup p (X' ⧸ CFSG.pCore 2 X') := isPGroup_coreQuot_subgroupOf hXH hXA
  obtain ⟨hX'2, hexp', hrk', hirrA'⟩ :=
    subgroupOf_transport hXH (inf_le_right : M ⊓ H ≤ H) E.no_quot E.exponent_eq E.rank_eq
      hp.one_lt E.irr_a
  have hW' : Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) = p ^ 2 := by
    rw [card_frattini_subgroupOf hXH, E.card_w]
  have hX'O2 : CFSG.pCore 2 X' ≠ ⊥ := by
    intro h0
    apply E.core_ne
    rw [← CFSG.pCore_map_iso 2 (subgroupOfEquivOfLe hXH), h0, Subgroup.map_bot]
  have hMX : M ≤ normalizer (X : Set G) := E.normalizer_eq.ge
  have hXM : X ≤ M := E.le_l.trans h.l_le
  have hX'A' : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨hXM (mem_subgroupOf.mp hx), x.2⟩
  have hAN : A ≤ normalizer (X' : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hMX (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'Cn : (CFSG.pCore 2 X').Normal := CFSG.pCore_normal
  set QX := (CFSG.pCore 2 X').map X'.subtype with hQX
  have hAQ : A ≤ normalizer (QX : Set H) :=
    hAN.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hKnn : ¬ K.Normal := by
    intro hKn
    apply hred
    rw [normalizer_eq_top_iff.mpr hKn, inf_top_eq]
    exact hirrA'
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H, CFSG.conjugate K h₀ ≠ K := by
    by_contra hall
    push Not at hall
    apply hKnn
    refine ⟨fun n hn g => ?_⟩
    have h1 := hall g⁻¹
    rw [CFSG.conjugate, inv_inv] at h1
    rw [← h1]
    exact ⟨n, hn, rfl⟩
  set K₂ := CFSG.conjugate K h₀ with hK₂
  have hK₂c : CFSG.IsCComponent K₂ := isCComponent_conjugate E.ccomp h₀
  have hSQT := isStronglyQuasithin_centralizer h E.mem_u E.ne_one
  have hrkE : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ C) ≤ 2 := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    have h1 := CFSG.SectionRank.pRank_quotient_two_group _ hC2 hr hr2
    have h2 := hSQT r hr hr2
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2 ⊢
    exact h1.trans_le h2
  have horb := (NQTerm.odd_rank_two_component_orbits_and_normalization hrkE).1 _ E.comp_e
  have hdich := conjugate_dichotomy hCsolv E.ccomp horb hh₀
  set J₁ := K.map π with hJ₁
  set J₂ := K₂.map π with hJ₂
  have hJ₂c : CFSG.IsComponent J₂ := by
    rw [hJ₂, hK₂, map_conjugate_hom]
    exact NQTerm.isComponent_conjugate E.comp_e _
  have hJne : J₁ ≠ J₂ := fun heq =>
    hh₀ (eq_of_map_eq_of_isCComponent hCsolv hK₂c E.ccomp heq.symm)
  have hJcomm : ⁅J₁, J₂⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute E.comp_e hJ₂c with h1 | h1
    · exact absurd h1 hJne
    · exact h1
  have hK₂N : K₂ ≤ normalizer (K : Set H) := normalizer_ge_of_commute_images hCsolv E.ccomp hJcomm
  have hKN₂ : K ≤ normalizer (K₂ : Set H) := by
    refine normalizer_ge_of_commute_images hCsolv hK₂c ?_
    rw [commutator_comm]
    exact hJcomm
  have hXK₂ : X' ≤ normalizer (K₂ : Set H) := by
    intro x hx
    rw [← conjugate_eq_self_iff]
    rcases hdich (h₀ * x) with h1 | h1
    · exfalso
      have h2 : CFSG.conjugate K x = K := conjugate_eq_self_iff.mpr (E.x_normalizes hx)
      rw [← conjugate_conjugate] at h1
      apply hh₀
      have h3 : CFSG.conjugate K₂ x = CFSG.conjugate K x := by rw [h2]; exact h1
      exact conjugate_injective h3
    · rw [← conjugate_conjugate] at h1
      rw [h1]
  have hHSQ := isSQTKCat_centralizer h E.mem_u E.ne_one
  have hESQ := isSQTKCat_quotient_pCore hHSQ
  have hJ₁SQ : CFSG.SectionRank.IsSQTKCat J₁ := hESQ.subgroup J₁
  have hZJ : ¬ p ∣ Nat.card (center J₁) := hcen _ E.comp_e.1 hJ₁SQ p hp hp5
  have hJconj : CFSG.conjugate J₁ (π h₀) ≠ J₁ := by
    rw [hJ₁, ← map_conjugate_hom]
    exact fun h1 => hJne h1.symm
  have hOut := hOD _ hESQ J₁ E.comp_e ⟨π h₀, hJconj⟩ p hp hp5
  have hpH : CFSG.pRank p H ≤ 2 := hSQT p hp hp2
  have hlat := isFrattiniLatticeIrreducible_of hirrA'
  have hdim : p ^ 2 ≤ Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) :=
    hW'.ge
  have hJX : ⁅J₁, X'.map π⁆ ≠ ⊥ := by
    intro h1
    apply E.escapes_e
    rw [commutator_eq_bot_iff_le_centralizer] at h1
    exact h1.trans (centralizer_le_normalizer _)
  have hJ0X : ⁅(K ⊔ K₂).map π, X'.map π⁆ ≠ ⊥ := fun h1 =>
    hJX (le_bot_iff.mp ((commutator_mono (map_mono le_sup_left) le_rfl).trans h1.le))
  obtain ⟨hXK₀, hK₀n, -, -, hrk₁, hrk₂⟩ :=
    hB3 H p hp hp2 hpH C hC2 K K₂ E.ccomp hh₀ hdich ⟨h₀, rfl⟩ E.comp_e hZJ hOut X' A
      (CFSG.pCore 2 X') hX'A' hAQ hAN CFSG.pCore_isPGroup (pow_mem_pCore_of_exponent hexp')
      hX'2 hdim hlat hJ0X
  obtain ⟨PH, hPH⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X'
  have hPHX : PH ≤ X' := hPH.le
  have hPHnc : ¬ IsCyclic PH := NQCat.not_isCyclic_of_isSylowOf_of_card_eq_sq hX'A hW' hPH
  have hPexp : ∀ x ∈ PH, x ^ p = 1 := by
    obtain ⟨P₀, hP₀⟩ := hPH.exists_sylow_eq_subgroupOf
    let e₀ : (P₀ : Subgroup X') ≃* X' ⧸ CFSG.pCore 2 X' :=
      MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hX'A P₀)
    intro x hx
    have hxX : x ∈ X' := hPHX hx
    have hxP : (⟨x, hxX⟩ : X') ∈ (P₀ : Subgroup X') := by rw [hP₀]; exact hx
    have h0 : ∀ y : X' ⧸ CFSG.pCore 2 X', y ^ p = 1 := fun y =>
      hexp' ▸ Monoid.pow_exponent_eq_one y
    have h1 : e₀ (⟨⟨x, hxX⟩, hxP⟩ ^ p) = 1 := by
      rw [map_pow]
      exact h0 _
    have h2 := e₀.injective (h1.trans (map_one e₀).symm)
    have h3 := congrArg (fun y : (P₀ : Subgroup X') => ((y : X') : H)) h2
    simpa using h3
  set K₀ := K ⊔ K₂ with hK₀
  have hK₁K₀ : K ≤ K₀ := le_sup_left
  have hK₂K₀ : K₂ ≤ K₀ := le_sup_right
  have hPK₀ : PH ≤ K₀ := hPHX.trans hXK₀
  have hK₁n : (K.subgroupOf K₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₁K₀).mpr (sup_le le_normalizer hK₂N)
  have hK₂n : (K₂.subgroupOf K₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₂K₀).mpr (sup_le hKN₂ le_normalizer)
  have hsup : K.subgroupOf K₀ ⊔ K₂.subgroupOf K₀ = ⊤ := by
    rw [← subgroupOf_sup hK₁K₀ hK₂K₀, subgroupOf_self]
  have hI : ¬ p ∣ Nat.card (K ⊓ K₂ : Subgroup H) := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (K ⊓ K₂ : Subgroup H)) p hdvd
    have hxo : orderOf (x : H) = p := by rw [Subgroup.orderOf_coe, hx]
    have hxJ₁ : π (x : H) ∈ J₁ := ⟨x, (mem_inf.mp x.2).1, rfl⟩
    have hxJ₂ : π (x : H) ∈ J₂ := ⟨x, (mem_inf.mp x.2).2, rfl⟩
    have hcent : (⟨π (x : H), hxJ₁⟩ : J₁) ∈ center J₁ := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := (commutator_eq_bot_iff_le_centralizer.mp hJcomm) y.2
      exact (mem_centralizer_iff.mp h1 _ hxJ₂).symm
    have hord : orderOf (⟨π (x : H), hxJ₁⟩ : J₁) = p := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (π (x : H)) = p
      have h1 : orderOf (π (x : H)) ∣ p := by
        rw [← hxo]
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
      · exfalso
        rw [orderOf_eq_one_iff] at h2
        have hxC : (x : H) ∈ C := (QuotientGroup.eq_one_iff _).mp h2
        have hCp : ¬ p ∣ Nat.card C := by
          obtain ⟨k, hk⟩ := hC2.exists_card_eq
          rw [hk]
          intro hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
        have h3 := NQTerm.eq_one_of_orderOf_dvd_prime_pow (k := 1) hp hCp hxC
          (by rw [hxo, pow_one])
        rw [h3, orderOf_one] at hxo
        exact hp.one_lt.ne hxo
      · exact h2
    apply hZJ
    have h4 := Subgroup.orderOf_dvd_natCard (center J₁) hcent
    rwa [hord] at h4
  have hrkK : ∀ K' : Subgroup H, CFSG.IsCComponent K' → CFSG.pRank p (K'.map π) = 1 →
      CFSG.pRank p K' ≤ 1 := by
    intro K' hK'c hK'r
    have hcap : (CFSG.pCore 2 K').map K'.subtype = K' ⊓ π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      have h1 := CFSG.LocalCores.prime_set_core_subnormal_intersection {⟨2, Nat.prime_two⟩}
        hK'c.2.2.1
      rw [← CFSG.LinearGroups.pCore_eq_piCore Nat.prime_two,
        ← CFSG.LinearGroups.pCore_eq_piCore Nat.prime_two] at h1
      exact h1
    have : (CFSG.pCore 2 K').Normal := CFSG.pCore_normal
    obtain ⟨e⟩ := NQBlock.nonempty_quotient_mulEquiv π rfl (CFSG.pCore 2 K') hcap
    have hK'p : ¬ p ∣ Nat.card (CFSG.pCore 2 K') := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K')).exists_card_eq
      rw [hk]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_quotient_eq _ hK'p,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_congr hp.one_lt e]
    exact hK'r.le
  have hrkK₁ := hrkK K E.ccomp hrk₁
  have hrkK₂ := hrkK K₂ hK₂c hrk₂
  have hPK₀p : IsPGroup p (PH.subgroupOf K₀) := by
    rw [← comap_subtype]
    exact hPH.isPGroup.comap_subtype
  have hPK₀nc : ¬ IsCyclic (PH.subgroupOf K₀) := fun hc =>
    hPHnc (isCyclic_of_surjective (subgroupOfEquivOfLe hPK₀).toMonoidHom
      (subgroupOfEquivOfLe hPK₀).surjective)
  have hIK₀ : ¬ p ∣ Nat.card (K.subgroupOf K₀ ⊓ K₂.subgroupOf K₀ : Subgroup K₀) := by
    rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hK₁K₀)]
    exact hI
  have hrkK₁' : CFSG.pRank p (K.subgroupOf K₀) ≤ 1 := by
    rw [pRank_congr hp.one_lt (subgroupOfEquivOfLe hK₁K₀)]
    exact hrkK₁
  have hrkK₂' : CFSG.pRank p (K₂.subgroupOf K₀) ≤ 1 := by
    rw [pRank_congr hp.one_lt (subgroupOfEquivOfLe hK₂K₀)]
    exact hrkK₂
  have hexpK₀ : ∀ x ∈ PH.subgroupOf K₀, x ^ p = 1 := by
    intro x hx
    apply Subtype.ext
    rw [coe_pow]
    exact hPexp _ (mem_subgroupOf.mp hx)
  obtain ⟨hPcard, hP₁card, hP₂card, hdisj, hPcomm, hPsup, -⟩ :=
    SteinbergCC.rank_one_normal_product_exponent_prime_intersection_splitting hp hsup hIK₀
      hrkK₁' hrkK₂' hPK₀p hPK₀nc hexpK₀
  rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hPK₀)] at hP₁card
  rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hPK₀)] at hP₂card
  rw [← subgroupOf_inf, ← subgroupOf_inf, ← subgroupOf_sup (inf_le_left.trans hPK₀)
    (inf_le_left.trans hPK₀)] at hPsup
  have hPsup' : (PH ⊓ K) ⊔ (PH ⊓ K₂) = PH :=
    subgroupOf_injective_of_le (sup_le (inf_le_left.trans hPK₀) (inf_le_left.trans hPK₀)) hPK₀
      hPsup
  have hPinf : (PH ⊓ K) ⊓ (PH ⊓ K₂) = ⊥ := by
    have h1 := disjoint_iff.mp hdisj
    rw [← subgroupOf_inf, ← subgroupOf_inf, ← subgroupOf_inf] at h1
    exact (subgroupOf_eq_bot_iff_of_le (inf_le_left.trans (inf_le_left.trans hPK₀))).mp h1
  have hperm : ∀ y : H, ({CFSG.conjugate K y, CFSG.conjugate K₂ y} : Set (Subgroup H)) =
      {K, K₂} := by
    intro y
    have hKy := hdich y
    have hK₂y : CFSG.conjugate K₂ y = K ∨ CFSG.conjugate K₂ y = K₂ := by
      rw [hK₂, conjugate_conjugate]
      rcases hdich (h₀ * y) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    have hne : CFSG.conjugate K y ≠ CFSG.conjugate K₂ y := fun h1 =>
      hh₀ (conjugate_injective h1).symm
    rcases hKy with h1 | h1 <;> rcases hK₂y with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
    · exact absurd (h1.trans h2.symm) hne
  set R := (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {v} with hR
  have hRH : R ≤ H := inf_le_right
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup.map _).to_le inf_le_left
  obtain ⟨Q', hQ'⟩ := E.sylow_h.exists_sylow_eq_subgroupOf
  set Y := X' ⊔ (Q' : Subgroup H) with hY
  have hXY : X' ≤ Y := le_sup_left
  have hQ'A : (Q' : Subgroup H) ≤ A := by
    rw [hQ']
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨h.t_le hx.1, hx.2⟩
  have hXYn : (X'.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXY).mpr (sup_le le_normalizer (hQ'A.trans hAN))
  have hcardX : Nat.card (X' ⧸ CFSG.pCore 2 X') = p ^ 2 := by
    obtain ⟨P₀, hP₀⟩ := hPH.exists_sylow_eq_subgroupOf
    rw [← Nat.card_congr (MulEquiv.ofBijective _
      (NQTerm.sylow_bijective_coreQuot hp2 hX'A P₀)).toEquiv, hP₀,
      card_subgroupOf_of_le hPHX]
    rw [← hPcard, card_subgroupOf_of_le hPK₀]
  have hRY : R.subgroupOf H ≤ Y := by
    intro r hr
    have hrR : (r : G) ∈ (CFSG.pCore 2 (X ⊔ (T ⊓ centralizer {v}) : Subgroup G)).map
        (X ⊔ (T ⊓ centralizer {v})).subtype := by
      rw [← E.r_eq]
      exact mem_subgroupOf.mp hr
    have h1 := (map_subtype_le _ : _ ≤ X ⊔ (T ⊓ centralizer {v})) hrR
    have h2 : (X ⊔ (T ⊓ centralizer {v})).subgroupOf H = Y := by
      rw [subgroupOf_sup hXH inf_le_right, hY, hQ']
    rw [← h2]
    exact mem_subgroupOf.mpr h1
  have hRYn : ((R.subgroupOf H).subgroupOf Y).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hRY).mpr ?_
    have h1 : X ⊔ (T ⊓ centralizer {v}) ≤ normalizer (R : Set G) := by
      have h2 := le_normalizer_pCore_map (X ⊔ (T ⊓ centralizer {v}))
      rw [← E.r_eq] at h2
      exact h2
    intro y hy
    have hyG : (y : G) ∈ X ⊔ (T ⊓ centralizer {v}) := by
      have h2 : Y.map H.subtype = X ⊔ (T ⊓ centralizer {v}) := by
        rw [hY, Subgroup.map_sup, hQ', hX', subgroupOf_map_subtype, subgroupOf_map_subtype,
          inf_of_le_left hXH, inf_of_le_left inf_le_right]
      rw [← h2]
      exact ⟨y, hy, rfl⟩
    exact subgroupOf_le_normalizer_of_le (L := H) h1 (mem_subgroupOf.mpr hyG)
  have hRH2 : IsPGroup 2 (R.subgroupOf H) := by
    rw [← comap_subtype]
    exact hR2.comap_subtype
  obtain ⟨hfp, -, -, -, -, -, -⟩ :=
    SteinbergCD.normal_prime_core_fixes_ambient_coprime_plane_factor_pair Nat.prime_two hp
      (Ne.symm hp2) hXY hXYn hcardX (fun y _ => hperm y) (E.x_normalizes) hXK₂ hPH hPinf
      hP₁card hP₂card
  have hRK : R.subgroupOf H ≤ normalizer (K : Set H) :=
    ((hfp _ hRY hRYn hRH2).1).trans inf_le_left
  have hRpush := eq_pCore_normalizer_subgroupOf hRH E.r_pushing
  have hRchar := normalizer_le_subgroupOf_of_characteristic hRH (fun D hD hD1 => by
    have := hD
    exact normalizer_le_of_characteristic_of_singleton E.singleton hR2 E.r_normalizer D hD1)
  have hKA : ¬ K ≤ A := fun hle => E.escapes (hle.trans hAN)
  have hKK₂ : ⁅K, K₂⁆ = ⊥ := by
    by_cases hKq : CFSG.IsQuasisimple K
    · have hKc : CFSG.IsComponent K := ⟨hKq, E.ccomp.2.2.1⟩
      have hK₂q : CFSG.IsComponent K₂ := NQTerm.isComponent_conjugate hKc h₀
      rcases CFSG.LocalCores.distinct_components_commute hKc hK₂q with h1 | h1
      · exact absurd h1.symm hh₀
      · exact h1
    · have hF := generalizedFitting_eq_pCore_of_not_quasisimple E.odd_core E.ccomp hKq
      obtain ⟨W, _, _, _, _, L₁, B₁, hLq, hirr, hBe, hB1, hBN, hquadB, hoff, ⟨e⟩⟩ :=
        hB8 H (R.subgroupOf H) hRH2 hRpush K E.ccomp hF E.quasi hRK A hKA hRchar
      have : Finite (Module.End (ZMod 2) W) :=
        Finite.of_injective (fun f : Module.End (ZMod 2) W => (f : W → W)) LinearMap.coe_injective
      have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
      have hSs : IsSimpleGroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
        E.quasi.2.1
      have hSnab := E.quasi.2.2
      obtain ⟨-, hScat⟩ := hsect _ hKSQ (center _) hSs hSnab
      have hcap : (CFSG.pCore 2 K).map K.subtype = K ⊓ π.ker := by
        rw [hπ, QuotientGroup.ker_mk']
        exact E.core_inf.symm
      obtain ⟨eJ⟩ := NQBlock.nonempty_quotient_mulEquiv π rfl (CFSG.pCore 2 K) hcap
      let eS : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* (J₁ ⧸ center J₁) :=
        QuotientGroup.congr _ _ eJ (map_center_mulEquiv eJ)
      have hthinS : ∀ r : ℕ, r.Prime → r ≠ 2 →
          CFSG.pRank r (L₁ ⧸ center L₁) ≤ 1 := by
        intro r hr hr2
        rw [pRank_congr hr.one_lt (e.trans eS)]
        exact hthin _ hESQ J₁ E.comp_e (π h₀) hJconj r hr hr2
      have hcatL : CFSG.Blueprint.Catalog (L₁ ⧸ center L₁) :=
        (CFSG.SectionRank.catalog_congr e).mpr hScat
      have hP₁K : PH ⊓ K ≤ K := inf_le_right
      have hP₁p : IsPGroup p ((PH ⊓ K).subgroupOf K) := by
        rw [← comap_subtype]
        exact (hPH.isPGroup.to_le inf_le_left).comap_subtype
      have hσker := not_dvd_card_ker_coreCenterQuot hp hp2 (hcen _ E.quasi hKSQ p hp hp5)
      have hσinj := injective_of_not_dvd_card_ker hp (coreCenterQuot K) hσker hP₁p
      set D₀ := ((PH ⊓ K).subgroupOf K).map (coreCenterQuot K) with hD₀
      have hrange : ((coreCenterQuot K).comp ((PH ⊓ K).subgroupOf K).subtype).range = D₀ := by
        rw [MonoidHom.range_comp, range_subtype]
      have hD₀card : Nat.card D₀ = p := by
        rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv,
          card_subgroupOf_of_le hP₁K]
        exact hP₁card
      have hQ'top : IsSylowOf 2 (Q' : Subgroup H) ⊤ := by
        rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
        exact ⟨le_top, Q'.isPGroup', Q'.not_dvd_index⟩
      have hQK₀ : IsSylowOf 2 ((Q' : Subgroup H) ⊓ K₀) K₀ :=
        hQ'top.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hK₀n).ge
      have hQK : IsSylowOf 2 ((Q' : Subgroup H) ⊓ K) K := by
        have h1 := hQK₀.inf_of_le_normalizer hK₁K₀ (sup_le le_normalizer hK₂N)
        rwa [inf_assoc, inf_of_le_right hK₁K₀] at h1
      have hOQ : QX ≤ (Q' : Subgroup H) := by
        rw [hQ']
        intro x hx
        rw [mem_subgroupOf]
        have h1 : (x : G) ∈ QX.map H.subtype := ⟨x, hx, rfl⟩
        rw [hQX, CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX',
          subgroupOf_map_subtype, inf_of_le_left hXH] at h1
        exact E.core_le_q h1
      have hPQ' : (PH : Set H) * ((Q' : Subgroup H) : Set H) =
          ((Q' : Subgroup H) : Set H) * (PH : Set H) :=
        mul_comm_sylow_of_core_le hX'A hPH (hQ'A.trans hAN) hOQ
      have hcop : Nat.Coprime (Nat.card PH) (Nat.card (Q' : Subgroup H)) := by
        obtain ⟨a, ha⟩ := hPH.isPGroup.exists_card_eq
        obtain ⟨b, hb⟩ := Q'.isPGroup'.exists_card_eq
        rw [ha, hb]
        exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      obtain ⟨-, -, hPQK⟩ :=
        SteinbergCD.coprime_permutable_product_normalized_subgroup_intersection hcop hPQ'
          (hPHX.trans E.x_normalizes)
      obtain ⟨QKs, hQKs⟩ := hQK.exists_sylow_eq_subgroupOf
      have hPQKK : (((PH ⊓ K).subgroupOf K : Subgroup K) : Set K) * ((QKs : Subgroup K) : Set K) =
          ((QKs : Subgroup K) : Set K) * (((PH ⊓ K).subgroupOf K : Subgroup K) : Set K) := by
        apply Set.image_injective.mpr K.subtype_injective
        rw [Set.image_mul, Set.image_mul, ← coe_map, ← coe_map, hQKs, subgroupOf_map_subtype,
          subgroupOf_map_subtype, inf_of_le_left hP₁K, inf_of_le_left inf_le_right, hPQK]
      set T₀ := QKs.mapSurjective (coreCenterQuot_surjective K) with hT₀
      have hDT₀ : (D₀ : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
          ((T₀ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
          ((T₀ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
            ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
            D₀ := by
        rw [hT₀, Sylow.coe_mapSurjective, hD₀]
        exact map_mul_comm_of_mul_comm (coreCenterQuot K) hPQKK
      set D := D₀.map e.symm.toMonoidHom with hD
      have hDcard : Nat.card D = p := by
        rw [hD, card_map_of_injective e.symm.injective, hD₀card]
      have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
      set Tℓ := T₀.mapSurjective hes with hTℓ
      have hDT : (D : Set (L₁ ⧸ center L₁)) *
          ((Tℓ : Subgroup (L₁ ⧸ center L₁)) : Set (L₁ ⧸ center L₁)) =
          ((Tℓ : Subgroup (L₁ ⧸ center L₁)) : Set (L₁ ⧸ center L₁)) *
            (D : Set (L₁ ⧸ center L₁)) := by
        rw [hTℓ, Sylow.coe_mapSurjective, hD]
        exact map_mul_comm_of_mul_comm e.symm.toMonoidHom hDT₀
      obtain ⟨f, hf, F, hFf, hFt, hFcard, ⟨θ⟩⟩ := hquad W L₁ hLq hirr hcatL hthinS p hp hp5 D
        hDcard Tℓ hDT B₁ hBe hB1 hBN hquadB hoff
      have hShort := hB9 H (R.subgroupOf H) hRH2 hRpush K E.ccomp hF E.quasi hRK A hKA hRchar f
        hf F hFcard ⟨e.symm.trans θ⟩
      exact NQTerm.short_Ccomponent_centralizes_every_distinct_Ccomponent E.ccomp hK₂c
        (Ne.symm hh₀) hShort
  obtain ⟨h₁, hh₁A, hh₁N⟩ : ∃ h₁ ∈ A, h₁ ∉ normalizer (K : Set H) := by
    by_contra hall
    push Not at hall
    apply hred
    rw [inf_of_le_left fun a ha => hall a ha]
    exact hirrA'
  have hK₁h : CFSG.conjugate K h₁ = K₂ := by
    rcases hdich h₁ with h1 | h1
    · exact absurd (conjugate_eq_self_iff.mp h1) hh₁N
    · exact h1
  have hK₂h : CFSG.conjugate K₂ h₁ = K := by
    have h1 := hperm h₁
    rw [hK₁h] at h1
    have h2 : CFSG.conjugate K₂ h₁ ∈ ({K, K₂} : Set (Subgroup H)) := by
      rw [← h1]
      exact Set.mem_insert_of_mem _ rfl
    rcases h2 with h2 | h2
    · exact h2
    · exfalso
      apply hh₀
      exact conjugate_injective (h2.trans hK₁h.symm)
  have hXQP : QX ⊔ PH = X' := by
    apply le_antisymm (sup_le (map_subtype_le _) hPHX)
    intro x hx
    obtain ⟨y, hyP, hyx⟩ := NQSetup.exists_mem_sylow_mk_eq hX'A hPH ⟨x, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyx
    have h1 : (y : H)⁻¹ * x ∈ QX := ⟨y⁻¹ * ⟨x, hx⟩, QuotientGroup.eq.mp hyx, rfl⟩
    have h2 : x = (y : H) * ((y : H)⁻¹ * x) := by group
    rw [h2]
    exact mul_mem (le_sup_right (a := QX) hyP) (le_sup_left (b := PH) h1)
  have hQX1 : QX ≠ ⊥ := by
    rw [hQX, Ne, map_eq_bot_iff_of_injective _ X'.subtype_injective]
    exact hX'O2
  obtain ⟨hA₁K, hA₂K, hPA₁, hPA₂, hQA₁A₂, hA₁A₂, hA₁P₂, hA₂P₁, hA₁P₁, hA₂P₂, -⟩ :=
    SteinbergCD.commuting_swapped_factors_produce_full_core_supports Nat.prime_two hp
      (Ne.symm hp2) hKK₂ hXK₀ hQX1 hX'2 hPH hXQP hP₁card hP₂card hPsup' (hAN hh₁A) hK₁h hK₂h
  set φ : Subgroup H → Subgroup L := fun S => (S.map H.subtype).subgroupOf L with hφ
  have hXL : X ≤ L := E.le_l
  have hX'G : X'.map H.subtype = X := by
    rw [hX', subgroupOf_map_subtype, inf_of_le_left hXH]
  have hleL : ∀ S : Subgroup H, S ≤ X' → S.map H.subtype ≤ L := fun S hS =>
    (map_mono hS).trans (hX'G.le.trans hXL)
  have hQXG : QX.map H.subtype = (CFSG.pCore 2 X).map X.subtype := by
    rw [hQX, CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX'G]
  have hQXL : φ QX = (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype := by
    rw [pCore_subgroupOf_of_le hXL]
    show (QX.map H.subtype).subgroupOf L = _
    rw [hQXG]
  have hφle : ∀ {S₁ S₂ : Subgroup H}, S₁ ≤ S₂ → φ S₁ ≤ φ S₂ := fun h12 =>
    comap_mono (map_mono h12)
  have hφcard : ∀ S : Subgroup H, S ≤ X' → Nat.card (φ S) = Nat.card S := fun S hS => by
    rw [hφ]
    dsimp only
    rw [card_subgroupOf_of_le (hleL S hS), card_map_of_injective H.subtype_injective]
  have hφsup : ∀ S₁ S₂ : Subgroup H, S₁ ≤ X' → S₂ ≤ X' → φ (S₁ ⊔ S₂) = φ S₁ ⊔ φ S₂ :=
    fun S₁ S₂ h₁ h₂ => by
      rw [hφ]
      dsimp only
      rw [Subgroup.map_sup, subgroupOf_sup (hleL S₁ h₁) (hleL S₂ h₂)]
  have hφinf : ∀ S₁ S₂ : Subgroup H, φ (S₁ ⊓ S₂) = φ S₁ ⊓ φ S₂ := fun S₁ S₂ => by
    rw [hφ]
    dsimp only
    rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, subgroupOf_inf]
  have hφbot : ∀ S : Subgroup H, S ≤ X' → (φ S = ⊥ ↔ S = ⊥) := fun S hS => by
    rw [hφ]
    dsimp only
    rw [subgroupOf_eq_bot_iff_of_le (hleL S hS), map_eq_bot_iff_of_injective _
      H.subtype_injective]
  have hφcomm : ∀ S₁ S₂ : Subgroup H, S₁ ≤ X' → S₂ ≤ X' → φ ⁅S₁, S₂⁆ = ⁅φ S₁, φ S₂⁆ :=
    fun S₁ S₂ h₁ h₂ => by
      rw [hφ]
      dsimp only
      rw [map_commutator, subgroupOf_commutator_of_le (hleL S₁ h₁) (hleL S₂ h₂)]
  have hφnorm : ∀ S₁ S₂ : Subgroup H, S₁ ≤ normalizer (S₂ : Set H) →
      φ S₁ ≤ normalizer ((φ S₂ : Subgroup L) : Set L) := fun S₁ S₂ h12 =>
    subgroupOf_le_normalizer_of_le ((map_mono h12).trans (le_normalizer_map _))
  have hφmul : ∀ S₀ S₁ S₂ : Subgroup H, S₀ ≤ X' → S₁ ≤ X' → S₂ ≤ X' →
      (S₀ : Set H) = (S₁ : Set H) * (S₂ : Set H) →
      ((φ S₀ : Subgroup L) : Set L) =
        ((φ S₁ : Subgroup L) : Set L) * ((φ S₂ : Subgroup L) : Set L) :=
    fun S₀ S₁ S₂ h₀ h₁ h₂ h012 => by
      refine coe_subgroupOf_mul_of_le (hleL S₀ h₀) (hleL S₁ h₁) (hleL S₂ h₂) ?_
      rw [coe_map, coe_map, coe_map, h012, Set.image_mul]
  have hP₁X : PH ⊓ K ≤ X' := inf_le_left.trans hPHX
  have hP₂X : PH ⊓ K₂ ≤ X' := inf_le_left.trans hPHX
  have hQXX : QX ≤ X' := map_subtype_le _
  have hA₁X : ⁅QX, PH ⊓ K⁆ ≤ X' := (hA₁K.trans inf_le_left).trans hQXX
  have hA₂X : ⁅QX, PH ⊓ K₂⁆ ≤ X' := (hA₂K.trans inf_le_left).trans hQXX
  have hLperf : Group.IsPerfect L :=
    ⟨by rw [_root_.commutator_def]; exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
  have hXLn : (X.subgroupOf L).Normal := by
    have := E.char_l
    infer_instance
  have hXLexp : Monoid.exponent (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = p := by
    rw [Monoid.exponent_eq_of_mulEquiv (coreQuotEquivSubgroupOf hXL), E.exponent_eq]
  have hXLcard : Nat.card (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = p ^ 2 := by
    rw [Nat.card_congr (coreQuotEquivSubgroupOf hXL).toEquiv,
      ← Nat.card_congr (coreQuotEquivSubgroupOf hXH).toEquiv, hcardX]
  have hWL : Nat.card ((X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) ⧸
      frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L))) = p ^ 2 := by
    rw [card_frattini_subgroupOf hXL, E.card_w]
  have hΦ : frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = ⊥ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)))
    rw [hXLcard, hWL] at h1
    have hpos : 0 < p ^ 2 := by positivity
    have h2 : Nat.card (frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L))) = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (mul_one _).symm)
    exact Subgroup.eq_bot_of_card_eq _ h2
  have hirrL := coreQuotConj_irreducible_of hΦ (frattiniQuotConj_irreducible_of hXL E.irr_l)
  have hXe := isElementaryAbelian_coreQuot hXLcard hXLexp
  have hSylL : IsSylowOf p (φ PH) (X.subgroupOf L) := by
    have h1 : IsSylowOf p (PH.map H.subtype) X := by
      rw [← hX'G]
      exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mpr hPH
    exact (isSylowOf_subgroupOf_iff (hleL PH hPHX) hXL).mpr h1
  have hP₁L : Nat.card (φ (PH ⊓ K)) = p := by rw [hφcard _ hP₁X, hP₁card]
  have hP₂L : Nat.card (φ (PH ⊓ K₂)) = p := by rw [hφcard _ hP₂X, hP₂card]
  have hsupL : φ (PH ⊓ K) ⊔ φ (PH ⊓ K₂) = φ PH := by rw [← hφsup _ _ hP₁X hP₂X, hPsup']
  have hinfL : φ (PH ⊓ K) ⊓ φ (PH ⊓ K₂) = ⊥ := by
    rw [← hφinf, hPinf, hφbot ⊥ bot_le]
  have hP₁₂ : ⁅PH ⊓ K, PH ⊓ K₂⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono inf_le_right inf_le_right).trans hKK₂.le)
  have hcommL : ⁅φ (PH ⊓ K), φ (PH ⊓ K₂)⁆ = ⊥ := by
    rw [← hφcomm _ _ hP₁X hP₂X, hP₁₂, hφbot ⊥ bot_le]
  have hA₁L : φ ⁅QX, PH ⊓ K⁆ ≤ (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype := by
    rw [← hQXL]
    exact hφle (hA₁K.trans inf_le_left)
  have hA₂L : φ ⁅QX, PH ⊓ K₂⁆ ≤ (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype := by
    rw [← hQXL]
    exact hφle (hA₂K.trans inf_le_left)
  have hprodL : (((CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype : Subgroup L) :
      Set L) = ((φ ⁅QX, PH ⊓ K⁆ : Subgroup L) : Set L) *
        ((φ ⁅QX, PH ⊓ K₂⁆ : Subgroup L) : Set L) := by
    rw [← hQXL]
    exact hφmul _ _ _ hQXX hA₁X hA₂X hQA₁A₂
  have hA₁₂L : ⁅φ ⁅QX, PH ⊓ K⁆, φ ⁅QX, PH ⊓ K₂⁆⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₁X hA₂X, show ⁅⁅QX, PH ⊓ K⁆, ⁅QX, PH ⊓ K₂⁆⁆ = ⊥ from hA₁A₂,
      hφbot ⊥ bot_le]
  have hA₁P₂L : ⁅φ ⁅QX, PH ⊓ K⁆, φ (PH ⊓ K₂)⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₁X hP₂X, show ⁅⁅QX, PH ⊓ K⁆, PH ⊓ K₂⁆ = ⊥ from hA₁P₂, hφbot ⊥ bot_le]
  have hA₂P₁L : ⁅φ ⁅QX, PH ⊓ K₂⁆, φ (PH ⊓ K)⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₂X hP₁X, show ⁅⁅QX, PH ⊓ K₂⁆, PH ⊓ K⁆ = ⊥ from hA₂P₁, hφbot ⊥ bot_le]
  have hA₁P₁L : ⁅φ ⁅QX, PH ⊓ K⁆, φ (PH ⊓ K)⁆ ≠ ⊥ := by
    rw [← hφcomm _ _ hA₁X hP₁X, Ne, hφbot _ (commutator_le_of_le hA₁X hP₁X)]
    exact hA₁P₁
  have hA₂P₂L : ⁅φ ⁅QX, PH ⊓ K₂⁆, φ (PH ⊓ K₂)⁆ ≠ ⊥ := by
    rw [← hφcomm _ _ hA₂X hP₂X, Ne, hφbot _ (commutator_le_of_le hA₂X hP₂X)]
    exact hA₂P₂
  exact (NQTerm.perfect_odd_plane_excludes_terminal_support_models hLperf hp hp5 hXe hXLcard
    hirrL).1 ⟨φ PH, φ (PH ⊓ K), φ (PH ⊓ K₂), φ ⁅QX, PH ⊓ K⁆, φ ⁅QX, PH ⊓ K₂⁆, hSylL,
      hφle inf_le_left, hφle inf_le_left, hP₁L, hP₂L, hsupL, hinfL, hcommL, hA₁L, hA₂L,
      hφnorm _ _ hPA₁, hφnorm _ _ hPA₂, hprodL, hA₁₂L, hA₁P₂L, hA₂P₁L, hA₁P₁L, hA₂P₂L⟩

end CFSG.Quasithin.H13.NQRigid
