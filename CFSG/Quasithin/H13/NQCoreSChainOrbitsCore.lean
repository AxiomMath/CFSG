module

public import CFSG.Quasithin.H13.NQRigidAsmSetup
public import CFSG.Quasithin.H13.NQCoreP134Normal
public import CFSG.LinearAlgebra.LinearGroups.OddPStableActionsSupport
public import CFSG.Quasithin.H13.NQRigidAsmPairData
public import CFSG.Quasithin.H13.NQRigidAsmSubgroupOf
public import CFSG.Quasithin.H13.NQTermComponentOrbits
public import CFSG.Quasithin.SteinbergCCRankOneSplitting

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.NQRigid
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

theorem sc_orbits_core (hB1 : StmtEscapingComponentAction)
    (hB2 : StmtOuterRankContainment) (hB3 : StmtPairContainment)
    (hOD : StmtOuterDerivedCoprime) (hcen : FactCenterOddPart) (houter : FactOuterPrime)
    (hthin : FactThinCentralQuotient) (h36 : Vol2Native.A36CoreForSQTKCat)
    {H : Type} [Group H] [Finite H] (hHSQ : CFSG.SectionRank.IsSQTKCat H)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X A : Subgroup H} (hXA : X ≤ A)
    (hXn : (X.subgroupOf A).Normal) (hAS : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ A)
    (hX2 : NoPQuotient 2 X) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : IsFrattiniIrreducible X A) (hNA : normalizer (X : Set H) = A) (hAlt : A < ⊤) :
    (CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)).comap (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤
        A ∧
      ⁅X.map (QuotientGroup.mk' (CFSG.pCore 2 H)), CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)⁆ =
        ⊥ ∧
      IsCyclic (CFSG.pCore p (H ⧸ CFSG.pCore 2 H)) ∧
      ∃ K : Subgroup H, CFSG.IsCComponent K ∧ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∧
        ¬ K ≤ A ∧ CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 H))) ∧
        ¬ K.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤
          normalizer ((X.map (QuotientGroup.mk' (CFSG.pCore 2 H)) :
            Subgroup (H ⧸ CFSG.pCore 2 H)) : Set (H ⧸ CFSG.pCore 2 H)) ∧
        K ⊓ CFSG.pCore 2 H = (CFSG.pCore 2 K).map K.subtype ∧
        X ≤ normalizer (K : Set H) ∧ ⁅K, X⁆ = K ∧
        (Nat.card (center (K.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) = 1 ∨
          Nat.card (center (K.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) = 3) ∧
        ((K.Normal ∧ X ≤ K ∧ CFSG.pRank p (K.map (QuotientGroup.mk' (CFSG.pCore 2 H))) = 2) ∨
          ∃ h₀ : H, CFSG.conjugate K h₀ ≠ K ∧
            (∀ g : H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K h₀) ∧
            CFSG.IsComponent ((CFSG.conjugate K h₀).map (QuotientGroup.mk' (CFSG.pCore 2 H))) ∧
            (K.subgroupOf (K ⊔ CFSG.conjugate K h₀)).Normal ∧
            ((CFSG.conjugate K h₀).subgroupOf (K ⊔ CFSG.conjugate K h₀)).Normal ∧
            (K ⊔ CFSG.conjugate K h₀).Normal ∧ X ≤ K ⊔ CFSG.conjugate K h₀ ∧
            X ≤ normalizer (CFSG.conjugate K h₀ : Set H) ∧
            CFSG.pRank p K = 1 ∧ CFSG.pRank p (CFSG.conjugate K h₀) = 1 ∧
            CFSG.pRank p (K.map (QuotientGroup.mk' (CFSG.pCore 2 H))) = 1 ∧
            CFSG.pRank p ((CFSG.conjugate K h₀).map (QuotientGroup.mk' (CFSG.pCore 2 H))) = 1 ∧
            (∀ r : ℕ, r.Prime → r ≠ 2 →
              CFSG.pRank r (K.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ⧸
                center (K.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) ≤ 1) ∧
            Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2 ∧
            ∀ P : Subgroup H, IsSylowOf p P X →
              (P ⊓ K) ⊔ (P ⊓ CFSG.conjugate K h₀) = P ∧
              (P ⊓ K) ⊓ (P ⊓ CFSG.conjugate K h₀) = ⊥ ∧
              Nat.card (P ⊓ K : Subgroup H) = p ∧
              Nat.card (P ⊓ CFSG.conjugate K h₀ : Subgroup H) = p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set C := CFSG.pCore 2 H with hC
  set π := QuotientGroup.mk' C with hπ
  have hC2 : IsPGroup 2 C := CFSG.pCore_isPGroup
  have hCn : C.Normal := CFSG.pCore_normal
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent C := hC2.isNilpotent
    infer_instance
  have hSQT := hHSQ.1
  have hrkH : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r H ≤ 2 := hSQT
  have hrkE : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ C) ≤ 2 := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    have h1 := CFSG.SectionRank.pRank_quotient_two_group _ hC2 hr hr2
    have h2 := hSQT r hr hr2
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2 ⊢
    exact h1.trans_le h2
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent hexp
  obtain ⟨-, -, -, hfit⟩ :=
    Sylow_containing_normalizer_lifts_quotient_Fitting_control hrkH hp hp2 hXA hXn hAS hX2 hexp
      hrk hirr
  obtain ⟨hFA, hcomm, hcyc⟩ := hfit hNA hAlt
  have hXs : Group.IsSolvable X := isSolvable_of_isPGroup_quotient_pCore hXp
  have hrank2 := two_le_pRank_map_mk hp2 hXp hrk C hC2
  obtain ⟨K, hKc, hKq, hKX, hJc, hJX, hKC⟩ :=
    NQBlock.cyclic_prime_core_Fitting_centralization_produces_escaping_Ccomponent hXs hrank2 hcyc
      hcomm
  have hKA : ¬ K ≤ A := fun hle => hKX (hle.trans hNA.ge)
  have hidx : ∀ D : Subgroup X, D.Normal → D.index ≠ 2 :=
    fun D hD => index_ne_two_of_noPQuotient hX2 D hD
  obtain ⟨hXK, hKXc⟩ := hB1 H C hCsolv X hidx hrkE K hKc hJc
  have hKXeq := hKXc hJX
  have hESQ := isSQTKCat_quotient_pCore hHSQ
  have hQ' : Vol2Native.SQTKHypCat (H ⧸ C) :=
    Vol2Native.SQTKHypCat.quotient_pCore H hHSQ
  have hZ13 : Nat.card (center (K.map π)) = 1 ∨ Nat.card (center (K.map π)) = 3 := by
    have hJcc : K.map π ∈ cComp (⊤ : Subgroup (H ⧸ C)) :=
      mem_cComp_top_iff_isCComponent.mpr (NQBlock.isCComponent_of_isComponent hJc)
    exact card_center_of_a36Common' hJc.1 (h36 _ hQ' _ hJcc).2.1
  have hJSQ : CFSG.SectionRank.IsSQTKCat (K.map π) := hESQ.subgroup _
  have hZJ : ¬ p ∣ Nat.card (center (K.map π)) := hcen _ hJc.1 hJSQ p hp hp5
  have hJXne : ⁅K.map π, X.map π⁆ ≠ ⊥ := by
    intro h1
    apply hJX
    rw [commutator_eq_bot_iff_le_centralizer] at h1
    exact h1.trans (centralizer_le_normalizer _)
  have hQX : A ≤ normalizer (((CFSG.pCore 2 X).map X.subtype : Subgroup H) : Set H) :=
    hNA.ge.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hAN : A ≤ normalizer (X : Set H) := hNA.ge
  refine ⟨hFA, hcomm, hcyc, K, hKc, hKq, hKA, hJc, hJX, hKC, hXK, hKXeq, hZ13, ?_⟩
  by_cases hKn : K.Normal
  ·
    left
    have hirr0 : IsFrattiniIrreducible X (A ⊓ normalizer (K : Set H)) := by
      rw [normalizer_eq_top_iff.mpr hKn, inf_top_eq]
      exact hirr
    have hlat := isFrattiniLatticeIrreducible_of hirr0
    have hOuter := houter _ hJc.1 hJSQ p hp hp5
    obtain ⟨-, hrkJ, -, hXK'⟩ :=
      hB2 H p hp hp2 (hSQT p hp hp2) C hC2 K hKc hJc hZJ hOuter X (A ⊓ normalizer (K : Set H))
        (CFSG.pCore 2 X) (le_inf hXA hXK) inf_le_right (inf_le_left.trans hQX)
        (inf_le_left.trans hAN) CFSG.pCore_isPGroup (pow_mem_pCore_of_exponent hexp) hX2 hW.ge
        hlat hJXne
    exact ⟨hKn, hXK', hrkJ⟩
  ·
    right
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H, CFSG.conjugate K h₀ ≠ K := by
      by_contra hall
      push Not at hall
      apply hKn
      refine ⟨fun n hn g => ?_⟩
      have h1 := hall g⁻¹
      rw [CFSG.conjugate, inv_inv] at h1
      rw [← h1]
      exact ⟨n, hn, rfl⟩
    set K₂ := CFSG.conjugate K h₀ with hK₂
    have hK₂c : CFSG.IsCComponent K₂ := isCComponent_conjugate hKc h₀
    have horb := (NQTerm.odd_rank_two_component_orbits_and_normalization hrkE).1 _ hJc
    have hdich := conjugate_dichotomy hCsolv hKc horb hh₀
    set J₁ := K.map π with hJ₁
    set J₂ := K₂.map π with hJ₂
    have hJ₂c : CFSG.IsComponent J₂ := by
      rw [hJ₂, hK₂, map_conjugate_hom]
      exact NQTerm.isComponent_conjugate hJc _
    have hJne : J₁ ≠ J₂ := fun heq =>
      hh₀ (eq_of_map_eq_of_isCComponent hCsolv hK₂c hKc heq.symm)
    have hJcomm : ⁅J₁, J₂⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hJc hJ₂c with h1 | h1
      · exact absurd h1 hJne
      · exact h1
    have hK₂N : K₂ ≤ normalizer (K : Set H) := normalizer_ge_of_commute_images hCsolv hKc hJcomm
    have hKN₂ : K ≤ normalizer (K₂ : Set H) := by
      refine normalizer_ge_of_commute_images hCsolv hK₂c ?_
      rw [commutator_comm]
      exact hJcomm
    have hXK₂ : X ≤ normalizer (K₂ : Set H) := by
      intro x hx
      rw [← conjugate_eq_self_iff]
      rcases hdich (h₀ * x) with h1 | h1
      · exfalso
        have h2 : CFSG.conjugate K x = K := conjugate_eq_self_iff.mpr (hXK hx)
        rw [← conjugate_conjugate] at h1
        apply hh₀
        have h3 : CFSG.conjugate K₂ x = CFSG.conjugate K x := by rw [h2]; exact h1
        exact conjugate_injective h3
      · rw [← conjugate_conjugate] at h1
        rw [h1]
    have hJconj : CFSG.conjugate J₁ (π h₀) ≠ J₁ := by
      rw [hJ₁, ← map_conjugate_hom]
      exact fun h1 => hJne h1.symm
    have hOut := hOD _ hESQ J₁ hJc ⟨π h₀, hJconj⟩ p hp hp5
    have hpH : CFSG.pRank p H ≤ 2 := hSQT p hp hp2
    have hlat := isFrattiniLatticeIrreducible_of hirr
    have hJ0X : ⁅(K ⊔ K₂).map π, X.map π⁆ ≠ ⊥ := fun h1 =>
      hJXne (le_bot_iff.mp ((commutator_mono (map_mono le_sup_left) le_rfl).trans h1.le))
    obtain ⟨hXK₀, hK₀n, -, -, hrk₁, hrk₂⟩ :=
      hB3 H p hp hp2 hpH C hC2 K K₂ hKc hh₀ hdich ⟨h₀, rfl⟩ hJc hZJ hOut X A
        (CFSG.pCore 2 X) hXA hQX hAN CFSG.pCore_isPGroup (pow_mem_pCore_of_exponent hexp) hX2
        hW.ge hlat hJ0X
    set K₀ := K ⊔ K₂ with hK₀
    have hK₁K₀ : K ≤ K₀ := le_sup_left
    have hK₂K₀ : K₂ ≤ K₀ := le_sup_right
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
    have hrkEq : ∀ K' : Subgroup H, CFSG.IsCComponent K' →
        CFSG.pRank p K' = CFSG.pRank p (K'.map π) := by
      intro K' hK'c
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
    have hrkK₁ : CFSG.pRank p K ≤ 1 := (hrkEq K hKc).trans_le hrk₁.le
    have hrkK₂ : CFSG.pRank p K₂ ≤ 1 := (hrkEq K₂ hK₂c).trans_le hrk₂.le
    have hrkK₁' : CFSG.pRank p (K.subgroupOf K₀) ≤ 1 := by
      rw [pRank_congr hp.one_lt (subgroupOfEquivOfLe hK₁K₀)]
      exact hrkK₁
    have hrkK₂' : CFSG.pRank p (K₂.subgroupOf K₀) ≤ 1 := by
      rw [pRank_congr hp.one_lt (subgroupOfEquivOfLe hK₂K₀)]
      exact hrkK₂
    have hIK₀ : ¬ p ∣ Nat.card (K.subgroupOf K₀ ⊓ K₂.subgroupOf K₀ : Subgroup K₀) := by
      rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hK₁K₀)]
      exact hI
    have hsplit : ∀ P : Subgroup H, IsSylowOf p P X →
        Nat.card P = p ^ 2 ∧ (P ⊓ K) ⊔ (P ⊓ K₂) = P ∧ (P ⊓ K) ⊓ (P ⊓ K₂) = ⊥ ∧
          Nat.card (P ⊓ K : Subgroup H) = p ∧ Nat.card (P ⊓ K₂ : Subgroup H) = p := by
      intro PH hPH
      have hPHX : PH ≤ X := hPH.le
      have hPHnc : ¬ IsCyclic PH := NQCat.not_isCyclic_of_isSylowOf_of_card_eq_sq hXp hW hPH
      have hPexp : ∀ x ∈ PH, x ^ p = 1 := by
        obtain ⟨P₀, hP₀⟩ := hPH.exists_sylow_eq_subgroupOf
        let e₀ : (P₀ : Subgroup X) ≃* X ⧸ CFSG.pCore 2 X :=
          MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hXp P₀)
        intro x hx
        have hxX : x ∈ X := hPHX hx
        have hxP : (⟨x, hxX⟩ : X) ∈ (P₀ : Subgroup X) := by rw [hP₀]; exact hx
        have h0 : ∀ y : X ⧸ CFSG.pCore 2 X, y ^ p = 1 := fun y =>
          hexp ▸ Monoid.pow_exponent_eq_one y
        have h1 : e₀ (⟨⟨x, hxX⟩, hxP⟩ ^ p) = 1 := by
          rw [map_pow]
          exact h0 _
        have h2 := e₀.injective (h1.trans (map_one e₀).symm)
        have h3 := congrArg (fun y : (P₀ : Subgroup X) => ((y : X) : H)) h2
        simpa using h3
      have hPK₀ : PH ≤ K₀ := hPHX.trans hXK₀
      have hPK₀p : IsPGroup p (PH.subgroupOf K₀) := by
        rw [← comap_subtype]
        exact hPH.isPGroup.comap_subtype
      have hPK₀nc : ¬ IsCyclic (PH.subgroupOf K₀) := fun hc =>
        hPHnc (isCyclic_of_surjective (subgroupOfEquivOfLe hPK₀).toMonoidHom
          (subgroupOfEquivOfLe hPK₀).surjective)
      have hexpK₀ : ∀ x ∈ PH.subgroupOf K₀, x ^ p = 1 := by
        intro x hx
        apply Subtype.ext
        rw [coe_pow]
        exact hPexp _ (mem_subgroupOf.mp hx)
      obtain ⟨hPcard, hP₁card, hP₂card, hdisj, -, hPsup, -⟩ :=
        SteinbergCC.rank_one_normal_product_exponent_prime_intersection_splitting hp hsup hIK₀
          hrkK₁' hrkK₂' hPK₀p hPK₀nc hexpK₀
      rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hPK₀)] at hP₁card
      rw [← subgroupOf_inf, card_subgroupOf_of_le (inf_le_left.trans hPK₀)] at hP₂card
      rw [← subgroupOf_inf, ← subgroupOf_inf, ← subgroupOf_sup (inf_le_left.trans hPK₀)
        (inf_le_left.trans hPK₀)] at hPsup
      have hPsup' : (PH ⊓ K) ⊔ (PH ⊓ K₂) = PH :=
        subgroupOf_injective_of_le (sup_le (inf_le_left.trans hPK₀) (inf_le_left.trans hPK₀))
          hPK₀ hPsup
      have hPinf : (PH ⊓ K) ⊓ (PH ⊓ K₂) = ⊥ := by
        have h1 := disjoint_iff.mp hdisj
        rw [← subgroupOf_inf, ← subgroupOf_inf, ← subgroupOf_inf] at h1
        exact (subgroupOf_eq_bot_iff_of_le (inf_le_left.trans (inf_le_left.trans hPK₀))).mp h1
      refine ⟨?_, hPsup', hPinf, hP₁card, hP₂card⟩
      rw [← hPcard, card_subgroupOf_of_le hPK₀]
    have hcardX : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2 := by
      obtain ⟨PH, hPH⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
      obtain ⟨P₀, hP₀⟩ := hPH.exists_sylow_eq_subgroupOf
      rw [← Nat.card_congr (MulEquiv.ofBijective _
        (NQTerm.sylow_bijective_coreQuot hp2 hXp P₀)).toEquiv, hP₀,
        card_subgroupOf_of_le hPH.le]
      exact (hsplit PH hPH).1
    have hthinJ := hthin _ hESQ J₁ hJc (π h₀) hJconj
    refine ⟨h₀, hh₀, hdich, hJ₂c, hK₁n, hK₂n, hK₀n, hXK₀, hXK₂, ?_, ?_, hrk₁, hrk₂, hthinJ,
      hcardX, fun P hP => (hsplit P hP).2⟩
    · rw [hrkEq K hKc, hrk₁]
    · rw [hrkEq K₂ hK₂c, hrk₂]

end CFSG.Quasithin.H13.NQCore
