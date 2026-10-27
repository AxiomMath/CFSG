module

public import CFSG.Quasithin.H13.NQRigidAsmSingleExcl
public import CFSG.Quasithin.H13.NQRigidObl
public import CFSG.Quasithin.SteinbergBTNoncyclicPrimeWitnessParabolic
public import CFSG.Quasithin.H13.NQRigidAsmModule
public import CFSG.Quasithin.H13.NQRigidAsmTransport
public import CFSG.Quasithin.H13.NQRigidSporadic
public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.Quasithin.SteinbergCDPermutableIntersection

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open Equiv
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergBT
  (original_noncyclic_prime_witness_forbids_full_even_linear_three_parabolic_image)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem rigidSingle_false (hcen : FactCenterOddPart)
    (hsect : FactSimpleQuotientSQT) (hnonsc : FactNonscalarG2Triality) (hree : FactLargeRee)
    (hQTE : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hB4 : StmtOrdinaryEvenSymplecticFour) (hB5 : StmtNoncyclicLocalSylowFourEven)
    (hB6 : StmtFourDivisibilityFields) (hB8 : StmtCPUOffenderSection)
    (hJ4 : StmtJ4SingleComponent) (hTits : StmtTitsSylowProduct)
    (hR2a : OblRigidCPUEvenLinearThreeParabolic) (hR2b : OblRigidCPUSymplecticFourDeleted)
    {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (E : RigidSingle T L M p X v K) : False := by
  classical
  have h := E.qtnq
  have hp := E.prime
  have hp5 := E.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hKn : K.Normal := E.normal
  have hXK : X.subgroupOf (centralizer ({v} : Set G)) ≤ K := E.x_le
  have hXH : X ≤ centralizer ({v} : Set G) := E.le_h
  let H := centralizer ({v} : Set G)
  have hH : H = centralizer ({v} : Set G) := rfl
  set A := (M ⊓ H).subgroupOf H with hA
  set X' := X.subgroupOf H with hX'
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
  have hX'A' : X' ≤ A := fun x hx =>
    mem_subgroupOf.mpr ⟨hXM (mem_subgroupOf.mp hx), x.2⟩
  have hAN : A ≤ normalizer (X' : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hMX (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'n : (X'.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hX'A').mpr hAN
  obtain ⟨Q', hQ'⟩ := E.sylow_h.exists_sylow_eq_subgroupOf
  have hQ'A : (Q' : Subgroup H) ≤ A := by
    rw [hQ']
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨h.t_le hx.1, hx.2⟩
  have hQGH : T ⊓ centralizer {v} ≤ H := inf_le_right
  have hQGN : T ⊓ centralizer {v} ≤ normalizer (X : Set G) := inf_le_left.trans (h.t_le.trans hMX)
  set eI := imageEquivSubgroupOf hXH hQGH hQGN with heI
  have hHSQ := isSQTKCat_centralizer h E.mem_u E.ne_one
  have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
  have hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := hcen _ E.quasi hKSQ p hp hp5
  have hSs : IsSimpleGroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) := E.quasi.2.1
  have hSnab : ∃ a b : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K), a * b ≠ b * a :=
    E.quasi.2.2
  obtain ⟨hSsqt, hScat⟩ := hsect _ hKSQ (center _) hSs hSnab
  have hσker := not_dvd_card_ker_coreCenterQuot hp hp2 hZ
  obtain ⟨PH, hPH⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X'
  have hPHX : PH ≤ X' := hPH.le
  have hPHK : PH ≤ K := hPHX.trans hXK
  have hQ'top : IsSylowOf 2 (Q' : Subgroup H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, Q'.isPGroup', Q'.not_dvd_index⟩
  have hQK : IsSylowOf 2 ((Q' : Subgroup H) ⊓ K) K :=
    hQ'top.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hKn).ge
  have hOQ : (CFSG.pCore 2 X').map X'.subtype ≤ (Q' : Subgroup H) := by
    rw [hQ']
    intro x hx
    rw [mem_subgroupOf]
    have h1 : (x : G) ∈ ((CFSG.pCore 2 X').map X'.subtype).map H.subtype := ⟨x, hx, rfl⟩
    rw [CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX', subgroupOf_map_subtype,
      inf_of_le_left hXH] at h1
    exact E.core_le_q h1
  have hPQ' : (PH : Set H) * ((Q' : Subgroup H) : Set H) =
      ((Q' : Subgroup H) : Set H) * (PH : Set H) :=
    mul_comm_sylow_of_core_le hX'A hPH (hQ'A.trans hAN) hOQ
  have hcop : Nat.Coprime (Nat.card PH) (Nat.card (Q' : Subgroup H)) := by
    obtain ⟨a, ha⟩ := hPH.isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := Q'.isPGroup'.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hPN : PH ≤ normalizer (K : Set H) := by
    rw [normalizer_eq_top_iff.mpr hKn]
    exact le_top
  obtain ⟨-, -, hPQK⟩ :=
    SteinbergCD.coprime_permutable_product_normalized_subgroup_intersection hcop hPQ' hPN
  rw [inf_of_le_left hPHK] at hPQK
  obtain ⟨QKs, hQKs⟩ := hQK.exists_sylow_eq_subgroupOf
  have hPQKK : ((PH.subgroupOf K : Subgroup K) : Set K) * ((QKs : Subgroup K) : Set K) =
      ((QKs : Subgroup K) : Set K) * ((PH.subgroupOf K : Subgroup K) : Set K) := by
    apply Set.image_injective.mpr K.subtype_injective
    rw [Set.image_mul, Set.image_mul, ← coe_map, ← coe_map, hQKs, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hPHK, inf_of_le_left inf_le_right, hPQK]
  have hPKp : IsPGroup p (PH.subgroupOf K) := by
    rw [← comap_subtype]
    exact hPH.isPGroup.comap_subtype
  have hPHnc : ¬ IsCyclic PH := NQCat.not_isCyclic_of_isSylowOf_of_card_eq_sq hX'A hW' hPH
  have hPKnc : ¬ IsCyclic (PH.subgroupOf K) := fun hc =>
    hPHnc (isCyclic_of_surjective (subgroupOfEquivOfLe hPHK).toMonoidHom
      (subgroupOfEquivOfLe hPHK).surjective)
  have hσinj := injective_of_not_dvd_card_ker hp (coreCenterQuot K) hσker hPKp
  set AS := (PH.subgroupOf K).map (coreCenterQuot K) with hAS
  have hrange : ((coreCenterQuot K).comp (PH.subgroupOf K).subtype).range = AS := by
    rw [MonoidHom.range_comp, range_subtype]
  let eA : PH.subgroupOf K ≃* AS :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hASp : IsPGroup p AS := hPKp.map _
  have hASnc : ¬ IsCyclic AS := fun hc =>
    hPKnc (isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective)
  set US := QKs.mapSurjective (coreCenterQuot_surjective K) with hUS
  have hAU : (AS : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
      ((US : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
      ((US : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * AS := by
    rw [hUS, Sylow.coe_mapSurjective, hAS]
    exact map_mul_comm_of_mul_comm (coreCenterQuot K) hPQKK
  set R := (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype ⊓ centralizer {v} with hR
  have hRH : R ≤ H := inf_le_right
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup.map _).to_le inf_le_left
  have hKA : ¬ K ≤ A := fun hle => E.escapes (hle.trans hAN)
  have hRpush := eq_pCore_normalizer_subgroupOf hRH E.r_pushing
  have hRchar := normalizer_le_subgroupOf_of_characteristic hRH (fun D hD hD1 => by
    have := hD
    exact normalizer_le_of_characteristic_of_singleton E.singleton hR2 E.r_normalizer D hD1)
  have hRH2 : IsPGroup 2 (R.subgroupOf H) := by
    rw [← comap_subtype]
    exact hR2.comap_subtype
  have hRK : R.subgroupOf H ≤ normalizer (K : Set H) := by
    rw [normalizer_eq_top_iff.mpr hKn]
    exact le_top
  have hcfg : ¬ CFSG.IsQuasisimple K → RigidSingleCPUConfig T L M p X v K := fun hKq =>
    ⟨h, E.module, hp, hp5, E.le_l, E.char_l, E.le_rad, E.core_ne, E.normalizer_eq, E.no_quot,
      E.exponent_eq, E.rank_eq, E.card_w, E.acts_l, E.irr_l, E.mem_u, E.ne_one, E.not_le,
      E.sylow_a, E.sylow_h, E.ccomp, hKn, hXK, hKA,
      generalizedFitting_eq_pCore_of_not_quasisimple E.odd_core E.ccomp hKq, E.quasi⟩
  have hQimg : (((Q' : Subgroup H)).subgroupOf (normalizer (X' : Set H))).map
      (normalizerFrattiniConj X') = (((T ⊓ centralizer {v}).subgroupOf H).subgroupOf
        (normalizer ((X.subgroupOf H : Subgroup H) : Set H))).map
        (normalizerFrattiniConj (X.subgroupOf H)) := by
    rw [hQ']
  have hnc_of : ¬ IsCyclic (((T ⊓ centralizer {v}).subgroupOf (normalizer (X : Set G))).map
      (normalizerFrattiniConj X)) →
      ¬ IsCyclic (((Q' : Subgroup H).subgroupOf (normalizer (X' : Set H))).map
        (normalizerFrattiniConj X')) := by
    intro hnc hc
    rw [hQimg] at hc
    exact hnc ((isCyclic_congr eI).mp hc)
  rcases hQTE _ hSnab hScat hSsqt p hp hp5 US AS hASp hASnc hAU with
    ⟨ℓ, hℓ, hℓ5, hS⟩ | ⟨f, hf, hS⟩ | ⟨f, hf, hS⟩ | (⟨f, hf, hS⟩ | ⟨f, hf, hS⟩) |
      (⟨a, ha, hS⟩ | hS) | ⟨⟨ψ₀⟩, -⟩
  ·
    have hℓ2 : ℓ ≠ 2 := by omega
    by_cases hKq : CFSG.IsQuasisimple K
    · exact central_cover_excludes_odd_three hKq hXK hp hp5 hPH hX'A hX'2 hX'O2 hℓ hℓ2 hS
    · obtain ⟨W, _, _, _, _, L₁, B₁, hLq, hirr, hBe, hB1, hBN, -, hoff, ⟨e⟩⟩ :=
        hB8 H (R.subgroupOf H) hRH2 hRpush K E.ccomp
          (generalizedFitting_eq_pCore_of_not_quasisimple E.odd_core E.ccomp hKq) E.quasi hRK A
          hKA hRchar
      exact offender_excludes_odd_three L₁ B₁ hLq hirr hBe hB1 hBN hoff e hℓ hℓ5 hS
  ·
    by_cases hKq : CFSG.IsQuasisimple K
    · exact even_linear_three_ordinary_excluded h hp hp5 E.le_l E.char_l E.core_ne E.exponent_eq
        E.card_w E.irr_l E.no_quot hXH hKq hXK hZ (by omega) hS
    · obtain ⟨k, _, _, hk, φ, hφ, E₀, hE₀, hφE⟩ := hR2a G T L M p X v K (hcfg hKq) f hf hS
      have hkev : Even (Nat.card k) := by
        rw [hk]
        exact (Nat.even_pow' (by omega)).mpr even_two
      have hk4 : 4 ≤ Nat.card k := by
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hnc := not_isCyclic_coreQuot_of_card_frattini hX'A hW'
      exact (original_noncyclic_prime_witness_forbids_full_even_linear_three_parabolic_image
          A K hp hp2 X' hX'A' hX'n hXK hX'A hnc hkev hk4 φ hφ).1 E₀ hE₀ hφE
  ·
    rcases noncyclic_or_deleted_weight_two h E.module hp hp5 E.le_l E.char_l hXA E.card_w E.acts_l
        E.mem_u E.sylow_a with hnc | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ, hw⟩
    · exact (hB5 H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A (hnc_of hnc) hZ).1 f hf hS
    · by_cases hKq : CFSG.IsQuasisimple K
      ·
        set KG := K.map H.subtype with hKG
        let eK : K ≃* KG := K.equivMapOfInjective H.subtype H.subtype_injective
        have hKGq : CFSG.IsQuasisimple KG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
        have hXKG : X ≤ KG := fun x hx => ⟨⟨x, hXH hx⟩, hXK (mem_subgroupOf.mpr hx), rfl⟩
        have hXnL : (X.subgroupOf L).Normal := by
          have := E.char_l
          infer_instance
        have hLperf : Group.IsPerfect L :=
          ⟨by rw [commutator_def]; exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
        have hZG : ¬ p ∣ Nat.card (center (KG ⧸ CFSG.pCore 2 KG)) := by
          rw [← card_center_coreQuot_congr eK]
          exact hZ
        exact hB4 G L KG X hLperf hKGq E.le_l hXKG hXnL p hp hp5 E.core_ne hXA E.exponent_eq
          E.card_w E.irr_l E.no_quot hZG f hf
          (CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv
            (centerQuotEquiv eK) hS)
      ·
        obtain ⟨-, -, h4⟩ :=
          NQSetup.deleted_weight_two_centralizer_has_original_cyclic_four_Sylow_image h hΩ β θ hθ hp
            hp5 E.le_l E.char_l hXA E.card_w E.acts_l E.mem_u hw E.sylow_a
        have h4H : 4 ∣ Nat.card (((Q' : Subgroup H).subgroupOf (normalizer (X' : Set H))).map
            (normalizerFrattiniConj X')) := by
          rw [hQimg, Nat.card_congr eI.toEquiv]
          exact h4
        have hfev := (hB6 H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A h4H hZ).1 f hf hS
        exact hR2b G T L M p X v K (hcfg hKq) Ω hΩ β θ hθ E.mem_u hw f hf hfev hS
  ·
    rcases noncyclic_or_deleted_weight_two h E.module hp hp5 E.le_l E.char_l hXA E.card_w E.acts_l
        E.mem_u E.sylow_a with hnc | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ, hw⟩
    · exact (hB5 H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A (hnc_of hnc) hZ).2.1 f hf hS
    · obtain ⟨γ, hγ, hγns⟩ := exists_nonscalar_of_deleted_weight_two h hΩ β θ hθ hp hp5 E.le_l
        E.char_l hXA E.card_w E.acts_l E.mem_u hw E.sylow_a
      exact (hnonsc H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A
        (nonscalar_image_subgroupOf hXH hQGH hQGN hQ' hγ hγns) hZ).1 f hf hS
  ·
    rcases noncyclic_or_deleted_weight_two h E.module hp hp5 E.le_l E.char_l hXA E.card_w E.acts_l
        E.mem_u E.sylow_a with hnc | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ, hw⟩
    · exact (hB5 H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A (hnc_of hnc) hZ).2.2.1 f hf hS
    · obtain ⟨γ, hγ, hγns⟩ := exists_nonscalar_of_deleted_weight_two h hΩ β θ hθ hp hp5 E.le_l
        E.char_l hXA E.card_w E.acts_l E.mem_u hw E.sylow_a
      exact (hnonsc H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A
        (nonscalar_image_subgroupOf hXH hQGH hQGN hQ' hγ hγns) hZ).2 f hf hS
  ·
    have htriv := hree H p hp hp2 A Q' hQ'A K X' hX'A' hAN hXK hX'A hZ ⟨a, ha, hS⟩
    apply image_ne_bot_of_module h E.module hp hp5 E.le_l E.char_l hXA E.card_w E.acts_l E.mem_u
      E.sylow_a
    have hbot : (((Q' : Subgroup H)).subgroupOf (normalizer (X' : Set H))).map
        (normalizerFrattiniConj X') = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨n, hn, rfl⟩
      rw [mem_bot]
      have h1 := htriv (n : H) (mem_subgroupOf.mp hn)
      exact h1
    have hcard : Nat.card (((T ⊓ centralizer {v}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) = 1 := by
      rw [← Nat.card_congr eI.toEquiv, ← hQimg, hbot, card_bot]
    exact Subgroup.eq_bot_of_card_eq _ hcard
  ·
    exact hTits K _ p hp hp2 (coreCenterQuot K) (coreCenterQuot_surjective K) hσker
      (PH.subgroupOf K) hPKp hPKnc QKs hPQKK hS
  ·
    have hDK : A ≤ normalizer (K : Set H) := by
      rw [normalizer_eq_top_iff.mpr hKn]
      exact le_top
    exact (hJ4 H A K X' hDK hX'A' hX'n hXK p hp hp5 hX'A hW'.ge hirrA' hZ PH
      ((Q' : Subgroup H) ⊓ K) hPH hQK hPQK).false ψ₀

end CFSG.Quasithin.H13.NQRigid
