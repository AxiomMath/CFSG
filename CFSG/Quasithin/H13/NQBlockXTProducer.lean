module

public import CFSG.Quasithin.H13.NQBlockXTInputs
public import CFSG.Quasithin.H13.NQBlockExcludesCrossLinearThree
public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge
public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

theorem sqt_catalog_of_surjective
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.SectionRank.IsSQTKCat X) (H : Subgroup X) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (φ : H →* S)
    (hφ : Function.Surjective φ) :
    CFSG.IsStronglyQuasithin S ∧ CFSG.Blueprint.Catalog S := by
  let e : (H ⧸ φ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (H ⧸ φ.ker) := MulEquiv.isSimpleGroup e
  have hnab' : ∃ a b : H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  obtain ⟨hsqt, hcat⟩ := CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hX H φ.ker hnab'
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hsqt,
    CFSG.SectionRank.catalog_of_mulEquiv e.symm hcat⟩

variable {G : Type} [Group G] [Finite G]

theorem sylow_image_noncyclic {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X K P : Subgroup G}
    (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hP : IsSylowOf p P X) {E : Type*} [Group E] (θ : K →* E)
    (hθinj : Function.Injective (θ.comp (P.subgroupOf K).subtype)) :
    IsPGroup p ((P.subgroupOf K).map θ) ∧ ¬ IsCyclic ((P.subgroupOf K).map θ) ∧
      (∀ y ∈ (P.subgroupOf K).map θ, y ^ p = 1) ∧
      Nat.card ((P.subgroupOf K).map θ) = Nat.card (X ⧸ CFSG.pCore 2 X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  obtain ⟨Q, hQ⟩ := hP
  have hbij := NQTerm.sylow_bijective_coreQuot hp2 hXA Q
  have hcardP : Nat.card P = Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hQ, card_map_of_injective X.subtype_injective]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcardW : p ^ 2 ≤ Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hW]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 X) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)).exists_card_eq
    rw [hm]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hPexp : ∀ z ∈ P, z ^ p = 1 := by
    intro z hz
    have hzX : z ∈ X := hPX hz
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ((⟨z, hzX⟩ : X) ^ p) = 1 := by
      rw [map_pow, ← hexp]
      exact Monoid.pow_exponent_eq_one _
    have h2 : (⟨z, hzX⟩ : X) ^ p ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨z, hz⟩
    rw [Subgroup.orderOf_mk] at hk
    have h5 : orderOf ((⟨z, hzX⟩ : X) ^ p) ∣ p ^ k := by
      refine (orderOf_pow_dvd p).trans ?_
      rw [Subgroup.orderOf_mk, hk]
    have h6 := NQTerm.eq_one_of_orderOf_dvd_prime_pow hp h4 h2 h5
    simpa using congrArg Subtype.val h6
  have hPstmap : (P.subgroupOf K).map θ = (θ.comp (P.subgroupOf K).subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  have hcardPst : Nat.card ((P.subgroupOf K).map θ) = Nat.card P := by
    rw [hPstmap, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hPstexp : ∀ y ∈ (P.subgroupOf K).map θ, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h1 : x ^ p = 1 := Subtype.ext (by simpa using hPexp _ (mem_subgroupOf.mp hx))
    rw [h1, map_one]
  refine ⟨(hPp.comap_subtype (K := K)).map θ, fun hcyc => ?_, hPstexp, hcardPst.trans hcardP⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (P.subgroupOf K).map θ)
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hPstexp _ g.2)
  have htop : zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have h1 : Nat.card ((P.subgroupOf K).map θ) ≤ p := by
    have h2 : Nat.card (zpowers g) = orderOf g := Nat.card_zpowers g
    rw [htop, card_top] at h2
    rw [h2]
    exact orderOf_le_of_pow_eq_one hp.pos hgp
  rw [hcardPst, hcardP] at h1
  have h2 := hcardW.trans h1
  nlinarith [hp.two_le]

theorem originalXTNormalComponent_of
    (hPl : OriginalXTPlacement) (hCPU : CPUOffenderSection)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) : OriginalXTNormalComponent := by
  intro G _ _ T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr P hP Y hXTY hY2 hYM
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : X ≤ L := hXR.trans (map_subtype_le _)
  obtain ⟨K, hKc, hKloc, hKY, hKn, hXK, hKM, hKF, hJq, hZ13, hJrk, hKX, hRXK, hRXN, hND⟩ :=
    hPl G T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr Y hXTY hY2 hYM
  have hpZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := by
    rcases hZ13 with hZ | hZ <;> rw [hZ] <;> intro hd
    · exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    · have := Nat.le_of_dvd (by norm_num) hd
      omega
  obtain ⟨hσinj, ⟨U', hU'⟩, hAU, -⟩ :=
    NQTerm.original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hpZ P hP
  rw [← hU'] at hAU
  obtain ⟨hAp, hAnc, -, -⟩ := sylow_image_noncyclic hp hp5 hXK hXA hexp hW hP _ hσinj
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  have hTY : T ≤ Y := le_sup_right.trans hXTY
  have hYK : Y ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKY).mp hKn
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  have hTKs : IsSylowOf 2 (T ⊓ K) K := (hTtop.of_le hTY le_top).inf_of_le_normalizer hKY hYK
  obtain ⟨AX, hAXdef⟩ : ∃ AX : Subgroup G, AX = (CFSG.pCore 2 X).map X.subtype := ⟨_, rfl⟩
  have hAX2 : IsPGroup 2 AX := hAXdef ▸ CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x => by
    rw [hAXdef]
    exact mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) := by
    rw [hAXdef]
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (h.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h1, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hPT : ∀ y ∈ P, ∀ q ∈ T, ∃ q' ∈ T, ∃ y' ∈ P, y * q = q' * y' := by
    intro y hy q hq
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hTN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hAXT (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  have hTP : ∀ q ∈ T, ∀ y ∈ P, ∃ y' ∈ P, ∃ q' ∈ T, q * y = y' * q' := by
    intro q hq y hy
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hAXT hya) hq, by group⟩
  have hprod1 : (P : Set G) * ((T ⊓ K : Subgroup G) : Set G) =
      ((T ⊓ K : Subgroup G) : Set G) * P := by
    ext z
    constructor
    · rintro ⟨y, hy, q, hq, rfl⟩
      have hq' : q ∈ T ⊓ K := hq
      obtain ⟨q', hq'T, y', hy', he⟩ := hPT y hy q (mem_inf.mp hq').1
      have hq'K : q' ∈ K := by
        rw [show q' = y * q * y'⁻¹ by rw [he]; group]
        exact mul_mem (mul_mem (hPK hy) (mem_inf.mp hq').2) (inv_mem (hPK hy'))
      exact ⟨q', mem_inf.mpr ⟨hq'T, hq'K⟩, y', hy', he.symm⟩
    · rintro ⟨q, hq, y, hy, rfl⟩
      have hq' : q ∈ T ⊓ K := hq
      obtain ⟨y', hy', q', hq'T, he⟩ := hTP q (mem_inf.mp hq').1 y hy
      have hq'K : q' ∈ K := by
        rw [show q' = y'⁻¹ * (q * y) by rw [he]; group]
        exact mul_mem (inv_mem (hPK hy')) (mul_mem (mem_inf.mp hq').2 (hPK hy))
      exact ⟨y', hy', q', mem_inf.mpr ⟨hq'T, hq'K⟩, he.symm⟩
  have hprod2 : (P : Set G) * ((T ⊓ K : Subgroup G) : Set G) =
      (P : Set G) * (T : Set G) ∩ (K : Set G) := by
    ext z
    constructor
    · rintro ⟨y, hy, q, hq, rfl⟩
      have hq' : q ∈ T ⊓ K := hq
      exact ⟨⟨y, hy, q, (mem_inf.mp hq').1, rfl⟩, mul_mem (hPK hy) (mem_inf.mp hq').2⟩
    · rintro ⟨⟨y, hy, q, hq, rfl⟩, hz⟩
      have hz' : y * q ∈ K := hz
      have hqK : q ∈ K := by
        have h1 := mul_mem (inv_mem (hPK hy)) hz'
        rwa [inv_mul_cancel_left] at h1
      exact ⟨y, hy, q, mem_inf.mpr ⟨hq, hqK⟩, rfl⟩
  have : IsSimpleGroup G := h.simple
  have hYsqtk : CFSG.SectionRank.IsSQTKCat Y :=
    ⟨QuasithinUnique.isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.qtke.2.2 hY2,
      QuasithinUnique.isKGroupCat_of_kProper h.qtke.1
        (QuasithinUnique.ne_top_of_pCoreOf_ne_bot_of_simple h.nonabelian hY2)⟩
  obtain ⟨-, hSs, hSnab⟩ := id hJq
  have hσs : Function.Surjective ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))) := fun z => by
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ CFSG.pCore 2 K)) z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) j
    exact ⟨k, rfl⟩
  obtain ⟨hSsqt, hScat⟩ := sqt_catalog_of_surjective hYsqtk (K.subgroupOf Y) hSnab
    (((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).comp (subgroupOfEquivOfLe hKY).toMonoidHom)
    (hσs.comp (subgroupOfEquivOfLe hKY).surjective)
  rcases hCat _ hSnab hScat hSsqt p hp hp5 U' _ hAp hAnc hAU with ⟨ℓ, hℓ, hℓ5, hmod⟩ | halt
  ·
    exfalso
    have hRXY : pCoreOf 2 (X ⊔ T) ≤ Y := (map_subtype_le _).trans hXTY
    have hRX2 : IsPGroup 2 (pCoreOf 2 (X ⊔ T)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
    obtain ⟨W₁, _, _, _, _, L₁, B₁, hL₁q, hL₁irr, hB₁N, hB₁ne, hB₁el, -, hineq, ⟨eS⟩⟩ :=
      hCPU G Y (pCoreOf 2 (X ⊔ T)) K (Y ⊓ M) hRXY hRX2 hRXN hKc hKF hJq hRXK inf_le_left
        (fun hle => hKM (hle.trans inf_le_right)) hND
    have h1 := offender_lt_of_mulAut_exclusion L₁ B₁ hL₁irr hL₁q.1 hB₁el hB₁ne hB₁N
      fun L' hL'p hL'irr ⟨e'⟩ A hAN hA1 hAe => by
        rcases hmod with hmod | hmod
        · exact CFSG.QuasithinUnique.Setup.Family.primeLinearThreeExclusion ℓ hℓ (by omega)
            (Multiplicative W₁) multiplicative_mul_self L' hL'p ⟨inferInstance, hL'irr⟩
            (CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv
              (e'.trans eS).symm hmod) A hAN hA1 hAe
        · exact CFSG.QuasithinUnique.Setup.Family.primeUnitaryThreeExclusion ℓ hℓ hℓ5
            (Multiplicative W₁) multiplicative_mul_self L' hL'p ⟨inferInstance, hL'irr⟩
            (CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv
              (e'.trans eS).symm hmod) A hAN hA1 hAe
    omega
  · refine ⟨K, hKc, hKloc, hKY, hKn, hXK, hKM, hKF, hKX, hRXK, hJq, hZ13, hJrk, hScat, hSsqt,
      hσinj, hTKs, hprod1, hprod2, ?_⟩
    rcases halt with h3 | h4 | (hG2 | hD4) | (hRee | hTits) | hJ4
    · exact Or.inl h3
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl hG2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hD4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRee))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hTits)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ4)))))

theorem original_characteristic_witness_singleton_of_placement
    (hPl : OriginalXTPlacement)
    (hCPU : CPUOffenderSection) (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hSp4 : OriginalWitnessExcludesEvenSymplecticFour)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M :=
  original_characteristic_witness_singleton_of (originalXTNormalComponent_of hPl hCPU hCat) hSp4
    h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr

end CFSG.Quasithin.H13.NQBlock
