module

public import CFSG.Quasithin.H13.NQCoreSChainOrbitsCore
public import CFSG.Quasithin.H13.NQBlockRootChain
public import CFSG.Quasithin.H13.NQBlockXTPlacement
public import CFSG.Quasithin.H13.NQCoreLocalChar
public import CFSG.Quasithin.H13.NQRigidB1
public import CFSG.Quasithin.H13.NQRigidB3
public import CFSG.Quasithin.H13.NQRigidAsmPair

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sylow_structure_of_le_normalizer {T X P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hT : quasithinIsSylowTwo T) (hTN : T ≤ normalizer (X : Set G))
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hP : IsSylowOf p P X) :
    pCoreOf 2 X ≤ T ∧ pCoreOf 2 X ⊔ P = X ∧ P ⊔ T = X ⊔ T ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) ∧
      T = pCoreOf 2 X ⊔ (T ⊓ normalizer (P : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, hT.1, hT.2⟩
  have hqX : pCoreOf 2 X = (CFSG.pCore 2 X).map X.subtype := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
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
      (hT.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hAXX : AX ≤ X := by
    rw [hAXdef]
    exact map_subtype_le _
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
  have hsup : AX ⊔ P = X := by
    refine le_antisymm (sup_le hAXX hPX) fun x hx => ?_
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx', sup_comm]
    exact mul_mem_sup hy hya
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
  have hset : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
    ext z
    constructor
    · rintro ⟨y, hy, q, hq, rfl⟩
      obtain ⟨q', hq', y', hy', he⟩ := hPT y hy q hq
      exact ⟨q', hq', y', hy', he.symm⟩
    · rintro ⟨q, hq, y, hy, rfl⟩
      obtain ⟨y', hy', q', hq', he⟩ := hTP q hq y hy
      exact ⟨y', hy', q', hq', he.symm⟩
  have hPTX : P ⊔ T = X ⊔ T := by
    refine le_antisymm (sup_le_sup_right hPX T) (sup_le ?_ le_sup_right)
    rw [← hsup]
    exact sup_le (hAXT.trans le_sup_right) le_sup_left
  have hfrat : T = AX ⊔ (T ⊓ normalizer (P : Set G)) := by
    refine le_antisymm (fun t ht => ?_) (sup_le hAXT inf_le_left)
    set P' := P.map (MulAut.conj t).toMonoidHom with hP'
    have hP'X : P' ≤ X := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp (hTN ht) y).mp (hPX hy)
    have hcard : Nat.card P' = Nat.card P :=
      card_map_of_injective (MulAut.conj t).injective
    have hP'S : IsSylowOf p P' X :=
      CFSG.ABGLocalTools.isSylowOf_of_card hP'X (hcard.trans hP.card_eq)
    obtain ⟨k, hkX, hk⟩ := hP'S.exists_mem_conj hP
    have hmemP' : ∀ x : G, x ∈ P' ↔ t⁻¹ * x * t ∈ P := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
      · intro hx
        exact ⟨t⁻¹ * x * t, hx, by simp [mul_assoc]⟩
    have hkt : (k * t)⁻¹ ∈ normalizer (P : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      rw [hk x, hmemP']
      constructor
      · intro h
        simpa [mul_assoc] using h
      · intro h
        simpa [mul_assoc] using h
    have hkt' : k * t ∈ normalizer (P : Set G) := by simpa using inv_mem hkt
    obtain ⟨y, hy, hya⟩ := hXPA k hkX
    have hn : (y⁻¹ * k) * t ∈ T := by
      have : y⁻¹ * k ∈ T := hAXT hya
      exact mul_mem this ht
    have hnN : (y⁻¹ * k) * t ∈ normalizer (P : Set G) := by
      have : y⁻¹ ∈ normalizer (P : Set G) := le_normalizer (inv_mem hy)
      simpa [mul_assoc] using mul_mem this hkt'
    have ht' : t = (y⁻¹ * k)⁻¹ * ((y⁻¹ * k) * t) := by group
    rw [ht']
    exact mul_mem_sup (inv_mem hya) ⟨hn, hnN⟩
  rw [hqX, ← hAXdef]
  exact ⟨hAXT, hsup, hPTX, hset, hfrat⟩

theorem card_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) := by
  rw [← Subgroup.map_center_eq e]
  exact (card_map_of_injective (f := e.toMonoidHom) e.injective).symm

omit [Finite G] in
theorem mem_normalizer_map_subtype_iff {H : Subgroup G} {K : Subgroup ↥H} {h : ↥H} :
    h ∈ normalizer (K : Set ↥H) ↔
      (h : G) ∈ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  constructor
  · intro hh
    have := Subgroup.mem_map_of_mem H.subtype hh
    rw [map_subtype_normalizer_eq] at this
    exact this.2
  · intro hh
    have h1 : (h : G) ∈ H ⊓ normalizer ((K.map H.subtype : Subgroup G) : Set G) := ⟨h.2, hh⟩
    rw [← map_subtype_normalizer_eq] at h1
    obtain ⟨h', hh', he⟩ := h1
    rw [← Subtype.ext he]
    exact hh'

omit [Finite G] in
theorem le_normalizer_map_subtype {H : Subgroup G} {K B : Subgroup ↥H}
    (hB : B ≤ normalizer (K : Set ↥H)) :
    B.map H.subtype ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨b, hb, rfl⟩
  exact mem_normalizer_map_subtype_iff.mp (hB hb)

omit [Finite G] in
theorem normal_subgroupOf_map_subtype {H : Subgroup G} {K B : Subgroup ↥H} (hKB : K ≤ B)
    (hn : (K.subgroupOf B).Normal) :
    ((K.map H.subtype).subgroupOf (B.map H.subtype)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hKB)]
  exact le_normalizer_map_subtype ((Subgroup.normal_subgroupOf_iff_le_normalizer hKB).mp hn)

theorem original_XT_orbit_placement_of
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F)
    (hOD : NQRigid.StmtOuterDerivedCoprime) : OriginalXTOrbitPlacement := by
  intro G _ _ T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr P hP H hXTH hH2 hHM
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := h.simple
  obtain ⟨hNX, -, -, -, hB, -⟩ := stmtOriginalRadicalNormalizerCoreControl_of_catalog hCat hI G T
    L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  obtain ⟨-, hconf⟩ := stmtEveryOriginalRadicalCharNormalizerConfined_of_catalog hCat hI G T L M
    h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  have hXH : X ≤ H := le_sup_left.trans hXTH
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have hXL : X ≤ L := hXR.trans (Subgroup.map_subtype_le _)
  have hXM : X ≤ M := hXL.trans h.l_le
  have hTM : T ≤ M := h.t_le
  have hXRn : X ≤ normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T))
  have ha : pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) := by
    set N := H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G) with hNdef
    have hRH : pCoreOf 2 (X ⊔ T) ≤ H := (map_subtype_le _).trans hXTH
    have hRN : pCoreOf 2 (X ⊔ T) ≤ N := le_inf hRH le_normalizer
    have h1 : pCoreOf 2 (X ⊔ T) ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRN inf_le_right
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T))
    have hXN : X ≤ N := le_inf hXH hXRn
    exact hB _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hXN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)) h1
  refine ⟨ha, fun D hD1 hDR hDc => inf_le_inf_left H (hconf D hD1 hDR hDc), ?_⟩
  have hHSQ : CFSG.SectionRank.IsSQTKCat ↥H :=
    (NQCore.qt_positive_two_core_SQTK h.nonabelian h.qtke hH2).2
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTH
  have hirrT : NQRigid.IsFrattiniIrreducible X T :=
    (NQRigid.sylow_irreducible_of_qtnq h hp hp5 hXL hXc hexp hW hirr).2
  obtain ⟨hqT, -, -, -, hfrat⟩ :=
    sylow_structure_of_le_normalizer h.sylow (hTM.trans hNX.ge) hXA hP
  set X' := X.subgroupOf H with hX'
  set A := (H ⊓ M).subgroupOf H with hA
  have hirrX : NQRigid.IsFrattiniIrreducible X (H ⊓ M) :=
    NQRigid.IsFrattiniIrreducible.mono hirrT (le_inf hTH hTM)
  obtain ⟨hX'2, hexp', hrk', hirr'⟩ :=
    NQRigid.subgroupOf_transport hXH (inf_le_left : H ⊓ M ≤ H) hXno hexp hrk hp.one_lt hirrX
  have hW' : Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) = p ^ 2 :=
    (NQRigid.card_frattini_subgroupOf hXH).trans hW
  have hX'A : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨x.2, hXM (mem_subgroupOf.mp hx)⟩
  have hNA : normalizer (X' : Set ↥H) = A := by
    ext g
    constructor
    · intro hg
      have hgN : (g : G) ∈ normalizer (X : Set G) := by
        rw [mem_normalizer_iff]
        intro y
        by_cases hy : y ∈ H
        · have := mem_normalizer_iff.mp hg ⟨y, hy⟩
          simpa [hX', mem_subgroupOf] using this
        · have h1 : y ∉ X := fun hyX => hy (hXH hyX)
          have h2 : (g : G) * y * (g : G)⁻¹ ∉ X := fun hyX => hy (by
            have := H.mul_mem (H.mul_mem (H.inv_mem g.2) (hXH hyX)) g.2
            simpa [mul_assoc] using this)
          exact iff_of_false h1 h2
      rw [hNX] at hgN
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨g.2, hgN⟩)
    · intro hg
      rw [hA, mem_subgroupOf] at hg
      rw [mem_normalizer_iff]
      intro y
      simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp (hNX.ge (mem_inf.mp hg).2) y
  have h5 : H ⊓ M < H := by
    refine lt_of_le_of_ne inf_le_left fun heq => hHM ?_
    rw [← heq]
    exact inf_le_right
  have hAlt : A < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => h5.ne ?_
    refine le_antisymm inf_le_left fun g hg => ?_
    have : (⟨g, hg⟩ : ↥H) ∈ A := htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hTH2 : IsPGroup 2 (T.subgroupOf H) := hTs.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hTHi : ¬ 2 ∣ (T.subgroupOf H).index := hTs.2.2
  have hTHA : T.subgroupOf H ≤ A := fun x hx =>
    mem_subgroupOf.mpr ⟨x.2, hTM (mem_subgroupOf.mp hx)⟩
  have hAS : ∃ S : Sylow 2 ↥H, (S : Subgroup ↥H) ≤ A := by
    refine ⟨hTH2.toSylow hTHi, ?_⟩
    rw [IsPGroup.toSylow_coe hTH2 hTHi]
    exact hTHA
  have hXn' : (X'.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hX'A).mpr hNA.ge
  obtain ⟨-, -, -, K, hKc, hKq, hKA, -, -, hKC, hXK, hKXeq, hZ13, hbr⟩ :=
    NQCore.sc_orbits_core NQRigid.stmtEscapingComponentAction_holds
      NQRigid.stmtOuterRankContainment_holds NQRigid.stmtPairContainment_holds hOD
      NQRigid.factCenterOddPart_holds NQRigid.factOuterPrime_holds
      NQRigid.factThinCentralQuotient_holds Vol2Native.a36CoreForSQTKCat_proved hHSQ hp hp5 hX'A
      hXn' hAS hX'2 hexp' hrk' hW' hirr' hNA hAlt
  set KG := K.map H.subtype with hKGdef
  have hKG : KG ∈ cComp H := map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr hKc)
  have hKloc : quasithinIsLocal T KG := isLocal_of_mem_cComp_of_sylow hTs hH2 hKG
  have hKnot : ¬ KG ≤ M := by
    intro hle
    apply hKA
    intro k hk
    exact mem_subgroupOf.mpr ⟨k.2, hle ⟨k, hk, rfl⟩⟩
  have hKF : quasithinGenFitting KG = pCoreOf 2 KG :=
    (NQCore.qt_full_Sylow_local_characteristic_two h.qtke h.sylow hKloc).1
  let eK : ↥K ≃* ↥KG := K.equivMapOfInjective H.subtype H.subtype_injective
  let eQ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥KG ⧸ CFSG.pCore 2 ↥KG :=
    QuotientGroup.congr _ _ eK (CFSG.pCore_map_iso 2 eK)
  obtain ⟨eJ⟩ : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃*
      ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) := by
    refine nonempty_quotient_mulEquiv (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) rfl
      (CFSG.pCore 2 ↥K) ?_
    rw [QuotientGroup.ker_mk']
    exact hKC.symm
  let e : ↥KG ⧸ CFSG.pCore 2 ↥KG ≃* ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :=
    eQ.symm.trans eJ
  have hqKG : CFSG.IsQuasisimple (↥KG ⧸ CFSG.pCore 2 ↥KG) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eQ).1 hKq
  have hZKG : Nat.card (center (↥KG ⧸ CFSG.pCore 2 ↥KG)) = 1 ∨
      Nat.card (center (↥KG ⧸ CFSG.pCore 2 ↥KG)) = 3 := by
    rw [card_center_congr e]
    exact hZ13
  have hXKG : X ≤ normalizer (KG : Set G) := by
    intro x hx
    have hx' : (⟨x, hXH hx⟩ : ↥H) ∈ X' := hx
    exact mem_normalizer_map_subtype_iff.mp (hXK hx')
  have hX'map : X'.map H.subtype = X := map_subgroupOf_eq_of_le hXH
  have hKXG : ⁅KG, X⁆ = KG := by
    rw [hKGdef, ← hX'map, ← Subgroup.map_commutator, hKXeq]
  have hKsub : KG.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
  rcases hbr with ⟨hKn, hX'K, hrkJ⟩ | ⟨h₀, hh₀, hdich, -, hK₁n, hK₂n, hK₀n, hXK₀, hXK₂,
      -, -, -, -, hthinJ, hcardX, hsplit⟩
  ·
    have hKGn : (KG.subgroupOf H).Normal := by
      rw [hKsub]
      exact hKn
    have hHN : H ≤ normalizer (KG : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hKGn
    refine ⟨KG, hKG, hKloc, hKnot, hKF, hqKG, hZKG, hXKG, hKXG,
      ((map_subtype_le _).trans hXTH).trans hHN, Or.inl ⟨hKGn, ?_, ?_⟩⟩
    · rw [← hX'map]
      exact Subgroup.map_mono hX'K
    · exact (NQRigid.pRank_congr hp.one_lt e).trans hrkJ
  ·
    set N := normalizer (K : Set ↥H) with hNdef
    have hh₀N : h₀ ∉ N := fun hm => hh₀ (NQRigid.conjugate_eq_self_iff.mpr hm)
    have hNidx : N.index = 2 := by
      rw [index_eq_two_iff']
      refine ⟨h₀, fun b => ?_⟩
      by_cases hb : b ∈ N
      · refine Or.inr ⟨hb, fun hab => hh₀N ?_⟩
        have := N.mul_mem hab (N.inv_mem hb)
        simpa [mul_assoc] using this
      · refine Or.inl ⟨?_, hb⟩
        have hKb : CFSG.conjugate K b = CFSG.conjugate K h₀ := by
          rcases hdich b with h1 | h1
          · exact absurd (NQRigid.conjugate_eq_self_iff.mp h1) hb
          · exact h1
        rcases hdich (h₀ * b) with h1 | h1
        · exact NQRigid.conjugate_eq_self_iff.mp h1
        · exfalso
          rw [← NQRigid.conjugate_conjugate] at h1
          have h2 : CFSG.conjugate (CFSG.conjugate K h₀) b = CFSG.conjugate K b := by
            rw [h1, hKb]
          exact hh₀ (NQRigid.conjugate_injective h2)
    obtain ⟨t₀, ht₀T, ht₀P, ht₀N⟩ : ∃ t₀ : G, ∃ h : t₀ ∈ T, t₀ ∈ normalizer (P : Set G) ∧
        (⟨t₀, hTH h⟩ : ↥H) ∉ N := by
      by_contra hall
      push Not at hall
      have hTN : T ≤ N.map H.subtype := by
        rw [hfrat]
        refine sup_le ?_ ?_
        · intro q hq
          have hqH : q ∈ H := hTH (hqT hq)
          have hqX : q ∈ X := (map_subtype_le _ : pCoreOf 2 X ≤ X) hq
          exact ⟨⟨q, hqH⟩, hXK (mem_subgroupOf.mpr hqX), rfl⟩
        · rintro s ⟨hsT, hsP⟩
          exact ⟨⟨s, hTH hsT⟩, hall s hsT hsP, rfl⟩
      have hTHN : T.subgroupOf H ≤ N := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hTN (mem_subgroupOf.mp hx)
        rwa [show y = x from Subtype.ext hyx] at hy
      apply hTHi
      rw [← hNidx]
      exact index_dvd_of_le hTHN
    set t : ↥H := ⟨t₀, hTH ht₀T⟩ with ht
    have hKt : CFSG.conjugate K t ≠ K := fun h1 => ht₀N (NQRigid.conjugate_eq_self_iff.mp h1)
    have htK₂ : CFSG.conjugate K t = CFSG.conjugate K h₀ := by
      rcases hdich t with h1 | h1
      · exact absurd h1 hKt
      · exact h1
    rw [← htK₂] at hK₁n hK₂n hK₀n hXK₀ hXK₂ hsplit
    have hdich' : ∀ g : ↥H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t :=
      fun g => htK₂ ▸ hdich g
    have hPH : P ≤ H := hP.le.trans hXH
    have hP' : IsSylowOf p (P.subgroupOf H) X' :=
      (NQRigid.isSylowOf_subgroupOf_iff hPH hXH).mpr hP
    obtain ⟨hPsup, hPinf, hP₁card, hP₂card⟩ := hsplit _ hP'
    set Y := X' ⊔ T.subgroupOf H with hY
    have hXY : X' ≤ Y := le_sup_left
    have hXYn : (X'.subgroupOf Y).Normal :=
      (normal_subgroupOf_iff_le_normalizer hXY).mpr
        (sup_le le_normalizer (hTHA.trans hNA.ge))
    have hperm : ∀ y : ↥H, ({CFSG.conjugate K y, CFSG.conjugate (CFSG.conjugate K t) y} :
        Set (Subgroup ↥H)) = {K, CFSG.conjugate K t} := by
      intro y
      have hKy := hdich' y
      have hK₂y : CFSG.conjugate (CFSG.conjugate K t) y = K ∨
          CFSG.conjugate (CFSG.conjugate K t) y = CFSG.conjugate K t := by
        rw [NQRigid.conjugate_conjugate]
        exact hdich' (t * y)
      have hne : CFSG.conjugate K y ≠ CFSG.conjugate (CFSG.conjugate K t) y := fun h1 =>
        hKt (NQRigid.conjugate_injective h1).symm
      rcases hKy with h1 | h1 <;> rcases hK₂y with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]
      · rw [h1, h2, Set.pair_comm]
      · exact absurd (h1.trans h2.symm) hne
    obtain ⟨hfp, -, -, -, -, -, -⟩ :=
      SteinbergCD.normal_prime_core_fixes_ambient_coprime_plane_factor_pair Nat.prime_two hp
        (by omega) hXY hXYn hcardX (fun y _ => hperm y) hXK hXK₂ hP' hPinf hP₁card hP₂card
    set RH := (pCoreOf 2 (X ⊔ T)).subgroupOf H with hRH
    have hXTsub : (X ⊔ T).subgroupOf H = Y := by rw [subgroupOf_sup hXH hTH]
    have hRY : RH ≤ Y := by
      rw [← hXTsub]
      intro r hr
      exact mem_subgroupOf.mpr ((map_subtype_le _ : pCoreOf 2 (X ⊔ T) ≤ X ⊔ T)
        (mem_subgroupOf.mp hr))
    have hRYn : (RH.subgroupOf Y).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hRY).mpr ?_
      rw [← hXTsub]
      exact NQRigid.subgroupOf_le_normalizer_of_le
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hR2 : IsPGroup 2 RH := by
      rw [hRH, ← comap_subtype]
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)).comap_subtype
    have hRK := (hfp RH hRY hRYn hR2).1
    have hK₂G : (CFSG.conjugate K t).map H.subtype = CFSG.conjugate KG t₀ :=
      NQRigid.map_conjugate_hom H.subtype K t
    have hK₀G : (K ⊔ CFSG.conjugate K t).map H.subtype = KG ⊔ CFSG.conjugate KG t₀ := by
      rw [Subgroup.map_sup, hK₂G]
    have hRG : pCoreOf 2 (X ⊔ T) ≤
        normalizer (KG : Set G) ⊓ normalizer (CFSG.conjugate KG t₀ : Set G) := by
      intro r hr
      have hrH : r ∈ H := ((map_subtype_le _).trans hXTH) hr
      have hr' : (⟨r, hrH⟩ : ↥H) ∈ RH := mem_subgroupOf.mpr hr
      obtain ⟨h1, h2⟩ := mem_inf.mp (hRK hr')
      refine ⟨mem_normalizer_map_subtype_iff.mp h1, ?_⟩
      rw [← hK₂G]
      exact mem_normalizer_map_subtype_iff.mp h2
    have hcardXG : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2 :=
      (Nat.card_congr (NQRigid.coreQuotEquivSubgroupOf hXH).toEquiv).symm.trans hcardX
    have hP'map : (P.subgroupOf H).map H.subtype = P := map_subgroupOf_eq_of_le hPH
    have hPK : ((P.subgroupOf H) ⊓ K).map H.subtype = P ⊓ KG := by
      rw [Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective, hP'map]
    have hPK₂ : ((P.subgroupOf H) ⊓ CFSG.conjugate K t).map H.subtype =
        P ⊓ CFSG.conjugate KG t₀ := by
      rw [Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective, hP'map, hK₂G]
    refine ⟨KG, hKG, hKloc, hKnot, hKF, hqKG, hZKG, hXKG, hKXG, fun r hr => (hRG hr).1,
      Or.inr ⟨t₀, ht₀T, ht₀P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        NQRigid.isElementaryAbelian_coreQuot hcardXG hexp, hcardXG⟩⟩
    ·
      intro h1
      apply hKt
      apply Subgroup.map_injective H.subtype_injective
      rw [hK₂G, h1]
    ·
      intro g hg
      have hmap : (CFSG.conjugate K ⟨g, hg⟩).map H.subtype = CFSG.conjugate KG g :=
        NQRigid.map_conjugate_hom H.subtype K ⟨g, hg⟩
      rcases hdich' ⟨g, hg⟩ with h1 | h1
      · left
        rw [← hmap, h1]
      · right
        rw [← hmap, h1, hK₂G]
    · rw [← hK₀G]
      exact normal_subgroupOf_map_subtype le_sup_left hK₁n
    · rw [← hK₀G, ← hK₂G]
      exact normal_subgroupOf_map_subtype le_sup_right hK₂n
    · have hsub : ((K ⊔ CFSG.conjugate K t).map H.subtype).subgroupOf H =
          K ⊔ CFSG.conjugate K t := comap_map_eq_self_of_injective H.subtype_injective _
      rw [← hK₀G, hsub]
      exact hK₀n
    · rw [← hK₀G, ← hX'map]
      exact Subgroup.map_mono hXK₀
    · intro r hr hr2
      have : Fact r.Prime := ⟨hr⟩
      let eZ := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact (NQRigid.pRank_congr hr.one_lt eZ).trans_le (hthinJ r hr hr2)
    · rw [← hPK, card_map_of_injective H.subtype_injective]
      exact hP₁card
    · rw [← hPK₂, card_map_of_injective H.subtype_injective]
      exact hP₂card
    · rw [← hPK, ← hPK₂, ← Subgroup.map_sup, hPsup, hP'map]
    · rw [← hPK, ← hPK₂, ← Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective, hPinf,
        Subgroup.map_bot]

end CFSG.Quasithin.H13.NQBlock
