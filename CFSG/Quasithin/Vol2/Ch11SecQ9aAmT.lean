module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmS
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmP
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmA
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.MinimalNormalFactors
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocalIntersections
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmC
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShE
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym3
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed
public import CFSG.Quasithin.Vol2.KGNatSp4Levi
public import CFSG.Quasithin.Vol2.KGNatSp4Sim
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Walter.J1
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.QuasithinUnique.Setup.X6


theorem factG2FourLongParabolic_holds : FactG2FourLongParabolic := by
  intro Y _ _ hY T M K V A B hT _ hNT hKM hMK hKK hKq hVM hMV hV4 hKV hAB hBO _ hKA hKB hne y hy
    hy3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : LieModel Y .G2 0 2 2 := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · omega
    · exact hL
  have hX := C11P9A.chevalleyExceptionalModel_of_lieModel hL
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity Y 2 2 hX).2
  obtain ⟨k, _, _, _, φ, hk, hU, hres, -⟩ := even_rank_two_residual_G2 hX hT
  have hk4 : Nat.card k = 4 := by rw [hk]; norm_num
  have : Finite (ModGL Tag.G2 k) := finite_modGL
  have hpp := C11P9A.parabPair_of_residual hT hres fun j =>
    C11P9A.dInf_map_ne_bot φ.symm (factG2FourParabNonsolv_holds k hk4 j)
  set ι : Y →* ModGL Tag.G2 k := (adjointGroup Tag.G2 k).subtype.comp φ.toMonoidHom with hι
  have hιi : Function.Injective ι := Subtype.val_injective.comp φ.injective
  obtain ⟨a, ha⟩ := C11AmS.exists_card_eq_of_SL2 hKq
  have hTM : T ≤ M := Subgroup.le_normalizer.trans hNT
  have hK24 : IsL24Sub T K := by
    refine ⟨fun h0 => ?_, hKK, Subgroup.le_normalizer.trans (hNT.trans hMK), hKq⟩
    rw [h0, Subgroup.card_bot] at ha
    have h60 : 60 ∣ 1 := Dvd.intro_left (2 ^ a) ha.symm
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, K = dInf (((parabolicSubgroup Tag.G2 k {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 k)).map φ.symm.toMonoidHom) := by
    rcases hpp.eq_or_eq_of_isL24Sub hK24 with hj | hj | hj
    · exact ⟨0, hj⟩
    · exact ⟨1, hj⟩
    · exfalso
      rw [hj, Subgroup.card_top] at ha
      have h9 : 9 ∣ Nat.card Y := by
        have hN := (factG2FourBorelNorm_holds k hk4).2
        have hd := Subgroup.card_subgroup_dvd_card (Subgroup.normalizer
          (((posUnipotent Tag.G2 k).subgroupOf (adjointGroup Tag.G2 k) :
            Subgroup ↥(adjointGroup Tag.G2 k)) : Set ↥(adjointGroup Tag.G2 k)))
        rw [hN, ← Nat.card_congr φ.toEquiv] at hd
        exact (Dvd.intro_left _ rfl).trans hd
      rw [ha] at h9
      have hc : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
      have := hc.dvd_of_dvd_mul_left h9
      omega
  have hKe : K.map ι = perfectCore (parabolicSubgroup Tag.G2 k {g2Index j}) := by
    rw [hj, CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, map_perfectCore,
      Subgroup.map_map]
    have e : ι.comp φ.symm.toMonoidHom = (adjointGroup Tag.G2 k).subtype := by
      ext x
      simp [hι]
    rw [e, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 k _)]
  generalize g2Index j = i at hKe
  have hmemK : ∀ g ∈ (simpleRootSL2 Tag.G2 k i).range, ∃ x ∈ K, ι x = g := fun g hg => by
    have h := C11AmS.range_simpleRootSL2_le_perfectCore hk4 i hg
    rwa [← hKe] at h
  have hTU : ∀ t ∈ T, ι t ∈ posUnipotent Tag.G2 k := by
    intro t ht
    have h1 : φ t ∈ T.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ ht
    rwa [hU, Subgroup.mem_subgroupOf] at h1
  have hOT : pCoreOf 2 M ≤ T := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (CFSG.QuasithinUnique.isSylowTwoOf_of_le hT hTM)
  obtain ⟨t₀, ht₀3, ht₀1⟩ : ∃ t : kˣ, t ^ 3 = 1 ∧ t ≠ 1 := by
    have hu : Nat.card kˣ = 3 := by rw [Nat.card_units, hk4]
    have : Nontrivial kˣ := by
      rw [← Finite.one_lt_card_iff_nontrivial, hu]
      norm_num
    obtain ⟨u, hu1⟩ := exists_ne (1 : kˣ)
    exact ⟨u, by rw [← hu]; exact pow_card_eq_one', hu1⟩
  have hconj : ∀ {S : Subgroup Y}, K ≤ Subgroup.normalizer (S : Set Y) → ∀ x ∈ K,
      ∀ g ∈ S.map ι, ι x * g * (ι x)⁻¹ ∈ S.map ι := by
    rintro S hS x hx _ ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 (hS hx) s).1 hs, by
      rw [map_mul, map_mul, map_inv]⟩
  have hi : i = g2ia ∨ i = g2ir := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hi with rfl | rfl
  ·
    exfalso
    have hVO : V ≤ pCoreOf 2 M := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV
      (IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num))
    obtain ⟨d, hdK, hdι⟩ := hmemK _ ⟨HSL t₀, simpleRootSL2_HSL g2ia t₀⟩
    obtain ⟨x, hxT, hxι⟩ : ∃ x ∈ T, ι x = pinnedX Tag.G2 k g2r 1 := by
      have hC : pinnedX Tag.G2 k g2r 1 ∈ adjointGroup Tag.G2 k := by
        rw [← xUnit_g2ir]
        exact xUnit_mem_adjointGroup g2ir 1
      have h1 : (⟨_, hC⟩ : adjointGroup Tag.G2 k) ∈ T.map φ.toMonoidHom := by
        rw [hU, Subgroup.mem_subgroupOf]
        show pinnedX Tag.G2 k g2r 1 ∈ posUnipotent Tag.G2 k
        rw [pinnedX_r_eq_g2N]
        exact g2N_mem_posUnipotent _ _ _ _ _ _
      obtain ⟨x, hx, hxe⟩ := h1
      exact ⟨x, hx, congrArg Subtype.val hxe⟩
    have hbot := C11AmS.eq_bot_of_commute_torusElt_a ht₀3 ht₀1 (N := V.map ι)
      (by
        rintro _ ⟨v, hv, rfl⟩
        exact hTU v (hOT (hVO hv)))
      (by
        rintro _ ⟨v, hv, rfl⟩
        rw [← hdι]
        exact Commute.map (show Commute d v from
          (Subgroup.mem_centralizer_iff.1 (hKV hdK) v hv).symm) ι)
      (by
        rintro _ ⟨v, hv, rfl⟩
        rw [← hxι]
        exact ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.1 (hMV (hTM hxT)) v).1 hv, by
          rw [map_mul, map_mul, map_inv]⟩)
    rw [(Subgroup.map_eq_bot_iff_of_injective V hιi).1 hbot, Subgroup.card_bot] at hV4
    omega
  ·
    have hXr : ∀ s : k, ∃ x ∈ K, ι x = pinnedX Tag.G2 k g2r s := fun s =>
      hmemK _ ⟨uSL s, (simpleRootSL2_uSL g2ir s).trans (xUnit_g2ir s)⟩
    obtain ⟨nr, hnrK, hnrι⟩ := hmemK _ ⟨WSL, simpleRootSL2_WSL g2ir⟩
    obtain ⟨d, hdK, hdι⟩ := hmemK _ ⟨HSL t₀, simpleRootSL2_HSL g2ir t₀⟩
    have hOQ : (pCoreOf 2 M).map ι ≤ g2LongRadical k := by
      refine C11AmS.le_g2LongRadical_of_conj ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hTU x (hOT hx)
      · rintro _ ⟨x, hx, rfl⟩
        rw [← hnrι]
        exact ⟨nr * x * nr⁻¹, (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hnrK)) x).1 hx, by
          rw [map_mul, map_mul, map_inv]⟩
    have hω : (t₀ : k) ^ 2 + (t₀ : k) + 1 = 0 := by
      have h3 : (t₀ : k) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ht₀3, Units.val_one]
      have h1 : ((t₀ : k) - 1) * ((t₀ : k) ^ 2 + (t₀ : k) + 1) = 0 := by
        linear_combination h3
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) ht₀1
      · exact h
    obtain ⟨c, F, hcB, hcA⟩ := C11AmS.exists_g2N_mem_sdiff hω (Subgroup.map_mono hAB)
      (fun h => hne (Subgroup.map_injective hιi h)) ((Subgroup.map_mono hBO).trans hOQ)
      (fun s g hg => by
        obtain ⟨x, hx, hxι⟩ := hXr s
        rw [← hxι]
        exact hconj hKA x hx g hg)
      (fun s g hg => by
        obtain ⟨x, hx, hxι⟩ := hXr s
        rw [← hxι]
        exact hconj hKB x hx g hg)
      (fun g hg => by
        rw [← hnrι]
        exact hconj hKA nr hnrK g hg)
      (fun g hg => by
        rw [← hnrι]
        exact hconj hKB nr hnrK g hg)
    obtain ⟨b₀, hb₀B, hb₀ι⟩ := hcB
    have hb₀A : b₀ ∉ A := fun h => hcA ⟨b₀, h, hb₀ι⟩
    have hdb : Commute d b₀ := by
      have h1 := C11AmS.commute_torusElt_r_g2N ht₀3 c F
      rw [← hdι, ← hb₀ι] at h1
      exact hιi (by simpa only [map_mul] using h1.eq)
    have hd3 : orderOf d = 3 := by
      rw [← orderOf_injective ι hιi d, hdι]
      exact C11AmS.orderOf_torusElt_r ht₀3 ht₀1
    obtain ⟨g, hgK, n, rfl⟩ := C11AmS.exists_conj_zpow_of_card ha hy hdK hy3 hd3
    refine ⟨g * b₀ * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hKB hgK) b₀).1 hb₀B,
      fun h => hb₀A ((Subgroup.mem_normalizer_iff.1 (hKA hgK) b₀).2 h), ?_⟩
    have e : g * d ^ n * g⁻¹ * (g * b₀ * g⁻¹) * (g * d ^ n * g⁻¹)⁻¹ * (g * b₀ * g⁻¹)⁻¹ =
        g * (d ^ n * b₀ * (d ^ n)⁻¹ * b₀⁻¹) * g⁻¹ := by group
    rw [e, (hdb.zpow_left n).eq, mul_inv_cancel_right, mul_inv_cancel, mul_one, mul_inv_cancel]
    exact A.one_mem

end CFSG.Quasithin.Vol2.Ch11.SecS
