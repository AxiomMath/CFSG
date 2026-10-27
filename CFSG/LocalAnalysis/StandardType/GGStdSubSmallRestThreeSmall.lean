module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace StdSubRestThree

variable {G : Type} [Group G] [Finite G]

theorem ggStdSubSmallHyp_of_config {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hsm : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) {a : MulAut L}
    (hJE : J = (LargeEvenLayer (ggFix a)).map L.subtype) :
    GGStdSubSmallHyp p (ggGamma L hBN).range a := by
  intro E hE hEJ hEfix hor
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have hfix : ∀ b : B, ∀ e ∈ E, ggGamma L hBN b e = e := fun b e he => hEfix _ ⟨b, rfl⟩ e he
  have hEB : E.map L.subtype ≤ B := by
    rcases hor with hconj | ⟨U, hU, hU2, hUA, hEU⟩
    · rintro _ ⟨e, he, rfl⟩
      exact mem_of_conj_mem_range hp hS hBN (hE.2 e he) (fun b => hfix b e he) (hconj e he)
    · exact map_le_of_twoGroup hp hS.1 hBN hE hfix hU hU2 (fun b u hu => hUA _ ⟨b, rfl⟩ u hu)
        hEU
  have hEJ' : E.map L.subtype ≤ J := hJE ▸ Subgroup.map_mono hEJ
  have hle : E.map L.subtype ≤ Bs ⊓ J := le_inf (hEB.trans hcfg.2.1.1) hEJ'
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
  exact h1.trans_lt hsm

end StdSubRestThree

open StdSubRestThree

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggStdSubInputs_of_twoTorusNormSmall (ha₀ : GGLNoncyclicInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hsm : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusNormSmall p r R I ∧
        GGStdSubTwoTorusDeltaSmall p r R I) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G) := by
  have hnc := ha₀ G p B x L hcfg.1
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBs : GGBstar p B Bs := hcfg.2.1
  obtain ⟨hDB, hDe, hDcard, hxD, hJdef, hJcomp, hDC⟩ := hcfg.2.2.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBN, h3⟩, hOD, r, hlift, htn, htd⟩ :=
    largeEvenRawDatum_exists hraw
  set γ := ggGamma L hBN with hγ
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨d, hdD, hdx⟩ := exists_mem_not_mem_zpowers hp hDcard (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
    eq_sup_zpowers_of_card hp hDe hDcard hxD hS.2.2.1 hdD hdx
  set d₀ : B := ⟨d, hDB hdD⟩ with hd₀
  set a := γ d₀ with ha
  have hfix : (ggFix a).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d₀
  have hJE : J = (LargeEvenLayer (ggFix a)).map L.subtype := by
    rw [hJdef, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  have hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
    have h1 := isComponentOf_comap_of_injective L.subtype L.subtype_injective
      (K' := J) (C := ggFix a) (by rw [hfix]; exact hJcomp)
    have h2 : J.comap L.subtype = LargeEvenLayer (ggFix a) := by
      rw [hJE, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [← h2]
    exact h1.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [ha, ggGamma_eq_one_iff] at h
    apply hdx
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hDB hdD, h⟩
  have hcentA : ∀ a' ∈ γ.range,
      ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
    rintro _ ⟨b, rfl⟩
    constructor
    · intro hb
      have hbJ : (b : G) ∈ B ⊓ Subgroup.centralizer (J : Set G) := by
        refine ⟨b.2, ?_⟩
        show (b : G) ∈ Subgroup.centralizer (J : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hJE] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        have h1 := congrArg Subtype.val (hb j hj)
        rw [ggGamma_coe] at h1
        calc (j : G) * b = b * j * (b : G)⁻¹ * b := by rw [h1]
          _ = b * j := by group
      rw [← hDC] at hbJ
      set H := (Subgroup.zpowers a).comap γ with hH
      have hxH : (⟨x, hS.2.1⟩ : B) ∈ H := by
        change γ ⟨x, hS.2.1⟩ ∈ Subgroup.zpowers a
        rw [(ggGamma_eq_one_iff L hBN _).mpr (mem_centralizer_of_le_centralizer hLx)]
        exact one_mem _
      have hdH : d₀ ∈ H := Subgroup.mem_zpowers a
      have hDH : D ≤ H.map B.subtype := by
        rw [hD]
        exact sup_le (Subgroup.zpowers_le.mpr ⟨_, hxH, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨_, hdH, rfl⟩)
      obtain ⟨b', hb'H, hb'⟩ := hDH hbJ
      have hbb : b' = b := Subtype.ext hb'
      rw [← hbb]
      exact hb'H
    · intro hmem j hj
      have hj1 : a j = j := mem_ggFix.mp (hEcomp.1 hj)
      have hstab : a ∈ MulAction.stabilizer (MulAut L) j :=
        MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hj1)
      have h1 := MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hstab) hmem)
      rwa [MulAut.smul_def] at h1
  have hsmall : GGStdSubSmallHyp p γ.range a := ggStdSubSmallHyp_of_config hcfg hsm hBN hJE
  have hconcl : GGStdSubTwoTorusConcl p γ.range a := by
    rcases ggNormTwoR_or_delta hp hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hα | hδ
    · exact htn L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA
        hAI hr h3' hα a ⟨d₀, rfl⟩ ha1 hEcomp hcentA hsmall
    · exact htd L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA
        hAI hr h3' (ggDeltaAdm_of_delta hp hS hBN hδ) a ⟨d₀, rfl⟩ ha1 hEcomp hcentA hsmall
  obtain ⟨U, hU, hU2, hUE, hAU, t, htE, htp, htA, htU, j, hjE, htj⟩ := hconcl
  set T := U.map L.subtype with hTdef
  have hT1 : T ≠ ⊥ := by
    rw [Ne, hTdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hT2 : IsPGroup 2 T := hU2.map _
  have hTJ : T ≤ J := hJE ▸ Subgroup.map_mono hUE
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨u, hu, rfl⟩
    exact ⟨γ ⟨b, hb⟩ u, hAU _ ⟨⟨b, hb⟩, rfl⟩ u hu, ggGamma_coe L hBN ⟨b, hb⟩ u⟩
  refine ⟨ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hT1, hT2, hTJ, hBT⟩, ?_⟩
  have ht'J : (t : G) ∈ J := hJE ▸ ⟨t, htE, rfl⟩
  have ht'p : (t : G) ^ p = 1 := by
    rw [← Subgroup.coe_pow, htp, Subgroup.coe_one]
  have ht'B : ∀ b ∈ B, ∀ c ∈ Subgroup.zpowers (t : G), b * c = c * b := by
    intro b hb c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 : b * (t : G) = (t : G) * b := by
      have h2 := congrArg Subtype.val (htA _ ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at h2
      calc b * (t : G) = b * (t : G) * b⁻¹ * b := by group
        _ = (t : G) * b := by rw [h2]
    exact (Commute.zpow_right h1 k)
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers (t : G)) :=
    isElemAbelian_sup hS.1.1 (isElemAbelian_zpowers ht'p) ht'B
  have htN : (t : G) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer_map L.subtype ⟨t, htU, rfl⟩
  have hEN : B ⊔ Subgroup.zpowers (t : G) ≤ Subgroup.normalizer (T : Set G) :=
    sup_le hBT (Subgroup.zpowers_le.mpr htN)
  have hcard := card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hEN hE
  rw [← hS.1.2.1] at hcard
  have hBE := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers (t : G)) hcard
  have htB : (t : G) ∈ B := hBE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (t : G))
  refine ⟨t, ⟨hBs.1 htB, ht'J⟩, fun hC => htj ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hC (j : G) (hJE ▸ ⟨j, hjE, rfl⟩)
  exact Subtype.ext h1.symm

end Config

theorem ggStdSubSmallInputOn_of_labels_normSmall (ha₀ : GGLNoncyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusNormSmall p r R I ∧
          GGStdSubTwoTorusDeltaSmall p r R I) :
    GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM hsm
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  exact ggStdSubInputs_of_twoTorusNormSmall ha₀ hcfg hsm
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')

end CFSG.StandardType
