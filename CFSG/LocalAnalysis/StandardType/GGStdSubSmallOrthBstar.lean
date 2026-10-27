module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInner
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreField
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace SmallOrth

theorem largeEvenLabelAll_bstarEq_twDFour {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : TwDFourLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨ht, hl, hn2, hpq⟩ := h
  have hn1 : 1 ≤ lab.n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn1 hpq
  by_cases hpn : p ∣ lab.n
  · have hfield : GGIOneMoreFieldLabel p lab :=
      Or.inr (Or.inl ⟨ht, by omega, ⟨2, by omega⟩, hpq, hpn⟩)
    exact largeEvenLabelAll_and (ggIOneMoreFieldCorFourTwoInput_holds p lab hp hlab hfield)
      (IOneMore.largeEvenLabelAll_normAbove_field hp hlab hfield)
  · have horth : GGIOneMoreOrthEqLabel p lab :=
      Or.inl ⟨ht, by omega, ⟨2, by omega⟩, hpq, hpn⟩
    exact (largeEvenLabelAll_bstarEq_orthEq hp hp2 horth).mono
      fun _ _ _ _ ⟨hb, r, hr, hrk⟩ => ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩

theorem largeEvenLabelAll_twDFour_data {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : TwDFourLabel p lab) (hI : TwDFourInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I := by
  refine largeEvenLabelAll_and (largeEvenLabelAll_bstarEq_twDFour hp hlab h) ?_
  obtain ⟨ht, hl, hn2, hpq⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hn2 hpq
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩ := hQ
    have hcen := ggOrthRestCenterInput_holds.1 K n 3 p b c hK (le_refl 3) hp hpq hbc
    exact ⟨K, i1, i2, hK, b, c, hbc, hQ', 3,
      ggOrthRestTorusLiftInput_holds.1 K n 3 p b c hK (le_refl 3) hp hpq hbc,
      ggStdSubTwoTorusInnerSmall_of_elt hp OrthRest.ggOutdiagPrime_inn hcen.1 hcen.2
        (hI K n p b c hK hn2 hp hpq hbc)⟩

end SmallOrth

open StdSubRestThree

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggStdSubInputs_of_innerSmall (ha₀ : GGLNoncyclicInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hsm : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G) := by
  have hnc := ha₀ G p B x L hcfg.1
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBs : GGBstar p B Bs := hcfg.2.1
  obtain ⟨hDB, hDe, hDcard, hxD, hJdef, hJcomp, hDC⟩ := hcfg.2.2.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBN, h3⟩, ⟨⟨r₁, hl₁, hb⟩, r₂, hl₂, hn⟩, r₃, hl₃, hinner⟩ :=
    largeEvenRawDatum_exists hraw
  have hBeq : B = Bs := bstar_eq_of_bound_norm hcfg.1 hBs hnc hL θ hBN h3 hl₁ hb hl₂ hn
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
    rw [← hBeq]
    exact hDC.symm.le
  refine ⟨hI1, ?_⟩
  set γ := ggGamma L hBN with hγ
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hl₃
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
  obtain ⟨t, htE, htp, htA, htc, j, hjE, htj⟩ :=
    hinner L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr
      h3' a ⟨d₀, rfl⟩ ha1 hEcomp hcentA hsmall
  have htB : (t : G) ∈ B :=
    mem_of_conj_mem_range hp hS hBN htp (fun b => htA _ ⟨b, rfl⟩) htc
  have ht'J : (t : G) ∈ J := hJE ▸ ⟨t, htE, rfl⟩
  refine ⟨t, ⟨hBeq ▸ htB, ht'J⟩, fun hC => htj ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hC (j : G) (hJE ▸ ⟨j, hjE, rfl⟩)
  exact Subtype.ext h1.symm

end Config

theorem ggStdSubSmallInputOn_of_labels_innerSmall (ha₀ : GGLNoncyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
          ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I) :
    GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM hsm
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  exact ggStdSubInputs_of_innerSmall ha₀ hcfg hsm
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')


theorem ggStdSubSmallInputOn_twDFour_of_input (hI : SmallOrth.TwDFourInput) :
    GGStdSubSmallInputOn SmallOrth.TwDFourLabel :=
  ggStdSubSmallInputOn_of_labels_innerSmall ggLNoncyclicInput_holds fun _ _ hp hlab hS _ =>
    SmallOrth.largeEvenLabelAll_twDFour_data hp hlab hS hI

end CFSG.StandardType

end
