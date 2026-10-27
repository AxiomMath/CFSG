module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6
public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistWeyl
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth

public noncomputable section


namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TwE6Lang
  CFSG.StandardType.TBE6IndTwist

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6_nrep_eq_weylHom (w : WeylGroup .E6) :
    nrep (e6Datum_isCTGroupDatum K) w = weylHom K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .E6).exists_isReduced w
  rw [nrep_wordProd (e6Datum_isCTGroupDatum K) hω]
  change (ω.map (e6Data_valid.nm K)).prod = weylHom K ((ω.map (simple .E6)).prod)
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, weylHom_simple]

theorem e6W0_eq_frameLongest :
    (e6W0 K : WeylGroup .E6) = frameLongest := by
  refine CFSG.LieType.Chevalley.ext_single (τ := .E6)
    (w := (e6W0 K : WeylGroup .E6)) (w' := frameLongest) ?_
  intro i
  have h := frameLongest_rho (rho (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
  rw [rho_rho, rho_single] at h
  exact (e6W0_table K i).trans h.symm

theorem langG_lang_eq_e6_nrep (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    {l : K} (hl : σ l = l + 1) :
    (langG K σ.toRingHom l)⁻¹ *
        (e6Frob σ.toRingHom hσ).φ (langG K σ.toRingHom l) =
      nrep (e6Datum_isCTGroupDatum K) (e6W0 K) := by
  have hne : σ.toRingHom l ≠ l := by
    change σ l ≠ l
    rw [hl]
    exact add_ne_left.mpr one_ne_zero
  have hd : negDelta σ.toRingHom hne = 1 := by
    apply Units.ext
    change -(l - σ l) = (1 : K)
    rw [hl]
    ring
  have hs := sigma_langG σ.toRingHom hσ hne
  change (langG K σ.toRingHom l)⁻¹ * sigma K σ.toRingHom (langG K σ.toRingHom l) = _
  rw [hs, hd, langMM_one, ← e6W0_eq_frameLongest (K := K),
    ← e6_nrep_eq_weylHom (K := K)]
  group




open CFSG.LieType.BorelTits CFSG.LieType.Universal
open CFSG.StandardType CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer

theorem exists_e6_rootNormalizer_lang (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ c, σ c ≠ c) :
    ∃ g : e6Data_valid.minGroup K,
      g ∈ Subgroup.normalizer (CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup (nd 1) :
        Set (e6Data_valid.minGroup K)) ∧
      g⁻¹ * (e6Frob σ.toRingHom hσ).φ g =
        nrep (e6Datum_isCTGroupDatum K) (e6W0 K) := by
  have hσ1 : σ ≠ 1 := by
    intro hs
    obtain ⟨c, hc⟩ := hne
    exact hc (by simpa [hs])
  have hσσ : σ * σ = 1 := by
    ext c
    exact hσ c
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  refine ⟨langG K σ.toRingHom l, ?_, langG_lang_eq_e6_nrep σ hσ hl⟩
  have hroot : frameRoot 0 = eOne := by
    funext i
    fin_cases i <;> rfl
  change langG K σ.toRingHom l ∈ Subgroup.normalizer
    (TwE6Lang.rankOne K eOne : Set (e6Data_valid.minGroup K))
  simpa only [hroot] using langG_mem_normalizer_rankOne σ.toRingHom l

theorem exists_e6_fixed_primitive_root_with_params {k : Type} [Field k]
    (σ : K ≃+* K) (e : k →+* K)
    (hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range e)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup K σ.toRingHom,
      Function.Injective phi ∧
      (∀ t, (phi (sl2Upper t) : e6Data_valid.minGroup K) = e6Data_valid.xm K (Pi.single i 1) (e t)) ∧
      (∀ t, (phi (sl2Lower t) : e6Data_valid.minGroup K) = e6Data_valid.xm K (-Pi.single i 1) (e t)) ∧
      (sl2UpperUniSub k).map phi =
        (twistedDatum K σ.toRingHom).rootGroup (proj (Pi.single i 1)) ∧
      (∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (twistedDatum K σ.toRingHom)) ∧
      phi.range.map (fixedGroup K σ.toRingHom).subtype =
        CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup i ⊓ fixedGroup K σ.toRingHom := by
  have he (c : k) : σ.toRingHom (e c) = e c := (hfix _).2 ⟨c, rfl⟩
  have hfixed (c : K) (hc : σ.toRingHom c = c) : ∃ a, e a = c := (hfix c).1 hc
  obtain ⟨phi, hphi, hu, hl⟩ := exists_sl2Hom_fixed σ.toRingHom e he i hi
  obtain ⟨P, hP, hPu, hPl⟩ := e6Data_valid.exists_sl2Hom K i
  let E := (fixedGroup K σ.toRingHom).subtype
  have hEP : E.comp phi = P.comp (Matrix.SpecialLinearGroup.map e) := by
    apply MonoidHom.eq_of_eqOn_dense closure_sl2Upper_sl2Lower_eq_top
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change (phi (sl2Upper c) : e6Data_valid.minGroup K) =
        P (Matrix.SpecialLinearGroup.map e (sl2Upper c))
      rw [sl2_map_upper, hPu]
      exact hu c
    · change (phi (sl2Lower c) : e6Data_valid.minGroup K) =
        P (Matrix.SpecialLinearGroup.map e (sl2Lower c))
      rw [sl2_map_lower, hPl]
      exact hl c
  have hσP : (sigma K σ.toRingHom).comp P =
      P.comp (Matrix.SpecialLinearGroup.map σ.toRingHom) := by
    apply MonoidHom.eq_of_eqOn_dense closure_sl2Upper_sl2Lower_eq_top
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change sigma K σ.toRingHom (P (sl2Upper c)) =
        P (Matrix.SpecialLinearGroup.map σ.toRingHom (sl2Upper c))
      rw [hPu, sigma_xm_single, hi, sl2_map_upper, hPu]
    · change sigma K σ.toRingHom (P (sl2Lower c)) =
        P (Matrix.SpecialLinearGroup.map σ.toRingHom (sl2Lower c))
      rw [hPl, sigma_xm_neg_single, hi, sl2_map_lower, hPl]
  let O := Classical.choice (e6_nonempty_commOrder (k := K))
  have hE := (e6Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E6 K
    posDef_cartan_E6 neighbour_E6 O).2
  have hle := CFSG.LieType.Steinberg.rankOne_le_range_of_sl2 hE.param i hPu hPl
  have hr : CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup i = P.range :=
    CFSG.ClassicalInvolution.ModelFacts.rankOne_eq_range_of_sl2 P
      (fun c => by rw [hPu c]; exact e6Data_valid.xm_mem_rootGroup K _ _)
      (fun c => by rw [hPl c]; exact e6Data_valid.xm_mem_rootGroup K _ _) hle
  refine ⟨phi, hphi, hu, hl,
    map_sl2UpperUniSub_eq_twistedRootGroup σ.toRingHom e he hfixed i
      hi phi hu, ?_, ?_⟩
  · intro a
    apply RootDetectTwE6.mem_ggTorus_twisted σ.toRingHom
    have hmap : Matrix.SpecialLinearGroup.map e (sl2Diag a) =
        sl2Diag (Units.map e.toMonoidHom a) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_sl2Diag]
    change E (phi (sl2Diag a)) ∈ ggTorus (e6Datum K)
    rw [show E (phi (sl2Diag a)) = P (Matrix.SpecialLinearGroup.map e (sl2Diag a)) from
      DFunLike.congr_fun hEP _, hmap]
    exact map_sl2Diag_mem_ggTorus hE i P hPu hPl _
  · apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨g, ⟨M, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨?_, (phi M).property⟩
      rw [hr]
      exact ⟨Matrix.SpecialLinearGroup.map e M, (DFunLike.congr_fun hEP M).symm⟩
    · rintro ⟨hx, hxf⟩
      rw [hr] at hx
      obtain ⟨M, rfl⟩ := hx
      have hM : Matrix.SpecialLinearGroup.map σ.toRingHom M = M :=
        hP ((DFunLike.congr_fun hσP M).symm.trans hxf)
      obtain ⟨A, hA⟩ := CFSG.SeitzReduction.OmegaPilot.exists_map_eq_of_fixed e hfix hM
      exact Subgroup.mem_map.2 ⟨phi A, ⟨A, rfl⟩,
        (DFunLike.congr_fun hEP A).trans (congrArg P hA)⟩

theorem exists_e6_fixed_primitive_root {k : Type} [Field k]
    (σ : K ≃+* K) (e : k →+* K)
    (hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range e) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup K σ.toRingHom,
      Function.Injective phi ∧
      (sl2UpperUniSub k).map phi =
        (twistedDatum K σ.toRingHom).rootGroup (proj eOne) ∧
      (∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (twistedDatum K σ.toRingHom)) ∧
      phi.range.map (fixedGroup K σ.toRingHom).subtype =
        CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup (nd 1) ⊓ fixedGroup K σ.toRingHom := by
  obtain ⟨phi, hphi, -, -, hup, hdiag, hrootimage⟩ :=
    exists_e6_fixed_primitive_root_with_params σ e hfix (nd 1) rhoPerm_nd_one
  exact ⟨phi, hphi, hup, hdiag, hrootimage⟩

section NativeNode

open CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.LieEmbed

theorem exists_e6_stdConfig_primitive_node {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ (γ : Fin (ggU .twistedE6 0 f).D.rank → ℤ)
      (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* (ggU .twistedE6 0 f).K),
      Function.Injective phi ∧ γ ∈ (ggU .twistedE6 0 f).D.roots ∧
      (sl2UpperUniSub (GaloisField 2 f)).map phi = (ggU .twistedE6 0 f).D.rootGroup γ ∧
      (∀ a : (GaloisField 2 f)ˣ, phi (sl2Diag a) ∈ ggTorus (ggU .twistedE6 0 f).D) ∧
      ∃ v : (ggU .twistedE6 0 f).K,
        phi.range.map (MulAut.conj v).toMonoidHom = ((e6StdConfig F f hF hf).S.ι (1 : Fin 6)).range := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K0 := GaloisField 2 (2 * f)
  let σ := frobQEquiv hf
  have hσeq : σ.toRingHom = frobQ 2 f := rfl
  have hσ : ∀ c : K0, σ (σ c) = c := frobQ_frobQ 2 f hf
  have hne : ∃ c : K0, σ c ≠ c := exists_frobQ_ne hf
  have hfix : ∀ c : K0, σ c = c ↔ c ∈ Set.range (gfEmbed 2 f hf).toRingHom :=
    fun c => frobQ_eq_iff_mem_range 2 f hf c
  obtain ⟨phi, hphi, hup, hdiag, hrootimage⟩ :=
    exists_e6_fixed_primitive_root (K := K0) σ (gfEmbed 2 f hf).toRingHom hfix
  let S := e6StdInput (frobQ 2 f) (frobQ_frobQ 2 f hf)
    (exists_frobQ_ne hf) (exists_mul_frobQ_eq hf)
  let efix := e6FrobFixEquiv (frobQ 2 f) (frobQ_frobQ 2 f hf)
  let E := (fixedGroup K0 (frobQ 2 f)).subtype
  let B := CFSG.LieType.CurtisTits.rankOne (e6Datum K0).rootGroup (nd 1)
  let N := ((S.family efix (e6Kappa hF hf) (e6Kappa_spec hF hf)).ι (nd 1)).range
  let A := S.F.φ
  let n0 := nrep S.hct S.w₀
  let z := S.lang
  obtain ⟨g, hgN, hg0⟩ := exists_e6_rootNormalizer_lang (K := K0) σ hσ hne
  have hg : g⁻¹ * A g = n0 := hg0
  have hz : z⁻¹ * A z = n0 := S.lang_spec
  have herange : E.range = MonoidHom.eqLocus A (MonoidHom.id (e6Data_valid.minGroup K0)) := by
    change (fixedGroup K0 (frobQ 2 f)).subtype.range = fixedGroup K0 (frobQ 2 f)
    exact (fixedGroup K0 (frobQ 2 f)).range_subtype
  have hN : N.map ((MulAut.conj z⁻¹).toMonoidHom.comp E) =
      B ⊓ MonoidHom.eqLocus ((MulAut.conj n0).toMonoidHom.comp A)
        (MonoidHom.id (e6Data_valid.minGroup K0)) :=
    S.map_node_family_eq_rankOne_inf_stdFix efix (e6Kappa hF hf) (e6Kappa_spec hF hf) (nd 1)
  have hR : phi.range.map E =
      B ⊓ MonoidHom.eqLocus A (MonoidHom.id (e6Data_valid.minGroup K0)) := hrootimage
  obtain ⟨v, hv⟩ := Subgroup.exists_conj_of_lang_node_images A hz hg B hgN E
    Subtype.val_injective herange N phi.range hN hR
  have hstd : ((e6StdConfig F f hF hf).S.ι (1 : Fin 6)).range = N :=
    congrArg MonoidHom.range (PhanEConfig.iota_ofEq
      (S.config efix (e6Kappa hF hf) (e6Kappa_spec hF hf)) (coxeterMatrix_e6Datum K0) (nd 1))
  refine ⟨proj eOne, phi, hphi, ?_, hup, hdiag, v, hv.trans hstd.symm⟩
  change proj eOne ∈ (twistedDatum K0 (frobQ 2 f)).roots
  rw [twistedDatum_roots]
  exact isRoot_proj (isRoot_single .E6 (nd 1))

end NativeNode

end CFSG.ClassicalInvolution.Phan.PhanE
