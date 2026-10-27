module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2Part2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner
import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallUnitary
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnField
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
open CFSG.StandardType.F4ExplicitPos.RationalA2
open CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG.StandardType.F4ExplicitPos.SelectedLiteral
open CFSG.StandardType.F4ExplicitPos.RationalA2Finish
open CFSG.StandardType.F4ExplicitPos.NativePinFinal
open CFSG.StandardType.F4ExplicitPos.UnitaryPair
open scoped Matrix MatrixGroups

private theorem l10lG4b_step_injective
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {D : LangDatum Tag.F4 Ω} {f : ℕ} (hqf : D.q = 2 ^ f) :
    Function.Injective D.step := by
  obtain ⟨Fr, hFr, P, -, hΦ⟩ := D.steinberg
  have hFr_eq : Fr = iterateFrobenius Ω 2 f := by
    ext c
    simp only [hFr c, iterateFrobenius_def, hqf]
  have hFr_inj : Function.Injective Fr := by
    rw [hFr_eq]
    exact (iterateFrobenius Ω 2 f).injective
  have hU_inj : Function.Injective (Units.map (entrywiseHom Fr) :
      ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) :=
    Units.map_injective (f := entrywiseHom Fr) (entrywise_injective Fr)
  have hΦ_eq : D.Φ = (MulAut.conj P).toMonoidHom.comp
      (Units.map (entrywiseHom Fr) : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) := by
    ext g
    rw [hΦ g]
    rfl
  have hΦ_inj : Function.Injective D.Φ := by
    rw [hΦ_eq]
    exact (MulAut.conj P).injective.comp hU_inj
  have hstep_eq : D.step = (MulAut.conj D.n).toMonoidHom.comp D.Φ := rfl
  rw [hstep_eq]
  exact (MulAut.conj D.n).injective.comp hΦ_inj

private theorem l10lG4b_model_of_unitary_frame
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] [IsAlgClosure k Ω]
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    (hstep_inj : Function.Injective D.step)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ)
    (hframe : IsSLFrame ρ r) (hρinj : Function.Injective ρ)
    (hframe_eq : frameRoots r = componentRoots χ i)
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (π : Equiv.Perm (Fin 3))
    (hunitary : ∀ a b : Fin 3, a ≠ b → ρperm (r a b) = r (π b) (π a)) :
    GGLieSU3Model ↥(rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model) f := by
  classical
  have hρrange : ρ.range = rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [hframe.range, hframe_eq]
  obtain ⟨ρ₀, hρeq, hρ₀par⟩ := step_pinnedX_F4_perm (Ω := Ω) D ρperm hρperm
  let σ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω 2 f
  have hσc : ∀ c : Ω, σ c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def Ω 2 f c
  have hσq : ∀ c : Ω, σ c = c ^ D.q := by intro c; rw [hσc, hq]
  have hρ₀unitary : ∀ a b : Fin 3, a ≠ b → ρ₀ (r a b) = r (π b) (π a) := by
    intro a b hab
    exact (hρeq (r a b) (hframe.isRoot a b hab)).symm.trans (hunitary a b hab)
  have hΨ : ∀ a b : Fin 3, a ≠ b → ∃ bu : Ωˣ, ∀ c : Ω,
      D.step (pinnedX Tag.F4 Ω (r a b) c) =
        pinnedX Tag.F4 Ω (r (π b) (π a)) ((bu : Ω) * σ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := hρ₀par (r a b) (hframe.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hρ₀unitary a b hab]
    congr 2
    rw [hσq]
  obtain ⟨Φ', hΦ', bu, hshape⟩ :=
    inducedAut_unitary (τ := Tag.F4) (L := Ω) hframe hρinj σ.toRingHom σ.bijective D.step
      hstep_inj π hΨ
  have hΦ'' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : Ω),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single (π b) (π a) ((bu a b : Ω) * t ^ 2 ^ f) := by
    intro a b hab t
    rw [hshape a b hab t, show σ.toRingHom t = t ^ 2 ^ f from hσc t]
  obtain ⟨H, -, hfix⟩ :=
    unitary_full_intertwining (ℓ := 2) (f := f) (k := k) (Ω := Ω) Nat.prime_two hf hk
      (n := 3) (by norm_num) σ.toRingHom hσc π Φ' bu hΦ''
  obtain ⟨F, μ, hF, hFcard, -, -, -, -, -, -⟩ :=
    exists_unitary_opposite_pair (Ω := Ω) hf σ hσc
  have hNdef : (kappaSU ρ H F 2 f).range = ρ.range ⊓ D.model := by
    rw [kappaSU_range (ρ := ρ) (H := H) F (ℓ := 2) (f := f) Nat.prime_two hF hFcard hρinj
      D.step Φ' hΦ' hfix, LangDatum.model, ← inf_assoc,
      inf_eq_left.mpr hframe.range_le_adjointGroup]
  have hrange : (kappaSU ρ H F 2 f).range =
      rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    rw [hNdef, hρrange]
  have hκinj : Function.Injective (kappaSU ρ H F 2 f) :=
    kappaSU_injective ρ H F 2 f hρinj
  have : Finite F :=
    Nat.finite_of_card_ne_zero (by rw [hFcard]; exact pow_ne_zero 2 (by norm_num))
  exact ⟨F, inferInstance, inferInstance, hFcard,
    ⟨((MonoidHom.ofInjective hκinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩⟩

private theorem l10lG4b_model_long
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {D : LangDatum Tag.F4 Ω} {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f)
    (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hout : ¬ twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u))
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots (jointChar a₁ a₂) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport) :
    GGLieSU3Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  classical
  set ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
      (f4rhoLong_actual (K := Ω)) with hρAdef
  set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
    fun a b => v • chainRoot f4chainLong a b with hr
  have hframeA : IsA2Frame ρA r := f4Long_frame_actual_transport (L := Ω) v
  have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
  have hframe_eq : frameRoots r = componentRoots (jointChar a₁ a₂) i := by
    rw [frameRoots_f4chainLong_smul (v := v), hΨ]
  have hρinj : Function.Injective ρA := hframeA.injective
  have hnorm : ∀ a b : Fin 3, a ≠ b → iform (r a b) (r a b) = 2 * (2 : ℤ) := by
    intro a b hab
    have h1 : iform (r a b) (r a b) =
        iform (chainRoot f4chainLong a b) (chainRoot f4chainLong a b) := by
      rw [hr, iform_smul]
    rw [h1]
    exact (f4_long12_isRoot a b hab).2.2
  have hmaps : ∀ a b : Fin 3, a ≠ b →
      (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) (r a b) ∈ frameRoots r := by
    intro a b hab
    have hmem : r a b ∈ componentRoots (jointChar a₁ a₂) i := by
      rw [← hframe_eq]; exact ⟨a, b, hab, rfl⟩
    have h2 : ρ (r a b) ∈
        (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
          componentRoots (jointChar a₁ a₂) i := Set.mem_image_of_mem _ hmem
    rw [hρΨ] at h2
    rwa [hframe_eq]
  obtain ⟨π, hunitary⟩ := exists_unitary_perm_of_not_twistInner (ν := 3) (by norm_num)
    hframe (κ := 2) (by norm_num) hnorm hmaps h.frob.neg_eq h.frob.iform_eq
    (by rw [hframe_eq]; exact hout)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosure (ZMod 2) Ω := ⟨inferInstance, inferInstance⟩
  let k : Type := ↥(CFSG.GH74.GLS.Stage2.Bender.Thm1.frobFixField 2 Ω f)
  have : IsAlgClosure k Ω :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.isAlgClosure_frobFixField 2 Ω
      (K := ZMod 2) (m := 1) (n := f) (by rw [Nat.card_zmod, pow_one]) (one_dvd f)
  have hkcard : Nat.card k = 2 ^ f :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.card_frobFixField 2 Ω hf
  exact l10lG4b_model_of_unitary_frame (k := k) hf hkcard D hqf
    (l10lG4b_step_injective hqf) i ρA r hframe hρinj hframe_eq ρ h.frob π hunitary

private theorem l10lG4b_model_short
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {D : LangDatum Tag.F4 Ω} {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f)
    (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hout : ¬ twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u))
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots (jointChar a₁ a₂) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport) :
    GGLieSU3Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  classical
  set ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
      (f4rhoShort_actual (K := Ω)) with hρAdef
  set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
    fun a b => v • f4ShortSigma a b with hr
  have hframeA : IsA2Frame ρA r := f4Short_frame_actual_transport (L := Ω) v
  have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
  have hframe_eq : frameRoots r = componentRoots (jointChar a₁ a₂) i := by
    rw [frameRoots_f4ShortSigma_smul (v := v), hΨ]
  have hρinj : Function.Injective ρA := hframeA.injective
  have hnorm : ∀ a b : Fin 3, a ≠ b → iform (r a b) (r a b) = 2 * (1 : ℤ) := by
    intro a b hab
    have h1 : iform (r a b) (r a b) =
        iform (f4ShortSigma a b) (f4ShortSigma a b) := by
      rw [hr, iform_smul]
    rw [h1]
    exact (f4_short_isRoot a b hab).2.2
  have hmaps : ∀ a b : Fin 3, a ≠ b →
      (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) (r a b) ∈ frameRoots r := by
    intro a b hab
    have hmem : r a b ∈ componentRoots (jointChar a₁ a₂) i := by
      rw [← hframe_eq]; exact ⟨a, b, hab, rfl⟩
    have h2 : ρ (r a b) ∈
        (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
          componentRoots (jointChar a₁ a₂) i := Set.mem_image_of_mem _ hmem
    rw [hρΨ] at h2
    rwa [hframe_eq]
  obtain ⟨π, hunitary⟩ := exists_unitary_perm_of_not_twistInner (ν := 3) (by norm_num)
    hframe (κ := 1) (by norm_num) hnorm hmaps h.frob.neg_eq h.frob.iform_eq
    (by rw [hframe_eq]; exact hout)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosure (ZMod 2) Ω := ⟨inferInstance, inferInstance⟩
  let k : Type := ↥(CFSG.GH74.GLS.Stage2.Bender.Thm1.frobFixField 2 Ω f)
  have : IsAlgClosure k Ω :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.isAlgClosure_frobFixField 2 Ω
      (K := ZMod 2) (m := 1) (n := f) (by rw [Nat.card_zmod, pow_one]) (one_dvd f)
  have hkcard : Nat.card k = 2 ^ f :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.card_frobFixField 2 Ω hf
  exact l10lG4b_model_of_unitary_frame (k := k) hf hkcard D hqf
    (l10lG4b_step_injective hqf) i ρA r hframe hρinj hframe_eq ρ h.frob π hunitary

theorem ggLieF4A2out_fixedGroup_alg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {D : LangDatum Tag.F4 Ω}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 2 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 6)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hout : ¬ twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u)) :
    GGLieSU3Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  have ha : ∀ j, a₁ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₁) h.pow₁
  have hd : ∀ j, a₂ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₂) h.pow₂
  have hne : rootDiagUnit Tag.F4 a₁ ≠ 1 ∨ rootDiagUnit Tag.F4 a₂ ≠ 1 := by
    by_contra hc
    have hb₁ : rootDiagUnit Tag.F4 a₁ = 1 := by
      by_contra hb; exact hc (Or.inl hb)
    have hb₂ : rootDiagUnit Tag.F4 a₂ = 1 := by
      by_contra hb; exact hc (Or.inr hb)
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 Ω)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    have hcard := h.card
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨w, hcases⟩ :=
    CFSG.StandardType.F4ExplicitPos.JointShapes.f4_joint_component_six_shape
      (p := 3) (by norm_num) (by norm_num) a₁ a₂ ha hd hne i
  rcases hcases with ⟨j, hj⟩ | hlong | hshort | hb2 | hB3 | hC3
  · exfalso
    have h6 := hshape.2
    rw [hj, ncard_image_smul] at h6
    have h2 : ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
      rw [Set.ncard_pair]
      intro hcontra
      have := congrFun hcontra j
      norm_num at this
    rw [h2] at h6
    omega
  · exact l10lG4b_model_long h hf hqf i hρΨ hout w hlong
  · exact l10lG4b_model_short h hf hqf i hρΨ hout w hshort
  · exfalso
    exact hout (CFSG.StandardType.F4ExplicitPos.B2Inner.b2_component_rho_twistInner
      (χ := jointChar a₁ a₂) (D := D) (ρ := ρ) h.frob i hb2 hρΨ)
  · exfalso
    have h2 := hshape.1
    rw [hB3, compRank_image] at h2
    rw [CFSG.StandardType.F4ExplicitPos.SelectedLiteral.compRank_parabolicRoots_f4LeviB3] at h2
    omega
  · exfalso
    have h2 := hshape.1
    rw [hC3, compRank_image] at h2
    rw [CFSG.StandardType.F4ExplicitPos.SelectedLiteral.compRank_parabolicRoots_f4LeviC3] at h2
    omega

end CFSG.StandardType.LieCore

end
