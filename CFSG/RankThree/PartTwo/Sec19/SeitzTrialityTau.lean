module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

variable {X : Type} [Field X] (σ : X ≃+* X)

theorem sl2_map_sigma_eq_iff (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g = g ↔
      ∃ y : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
        g = Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y := by
  constructor
  · intro h
    have hfix : ∀ i j, σ (g.1 i j) = g.1 i j := fun i j =>
      congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) X => M.1 i j) h
    let M : Matrix (Fin 2) (Fin 2) (fixSubfield σ) :=
      Matrix.of fun i j => (⟨g.1 i j, hfix i j⟩ : fixSubfield σ)
    have hdet : M.det = 1 := by
      apply (fixSubfield σ).subtype.injective
      rw [RingHom.map_det, map_one]
      have : (fixSubfield σ).subtype.mapMatrix M = g.1 := by
        ext i j
        rfl
      rw [this]
      exact g.2
    refine ⟨⟨M, hdet⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rfl
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    ext i j
    exact RingHom.mem_eqLocusField.mp (y.1 i j).2

end Plain

section Tau


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}


open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem entrywise_xd [CharP X 2] {p : ℕ} (hp : p < 24) (δ : X →+* X) (c : X) :
    Units.map (entrywiseHom δ) ((xd p c : adjointGroup d4 X) : ModGL d4 X) =
      ((xd p (δ c) : adjointGroup d4 X) : ModGL d4 X) := by
  have h2 : (2 : X) = 0 := CharTwo.two_eq_zero
  show _ = ((xPar (rootOperatorFamily d4) (d4Root p) (δ c) : adjointGroup d4 X) : ModGL d4 X)
  rw [CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ (isRoot_d4 hp),
    CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ (isRoot_d4 hp)]
  apply Units.ext
  rw [Units.coe_map]
  exact entrywise_pinnedX δ _ c


theorem coe_tauAut (x : C0 σ) :
    ((tauAut σ x : C0 σ) : ModGL TwistTag.D4.tag X) =
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag X) :=
  coe_fieldActor σ σ x

theorem tauAut_pow_three (P : D4Par n X σ) : tauAut σ ^ 3 = 1 := by
  have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [P.sigma_pow_three, map_one] at h
  exact h.symm

theorem coe_iotaA (P : D4Par n X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    ((iotaA P g : C0 σ) : ModGL TwistTag.D4.tag X) =
      (((CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom g :
        CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
          adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
            ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) := by
  have h1 := coe_eC P (iotaA P g)
  have h2 : eC P (iotaA P g) =
      CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom g :=
    (eC P).apply_symm_apply _
  rw [h2] at h1
  exact h1.symm

theorem coe_etaB (P : D4Par n X σ) (h : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :
    ((etaB P h : C0 σ) : ModGL TwistTag.D4.tag X) =
      (((CFSG.RankThree.PartOne.SEITZ7.psiB σ.toRingHom P.sigma_cube_hom h :
        CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
          adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
            ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) := by
  have h1 := coe_eC P (etaB P h)
  have h2 : eC P (etaB P h) =
      CFSG.RankThree.PartOne.SEITZ7.psiB σ.toRingHom P.sigma_cube_hom h :=
    (eC P).apply_symm_apply _
  rw [h2] at h1
  exact h1.symm

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem entrywise_xA [CharP X 2] (c : X) :
    Units.map (entrywiseHom σ.toRingHom) ((xA σ.toRingHom c : adjointGroup d4 X) : ModGL d4 X) =
      ((xA σ.toRingHom (σ c) : adjointGroup d4 X) : ModGL d4 X) := by
  simp only [xA, Subgroup.coe_mul, map_mul]
  rw [entrywise_xd (by norm_num) σ.toRingHom c, entrywise_xd (by norm_num) σ.toRingHom,
    entrywise_xd (by norm_num) σ.toRingHom]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem entrywise_xAm [CharP X 2] (c : X) :
    Units.map (entrywiseHom σ.toRingHom) ((xAm σ.toRingHom c : adjointGroup d4 X) : ModGL d4 X) =
      ((xAm σ.toRingHom (σ c) : adjointGroup d4 X) : ModGL d4 X) := by
  simp only [xAm, Subgroup.coe_mul, map_mul]
  rw [entrywise_xd (by norm_num) σ.toRingHom c, entrywise_xd (by norm_num) σ.toRingHom,
    entrywise_xd (by norm_num) σ.toRingHom]
  rfl


open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem tau_iotaA (P : D4Par n X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    tauAut σ (iotaA P g) = iotaA P (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  haveI := P.charP
  let Ψ₁ : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ := (tauAut σ).toMonoidHom.comp (iotaA P)
  let Ψ₂ : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
    (iotaA P).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  have hgen : Set.EqOn Ψ₁ Ψ₂ (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · apply Subtype.ext
      show ((tauAut σ (iotaA P (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) =
        ((iotaA P (Matrix.SpecialLinearGroup.map σ.toRingHom
          (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X)
      have e : Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.sl2Upper c) =
          CFSG.LieType.Steinberg.sl2Upper (σ c) := map_uSL (f := σ.toRingHom) c
      rw [e, coe_tauAut, coe_iotaA, coe_iotaA, slShort_upper_xA, slShort_upper_xA]
      exact entrywise_xA c
    · apply Subtype.ext
      show ((tauAut σ (iotaA P (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) =
        ((iotaA P (Matrix.SpecialLinearGroup.map σ.toRingHom
          (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X)
      have e : Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.sl2Lower c) =
          CFSG.LieType.Steinberg.sl2Lower (σ c) := map_vSL (f := σ.toRingHom) c
      rw [e, coe_tauAut, coe_iotaA, coe_iotaA, slShort_lower_xAm, slShort_lower_xAm]
      exact entrywise_xAm c
  have hmem : g ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)]
    exact Subgroup.mem_top g
  exact MonoidHom.eqOn_closure hgen hmem


open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem tau_etaB (P : D4Par n X σ) (h : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :
    tauAut σ (etaB P h) = etaB P h := by
  haveI := P.charP
  let Ψ₁ : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) →* C0 σ :=
    (tauAut σ).toMonoidHom.comp (etaB P)
  have hfix : ∀ c : fixSubfield σ, σ.toRingHom (c : X) = (c : X) := fun c =>
    RingHom.mem_eqLocusField.mp c.2
  have hgen : Set.EqOn Ψ₁ (etaB P)
      (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (fixSubfield σ)) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (fixSubfield σ))) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · apply Subtype.ext
      show ((tauAut σ (etaB P (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) = ((etaB P (CFSG.LieType.Steinberg.sl2Upper c) : C0 σ) :
          ModGL TwistTag.D4.tag X)
      rw [coe_tauAut, coe_etaB, psiB_upper]
      have := entrywise_xd (X := X) (p := 22) (by norm_num) σ.toRingHom (c : X)
      rw [hfix c] at this
      exact this
    · apply Subtype.ext
      show ((tauAut σ (etaB P (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) = ((etaB P (CFSG.LieType.Steinberg.sl2Lower c) : C0 σ) :
          ModGL TwistTag.D4.tag X)
      rw [coe_tauAut, coe_etaB, psiB_lower]
      have := entrywise_xd (X := X) (p := 23) (by norm_num) σ.toRingHom (c : X)
      rw [hfix c] at this
      exact this
  have hmem : h ∈ Subgroup.closure
      (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (fixSubfield σ)) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (fixSubfield σ))) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixSubfield σ)]
    exact Subgroup.mem_top h
  exact MonoidHom.eqOn_closure hgen hmem


theorem Bsub_le_Gsub (P : D4Par n X σ) : Bsub σ ≤ Gsub σ := by
  intro b hb
  rw [Bsub_eq_range_etaB P] at hb
  obtain ⟨h, rfl⟩ := hb
  exact tau_etaB P h

theorem tau_mem_Asub (P : D4Par n X σ) {x : C0 σ} (hx : x ∈ Asub σ) : tauAut σ x ∈ Asub σ := by
  rw [← iotaA_range P] at hx ⊢
  obtain ⟨g, rfl⟩ := hx
  exact ⟨_, (tau_iotaA P g).symm⟩

theorem mem_A0sub_iff (P : D4Par n X σ) {x : C0 σ} :
    x ∈ A0sub σ ↔ ∃ y : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      x = iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y) := by
  constructor
  · rintro ⟨hA, hG⟩
    rw [← iotaA_range P] at hA
    obtain ⟨g, rfl⟩ := hA
    have hτ : tauAut σ (iotaA P g) = iotaA P g := hG
    rw [tau_iotaA P g] at hτ
    have h1 := iotaA_injective P hτ
    obtain ⟨y, hy⟩ := (sl2_map_sigma_eq_iff σ g).mp h1
    exact ⟨y, by rw [← hy]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← iotaA_range P]
      exact ⟨_, rfl⟩
    · show tauAut σ (iotaA P _) = iotaA P _
      rw [tau_iotaA P, (sl2_map_sigma_eq_iff σ _).mpr ⟨y, rfl⟩]

theorem tauAut_ne_one (P : D4Par n X σ) : tauAut σ ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := P.exists_not_fixed
  have h2 : tauAut σ (iotaA P (CFSG.LieType.Steinberg.sl2Upper c)) =
      iotaA P (CFSG.LieType.Steinberg.sl2Upper c) := by
    rw [h1]
    rfl
  rw [tau_iotaA P] at h2
  have h3 := iotaA_injective P h2
  have h4 := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) X => (M : Matrix (Fin 2) (Fin 2) X) 0 1) h3
  have e : Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.sl2Upper c) =
      CFSG.LieType.Steinberg.sl2Upper (σ c) := map_uSL (f := σ.toRingHom) c
  rw [e] at h4
  simp [CFSG.LieType.Steinberg.sl2Upper] at h4
  exact hc h4

end Tau

end CFSG.RankThree.PartTwo.Sec19
