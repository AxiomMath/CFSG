module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestCore
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe glCongr_symm_coe
  glCongr_statedScalars statedProjCongr)

theorem ggRawInndiagIsoOn_of_subset_inn {S : LargeEvenLabel → Prop}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)) :
    GGRawInndiagIsoOn fun lab lab' => S lab ∧ S lab' := by
  intro lab hlab Q hQ
  by_cases hS : S lab
  · refine largeEvenRawDatum_mono ?_ (h lab hlab hS Q hQ)
    rintro R _ I F ⟨hQ, hIinn⟩
    refine ⟨hQ, fun hs hna lab' hlab' hl Q' hQ' => ?_⟩
    refine largeEvenRawDatum_mono ?_ (h lab' hlab' hl.2 Q' hQ')
    rintro R' _ I' F' ⟨hQ', hI'inn⟩
    exact ⟨hQ', fun hs' hna' => ggInndiag_congr_iff_of_subset_inn (hIinn hs hna) (hI'inn hs' hna')⟩
  · refine largeEvenRawDatum_mono ?_ hQ
    intro R _ I F hQ
    exact ⟨hQ, fun _ _ lab' _ hl => absurd hl.1 hS⟩

theorem ggRawInndiagIsoOn_of_noIso {S : LargeEvenLabel → LargeEvenLabel → Prop}
    (h : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard
      fun R _ _ _ => ∀ lab', LargeEvenInLambda2 lab' → S lab lab' →
        LargeEvenLabelAll lab' (LargeEvenSimpleGuard fun R' _ _ _ => IsEmpty (R ≃* R')))) :
    GGRawInndiagIsoOn S := by
  intro lab hlab Q hQ
  refine largeEvenRawDatum_mono ?_ (h lab hlab Q hQ)
  rintro R _ I F ⟨hQ, hS⟩
  refine ⟨hQ, fun hs hna lab' hlab' hl Q' hQ' => ?_⟩
  refine largeEvenRawDatum_mono ?_ (hS hs hna lab' hlab' hl Q' hQ')
  rintro R' _ I' F' ⟨hQ', hE⟩
  exact ⟨hQ', fun hs' hna' σ _ => ((hE hs' hna').false σ).elim⟩

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K] [Field L]

theorem congr_mem_ggInndiag_of (gl : GL ι K ≃* GL ι L) {H : Subgroup (GL ι K)}
    {H' : Subgroup (GL ι L)} (τ : LargeEvenProj H ≃* LargeEvenProj H')
    (hτ : ∀ (h : H) (h₁ : H'), (h₁ : GL ι L) = gl h →
      τ (LargeEvenProjMk H h) = LargeEvenProjMk H' h₁)
    (hsurj : ∀ h₁ : H', ∃ h : H, (h₁ : GL ι L) = gl h) {S : Set (GL ι K)} {S' : Set (GL ι L)}
    (hS : ∀ A ∈ S, gl A ∈ S') {φ : MulAut (LargeEvenProj H)}
    (hφ : φ ∈ ggInndiag (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S)) :
    MulAut.congr τ φ ∈
      ggInndiag (LargeEvenProj H') (LargeEvenMatConjImage (LargeEvenProjMk H') S') := by
  have key : ∀ ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
      MulAut.congr τ ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk H') S' := by
    rintro ψ ⟨A, hA, hgr⟩
    refine ⟨gl A, hS A hA, fun h₁ h₁' hrel => ?_⟩
    obtain ⟨h, hh⟩ := hsurj h₁
    obtain ⟨h', hh'⟩ := hsurj h₁'
    have hrel' : (h' : GL ι K) = A * h * A⁻¹ := gl.injective (by
      rw [map_mul, map_mul, map_inv, ← hh, ← hh']
      exact hrel)
    have e1 : τ.symm (LargeEvenProjMk H' h₁) = LargeEvenProjMk H h := by
      rw [MulEquiv.symm_apply_eq, hτ h h₁ hh]
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, e1, hgr h h' hrel',
      hτ h' h₁' hh']
  have hle : (ggInndiag (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S)).map
      (MulAut.congr τ).toMonoidHom ≤
      ggInndiag (LargeEvenProj H') (LargeEvenMatConjImage (LargeEvenProjMk H') S') := by
    rw [ggInndiag, Subgroup.map_sup, map_congr_range_conj, MonoidHom.map_closure]
    refine sup_le le_sup_left ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨ψ, hψ, rfl⟩
    exact subset_ggInndiag (key ψ hψ)
  exact hle ⟨φ, hφ, rfl⟩

theorem glCongr_mem_gspSet (ε : K ≃+* L) {m : ℕ} {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ LargeEvenGSpSet K m) : glCongr ε A ∈ LargeEvenGSpSet L m := by
  obtain ⟨μ, hμ, hAJ⟩ := hA
  refine ⟨ε μ, (map_ne_zero ε).mpr hμ, ?_⟩
  have hJ : (LargeEvenSpForm K m).map ε = LargeEvenSpForm L m := by
    rw [largeEvenSpForm_def, largeEvenSpForm_def, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero ε),
      Matrix.map_one _ (map_zero ε) (map_one ε), Matrix.map_neg _ (map_neg ε),
      Matrix.map_one _ (map_zero ε) (map_one ε)]
  have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M.map ε) hAJ
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  rw [glCongr_coe, ← hJ, h]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

end Transport

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K] [Field L]

theorem statedProjCongr_mk (Φ : GL ι K ≃* GL ι L) {H : Subgroup (GL ι K)}
    {H' : Subgroup (GL ι L)} (hH : H.map Φ.toMonoidHom = H')
    (hZ : (CFSG.Assembly.LowTwoRank.StatedScalars ι K).map Φ.toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedScalars ι L) (h : H) (h₁ : H')
    (hh : (h₁ : GL ι L) = Φ h) :
    statedProjCongr Φ hH hZ (LargeEvenProjMk H h) = LargeEvenProjMk H' h₁ := by
  have e : (H.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hH) h = h₁ := Subtype.ext hh.symm
  rw [← e]
  rfl

theorem ggInndiag_congr_iff_of_transport (gl : GL ι K ≃* GL ι L) {H : Subgroup (GL ι K)}
    {H' : Subgroup (GL ι L)} (τ : LargeEvenProj H ≃* LargeEvenProj H')
    (hτ : ∀ (h : H) (h₁ : H'), (h₁ : GL ι L) = gl h →
      τ (LargeEvenProjMk H h) = LargeEvenProjMk H' h₁)
    (hmap : ∀ h : H, gl h ∈ H') (hsurj : ∀ h₁ : H', ∃ h : H, (h₁ : GL ι L) = gl h)
    {S : Set (GL ι K)} {S' : Set (GL ι L)} (hS : ∀ A ∈ S, gl A ∈ S')
    (hS' : ∀ B ∈ S', gl.symm B ∈ S)
    (hN : GGInndiagNormal (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S))
    (σ : LargeEvenProj H ≃* LargeEvenProj H') (φ : MulAut (LargeEvenProj H)) :
    φ ∈ ggInndiag (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) ↔
      MulAut.congr σ φ ∈
        ggInndiag (LargeEvenProj H') (LargeEvenMatConjImage (LargeEvenProjMk H') S') := by
  have hτ' : ∀ (h₁ : H') (h : H), (h : GL ι K) = gl.symm h₁ →
      τ.symm (LargeEvenProjMk H' h₁) = LargeEvenProjMk H h := by
    intro h₁ h hh
    rw [MulEquiv.symm_apply_eq]
    exact (hτ h h₁ (by rw [hh, MulEquiv.apply_symm_apply])).symm
  have hsurj' : ∀ h : H, ∃ h₁ : H', (h : GL ι K) = gl.symm h₁ :=
    fun h => ⟨⟨gl h, hmap h⟩, (gl.symm_apply_apply _).symm⟩
  have hσ : MulAut.congr σ φ = MulAut.congr τ ((σ.trans τ.symm) * φ * (σ.trans τ.symm)⁻¹) := by
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_def,
      MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hback : ∀ y : MulAut (LargeEvenProj H), MulAut.congr τ.symm (MulAut.congr τ y) = y := by
    intro y
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.symm_apply_apply]
  rw [hσ]
  constructor
  · intro hφ
    exact congr_mem_ggInndiag_of gl τ hτ hsurj hS (hN.conj_mem _ hφ)
  · intro h
    have h2 := congr_mem_ggInndiag_of gl.symm τ.symm hτ' hsurj' hS' h
    rw [hback] at h2
    have h3 := hN.conj_mem (σ.trans τ.symm)⁻¹ h2
    rwa [show (σ.trans τ.symm)⁻¹ * ((σ.trans τ.symm) * φ * (σ.trans τ.symm)⁻¹) *
      (σ.trans τ.symm)⁻¹⁻¹ = φ by group] at h3

end Transport

section B2der

variable {K L : Type} [Field K] [Field L]

theorem glCongr_map_b2der (ε : K ≃+* L) :
    (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup (GL (Fin 2 ⊕ Fin 2) K)).map
      (glCongr (ι := Fin 2 ⊕ Fin 2) ε).toMonoidHom =
      ⁅LargeEvenSpGroup L 2, LargeEvenSpGroup L 2⁆ := by
  have hSp : (LargeEvenSpGroup K 2).map (glCongr (ι := Fin 2 ⊕ Fin 2) ε).toMonoidHom =
      LargeEvenSpGroup L 2 := CFSG.Blueprint.EvenSource.glCongr_statedSp ε 2
  rw [Subgroup.map_commutator, hSp]

theorem b2der_inndiag_congr_iff [Finite K] [Finite L] (hK : Nat.card K = 2) (hL : Nat.card L = 2)
    (σ : LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃*
      LargeEvenProj ⁅LargeEvenSpGroup L 2, LargeEvenSpGroup L 2⁆)
    (φ : MulAut (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) :
    φ ∈ ggInndiag (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2)) ↔
      MulAut.congr σ φ ∈ ggInndiag (LargeEvenProj ⁅LargeEvenSpGroup L 2, LargeEvenSpGroup L 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup L 2, LargeEvenSpGroup L 2⁆)
          (LargeEvenGSpSet L 2)) := by
  have hε := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (K := K) (L := L) (hK.trans hL.symm)
  have hH := glCongr_map_b2der hε
  obtain ⟨eA⟩ := nonempty_b2der_equiv_alternatingGroup hK
  refine ggInndiag_congr_iff_of_transport (glCongr hε)
    (statedProjCongr (glCongr hε) hH (glCongr_statedScalars hε))
    (statedProjCongr_mk (glCongr hε) hH (glCongr_statedScalars hε))
    (fun h => by rw [← hH]; exact ⟨h, h.2, rfl⟩) (fun h₁ => ?_)
    (fun A hA => glCongr_mem_gspSet hε hA) (fun B hB => ?_)
    (ggInndiagNormal_of_mulEquiv_alternatingSix eA _) σ φ
  · have hm : (h₁ : GL (Fin 2 ⊕ Fin 2) L) ∈
        (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup (GL (Fin 2 ⊕ Fin 2) K)).map
          (glCongr (ι := Fin 2 ⊕ Fin 2) hε).toMonoidHom := by
      rw [hH]
      exact h₁.2
    obtain ⟨h, hh, he⟩ := hm
    exact ⟨⟨h, hh⟩, he.symm⟩
  · have e : (glCongr (ι := Fin 2 ⊕ Fin 2) hε).symm B = glCongr (ι := Fin 2 ⊕ Fin 2) hε.symm B :=
      Units.ext (by rw [glCongr_symm_coe, glCongr_coe])
    rw [e]
    exact glCongr_mem_gspSet hε.symm hB

theorem ggRawInndiagIsoOn_b2der :
    GGRawInndiagIsoOn fun lab lab' => lab.tag = .B2der ∧ lab'.tag = .B2der := by
  intro lab hlab Q hQ
  by_cases ht : lab.tag = .B2der
  · refine largeEvenLabelAll_b2der ht (fun K _ _ hK _ _ lab' _ hl => ?_) Q hQ
    exact largeEvenLabelAll_b2der hl.2 fun K' _ _ hK' _ _ σ φ => b2der_inndiag_congr_iff hK hK' σ φ
  · refine largeEvenRawDatum_mono ?_ hQ
    intro R _ I F hQ
    exact ⟨hQ, fun _ _ lab' _ hl => absurd hl.1 ht⟩

end B2der

@[expose] def GGInnSubsetLabel (lab : LargeEvenLabel) : Prop :=
  GGInnerDiagInnLabel lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

theorem largeEvenLabelAll_subset_inn_ext
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGInnSubsetLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  rcases h with h | h | h
  · exact largeEvenLabelAll_subset_inn hlab h
  · exact TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab h
  · exact largeEvenLabelAll_subset_inn_twF4 hlab h

@[expose] def GGExclNoIsoPair (lab lab' : LargeEvenLabel) : Prop :=
  (GGInndiagCommExclLabel lab ∨ GGInndiagCommExclLabel lab') ∧
    ¬ (GGInnSubsetLabel lab ∧ GGInnSubsetLabel lab') ∧ ¬ (lab.tag = .B2der ∧ lab'.tag = .B2der)

@[expose] def GGExclNoIsoInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard
    fun R _ _ _ => ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' → GGExclNoIsoPair lab lab' →
      LargeEvenLabelAll lab' (LargeEvenSimpleGuard fun R' _ _ _ => IsEmpty (R ≃* R')))

theorem ggRawInndiagIsoExclInput_of_noIso
    (hN : GGExclNoIsoInput) : GGRawInndiagIsoExclInput := by
  refine ggRawInndiagIsoOn_of_or (ggRawInndiagIsoOn_of_subset_inn (S := GGInnSubsetLabel)
    fun lab hlab h => largeEvenLabelAll_subset_inn_ext hlab h)
    (ggRawInndiagIsoOn_of_or ggRawInndiagIsoOn_b2der (ggRawInndiagIsoOn_of_noIso hN)
      fun _ _ h => h) ?_
  rintro lab lab' ⟨-, hX⟩
  by_cases h1 : GGInnSubsetLabel lab ∧ GGInnSubsetLabel lab'
  · exact Or.inl h1
  by_cases h2 : lab.tag = .B2der ∧ lab'.tag = .B2der
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hX, h1, h2⟩)

end CFSG.StandardType

end
