module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Milestones.CL_LIT_Curtis_Tits_presentation_theorem
public import CFSG.LieType.CurtisTits.Unitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGMpLinearLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ ¬ (2 ^ lab.n - 1).Coprime (lab.rank + 1)

@[expose] def GGMpUnitaryLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)

theorem ggInnerDiagInnLabel_or_rest (lab : LargeEvenLabel) (h : ¬ GGInnerDiagInnLabel lab) :
    GGMpLinearLabel lab ∨ GGMpUnitaryLabel lab ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
      lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der := by
  obtain ⟨t, l, n⟩ := lab
  simp only [GGInnerDiagInnLabel, GGInndiagInnLabel, GGLinearInnLabel, not_or, not_and] at h
  simp only [GGMpLinearLabel, GGMpUnitaryLabel]
  cases t <;> simp_all

section Cover

theorem ggInnerDiagMpInputOn_mono {S T : LargeEvenLabel → Prop}
    (hST : ∀ lab, LargeEvenInLambda2 lab → S lab → T lab) (hT : GGInnerDiagMpInputOn T) :
    GGInnerDiagMpInputOn S := by
  intro G _ _ t n f ψ hadm hrk hker G₀ hrange P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  exact hT G t n f ψ hadm hrk hker G₀ hrange P ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, h, hθ⟩ => ⟨hs, hna, θ, hST lab hlab h, hθ⟩) hraw⟩

theorem ggInnerDiagMpInputOn_or {S T : LargeEvenLabel → Prop} (hS : GGInnerDiagMpInputOn S)
    (hT : GGInnerDiagMpInputOn T) : GGInnerDiagMpInputOn fun lab => S lab ∨ T lab := by
  intro G _ _ t n f ψ hadm hrk hker G₀ hrange P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  obtain ⟨R, _, I, F, -, -, θ, h, -⟩ := largeEvenRawDatum_exists hraw
  rcases h with h | h
  · exact hS G t n f ψ hadm hrk hker G₀ hrange P ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hθ⟩ => ⟨hs, hna, θ, h, hθ⟩) hraw⟩
  · exact hT G t n f ψ hadm hrk hker G₀ hrange P ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hθ⟩ => ⟨hs, hna, θ, h, hθ⟩) hraw⟩

theorem ggInnerDiagMpInputOn_rest_of_families (hA : GGInnerDiagMpInputOn GGMpLinearLabel)
    (hU : GGInnerDiagMpInputOn GGMpUnitaryLabel)
    (hE6 : GGInnerDiagMpInputOn fun lab => lab.tag = .E6)
    (h2E6 : GGInnerDiagMpInputOn fun lab => lab.tag = .twE6)
    (hD4 : GGInnerDiagMpInputOn fun lab => lab.tag = .triD4)
    (hF4 : GGInnerDiagMpInputOn fun lab => lab.tag = .twF4)
    (hB : GGInnerDiagMpInputOn fun lab => lab.tag = .B2der) :
    GGInnerDiagMpInputOn fun lab => ¬ GGInnerDiagInnLabel lab :=
  ggInnerDiagMpInputOn_mono (fun lab _ h => ggInnerDiagInnLabel_or_rest lab h)
    (ggInnerDiagMpInputOn_or hA (ggInnerDiagMpInputOn_or hU (ggInnerDiagMpInputOn_or hE6
      (ggInnerDiagMpInputOn_or h2E6 (ggInnerDiagMpInputOn_or hD4
        (ggInnerDiagMpInputOn_or hF4 hB))))))

end Cover

section Transport

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*} [Group G] (ψ : U →* G)

@[expose] def GGRevProp (G₀ : Subgroup G) {R : Type} [Group R] (J : Set (MulAut R))
    (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R) : Prop :=
  ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
    (∃ φ ∈ J, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) →
      GGPsiInnerDiag Δ ψ c

variable {Δ ψ}

theorem ggRevProp_of_inndiagNormal {G₀ : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (hN : GGInndiagNormal R I) {θ₀ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R}
    (h₀ : GGRevProp Δ ψ G₀ (ggInndiag R I) θ₀) (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R) :
    GGRevProp Δ ψ G₀ I θ := by
  rintro c hc ⟨φ, hφ, hind⟩
  let β : MulAut R := θ.symm.trans θ₀
  refine h₀ c hc ⟨β * φ * β⁻¹, hN β φ hφ, fun l l' hl => ?_⟩
  have h1 : β⁻¹ (θ₀ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l) := by
    rw [MulAut.inv_apply]
    exact (MulEquiv.symm_apply_eq β).mpr (by simp [β])
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, hind l l' hl]
  simp [β]

end Transport

section Std

@[expose] def GGInnerDiagStdOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K →
    ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        MarkedModel lab R → Nonempty (↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R) →
          ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R,
            GGRevProp (ggU t n f).D ψ ψ.range (ggInndiag R I) θ₀)


theorem ggInnerDiagMpInputOn_of_std {S : LargeEvenLabel → Prop}
    (hN : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I))
    (hstd : GGInnerDiagStdOn S) : GGInnerDiagMpInputOn S := by
  intro G _ _ t n f ψ hadm hrk hker G₀ hrange P hP
  subst hrange
  obtain ⟨hperf, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hP
  obtain ⟨R, _, I, F, -, -, θ, ⟨hS, -⟩, -⟩ := largeEvenRawDatum_exists hraw
  have hraw' := hstd G t n f ψ hadm hrk hker lab hlab hS _ (hN lab hlab hS _ hraw)
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨⟨hs, hna, θ, ⟨-, hP⟩, hM⟩, hNg⟩, hstdg⟩
  obtain ⟨θ₀, h₀⟩ := hstdg hs hna hM ⟨θ⟩
  exact ⟨hs, hna, θ, hP, ggRevProp_of_inndiagNormal (hNg hs hna) h₀ θ⟩

end Std

section Model

theorem ggU_perfect_lieModel {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hrk : 2 ≤ (ggU t n f).D.rank) :
    commutator (ggU t n f).K = ⊤ ∧
      LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f := by
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hCT : 3 ≤ bnRank t n → commutator (ggU t n f).K = ⊤ ∧
      LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f := fun h3 => by
    obtain ⟨⟨-, hq, hm⟩, -⟩ :=
      CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} t n 2 f hadm h3
    exact ⟨hq.1.commutator_eq_top, hm⟩
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    have hm : 2 ≤ m := hrk
    exact ⟨(SpecialLinear.isQuasisimple m (GaloisField 2 f) hm).1.commutator_eq_top,
      Or.inl ⟨by simp [classicalTags],
        SpecialLinear.statedClassicalModel_center_quotient m (GaloisField 2 f) hadm hcard⟩⟩
  | PSU =>
    have e : lieUniversal .PSU n 2 f Nat.prime_two =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [lieUniversal, hf, ↓reduceDIte]
    have h := (CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} hadm
      (card_galoisField_two_mul 2 f hf)).1
    rw [ggU, e]
    exact ⟨h.2.1.1.commutator_eq_top, h.2.2⟩
  | PSp =>
    exact ⟨(Symplectic.isQuasisimple_of_admissible n (GaloisField 2 f) hadm
      hcard).1.commutator_eq_top,
      Or.inl ⟨by simp [classicalTags],
        Symplectic.statedClassicalModel_center_quotient n (GaloisField 2 f) hadm hcard⟩⟩
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus => exact hCT (by simp only [bnRank]; have := hadm.2.2; omega)
  | POmegaMinus => exact hCT (by simp only [bnRank]; have := hadm.2.2; omega)
  | F4 => exact hCT (by simp [bnRank])
  | E6 => exact hCT (by simp [bnRank])
  | E7 => exact hCT (by simp [bnRank])
  | E8 => exact hCT (by simp [bnRank])
  | twistedE6 => exact hCT (by simp [bnRank])
  | G2 => exact absurd hrk (by change ¬ 2 ≤ 0; omega)
  | trialityD4 => exact absurd hrk (by change ¬ 2 ≤ 0; omega)
  | twistedB2 => exact absurd hrk (by change ¬ 2 ≤ 0; omega)
  | twistedG2 => exact absurd hrk (by change ¬ 2 ≤ 0; omega)
  | twistedF4 => exact absurd hrk (by change ¬ 2 ≤ 0; omega)
  | Tits => exact absurd hrk (by change ¬ 2 ≤ 0; omega)

theorem lieModel_range_centerQuot {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hrk : 2 ≤ (ggU t n f).D.rank)
    (ψ : (ggU t n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) :
    LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f := by
  obtain ⟨hperf, hmodel⟩ := ggU_perfect_lieModel hadm hrk
  have hZ : Subgroup.center ↥ψ.range = (Subgroup.center (ggU t n f).K).map ψ.rangeRestrict := by
    ext l
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
    constructor
    · intro hu
      exact ⟨u, InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker hu, rfl⟩
    · rintro ⟨v, hv, hvu⟩
      rw [← hvu, Subgroup.mem_center_iff]
      intro l'
      obtain ⟨w, rfl⟩ := ψ.rangeRestrict_surjective l'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hv w]
  exact lieModel_of_mulEquiv' (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective
    ψ.rangeRestrict ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    hZ) hmodel

end Model

end CFSG.StandardType
