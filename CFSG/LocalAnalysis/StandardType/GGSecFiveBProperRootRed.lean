module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryRankThreeCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.Line63.H5

variable {G : Type} [Group G] [Finite G]

private theorem redMkL_gamma_eq {X Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hNbar : (redMkB hN).range ≤ Subgroup.normalizer ((redMkL X).range : Set (RedGrp X)))
    (hinj : Function.Injective (redMkL X)) (b : Bs) (l : X) :
    ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b)
        (MonoidHom.ofInjective hinj l) =
      MonoidHom.ofInjective hinj (ggGamma X hN b l) := by
  apply Subtype.ext
  rw [ggGamma_coe]
  rw [MonoidHom.ofInjective_apply]
  exact redMk_conj (L := X) (Subgroup.inclusion hN b) l

theorem exists_model_of_redMkL_of_twoCenter_eq_bot {X Bs : Subgroup G} (hz : twoCenter X = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hNbar : (redMkB hN).range ≤ Subgroup.normalizer ((redMkL X).range : Set (RedGrp X)))
    {F : Type} [Field F] {f d : ℕ} {φ : ↥(unitarySU 2 f F d) →* (redMkL X).range}
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma (redMkL X).range hNbar).range, ∃ t : Fin d → F,
      LineU.ActsDiagU φ a t) :
    ∃ ψ : ↥(unitarySU 2 f F d) →* X, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t := by
  have hinj : Function.Injective (redMkL X) := by
    intro x y hxy
    have hmem : ((x * y⁻¹ : X) : G) ∈ twoCenter X := by
      rw [← redMkL_eq_one_iff]
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hz] at hmem
    have hxy' : x * y⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    exact mul_inv_eq_one.mp hxy'
  let e : X ≃* (redMkL X).range := MonoidHom.ofInjective hinj
  let ψ : ↥(unitarySU 2 f F d) →* X := e.symm.toMonoidHom.comp φ
  refine ⟨ψ, ⟨hM.field, e.symm.surjective.comp hM.surj, ?_⟩, ?_⟩
  · intro g hg
    apply hM.ker g
    have h2 : e.symm (φ g) = 1 := by simpa [ψ] using hg
    calc φ g = e (e.symm (φ g)) := (e.apply_symm_apply _).symm
      _ = e 1 := by rw [h2]
      _ = 1 := map_one e
  · rintro a ⟨b, rfl⟩
    obtain ⟨t, D, hD, hd, hact⟩ := hdiag
      (ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b))
      ⟨(redMkB hN).rangeRestrict b, rfl⟩
    refine ⟨t, D, hD, hd, ?_⟩
    intro s
    change ggGamma X hN b (e.symm (φ s)) = e.symm (φ (LineU.conjN D hD s))
    apply e.injective
    rw [e.apply_symm_apply]
    calc
      e (ggGamma X hN b (e.symm (φ s))) =
          ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b)
            (e (e.symm (φ s))) := (redMkL_gamma_eq hN hNbar hinj b _).symm
      _ = ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b) (φ s) := by
        rw [e.apply_symm_apply]
      _ = φ (LineU.conjN D hD s) := hact s

omit [Finite G] in
theorem unitaryTwoRawDatum {X Bs : Subgroup G} {r : ℕ}
    (hRig : GGLabelRigidInput) (hInn : GGInnerDiagOn Bs X)
    (hLab : GGHasLabel ⟨.twA, r, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, 1⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (_ : commutator X = ⊤)
      (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (unitarySU 2 1 F (r + 1)))
      (_ : Bs ≤ Subgroup.normalizer (X : Set G)),
      Nat.card F = 4 ∧
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (unitarySU 2 1 F (r + 1))) (LargeEvenGUSet (Fin (r + 1)) F (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  classical
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
  obtain ⟨_, _, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  exact ⟨F, hField, hFinite, this, hXperf, θ, hN, hF, hBsI⟩

theorem exists_diagonal_cover_of_unitary_four_two_of_twoCenter_eq_bot
    (hRig : GGLabelRigidInput) {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hInn : GGInnerDiagOn Bs X) (hz : twoCenter X = ⊥)
    (hLab : GGHasLabel ⟨.twA, 3, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, 1⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (φ : ↥(unitarySU 2 1 F 4) →* X),
      Nat.card F = (2 ^ 1) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 4 → F, LineU.ActsDiagU φ a t := by
  obtain ⟨F, hField, hFinite, hChar, hXp, θ, hN, hF, hBsI⟩ :=
    unitaryTwoRawDatum (r := 3) hRig hInn hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_four_two_red hF hXp θ hN hBs hBsI
  obtain ⟨ψ, hMψ, hdiagψ⟩ :=
    exists_model_of_redMkL_of_twoCenter_eq_bot hz hN hNbar hM hdiag
  exact ⟨F, hField, hFinite, hChar, hN, ψ, by simpa using hF, hMψ, hdiagψ⟩

theorem exists_diagonal_cover_of_unitary_six_two_of_twoCenter_eq_bot
    (hRig : GGLabelRigidInput) {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hInn : GGInnerDiagOn Bs X) (hz : twoCenter X = ⊥)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hcard : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (φ : ↥(unitarySU 2 1 F 6) →* X),
      Nat.card F = (2 ^ 1) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
  obtain ⟨F, hField, hFinite, hChar, hXp, θ, hN, hF, hBsI⟩ :=
    unitaryTwoRawDatum (r := 5) hRig hInn hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hXp θ hN hBs hBsI (hcard hN)
  obtain ⟨ψ, hMψ, hdiagψ⟩ :=
    exists_model_of_redMkL_of_twoCenter_eq_bot hz hN hNbar hM hdiag
  exact ⟨F, hField, hFinite, hChar, hN, ψ, by simpa using hF, hMψ, hdiagψ⟩

end CFSG.StandardType

end
