module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

variable {Ω : Type} [Field Ω]

theorem trialityC_mulVec_eq_reflect
    (α : Fin Tag.D4.rank → ℤ) :
    trialityC *ᵥ α = reflect Tag.D4 2 (reflect Tag.D4 0 (permLattice trialityRho α)) := by
  rw [(triality_three_six_unimodular_A2_root_partition).1, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, (triality_three_six_unimodular_A2_root_partition).2.1 α,
    reflMat_mulVec, reflMat_mulVec]

theorem twelveW_mulVec_eq_reflect
    (α : Fin TwistTag.D4.tag.rank → ℤ) :
    twelveW *ᵥ α =
      reflect TwistTag.D4.tag 2 (reflect TwistTag.D4.tag 0 (permLattice TwistTag.D4.perm α)) :=
  trialityC_mulVec_eq_reflect α

theorem isRoot_twelveW_mulVec
    {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) : IsRoot TwistTag.D4.tag (twelveW *ᵥ α) := by
  rw [twelveW_mulVec_eq_reflect]
  exact IsRoot.reflect 2 (IsRoot.reflect 0 (hα.permLattice (TwistTag.cartan_perm _)))

theorem isRoot_twelveW_pow_mulVec
    (k : ℕ) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) : IsRoot TwistTag.D4.tag ((twelveW ^ k) *ᵥ α) := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact isRoot_twelveW_mulVec ih

theorem trialityM_conj_pinnedX
    {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    ∃ η : Ω, η * η = 1 ∧ ∀ c : Ω, trialityM Ω * pinnedX TwistTag.D4.tag Ω α c *
      (trialityM Ω)⁻¹ = pinnedX TwistTag.D4.tag Ω (twelveW *ᵥ α) (η * c) := by
  obtain ⟨ε₁, h₁, hP⟩ := diagramMap_conj_pinnedX (K := Ω) TwistTag.D4 hα
  have hβ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α) :=
    hα.permLattice (TwistTag.cartan_perm _)
  obtain ⟨ε₂, h₂, h0⟩ := weylElt_mul_pinnedX_mul_inv Ω 0 hβ
  obtain ⟨ε₃, h₃, h2⟩ := weylElt_mul_pinnedX_mul_inv Ω 2 (IsRoot.reflect 0 hβ)
  refine ⟨ε₃ * (ε₂ * ε₁), by
    linear_combination (ε₂ * ε₁) * (ε₂ * ε₁) * h₃ + ε₁ * ε₁ * h₂ + h₁, fun c => ?_⟩
  rw [twelveW_mulVec_eq_reflect]
  calc trialityM Ω * pinnedX TwistTag.D4.tag Ω α c * (trialityM Ω)⁻¹ =
      weylElt TwistTag.D4.tag Ω 2 1 * (weylElt TwistTag.D4.tag Ω 0 1 *
        (diagramMap TwistTag.D4 Ω * pinnedX TwistTag.D4.tag Ω α c *
          (diagramMap TwistTag.D4 Ω)⁻¹) * (weylElt TwistTag.D4.tag Ω 0 1)⁻¹) *
        (weylElt TwistTag.D4.tag Ω 2 1)⁻¹ := by
        simp only [trialityM, trialityTwistN]
        group
    _ = _ := by
        rw [hP, h0, h2]
        congr 1
        ring

theorem trialityM_pow_conj_pinnedX
    (k : ℕ) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    ∃ η : Ω, η * η = 1 ∧ ∀ c : Ω, trialityM Ω ^ k * pinnedX TwistTag.D4.tag Ω α c *
      (trialityM Ω ^ k)⁻¹ = pinnedX TwistTag.D4.tag Ω ((twelveW ^ k) *ᵥ α) (η * c) := by
  induction k with
  | zero => exact ⟨1, one_mul 1, fun c => by simp⟩
  | succ k ih =>
    obtain ⟨η, hη, h⟩ := ih
    obtain ⟨η', hη', h'⟩ :=
      trialityM_conj_pinnedX (Ω := Ω) (isRoot_twelveW_pow_mulVec k hα)
    refine ⟨η' * η, by linear_combination η * η * hη' + hη, fun c => ?_⟩
    have hconj : ∀ a b x : ModGL TwistTag.D4.tag Ω, a * b * x * (a * b)⁻¹ =
        a * (b * x * b⁻¹) * a⁻¹ := fun a b x => by group
    calc trialityM Ω ^ (k + 1) * pinnedX TwistTag.D4.tag Ω α c * (trialityM Ω ^ (k + 1))⁻¹ =
        trialityM Ω * (trialityM Ω ^ k * pinnedX TwistTag.D4.tag Ω α c *
          (trialityM Ω ^ k)⁻¹) * (trialityM Ω)⁻¹ := by
          rw [pow_succ', hconj]
      _ = _ := by
          rw [h, h', pow_succ', ← Matrix.mulVec_mulVec, mul_assoc]

theorem units_map_entrywiseHom_pinnedX_D4
    (Fr : Ω →+* Ω) (α : Fin TwistTag.D4.tag.rank → ℤ)
    (c : Ω) : Units.map (entrywiseHom Fr) (pinnedX TwistTag.D4.tag Ω α c) =
      pinnedX TwistTag.D4.tag Ω α (Fr c) :=
  Units.ext (entrywise_pinnedX Fr α c)

theorem threeSixFrob_eq_conj
    (Fr : Ω →+* Ω) (ε : ℤ) (g : ModGL TwistTag.D4.tag Ω) :
    threeSixFrob Ω Fr ε g = trialityM Ω ^ threeSixExp ε * Units.map (entrywiseHom Fr) g *
      (trialityM Ω ^ threeSixExp ε)⁻¹ := by
  rw [threeSixFrob_apply, trialityFrob_apply, threeSixN]
  group

theorem threeSixFrob_pinnedX
    (Fr : Ω →+* Ω) (ε : ℤ) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    ∃ η : Ω, η * η = 1 ∧ ∀ c : Ω, threeSixFrob Ω Fr ε (pinnedX TwistTag.D4.tag Ω α c) =
      pinnedX TwistTag.D4.tag Ω (threeSixW ε *ᵥ α) (η * Fr c) := by
  obtain ⟨η, hη, h⟩ := trialityM_pow_conj_pinnedX (Ω := Ω) (threeSixExp ε) hα
  exact ⟨η, hη, fun c => by
    rw [threeSixFrob_eq_conj, units_map_entrywiseHom_pinnedX_D4, h]
    rfl⟩

theorem isRoot_threeSixW_mulVec
    (ε : ℤ) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) : IsRoot TwistTag.D4.tag (threeSixW ε *ᵥ α) :=
  isRoot_twelveW_pow_mulVec _ hα

theorem map_rootSubgroup_of_pinnedX
    (f : ModGL TwistTag.D4.tag Ω →* ModGL TwistTag.D4.tag Ω)
    {φ : Ω → Ω} (hφ : Function.Surjective φ) {α β : Fin TwistTag.D4.tag.rank → ℤ} {η : Ω}
    (hη : η * η = 1) (h : ∀ c : Ω, f (pinnedX TwistTag.D4.tag Ω α c) =
      pinnedX TwistTag.D4.tag Ω β (η * φ c)) :
    (rootSubgroup TwistTag.D4.tag Ω α).map f = rootSubgroup TwistTag.D4.tag Ω β := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact mem_rootSubgroup.2 ⟨_, (h c).symm⟩
  · intro hy
    obtain ⟨c', rfl⟩ := mem_rootSubgroup.1 hy
    obtain ⟨c, hc⟩ := hφ (η * c')
    refine ⟨pinnedX TwistTag.D4.tag Ω α c, mem_rootSubgroup.2 ⟨c, rfl⟩, ?_⟩
    rw [h, hc, ← mul_assoc, hη, one_mul]

theorem map_rootSpan_of_map_rootSubgroup
    (f : ModGL TwistTag.D4.tag Ω →* ModGL TwistTag.D4.tag Ω)
    {w : (Fin TwistTag.D4.tag.rank → ℤ) → Fin TwistTag.D4.tag.rank → ℤ}
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (h : ∀ α ∈ S, (rootSubgroup TwistTag.D4.tag Ω α).map f = rootSubgroup TwistTag.D4.tag Ω (w α)) :
    (rootSpan TwistTag.D4.tag Ω S).map f = rootSpan TwistTag.D4.tag Ω (w '' S) := by
  rw [rootSpan, rootSpan, Subgroup.map_iSup, iSup_image]
  refine iSup_congr fun α => ?_
  rw [Subgroup.map_iSup]
  refine le_antisymm (iSup_le fun hα => ?_) (iSup_le fun hα => ?_)
  · rw [h α hα]
    exact le_iSup_of_le hα le_rfl
  · rw [← h α hα]
    exact le_iSup_of_le hα le_rfl

theorem map_conj_trialityM_pow_rootSpan
    (ε : ℤ) {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α) :
    (rootSpan TwistTag.D4.tag Ω S).map (MulAut.conj (trialityM Ω ^ threeSixExp ε)).toMonoidHom =
      rootSpan TwistTag.D4.tag Ω ((fun α => threeSixW ε *ᵥ α) '' S) := by
  refine map_rootSpan_of_map_rootSubgroup _ fun α hα => ?_
  obtain ⟨η, hη, h⟩ := trialityM_pow_conj_pinnedX (Ω := Ω) (threeSixExp ε) (hS α hα)
  exact map_rootSubgroup_of_pinnedX _ Function.surjective_id hη fun c => h c

theorem map_threeSixFrob_rootSpan
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) (ε : ℤ)
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α) :
    (rootSpan TwistTag.D4.tag Ω S).map (threeSixFrob Ω Fr ε) =
      rootSpan TwistTag.D4.tag Ω ((fun α => threeSixW ε *ᵥ α) '' S) := by
  refine map_rootSpan_of_map_rootSubgroup _ fun α hα => ?_
  obtain ⟨η, hη, h⟩ := threeSixFrob_pinnedX (Ω := Ω) Fr ε (hS α hα)
  exact map_rootSubgroup_of_pinnedX _ hFr hη h

theorem threeSixFrob_injective
    (Fr : Ω →+* Ω) (ε : ℤ) :
    Function.Injective (threeSixFrob Ω Fr ε) := by
  intro x y h
  rw [threeSixFrob_eq_conj, threeSixFrob_eq_conj, mul_left_inj, mul_right_inj] at h
  exact Units.ext (entrywise_injective Fr (congrArg Units.val h))

variable (Ω) in
@[expose] def tsFrob
    (Fr : Ω →+* Ω) (ε : ℤ) : ModGL Tag.D4 Ω →* ModGL Tag.D4 Ω :=
  threeSixFrob Ω Fr ε

@[expose] def tsW (ε : ℤ) : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ := threeSixW ε

variable (Ω) in
@[expose] def tsM
    : ModGL Tag.D4 Ω := trialityM Ω

theorem tsFrob_eq_conj
    (Fr : Ω →+* Ω) (ε : ℤ) (g : ModGL Tag.D4 Ω) :
    tsFrob Ω Fr ε g = tsM Ω ^ threeSixExp ε * Units.map (entrywiseHom Fr) g *
      (tsM Ω ^ threeSixExp ε)⁻¹ :=
  threeSixFrob_eq_conj Fr ε g

theorem tsFrob_pinnedX
    (Fr : Ω →+* Ω) (ε : ℤ) {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    ∃ η : Ω, η * η = 1 ∧ ∀ c : Ω, tsFrob Ω Fr ε (pinnedX Tag.D4 Ω α c) =
      pinnedX Tag.D4 Ω (tsW ε *ᵥ α) (η * Fr c) :=
  threeSixFrob_pinnedX Fr ε hα

theorem isRoot_tsW_mulVec
    (ε : ℤ) {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    IsRoot Tag.D4 (tsW ε *ᵥ α) :=
  isRoot_threeSixW_mulVec ε hα

theorem tsFrob_injective
    (Fr : Ω →+* Ω) (ε : ℤ) : Function.Injective (tsFrob Ω Fr ε) :=
  threeSixFrob_injective Fr ε

theorem map_tsFrob_rootSpan
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) (ε : ℤ)
    {S : Set (Fin Tag.D4.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot Tag.D4 α) :
    (rootSpan Tag.D4 Ω S).map (tsFrob Ω Fr ε) =
      rootSpan Tag.D4 Ω ((fun α => tsW ε *ᵥ α) '' S) :=
  map_threeSixFrob_rootSpan Fr hFr ε hS

theorem map_conj_tsM_pow_rootSpan
    (ε : ℤ) {S : Set (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.D4 α) :
    (rootSpan Tag.D4 Ω S).map (MulAut.conj (tsM Ω ^ threeSixExp ε)).toMonoidHom =
      rootSpan Tag.D4 Ω ((fun α => tsW ε *ᵥ α) '' S) :=
  map_conj_trialityM_pow_rootSpan ε hS

end CFSG.RankThree.Chevalley
