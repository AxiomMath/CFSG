module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFour
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneBraid
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneMovedKill
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.CLSEvenCoordinateFieldsFourGroup

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.E6GraphNoneSteps CFSG.RankThree.E6


noncomputable abbrev wt (ω : List (Fin TwistTag.E6.tag.rank)) : WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd ω

private theorem perm_eq_rhoV (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm v = rhoV v :=
  (rhoV_eq v).symm

theorem rho_rho (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm v) = v :=
  E6SignedGraph.rho_rho v

theorem rho_neg (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (-v) = -permLattice TwistTag.E6.perm v := rfl

theorem moved_facts {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ movedPos) :
    (IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∧
    (IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) ∧
      0 < height (permLattice TwistTag.E6.perm α)) ∧
    α ≠ permLattice TwistTag.E6.perm α ∧ α ≠ -permLattice TwistTag.E6.perm α ∧
    ¬ IsRoot TwistTag.E6.tag (α + permLattice TwistTag.E6.perm α) ∧
    ¬ IsRoot TwistTag.E6.tag (α + -permLattice TwistTag.E6.perm α) := by
  obtain ⟨⟨m, hm⟩, ⟨m', hm'⟩, hne, hp, hmi, h1, h2⟩ := movedPos_spec α hα
  have e := perm_eq_rhoV α
  have hr : IsRoot TwistTag.E6.tag α := isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩
  have hr' : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) := by
    rw [e]; exact isRoot_iff_exists_e6RootVec.2 ⟨m', hm'⟩
  rw [← e] at hne hp hmi h2
  refine ⟨⟨hr, h1⟩, ⟨hr', h2⟩, Ne.symm hne, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : height α = -height (permLattice TwistTag.E6.perm α) :=
      (congrArg height h).trans (height_neg _)
    change 0 < height (permLattice TwistTag.E6.perm α) at h2
    change 0 < height α at h1
    linarith
  · obtain ⟨k, hk⟩ := isRoot_iff_exists_e6RootVec.1 h
    exact hp k hk
  · obtain ⟨k, hk⟩ := isRoot_iff_exists_e6RootVec.1 h
    exact hmi k hk

section L

variable {L : Type} [Field L] [CharP L 2]

omit
  [CharP L 2] in
theorem commute_rdu_pinnedX {a : Fin TwistTag.E6.tag.rank → Lˣ}
    {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (ha : rootChar a δ = 1) (c : L) :
    Commute (rootDiagUnit TwistTag.E6.tag a) (pinnedX TwistTag.E6.tag L δ c) := by
  have h := rootDiagUnit_conj_pinnedX (τ := TwistTag.E6.tag) (K := L) a hδ c
  rw [ha, Units.val_one, one_mul] at h
  exact (eq_mul_inv_iff_mul_eq.1 h.symm).symm

omit
  [CharP L 2] in
theorem frob_pinnedX_one (Fr : L →+* L) (δ : Fin TwistTag.E6.tag.rank → ℤ) :
    Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L δ 1) = pinnedX TwistTag.E6.tag L δ 1 :=
  Units.ext (by
    rw [Units.coe_map]
    exact CFSG.LieType.Chevalley.entrywise_pinnedX_one Fr δ)

theorem weylWord_conj_pinnedX' (ω : List (Fin TwistTag.E6.tag.rank))
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) (c : L) :
    weylWord (τ := TwistTag.E6.tag) L ω * pinnedX TwistTag.E6.tag L δ c *
        (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ =
      pinnedX TwistTag.E6.tag L (wt ω • δ) c := by
  have hw : weylWord (τ := TwistTag.E6.tag) L ω =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L ((coxeterSystem TwistTag.E6.tag).wordProd ω) :=
    (CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo ω).symm
  rw [hw]
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux.canonicalRep_conj_pinnedX_two _
    hδ c

private theorem exists_z0_of_inverting_neg (Fr : L →+* L) (ω : List (Fin TwistTag.E6.tag.rank))
    (hw : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, wt ω • v = -v)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ movedPos) (hka : rootChar a α = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      weylWord (τ := TwistTag.E6.tag) L ω * Units.map (entrywiseHom Fr) z₀ *
          (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ := by
  obtain ⟨hαr, hβr, hne, hne', hp, hm⟩ := moved_facts hα
  set β := permLattice TwistTag.E6.perm α with hβ
  set n := weylWord (τ := TwistTag.E6.tag) L ω
  set x : (Fin TwistTag.E6.tag.rank → ℤ) → ModGL TwistTag.E6.tag L :=
    fun δ => pinnedX TwistTag.E6.tag L δ 1 with hx
  have hFx : ∀ δ, Units.map (entrywiseHom Fr) (x δ) = x δ := fun δ => frob_pinnedX_one Fr δ
  have hnx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → n * x δ * n⁻¹ =
      x (wt ω • δ) := fun hδ => weylWord_conj_pinnedX' ω hδ 1
  have hPx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → diagramMap TwistTag.E6 L * x δ *
      (diagramMap TwistTag.E6 L)⁻¹ = x (permLattice TwistTag.E6.perm δ) :=
    fun hδ => diagram_conj_pinnedX hδ 1
  have hdx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → rootChar a δ = 1 →
      Commute (rootDiagUnit TwistTag.E6.tag a) (x δ) := fun hδ h => commute_rdu_pinnedX hδ h 1
  have hka' : rootChar a (-α) = 1 := by rw [E6SignedGraph.rootChar_neg', hka, inv_one]
  have hadj : ∀ δ, x δ ∈ adjointGroup TwistTag.E6.tag L := fun δ =>
    pinnedX_mem_adjointGroup δ 1
  have cm : ∀ (u y y' : ModGL TwistTag.E6.tag L),
      u * (y * y') * u⁻¹ = (u * y * u⁻¹) * (u * y' * u⁻¹) := fun u y y' => by group
  refine ⟨x α * x (-α) * x α, mul_mem (mul_mem (hadj _) (hadj _)) (hadj _), ?_, ?_, ?_⟩
  · exact (((hdx hαr.1 hka).mul_right (hdx (IsRoot.neg hαr.1) hka')).mul_right
      (hdx hαr.1 hka)).symm
  · rw [map_mul, map_mul, hFx, hFx, cm, cm, hnx hαr.1, hnx (IsRoot.neg hαr.1), hw, hw,
      neg_neg]
    exact (nRoot_eq' (L := L) hαr.1).symm
  · rw [cm, cm, hPx hαr.1, hPx (IsRoot.neg hαr.1), rho_neg]
    intro h
    exact nRoot_ne (L := L) hαr hβr.1 hne hne' hp hm h.symm

private theorem exists_z0_of_inverting_neg_rho (Fr : L →+* L)
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hw : ∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      wt ω • v = -permLattice TwistTag.E6.perm v)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ movedPos) (hka : rootChar a α = 1)
    (hkρ : rootChar a (permLattice TwistTag.E6.perm α) = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      weylWord (τ := TwistTag.E6.tag) L ω * Units.map (entrywiseHom Fr) z₀ *
          (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ := by
  obtain ⟨hαr, hβr, hne, hne', hp, hm⟩ := moved_facts hα
  set β := permLattice TwistTag.E6.perm α with hβ
  set n := weylWord (τ := TwistTag.E6.tag) L ω
  set x : (Fin TwistTag.E6.tag.rank → ℤ) → ModGL TwistTag.E6.tag L :=
    fun δ => pinnedX TwistTag.E6.tag L δ 1 with hx
  have hFx : ∀ δ, Units.map (entrywiseHom Fr) (x δ) = x δ := fun δ => frob_pinnedX_one Fr δ
  have hnx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → n * x δ * n⁻¹ =
      x (wt ω • δ) := fun hδ => weylWord_conj_pinnedX' ω hδ 1
  have hPx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → diagramMap TwistTag.E6 L * x δ *
      (diagramMap TwistTag.E6 L)⁻¹ = x (permLattice TwistTag.E6.perm δ) :=
    fun hδ => diagram_conj_pinnedX hδ 1
  have hdx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → rootChar a δ = 1 →
      Commute (rootDiagUnit TwistTag.E6.tag a) (x δ) := fun hδ h => commute_rdu_pinnedX hδ h 1
  have hkρ' : rootChar a (-β) = 1 := by rw [E6SignedGraph.rootChar_neg', hkρ, inv_one]
  have hadj : ∀ δ, x δ ∈ adjointGroup TwistTag.E6.tag L := fun δ =>
    pinnedX_mem_adjointGroup δ 1
  have cm : ∀ (u y y' : ModGL TwistTag.E6.tag L),
      u * (y * y') * u⁻¹ = (u * y * u⁻¹) * (u * y' * u⁻¹) := fun u y y' => by group
  have hc : Commute (x α) (x (-β)) := commute_pinnedX (L := L) hαr.1 (IsRoot.neg hβr.1) hne'
    (fun h => hne (h.trans (neg_neg _))) hm 1 1
  refine ⟨x α * x (-β), mul_mem (hadj _) (hadj _), ?_, ?_, ?_⟩
  · exact ((hdx hαr.1 hka).mul_right (hdx (IsRoot.neg hβr.1) hkρ')).symm
  · rw [map_mul, hFx, hFx, cm, hnx hαr.1, hnx (IsRoot.neg hβr.1), hw, hw, rho_neg, neg_neg,
      ← hβ, rho_rho]
    exact hc.eq.symm
  · rw [cm, hPx hαr.1, hPx (IsRoot.neg hβr.1), rho_neg, ← hβ, rho_rho]
    intro h
    exact pinnedX_mul_ne (L := L) hαr hβr hne h.symm

theorem exists_z0 (Fr : L →+* L) (ω : List (Fin TwistTag.E6.tag.rank))
    (hw : (∀ v : Fin TwistTag.E6.tag.rank → ℤ, wt ω • v = -v) ∨
      (∀ v : Fin TwistTag.E6.tag.rank → ℤ, wt ω • v = -permLattice TwistTag.E6.perm v))
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ movedPos)
    (hka : rootChar a α = 1) (hkρ : rootChar a (permLattice TwistTag.E6.perm α) = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      weylWord (τ := TwistTag.E6.tag) L ω * Units.map (entrywiseHom Fr) z₀ *
          (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ := by
  rcases hw with hw | hw
  · exact exists_z0_of_inverting_neg Fr ω hw hα hka
  · exact exists_z0_of_inverting_neg_rho Fr ω hw hα hka hkρ

end L

end CFSG.StandardType.E6GraphNoneSteps
