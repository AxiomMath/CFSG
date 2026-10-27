module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)

variable {G : Type} [Group G] [Finite G]

private theorem uc22p22qb_mem_of_isTI (D : Data G) {V₀ : Subgroup G} (hV₀ : InCalV D.M V₀)
    (hTI₀ : IsTI V₀) {t g : G} (ht : t ∈ V₀) (ht1 : t ≠ 1) (hg : g⁻¹ * t * g ∈ V₀) : g ∈ D.M := by
  have hmem : t ∈ V₀ ⊓ conjSubgroup g V₀ := ⟨ht, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr hg⟩
  have hne : V₀ ⊓ conjSubgroup g V₀ ≠ ⊥ := fun h => ht1 (Subgroup.mem_bot.mp (h ▸ hmem))
  have hle : V₀ ≤ conjSubgroup g V₀ := inf_eq_left.mp ((hTI₀ g).resolve_left hne)
  have hcard : Nat.card (conjSubgroup g V₀) ≤ Nat.card V₀ :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).le
  have heq : V₀ = conjSubgroup g V₀ := Subgroup.eq_of_le_of_card_ge hle hcard
  have hgN : g ∈ normalizer (V₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    rw [← CFSG.CGT.Timmesfeld75.mem_conjSubgroup, ← heq]
  rw [← PartTwo.normalizer_eq_of_inCalV D hV₀]
  exact hgN

private theorem uc22p22qb_mem_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) {a : G} (h : G)
    (hXa : X ≤ centralizer ({a} : Set G)) (hCb : centralizer ({h * a * h⁻¹} : Set G) ≤ D.M) :
    h ∈ D.M := by
  have hXM' : X ≤ uniqueFourConj h D.M := by
    intro x hx
    rw [UC6.mem_uniqueFourConj_iff]
    apply hCb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp (hXa hx) a rfl
    calc h * a * h⁻¹ * (h * x * h⁻¹) = h * (a * x) * h⁻¹ := by group
      _ = h * (x * a) * h⁻¹ := by rw [hxa]
      _ = h * x * h⁻¹ * (h * a * h⁻¹) := by group
  have hmem : uniqueFourConj h D.M ∈ calMOf X := ⟨UC6.isMaxTwoLocal_conj D.maxLocal h, hXM'⟩
  rw [h61 p hp X hXM hXp hXc] at hmem
  have hconj : uniqueFourConj h D.M = D.M := Set.mem_singleton_iff.mp hmem
  rw [← UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal]
  exact UC6.uniqueFourConj_eq_self_iff.mp hconj

theorem uc22p22q_isTI_of_cover (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {V₀ V : Subgroup G} (hV : InCalV D.M V) (hV₀ : InCalV D.M V₀) (_hV₀V : V₀ ≤ V) (hTI₀ : IsTI V₀)
    (hcov : ∀ u ∈ V, u ∉ V₀ → ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧
      X ≤ centralizer ({u} : Set G)) : IsTI V := by
  have hsq : ∀ v ∈ V, ∃ n : ℕ, v ^ (2 ^ n) = 1 := fun v hv => ⟨1, by simpa using hV.2.2.2.2 v hv⟩
  have hCA : ∀ t ∈ V, t ≠ 1 → centralizer ({t} : Set G) ≤ D.M := by
    intro t ht ht1
    by_cases htV₀ : t ∈ V₀
    · intro z hz
      have hzt : t * z = z * t := Subgroup.mem_centralizer_iff.mp hz t rfl
      have hconj : z⁻¹ * t * z = t := by
        calc z⁻¹ * t * z = z⁻¹ * (t * z) := by group
          _ = z⁻¹ * (z * t) := by rw [hzt]
          _ = t := by group
      exact uc22p22qb_mem_of_isTI D hV₀ hTI₀ htV₀ ht1 (by rw [hconj]; exact htV₀)
    · obtain ⟨X, hXM, hXp, hXc, hXt⟩ := hcov t ht htV₀
      exact PartTwo.centralizer_le_of_noncyclic D h61 hp hXM hXp hXc ht1 (hsq t ht) hXt
  intro g
  by_cases hbot : V ⊓ conjSubgroup g V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huV : u ∈ V := hu.1
  have hw : g⁻¹ * u * g ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hu.2
  have hw1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hgM : g ∈ D.M := by
    by_cases huV₀ : u ∈ V₀
    · by_cases hwV₀ : g⁻¹ * u * g ∈ V₀
      · exact uc22p22qb_mem_of_isTI D hV₀ hTI₀ huV₀ hu1 hwV₀
      · obtain ⟨X, hXM, hXp, hXc, hXw⟩ := hcov _ hw hwV₀
        refine uc22p22qb_mem_of_noncyclic D h61 hp hXM hXp hXc g hXw ?_
        have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
        rw [e]
        exact hCA u huV hu1
    · obtain ⟨X, hXM, hXp, hXc, hXu⟩ := hcov u huV huV₀
      have hg' : g⁻¹ ∈ D.M := by
        refine uc22p22qb_mem_of_noncyclic D h61 hp hXM hXp hXc g⁻¹ hXu ?_
        rw [inv_inv]
        exact hCA _ hw hw1
      exact inv_mem_iff.mp hg'
  have hgV : g ∈ normalizer (V : Set G) := hV.2.2.1 hgM
  have hVc : conjSubgroup g V = V := by
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    exact ((Subgroup.mem_normalizer_iff'').mp hgV x).symm
  change V ⊓ conjSubgroup g V = V
  rw [hVc, inf_idem]

end CFSG.LocalAnalysis.UniquenessCase.UC22
