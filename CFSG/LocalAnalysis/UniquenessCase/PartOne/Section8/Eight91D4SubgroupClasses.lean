module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionTrialityConj
import CFSG.GroupTheory.PrimeOrderSubgroups
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof (d4S0 d4S0_mem d4T0 d4T0_mem)

private lemma zpowers_eq_map_conj_of_conj_eq {G : Type} [Group G] {x y g k : G}
    (h : g * x * g⁻¹ = k * y * k⁻¹) :
    zpowers y = (zpowers x).map (MulAut.conj (k⁻¹ * g)).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  congr 1
  change y = (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹
  have hy : y = k⁻¹ * (k * y * k⁻¹) * k := by group
  rw [hy, ← h]
  group

theorem subgroup_classes_of_two_reps {G : Type} [Group G] {s t : G}
    (h : ∀ x : G, orderOf x = 3 → ∃ g : G, g * x * g⁻¹ = s ∨ g * x * g⁻¹ = t)
    {Z A : Subgroup G} (hZ : Nat.card Z = 3) (hA : Nat.card A = 3)
    (hnot : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≠ Z)
    (B : Subgroup G) (hB : Nat.card B = 3) :
    (∃ g : G, B = Z.map (MulAut.conj g).toMonoidHom) ∨
      ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨z, -, hz, rfl⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hZ
  obtain ⟨a, -, ha, rfl⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hA
  obtain ⟨b, -, hb, rfl⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hB
  obtain ⟨gz, hgz⟩ := h z hz
  obtain ⟨ga, hga⟩ := h a ha
  obtain ⟨gb, hgb⟩ := h b hb
  have hsame : ∀ {r : G}, gz * z * gz⁻¹ = r → ga * a * ga⁻¹ = r → False := fun h1 h2 =>
    hnot (gz⁻¹ * ga) (zpowers_eq_map_conj_of_conj_eq (h2.trans h1.symm)).symm
  rcases hgb with hb' | hb' <;> rcases hgz with hz' | hz' <;> rcases hga with ha' | ha' <;>
    first
    | exact (hsame hz' ha').elim
    | exact Or.inl ⟨gb⁻¹ * gz, zpowers_eq_map_conj_of_conj_eq (hz'.trans hb'.symm)⟩
    | exact Or.inr ⟨gb⁻¹ * ga, zpowers_eq_map_conj_of_conj_eq (ha'.trans hb'.symm)⟩


theorem r891_subgroup_classes {X : Type} [Group X] {n : ℕ} (hX : Is3D4 X n)
    {Z A : Subgroup X} (hZ : Nat.card Z = 3) (hA : Nat.card A = 3)
    (hnot : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ Z)
    (B : Subgroup X) (hB : Nat.card B = 3) :
    (∃ g : X, B = Z.map (MulAut.conj g).toMonoidHom) ∨
      ∃ g : X, B = A.map (MulAut.conj g).toMonoidHom := by
  have hadm := hX.admissible
  rcases hX with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two
        hadm.2.1 hM.2
    refine subgroup_classes_of_two_reps (s := e.symm ⟨d4S0 σ, d4S0_mem σ⟩)
      (t := e.symm ⟨d4T0 σ, d4T0_mem σ⟩) (fun x hx => ?_) hZ hA hnot B hB
    have hx' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    obtain ⟨g, hg⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion.exists_conj_eq_d4S0_or_d4T0
        Nat.prime_two (by norm_num) hadm.2.1 hcard hσ hx'
    refine ⟨e.symm g, ?_⟩
    rcases hg with hg | hg
    · left
      rw [← hg]
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    · right
      rw [← hg]
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
