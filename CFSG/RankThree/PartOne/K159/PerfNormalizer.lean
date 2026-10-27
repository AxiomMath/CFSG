module

public import CFSG.RankThree.PartOne.K159.InnLayerRows
public import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Stated

variable (K : Type) [Field K]

noncomputable def statedProjSLEquiv (n : ℕ) : StatedProj (StatedSL n K) ≃* projSL n K :=
  statedProjEquivOfGLEquiv (MulEquiv.refl (GL (Fin n) K)) (by simp) (by simp)
    (projImage_statedSL_eq_projSL n K)

noncomputable def statedProjSpEquiv (n : ℕ) : StatedProj (StatedSp n K) ≃* projSp n K :=
  statedProjEquivOfGLEquiv (MulEquiv.refl (GL (Fin n ⊕ Fin n) K)) (by simp) (by simp)
    (projImage_statedSp_eq_projSp n K)

noncomputable def statedProjOmegaMinusEquiv (n : ℕ) (b c : K) :
    StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃* projOmegaMinus (n - 1) K b c :=
  statedProjEquivOfGLEquiv (MulEquiv.refl (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)) (by simp)
    (by simp) (projImage_statedOmegaMinus_eq_projOmegaMinus n K b c)

end Stated

section Catalog

variable {G : Type} [Group G]

theorem catalog_of_lieRow {r p : ℕ} {I : Subgroup G} (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (h : LieRow r p I) : CFSG.Blueprint.Catalog ↥I := by
  interval_cases r
  · obtain ⟨f, hf, -, ⟨e⟩⟩ := h
    have hmod : StatedClassicalModel ↥I .PSL 4 2 f :=
      ⟨⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩, GaloisField 2 f, inferInstance,
        inferInstance, GaloisField.card 2 f (by omega),
        ⟨e.trans (statedProjSLEquiv (GaloisField 2 f) 4).symm⟩⟩
    exact Or.inr (Or.inr (Or.inl ⟨.PSL, 4, 2, f, hmod⟩))
  · obtain ⟨f, hf, -, ⟨e⟩⟩ := h
    have hmod : StatedClassicalModel ↥I .PSp 3 2 f :=
      ⟨⟨Nat.prime_two, hf, by norm_num, by simp⟩, GaloisField 2 f, inferInstance, inferInstance,
        GaloisField.card 2 f (by omega), ⟨e.trans (statedProjSpEquiv (GaloisField 2 f) 3).symm⟩⟩
    exact Or.inr (Or.inr (Or.inl ⟨.PSp, 3, 2, f, hmod⟩))
  · obtain ⟨f, hf, -, b, c, hirr, ⟨e⟩⟩ := h
    have hmod : StatedClassicalModel ↥I .POmegaMinus 4 2 f :=
      ⟨⟨Nat.prime_two, hf, by norm_num⟩, GaloisField 2 f, inferInstance, inferInstance,
        GaloisField.card 2 f (by omega), b, c, hirr,
        ⟨e.trans (statedProjOmegaMinusEquiv (GaloisField 2 f) 4 b c).symm⟩⟩
    exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, 2, f, hmod⟩))
  · obtain ⟨f, hf, -, b, c, hirr, ⟨e⟩⟩ := h
    have hmod : StatedClassicalModel ↥I .POmegaMinus 4 2 f :=
      ⟨⟨Nat.prime_two, hf, by norm_num⟩, GaloisField 2 f, inferInstance, inferInstance,
        GaloisField.card 2 f (by omega), b, c, hirr,
        ⟨e.trans (statedProjOmegaMinusEquiv (GaloisField 2 f) 4 b c).symm⟩⟩
    exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, 2, f, hmod⟩))

end Catalog

section Out

variable {G : Type} [Group G]

theorem le_sup_centralizer_of_outer_solvable {I Z : Subgroup G} (hZ : Group.IsPerfect ↥Z)
    (hZN : Z ≤ Subgroup.normalizer (I : Set G)) (hOut : Group.IsSolvable (Outer ↥I)) :
    Z ≤ I ⊔ Subgroup.centralizer (I : Set G) := by
  classical
  let ψ : ↥Z →* Outer ↥I :=
    (QuotientGroup.mk' (inner ↥I)).comp ((I.normalizerMonoidHom).comp (Subgroup.inclusion hZN))
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsolv : Group.IsSolvable ↥ψ.range := inferInstance
  have htriv : ∀ z : ↥Z, ψ z = 1 := by
    intro z
    by_contra hz
    have : Nontrivial ↥ψ.range :=
      ⟨⟨⟨ψ z, z, rfl⟩, 1, fun h => hz (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) hsolv
  intro z hz
  have h1 : ψ ⟨z, hz⟩ = 1 := htriv ⟨z, hz⟩
  have h2 : (I.normalizerMonoidHom ⟨z, hZN hz⟩) ∈ inner ↥I := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨i, hi⟩ := h2
  have hconj : ∀ x ∈ I, (i : G) * x * (i : G)⁻¹ = z * x * z⁻¹ := by
    intro x hx
    have := congrArg (fun a : MulAut ↥I => ((a ⟨x, hx⟩ : ↥I) : G)) hi
    simpa using this
  have hc : (i : G)⁻¹ * z ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hconj x hx
    calc x * ((i : G)⁻¹ * z) = (i : G)⁻¹ * ((i : G) * x * (i : G)⁻¹) * z := by group
      _ = (i : G)⁻¹ * (z * x * z⁻¹) * z := by rw [this]
      _ = (i : G)⁻¹ * z * x := by group
  have hz' : z = (i : G) * ((i : G)⁻¹ * z) := by group
  rw [hz']
  exact Subgroup.mul_mem_sup i.2 hc

theorem outer_solvable_of_card_two {X : Type} [Group X] (h : Nat.card X = 2) :
    Group.IsSolvable (Outer X) := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : X)).1 h
  have hsub : Subsingleton (MulAut X) := by
    refine ⟨fun φ ψ => ?_⟩
    ext x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · have h1 : φ x ≠ 1 := fun h1 => hx (φ.injective (h1.trans (map_one φ).symm))
      have h2 : ψ x ≠ 1 := fun h2 => hx (ψ.injective (h2.trans (map_one ψ).symm))
      exact (huniq _ h1).trans (huniq _ h2).symm
  have hsub' : Subsingleton (Outer X) :=
    (QuotientGroup.mk'_surjective (inner X)).subsingleton
  exact (inferInstance : Group.IsSolvable (Outer X))

end Out

section Main

theorem kfPerfNormalizer_of_schreier (hS : SchreierFor CFSG.Blueprint.Catalog) : KFPerfNormalizer := by
  intro G _ _ p A c L E h15 hF hout hEA Z hZ hZN
  obtain ⟨r, hr1, hr4, hrow⟩ := lieRow_of_outcome hout hEA
  have hsimple : IsSimpleGroup ↥(lieGenerated p E) := isSimpleGroup_of_lieRow hr1 hr4 hrow
  have hcat : CFSG.Blueprint.Catalog ↥(lieGenerated p E) := catalog_of_lieRow hr1 hr4 hrow
  by_cases hnonab : ∃ a b : ↥(lieGenerated p E), a * b ≠ b * a
  · exact le_sup_centralizer_of_outer_solvable hZ hZN (hS _ hnonab hcat)
  · push Not at hnonab
    have : IsMulCommutative ↥(lieGenerated p E) := ⟨⟨fun a b => hnonab a b⟩⟩
    have hprime : (Nat.card ↥(lieGenerated p E)).Prime :=
      Group.is_simple_iff_prime_card.1 hsimple
    have heven : Even (Nat.card ↥(lieGenerated p E)) := by
      rcases hout with h | h | h | h | h
      · obtain ⟨-, -, -, -, -, -, he⟩ := h
        exact he
      · obtain ⟨-, -, -, -, -, -, he⟩ := h
        exact he
      · obtain ⟨-, -, -, -, -, -, he⟩ := h
        exact he
      · obtain ⟨-, -, -, -, -, -, he⟩ := h
        exact he
      · obtain ⟨-, -, -, -, -, -, hne, -⟩ := h
        exact absurd hEA hne
    exact le_sup_centralizer_of_outer_solvable hZ hZN
      (outer_solvable_of_card_two ((Nat.Prime.even_iff hprime).1 heven))

end Main

end CFSG.RankThree.PartOne.K159
