module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Orbit

private lemma g5_edge_conj {τ : Tag} {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    ∃ u : WeylGroup τ, u • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  have hne : i ≠ j := by
    intro h
    subst h
    have hdiag := (isFiniteType_cartan τ).apply_self i
    rw [hdiag] at hij
    norm_num at hij
  have h1 : reflect τ j (Pi.single i 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 + Pi.single j 1 := by
    rw [← reflection_cartan, reflection_apply_coroot, coroot_single, hji]
    module
  have h2 : reflect τ i (Pi.single i 1 + Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
    rw [← reflection_cartan, reflection_apply_coroot]
    have hc : coroot τ.cartan i (Pi.single i 1 + Pi.single j 1 : Fin τ.rank → ℤ) = 1 := by
      rw [map_add, coroot_single, coroot_single, (isFiniteType_cartan τ).apply_self i, hij]
      norm_num
    rw [hc, one_smul]
    module
  exact ⟨simple τ i * simple τ j, by rw [mul_smul, simple_smul, simple_smul, h1, h2]⟩

private abbrev g5_e6Edge (a b : Fin 6) : Prop :=
  Tag.cartan .E6 a b = -1 ∧ Tag.cartan .E6 b a = -1

private abbrev g5_e7Edge (a b : Fin 7) : Prop :=
  Tag.cartan .E7 a b = -1 ∧ Tag.cartan .E7 b a = -1

private abbrev g5_e8Edge (a b : Fin 8) : Prop :=
  Tag.cartan .E8 a b = -1 ∧ Tag.cartan .E8 b a = -1

private lemma g5_conn_E6 : ∀ i j : Fin 6, Relation.ReflTransGen g5_e6Edge i j := by
  have hto : ∀ k : Fin 6, Relation.ReflTransGen g5_e6Edge k 3 := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 0 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 2 3))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 1 3)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 2 3)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 4 3)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 5 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 4 3))
  have hfrom : ∀ k : Fin 6, Relation.ReflTransGen g5_e6Edge 3 k := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 3 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 2 0))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 3 1)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 3 2)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 3 4)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 3 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e6Edge 4 5))
  intro i j
  exact (hto i).trans (hfrom j)

private lemma g5_conn_E7 : ∀ i j : Fin 7, Relation.ReflTransGen g5_e7Edge i j := by
  have hto : ∀ k : Fin 7, Relation.ReflTransGen g5_e7Edge k 3 := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 0 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 2 3))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 1 3)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 2 3)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 4 3)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 5 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 4 3))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 6 5)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 5 4)).trans
          (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 4 3)))
  have hfrom : ∀ k : Fin 7, Relation.ReflTransGen g5_e7Edge 3 k := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 2 0))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 1)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 2)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 4)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 4 5))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 3 4)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 4 5)).trans
          (Relation.ReflTransGen.single (by decide +kernel : g5_e7Edge 5 6)))
  intro i j
  exact (hto i).trans (hfrom j)

private lemma g5_conn_E8 : ∀ i j : Fin 8, Relation.ReflTransGen g5_e8Edge i j := by
  have hto : ∀ k : Fin 8, Relation.ReflTransGen g5_e8Edge k 3 := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 0 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 2 3))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 1 3)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 2 3)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 3)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 5 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 3))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 6 5)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 5 4)).trans
          (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 3)))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 7 6)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 6 5)).trans
          ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 5 4)).trans
            (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 3))))
  have hfrom : ∀ k : Fin 8, Relation.ReflTransGen g5_e8Edge 3 k := by
    intro k
    fin_cases k
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 2)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 2 0))
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 1)
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 2)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 4)
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 4)).trans
        (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 5))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 4)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 5)).trans
          (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 5 6)))
    · exact (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 3 4)).trans
        ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 4 5)).trans
          ((Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 5 6)).trans
            (Relation.ReflTransGen.single (by decide +kernel : g5_e8Edge 6 7))))
  intro i j
  exact (hto i).trans (hfrom j)

private lemma g5_simple_conj_of_conn {τ : Tag}
    (hconn : ∀ a b : Fin τ.rank, Relation.ReflTransGen
      (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) a b)
    (i j : Fin τ.rank) :
    ∃ u : WeylGroup τ, u • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  suffices h : ∀ a b : Fin τ.rank, Relation.ReflTransGen
      (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) a b →
      ∃ u : WeylGroup τ, u • (Pi.single a 1 : Fin τ.rank → ℤ) = Pi.single b 1 by
    exact h i j (hconn i j)
  intro a b hab
  induction hab with
  | refl => exact ⟨1, by simp⟩
  | tail _ hstep ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨v, hv⟩ := g5_edge_conj hstep.1 hstep.2
    exact ⟨v * u, by rw [mul_smul, hu, hv]⟩

private lemma g5_simple_conj {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i j : Fin τ.rank) :
    ∃ u : WeylGroup τ, u • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  rcases hτ with rfl | rfl | rfl
  · exact g5_simple_conj_of_conn (τ := .E6) g5_conn_E6 i j
  · exact g5_simple_conj_of_conn (τ := .E7) g5_conn_E7 i j
  · exact g5_simple_conj_of_conn (τ := .E8) g5_conn_E8 i j

theorem ggG5_orbit_simplyLaced {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β₀ β : Fin τ.rank → ℤ} (h₀ : IsRoot τ β₀) (h : IsRoot τ β) :
    ∃ u : WeylGroup τ, u • β₀ = β := by
  obtain ⟨w₀, i, hw₀⟩ := isRoot_iff_exists_smul_single.1 h₀
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 h
  obtain ⟨v, hv⟩ := g5_simple_conj hτ i j
  refine ⟨w * v * w₀⁻¹, ?_⟩
  rw [mul_smul, mul_smul, ← hw₀, inv_smul_smul, hv, hw]

theorem ggG5_orbit_F4
    {β₀ β : Fin Tag.F4.rank → ℤ} (h₀ : IsRoot .F4 β₀) (h : IsRoot .F4 β)
    (hlen : CFSG.LieType.Steinberg.Adjoint.iform β₀ β₀ = CFSG.LieType.Steinberg.Adjoint.iform β β) :
    ∃ u : WeylGroup .F4, u • β₀ = β := by
  rcases CFSG.SeitzReduction.F4Pilot.iform_self_eq_two_or_four h₀ with h2 | h4
  · have hβ : CFSG.LieType.Steinberg.Adjoint.iform β β = 2 := by rw [← hlen, h2]
    obtain ⟨w₀, hw₀⟩ := CFSG.SeitzReduction.F4Pilot.exists_smul_eq_rootS h₀ h2
    obtain ⟨w, hw⟩ := CFSG.SeitzReduction.F4Pilot.exists_smul_eq_rootS h hβ
    refine ⟨w⁻¹ * w₀, ?_⟩
    rw [mul_smul, hw₀, ← hw, inv_smul_smul]
  · have hβ : CFSG.LieType.Steinberg.Adjoint.iform β β = 4 := by rw [← hlen, h4]
    obtain ⟨w₀, hw₀⟩ := CFSG.SeitzReduction.F4Pilot.exists_smul_eq_rootR h₀ h4
    obtain ⟨w, hw⟩ := CFSG.SeitzReduction.F4Pilot.exists_smul_eq_rootR h hβ
    refine ⟨w⁻¹ * w₀, ?_⟩
    rw [mul_smul, hw₀, ← hw, inv_smul_smul]

private def g5_e6FixedBase : Fin TwistTag.E6.tag.rank → ℤ := ![-1, -2, -2, -3, -2, -1]

private def g5_e6FixedRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![-1, -2, -2, -3, -2, -1],
   ![-1, -1, -2, -3, -2, -1],
   ![-1, -1, -2, -2, -2, -1],
   ![-1, -1, -1, -2, -1, -1],
   ![-1, -1, -1, -1, -1, -1],
   ![-1, 0, -1, -1, -1, -1],
   ![0, -1, -1, -2, -1, 0],
   ![0, -1, -1, -1, -1, 0],
   ![0, -1, 0, -1, 0, 0],
   ![0, -1, 0, 0, 0, 0],
   ![0, 0, -1, -1, -1, 0],
   ![0, 0, 0, -1, 0, 0],
   ![0, 0, 0, 1, 0, 0],
   ![0, 0, 1, 1, 1, 0],
   ![0, 1, 0, 0, 0, 0],
   ![0, 1, 0, 1, 0, 0],
   ![0, 1, 1, 1, 1, 0],
   ![0, 1, 1, 2, 1, 0],
   ![1, 0, 1, 1, 1, 1],
   ![1, 1, 1, 1, 1, 1],
   ![1, 1, 1, 2, 1, 1],
   ![1, 1, 2, 2, 2, 1],
   ![1, 1, 2, 3, 2, 1],
   ![1, 2, 2, 3, 2, 1]]

private instance g5_f4RankNeZero : NeZero (Tag.rank .F4) := ⟨by decide⟩

private def g5_e6FixedWords : List (List (Fin TwistTag.E6.foldedTag.rank)) :=
  [[], [3], [2, 3], [1, 2, 3], [2, 1, 2, 3], [3, 2, 1, 2, 3], [0, 1, 2, 3], [2, 0, 1, 2, 3],
   [1, 2, 0, 1, 2, 3], [2, 1, 2, 0, 1, 2, 3], [3, 2, 0, 1, 2, 3], [3, 1, 2, 0, 1, 2, 3],
   [2, 3, 1, 2, 0, 1, 2, 3], [1, 2, 3, 1, 2, 0, 1, 2, 3], [3, 2, 1, 2, 0, 1, 2, 3],
   [2, 3, 2, 1, 2, 0, 1, 2, 3], [1, 2, 3, 2, 1, 2, 0, 1, 2, 3],
   [2, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3],
   [0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3],
   [1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3],
   [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3]]

private def g5_e6OrbitAct (a : Fin TwistTag.E6.foldedTag.rank)
    (v : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ℤ :=
  (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) v

private def g5_e6WordAct (l : List (Fin TwistTag.E6.foldedTag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ℤ :=
  l.foldr g5_e6OrbitAct v

private lemma g5_e6OrbitReflection_smul
    (a : Fin TwistTag.E6.foldedTag.rank)
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    TwistTag.E6.orbitReflection a • v = g5_e6OrbitAct a v := by
  unfold TwistTag.orbitReflection
  rw [wordProd_smul]
  rfl

private lemma g5_e6ProdOrbitReflection_smul
    (l : List (Fin TwistTag.E6.foldedTag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (l.map TwistTag.E6.orbitReflection).prod • v = g5_e6WordAct l v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, g5_e6OrbitReflection_smul]
    rfl

private lemma g5_e6FixedRoots_complete :
    ∀ β ∈ rootFinset TwistTag.E6.tag,
      permLattice TwistTag.E6.perm β = β → β ∈ g5_e6FixedRoots := by
  decide +kernel

private lemma g5_e6FixedWords_check :
    ∀ v ∈ g5_e6FixedRoots, ∃ l ∈ g5_e6FixedWords, g5_e6WordAct l g5_e6FixedBase = v := by
  decide +kernel

theorem ggG5_orbit_E6_graph
    {β₀ β : Fin TwistTag.E6.tag.rank → ℤ}
    (h₀ : IsRoot TwistTag.E6.tag β₀) (h : IsRoot TwistTag.E6.tag β)
    (h₀γ : permLattice TwistTag.E6.perm β₀ = β₀) (hγ : permLattice TwistTag.E6.perm β = β) :
    ∃ u : WeylGroup TwistTag.E6.tag, weylTwist TwistTag.E6 u = u ∧ u • β₀ = β := by
  have h₀mem : β₀ ∈ g5_e6FixedRoots :=
    g5_e6FixedRoots_complete β₀ (mem_rootFinset.2 h₀) h₀γ
  have hmem : β ∈ g5_e6FixedRoots :=
    g5_e6FixedRoots_complete β (mem_rootFinset.2 h) hγ
  obtain ⟨l₀, -, hprod₀⟩ := g5_e6FixedWords_check β₀ h₀mem
  obtain ⟨l, -, hprod⟩ := g5_e6FixedWords_check β hmem
  refine ⟨(l.map TwistTag.E6.orbitReflection).prod *
    ((l₀.map TwistTag.E6.orbitReflection).prod)⁻¹, ?_, ?_⟩
  · rw [← mem_relWeylTwist, relWeylTwist_eq_closure]
    exact Subgroup.mul_mem _
      (Subgroup.list_prod_mem _ fun x hx => Subgroup.subset_closure
        (by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact ⟨a, rfl⟩))
      (Subgroup.inv_mem _ (Subgroup.list_prod_mem _ fun x hx => Subgroup.subset_closure
        (by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact ⟨a, rfl⟩)))
  · calc ((l.map TwistTag.E6.orbitReflection).prod *
        ((l₀.map TwistTag.E6.orbitReflection).prod)⁻¹) • β₀
        = (l.map TwistTag.E6.orbitReflection).prod •
            (((l₀.map TwistTag.E6.orbitReflection).prod)⁻¹ • β₀) := by rw [mul_smul]
      _ = (l.map TwistTag.E6.orbitReflection).prod • g5_e6FixedBase := by
            have hb : ((l₀.map TwistTag.E6.orbitReflection).prod)⁻¹ • β₀ = g5_e6FixedBase := by
              rw [← hprod₀, ← g5_e6ProdOrbitReflection_smul l₀ g5_e6FixedBase, inv_smul_smul]
            rw [hb]
      _ = g5_e6WordAct l g5_e6FixedBase := g5_e6ProdOrbitReflection_smul l g5_e6FixedBase
      _ = β := hprod

end Orbit

end CFSG.StandardType.GGFinModel.G5
