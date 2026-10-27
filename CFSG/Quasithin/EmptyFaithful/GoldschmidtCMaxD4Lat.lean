module

public import CFSG.Quasithin.EmptyFaithful.S152RD4
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace GoldCMax

theorem isMaxSubgroupIn_of_two_node_lattice {G : Type*} [Group G] {ι : Type*} {B : Subgroup G}
    {Par : Set ι → Subgroup G} (hcases : ∀ J : Set ι, J = ∅ ∨ J = Set.univ ∨ ∃ a, J = {a})
    (hP0 : Par ∅ = B) (hPu : Par Set.univ = ⊤) (hmono : ∀ J J', Par J ≤ Par J' ↔ J ⊆ J')
    (hcl : ∀ A : Subgroup G, B ≤ A → ∃ J, A = Par J) {A : Subgroup G} (hBA : B ≤ A)
    (hne : A ≠ B) (htop : A ≠ ⊤) : IsMaxSubgroupIn ⊤ A := by
  obtain ⟨J, rfl⟩ := hcl A hBA
  rcases hcases J with rfl | rfl | ⟨a, rfl⟩
  · exact absurd hP0 hne
  · exact absurd hPu htop
  · refine ⟨lt_top_iff_ne_top.mpr htop, fun Y hAY _ => ?_⟩
    obtain ⟨J', rfl⟩ := hcl Y (hBA.trans hAY.le)
    have hsub : ({a} : Set ι) ⊆ J' := (hmono _ _).mp hAY.le
    rcases hcases J' with rfl | rfl | ⟨b, rfl⟩
    · exact absurd (hsub (Set.mem_singleton a)) (Set.notMem_empty a)
    · exact hPu
    · have hab : a = b := Set.mem_singleton_iff.mp (hsub (Set.mem_singleton a))
      subst hab
      exact absurd rfl hAY.ne

section D4


theorem isMaxSubgroupIn_d4_of_borel (K : Type) [Field K] (σ : K ≃+* K)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hBA : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ A)
    (hne : A ≠ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (htop : A ≠ ⊤) : IsMaxSubgroupIn ⊤ A := by
  obtain ⟨-, -, -, hmono, hP0, hPu⟩ := fixed_standard_parabolic_cells TwistTag.D4 K σ
  have hPle : ∀ J, graphFixedParabolic TwistTag.D4 K σ.toRingHom J ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun J =>
    graphFixedParabolic_le TwistTag.D4 K σ.toRingHom J
  refine isMaxSubgroupIn_of_two_node_lattice
    (Par := fun J => (graphFixedParabolic TwistTag.D4 K σ.toRingHom J).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ?_ ?_ ?_ ?_ ?_ hBA hne htop
  · intro J
    rcases set_foldedRank_D4_cases J with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨_, h⟩)
    · exact Or.inr (Or.inr ⟨_, h⟩)
    · exact Or.inr (Or.inl h)
  · simp only [hP0]
  · simp only [hPu, Subgroup.subgroupOf_self]
  · intro J J'
    rw [← hmono J J']
    constructor
    · intro h x hx
      exact h (show (⟨x, hPle J hx⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom J).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from hx)
    · exact fun h => Subgroup.comap_mono h
  · intro A hBA
    have hB' : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
        A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
      have h := Subgroup.map_mono (f := (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
        hBA
      rwa [Subgroup.map_subgroupOf_eq_of_le (graphFixedRootBorel_le TwistTag.D4 K
        σ.toRingHom)] at h
    obtain ⟨hAJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ _ hB'
      (Subgroup.map_subtype_le A)
    refine ⟨{a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection a) ∈
        A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype}, ?_⟩
    show A = (graphFixedParabolic TwistTag.D4 K σ.toRingHom _).comap
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
    rw [← hAJ]
    exact (Subgroup.comap_map_eq_self_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective A).symm

end D4

end GoldCMax

end CFSG.Quasithin
