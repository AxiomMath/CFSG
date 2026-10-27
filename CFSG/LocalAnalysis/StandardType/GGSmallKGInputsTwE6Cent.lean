module

public import CFSG.LieType.AlgebraicGroups.E6RationalTwistedFaithful
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace SmallKG

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {U : Subgroup G} {s : G}
    (hU : U.map (MulAut.conj s).toMonoidHom = U) : s ∈ Subgroup.normalizer (U : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [← hU]
    exact ⟨g, hg, rfl⟩
  · rw [← hU] at hg
    obtain ⟨g', hg', he⟩ := hg
    have he' : (MulAut.conj s) g' = (MulAut.conj s) g := he
    rwa [← (MulAut.conj s).injective he']

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}


theorem eq_one_of_rootDiagUnit_commute_orbitX {c : Fin t.tag.rank → Kˣ}
    (hc : ∀ a, rootDiagUnit t.tag c * (orbitX t K σ a 1 : ModGL t.tag K) =
      (orbitX t K σ a 1 : ModGL t.tag K) * rootDiagUnit t.tag c) : c = 1 := by
  funext i
  have h1 : rootDiagUnit t.tag c * (orbitX t K σ (t.orbitIndex i) 1 : ModGL t.tag K) *
      (rootDiagUnit t.tag c)⁻¹ = orbitX t K σ (t.orbitIndex i) 1 := by
    rw [hc, mul_inv_cancel_right]
  rw [← orbitXProd_one_eq_orbitX σ, TableB.TwE6.rootDiagUnit_conj_orbitXProd] at h1
  have h2 := eq_of_orbitXProd_eq t h1 i (t.mem_orbit_orbitIndex i)
  exact Units.ext (by simpa using h2)

theorem eq_one_of_rootDiagUnit_mul_of_commute (hσ : Function.Surjective σ)
    {b : Fin t.tag.rank → Kˣ} (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i))
    {h : ModGL t.tag K} (hh : h ∈ graphFixedRootGroup t K σ)
    (hz : ∀ y ∈ graphFixedRootGroup t K σ,
      rootDiagUnit t.tag b * h * y = y * (rootDiagUnit t.tag b * h)) :
    rootDiagUnit t.tag b * h = 1 := by
  have hconj : ∀ y ∈ graphFixedRootGroup t K σ,
      h * y * h⁻¹ = (rootDiagUnit t.tag b)⁻¹ * y * (rootDiagUnit t.tag b)⁻¹⁻¹ := fun y hy => by
    have e := hz y hy
    calc h * y * h⁻¹ = (rootDiagUnit t.tag b)⁻¹ * (rootDiagUnit t.tag b * h * y) * h⁻¹ := by
          group
      _ = (rootDiagUnit t.tag b)⁻¹ * (y * (rootDiagUnit t.tag b * h)) * h⁻¹ := by rw [e]
      _ = (rootDiagUnit t.tag b)⁻¹ * y * (rootDiagUnit t.tag b)⁻¹⁻¹ := by group
  have hb' : ∀ i, b⁻¹ (t.perm i) = Units.map σ.toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb, map_inv]
  have hsU : (rootDiagUnit t.tag b)⁻¹ ∈
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [rootDiagUnit_inv]
    exact mem_normalizer_of_map_conj_eq (map_conj_rootDiagUnit_graphFixedPosUnipotent hb')
  have hsV : (rootDiagUnit t.tag b)⁻¹ ∈
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [rootDiagUnit_inv]
    exact mem_normalizer_of_map_conj_eq (map_conj_rootDiagUnit_graphFixedNegUnipotent hb')
  have hU : h ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨hh, mem_normalizer_of_conj_eq
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hh hsU hconj⟩
  have hV : h ∈ graphFixedOppositeBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedNegUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨hh, mem_normalizer_of_conj_eq
      (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hh hsV hconj⟩
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hH : h ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hmax, map_conj_graphFixedRootBorel hmax hσ]
    exact Subgroup.mem_inf.2 ⟨hU, hV⟩
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  rw [← rootDiagUnit_mul] at hz ⊢
  rw [eq_one_of_rootDiagUnit_commute_orbitX (σ := σ) fun a => hz _
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a 1)), rootDiagUnit_one]

theorem eq_one_of_mul_rootDiagUnit_of_commute (hσ : Function.Surjective σ)
    {b : Fin t.tag.rank → Kˣ} (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i))
    {h : ModGL t.tag K} (hh : h ∈ graphFixedRootGroup t K σ)
    (hz : ∀ y ∈ graphFixedRootGroup t K σ,
      h * rootDiagUnit t.tag b * y = y * (h * rootDiagUnit t.tag b)) :
    h * rootDiagUnit t.tag b = 1 := by
  have hb' : ∀ i, b⁻¹ (t.perm i) = Units.map σ.toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb, map_inv]
  have e : h * rootDiagUnit t.tag b = rootDiagUnit t.tag b *
      (rootDiagUnit t.tag b⁻¹ * h * (rootDiagUnit t.tag b⁻¹)⁻¹) := by
    rw [← rootDiagUnit_inv, inv_inv]
    group
  have hh' : rootDiagUnit t.tag b⁻¹ * h * (rootDiagUnit t.tag b⁻¹)⁻¹ ∈
      graphFixedRootGroup t K σ :=
    (Subgroup.mem_normalizer_iff.1 (rootDiagUnit_mem_normalizer_graphFixedRootGroup hb') h).1 hh
  rw [e] at hz ⊢
  exact eq_one_of_rootDiagUnit_mul_of_commute hσ hb hh' hz

end SmallKG

end CFSG.StandardType
