module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOrthRadical
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Subgroup GGOrthRad
open scoped Pointwise

section Stabilizer

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isCharacteristicP_orthProjStabilizer (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (Q : QuadraticForm K V) [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    (hV : 5 ≤ Module.finrank K V) {W : Submodule K V} (h0 : W ≠ ⊥) (hW : ∀ w ∈ W, Q w = 0) :
    IsCharacteristicP p
      ↥((stabE Q W).map (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q)))) := by
  refine isCharacteristicP_of_normalPSubgroup_centralizer_le
    (Q := (orthRadical Q W).map (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q))))
    (Subgroup.map_mono (orthRadical_le_stabE Q W)) ?_ ((isPGroup_orthRadical p Q W).map _) ?_
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨s, hs, hsy⟩ := y.2
    refine Subgroup.mem_subgroupOf.2 ⟨s * u * s⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.1 ((orthRadical_normal Q W).conj_mem
        ⟨u, orthRadical_le_stabE Q W hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨s, hs⟩)
    · simp only [map_mul, map_inv, hux, hsy]
      rfl
  · rintro x ⟨hxc, s, hs, rfl⟩
    have hcs : ∀ u ∈ orthRadical Q W,
        s * u * s⁻¹ * u⁻¹ ∈ (scalars K V).subgroupOf (elementaryGroup Q) := by
      intro u hu
      rw [← QuotientGroup.ker_mk' ((scalars K V).subgroupOf (elementaryGroup Q)),
        MonoidHom.mem_ker]
      have h := mem_centralizer_iff.1 hxc (QuotientGroup.mk' _ u) ⟨u, hu, rfl⟩
      simp only [map_mul, map_inv]
      rw [← h]
      group
    obtain ⟨z, hz, q, hq, rfl⟩ := exists_scalar_mul_mem_orthRadical p hp Q hQ hV h0 hW hs hcs
    have hz' : z ∈ (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q))).ker := by
      rw [QuotientGroup.ker_mk']
      exact hz
    rw [map_mul, MonoidHom.mem_ker.1 hz', one_mul]
    exact ⟨q, hq, rfl⟩

end Stabilizer

section Glue

variable {E X : Type*} [Group E] [MulAction E X]

private theorem map_map_conj_mk (N : Subgroup E) [N.Normal] (H : Subgroup E) (g : E) :
    (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) =
      (H.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_map_stabilizer_of_isCoatom [Finite E] (Z : Subgroup E) [Z.Normal] (p : ℕ)
    [Fact p.Prime] (B : Subgroup E) (Φ : X → Prop) (hΦ : ∀ (g : E) (x : X), Φ x → Φ (g • x))
    (hB : ∀ M₁ : Subgroup E, IsCoatom M₁ → B ≤ M₁ →
      ∃ x, Φ x ∧ M₁ = MulAction.stabilizer E x)
    (U : Sylow p (E ⧸ Z))
    (hU : normalizer ((U : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) = B.map (QuotientGroup.mk' Z))
    {S M : Subgroup (E ⧸ Z)} (hS : IsPGroup p S) (hSi : ¬ p ∣ S.index) (hM : IsCoatom M)
    (hNM : normalizer (S : Set (E ⧸ Z)) ≤ M) :
    ∃ x, Φ x ∧ M = (MulAction.stabilizer E x).map (QuotientGroup.mk' Z) := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (E ⧸ Z) U (hS.toSylow hSi)
  have hSy : (U : Subgroup (E ⧸ Z)).map (MulAut.conj y).toMonoidHom = S := by
    have h1 := congrArg (fun T : Sylow p (E ⧸ Z) => (T : Subgroup (E ⧸ Z))) hy
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [Subgroup.pointwise_smul_def] at h1
    exact h1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
  have hN : normalizer (S : Set (E ⧸ Z)) =
      (B.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' Z) := by
    rw [← hSy, ← Subgroup.map_equiv_normalizer_eq, hU, map_map_conj_mk]
  have hBM : B ≤ (M.comap (QuotientGroup.mk' Z)).comap (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_le_iff_le_comap, ← Subgroup.map_le_iff_le_comap]
    rw [hN] at hNM
    exact hNM
  have hcoatom : IsCoatom ((M.comap (QuotientGroup.mk' Z)).comap (MulAut.conj g).toMonoidHom) :=
    (Subgroup.isCoatom_comap (MulAut.conj g)).2
      (Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective Z) hM)
  obtain ⟨x, hx, hxM⟩ := hB _ hcoatom hBM
  refine ⟨g • x, hΦ g x hx, ?_⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hxM,
    Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]

end Glue

section Tits

variable {G X : Type*} [Group G] [MulAction G X]

theorem exists_stabilizer_of_isCoatom_subgroupOf (E Bamb B : Subgroup G) (Φ : X → Prop)
    (hBB : Bamb ≤ B) (hBE : Bamb ≤ E)
    (hamb : ∀ M : Subgroup G, M ≤ E → Bamb ≤ M → M ≠ E →
      (∀ M' : Subgroup G, M ≤ M' → M' ≤ E → M' = M ∨ M' = E) →
        ∃ x, Φ x ∧ M = E ⊓ MulAction.stabilizer G x)
    {M₁ : Subgroup E} (hM₁ : IsCoatom M₁) (hB : B.subgroupOf E ≤ M₁) :
    ∃ x, Φ x ∧ M₁ = MulAction.stabilizer E x := by
  have hMG : M₁.map E.subtype ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBM : Bamb ≤ M₁.map E.subtype := fun g hg =>
    ⟨⟨g, hBE hg⟩, hB (Subgroup.mem_subgroupOf.2 (hBB hg)), rfl⟩
  have hne : M₁.map E.subtype ≠ E := by
    intro h
    refine hM₁.1 (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨y, hy, hyx⟩ : (x : G) ∈ M₁.map E.subtype := by
      rw [h]
      exact x.2
    exact (Subtype.ext hyx) ▸ hy
  have hmax : ∀ M' : Subgroup G, M₁.map E.subtype ≤ M' → M' ≤ E →
      M' = M₁.map E.subtype ∨ M' = E := by
    intro M' hMM' hM'E
    have h1 : M₁ ≤ M'.subgroupOf E := fun x hx => hMM' ⟨x, hx, rfl⟩
    have h2 := Subgroup.map_subgroupOf_eq_of_le hM'E
    rcases hM₁.le_iff.1 h1 with h | h
    · right
      rw [← h2, h, Subgroup.map_top, Subgroup.range_subtype]
    · left
      rw [← h2, h]
  obtain ⟨x, hx, hMx⟩ := hamb _ hMG hBM hne hmax
  refine ⟨x, hx, ?_⟩
  ext y
  rw [← Subgroup.mem_map_iff_mem E.subtype_injective, hMx, Subgroup.mem_inf,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩

end Tits

section Singular

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem singular_smul (Q : QuadraticForm K V) (g : elementaryGroup Q) {W : Submodule K V}
    (h : W ≠ ⊥ ∧ ∀ w ∈ W, Q w = 0) : g • W ≠ ⊥ ∧ ∀ w ∈ g • W, Q w = 0 := by
  have hg := elementaryGroup_le_orthogonalGroup Q g.2
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
    intro hbot
    have hmem : (g : V ≃ₗ[K] V) w ∈ g • W :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hw0 ((g : V ≃ₗ[K] V).map_eq_zero_iff.1 hmem)
  · obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
    exact (map_of_mem hg b).trans (h.2 b hb)

theorem ggNormalizerOvergroupsChar_projElementary [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) (Q : QuadraticForm K V) [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 5 ≤ Module.finrank K V)
    (Bamb B : Subgroup (V ≃ₗ[K] V)) (hBB : Bamb ≤ B) (hBE : Bamb ≤ elementaryGroup Q)
    (hamb : ∀ M : Subgroup (V ≃ₗ[K] V), M ≤ elementaryGroup Q → Bamb ≤ M →
      M ≠ elementaryGroup Q → (∀ M' : Subgroup (V ≃ₗ[K] V), M ≤ M' → M' ≤ elementaryGroup Q →
        M' = M ∨ M' = elementaryGroup Q) →
      ∃ W : Submodule K V, (W ≠ ⊥ ∧ ∀ w ∈ W, Q w = 0) ∧
        M = elementaryGroup Q ⊓ MulAction.stabilizer (V ≃ₗ[K] V) W)
    (U : Sylow p (ProjElementary Q))
    (hU : normalizer ((U : Subgroup (ProjElementary Q)) : Set (ProjElementary Q)) =
      (B.subgroupOf (elementaryGroup Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q)))) :
    GGNormalizerOvergroupsChar p (ProjElementary Q) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  haveI : Finite (elementaryGroup Q) := inferInstance
  refine GGNormalizerOvergroupsChar.of_coatoms fun S M hS hSi hNM hM => ?_
  obtain ⟨W, hW, rfl⟩ := exists_map_stabilizer_of_isCoatom
    ((scalars K V).subgroupOf (elementaryGroup Q)) p (B.subgroupOf (elementaryGroup Q))
    (fun W : Submodule K V => W ≠ ⊥ ∧ ∀ w ∈ W, Q w = 0) (fun g W h => singular_smul Q g h)
    (fun M₁ hM₁ hBM₁ => exists_stabilizer_of_isCoatom_subgroupOf (elementaryGroup Q) Bamb B _
      hBB hBE hamb hM₁ hBM₁) U hU hS hSi hM hNM
  exact isCharacteristicP_orthProjStabilizer p hp Q hQ hV hW.1 hW.2

end Singular

end CFSG.StandardType
