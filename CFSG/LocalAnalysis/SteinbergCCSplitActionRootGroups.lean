module

public import CFSG.LocalAnalysis.SteinbergCCConjugateRootGroupDatum
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis

namespace SplitActionRoot

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem mem_map_conj {U : Subgroup G} {g u : G} :
    u ∈ U.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ U := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_eq_of_smul_eq {a : Ω} {U : Subgroup G} (hUa : U ≤ rootPointStabilizer G a)
    (hUn : (U.subgroupOf (rootPointStabilizer G a)).Normal) {g h : G} (hgh : g • a = h • a) :
    U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom := by
  have hs : h⁻¹ * g ∈ rootPointStabilizer G a := by
    rw [mem_rootPointStabilizer_iff, mul_smul, hgh, inv_smul_smul]
  have key : ∀ s ∈ rootPointStabilizer G a, ∀ u ∈ U, s * u * s⁻¹ ∈ U := fun s hs u hu =>
    Subgroup.mem_subgroupOf.mp
      (hUn.conj_mem ⟨u, hUa hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨s, hs⟩)
  ext u
  rw [mem_map_conj, mem_map_conj]
  constructor
  · intro hu
    have h1 := key (h⁻¹ * g) hs _ hu
    rwa [show h⁻¹ * g * (g⁻¹ * u * g) * (h⁻¹ * g)⁻¹ = h⁻¹ * u * h by group] at h1
  · intro hu
    have h1 := key (h⁻¹ * g)⁻¹ (inv_mem hs) _ hu
    rwa [show (h⁻¹ * g)⁻¹ * (h⁻¹ * u * h) * (h⁻¹ * g)⁻¹⁻¹ = g⁻¹ * u * g by group] at h1

end SplitActionRoot

open SplitActionRoot in
theorem split_action_conjugate_root_group_construction {G Ω : Type*} [Group G] [MulAction G Ω]
    [Finite G] [Finite Ω] (htr : ∀ x y : Ω, ∃ g : G, g • x = y) (h3 : 3 ≤ Nat.card Ω) (a : Ω)
    (U : Subgroup G) (hUa : U ≤ rootPointStabilizer G a)
    (hUn : (U.subgroupOf (rootPointStabilizer G a)).Normal)
    (hreg : ∀ y z : Ω, y ≠ a → z ≠ a → ∃! u : U, (u : G) • y = z) :
    (∀ g h : G, g • a = h • a →
      U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom) ∧
    (∃! V : Ω → Subgroup G, IsFiniteConjugateRootGroupDatum G Ω V ∧ V a = U) ∧
    (∀ V : Ω → Subgroup G, IsFiniteConjugateRootGroupDatum G Ω V → V a = U →
      ∀ (x : Ω) (g : G), g • a = x → V x = U.map (MulAut.conj g).toMonoidHom) ∧
    (∀ x y x' y' : Ω, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y') := by
  have hind : ∀ g h : G, g • a = h • a →
      U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom :=
    fun g h hgh => map_conj_eq_of_smul_eq hUa hUn hgh
  have hformula : ∀ V : Ω → Subgroup G, IsFiniteConjugateRootGroupDatum G Ω V → V a = U →
      ∀ (x : Ω) (g : G), g • a = x → V x = U.map (MulAut.conj g).toMonoidHom := by
    intro V hV hVa x g hg
    rw [← hg, ← hV.conj g a, hVa]
  let V : Ω → Subgroup G := fun x => U.map (MulAut.conj (htr a x).choose).toMonoidHom
  have hVspec : ∀ x, (htr a x).choose • a = x := fun x => (htr a x).choose_spec
  have hVx : ∀ (x : Ω) (g : G), g • a = x → V x = U.map (MulAut.conj g).toMonoidHom :=
    fun x g hg => hind _ _ ((hVspec x).trans hg.symm)
  have hVa : V a = U := by
    rw [hVx a 1 (one_smul G a)]
    ext u
    rw [mem_map_conj]
    simp
  have hdatum : IsFiniteConjugateRootGroupDatum G Ω V := by
    refine ⟨inferInstance, inferInstance, h3, ?_, ?_, ?_⟩
    · intro x u hu
      obtain ⟨g, hg⟩ := htr a x
      rw [hVx x g hg, mem_map_conj] at hu
      have hfix : (g⁻¹ * u * g) • a = a := hUa hu
      rw [← hg]
      have h1 : u • g • a = g • (g⁻¹ * u * g) • a := by
        rw [smul_smul, smul_smul]
        congr 1
        group
      rw [h1, hfix]
    · intro x y z hy hz
      obtain ⟨g, hg⟩ := htr a x
      have hy' : g⁻¹ • y ≠ a := fun h => hy (by rw [← hg, ← h, smul_inv_smul])
      have hz' : g⁻¹ • z ≠ a := fun h => hz (by rw [← hg, ← h, smul_inv_smul])
      obtain ⟨v, hv, hvu⟩ := hreg _ _ hy' hz'
      have hVg := hVx x g hg
      refine ⟨⟨g * v * g⁻¹, by rw [hVg, mem_map_conj]; simp [mul_assoc]⟩, ?_, ?_⟩
      · show (g * v * g⁻¹) • y = z
        rw [mul_smul, mul_smul, hv, smul_inv_smul]
      · rintro ⟨w, hw⟩ hwy
        change w • y = z at hwy
        have hw' : g⁻¹ * w * g ∈ U := by
          rw [hVg, mem_map_conj] at hw
          exact hw
        have h1 := hvu ⟨g⁻¹ * w * g, hw'⟩ (by
          show (g⁻¹ * w * g) • g⁻¹ • y = g⁻¹ • z
          rw [mul_smul, smul_inv_smul, mul_smul, hwy])
        apply Subtype.ext
        have h2 := congrArg Subtype.val h1
        change g⁻¹ * w * g = (v : G) at h2
        change w = g * v * g⁻¹
        rw [← h2]
        group
    · intro h x
      obtain ⟨g, hg⟩ := htr a x
      rw [hVx x g hg, hVx (h • x) (h * g) (by rw [mul_smul, hg])]
      ext u
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_map_conj, mem_map_conj,
        show g⁻¹ * (h⁻¹ * u * h) * g = (h * g)⁻¹ * u * (h * g) by group]
  refine ⟨hind, ⟨V, ⟨hdatum, hVa⟩, fun W hW => funext fun x =>
    hformula W hW.1 hW.2 x _ (hVspec x)⟩, hformula, ?_⟩
  intro x y x' y' hxy hxy'
  obtain ⟨g₁, hg₁⟩ := htr x a
  obtain ⟨g₂, hg₂⟩ := htr x' a
  have hy₁ : g₁ • y ≠ a := fun h => hxy (by rw [← smul_left_cancel_iff g₁, hg₁, h])
  have hy₂ : g₂ • y' ≠ a := fun h => hxy' (by rw [← smul_left_cancel_iff g₂, hg₂, h])
  obtain ⟨u, hu, -⟩ := hreg _ _ hy₁ hy₂
  refine ⟨g₂⁻¹ * u * g₁, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hg₁, show (u : G) • a = a from hUa u.2, ← hg₂, inv_smul_smul]
  · rw [mul_smul, mul_smul, hu, inv_smul_smul]

end CFSG.LocalAnalysis
