module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigTorus
public import CFSG.Quasithin.Background.JonesParshallBasic
import CFSG.ClassicalGroups.Orthogonal.RootGroupPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Quasithin.JonesParshall

theorem w183_normalize_torus {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha : 1 ≤ a) {G M : Type} [Group G] [AddCommGroup M]
    (μ : G →* AddMonoid.End M) (h2 : ∀ m : M, m + m = 0) (φ : Kˣ →* G) {f : G → M}
    (hf : f ∈ Z1A μ) : ∃ m : M, ∀ c : Kˣ, f (φ c) = μ (φ c) m - m := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hodd : Odd (⊥ : Subgroup Kˣ).index := by
    rw [Subgroup.index_bot, Nat.card_units, hK, pow_succ]
    exact ⟨2 ^ b - 1, by have := Nat.one_le_two_pow (n := b); omega⟩
  obtain ⟨m, hm⟩ := mem_B1A_of_vanish h2 hodd (f := fun c : Kˣ => f (φ c)) (μ := μ.comp φ)
    (fun g h => by simp only [map_mul]; exact mem_Z1A.mp hf (φ g) (φ h))
    (fun h hh => by rw [Subgroup.mem_bot] at hh; subst hh; simpa using Z1A_one hf)
  exact ⟨m, fun c => by simpa [coboundaryA_apply] using (congrFun hm c).symm⟩

theorem w183_root_add {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {f : ↥(elementaryGroup Q) → V}
    (hf : f ∈ Z1A (w183ElemAct Q)) (P : HypPair Q) {u v : V} (hu : u ∈ P.perp)
    (hv : v ∈ P.perp) :
    f (w183El Q P.e (u + v)) = f (w183El Q P.e u) + eichler Q P.e u (f (w183El Q P.e v)) := by
  rw [← w183El_mul (HypPair.mem_perp.mp hu).1 (HypPair.mem_perp.mp hv).1, mem_Z1A.mp hf]
  rfl

theorem w183_root_conj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {f : ↥(elementaryGroup Q) → V}
    (hf : f ∈ Z1A (w183ElemAct Q)) (P : HypPair Q) {d : ↥(elementaryGroup Q)}
    (hd0 : f d = 0) {c : K} (hdx : (d : V ≃ₗ[K] V) P.e = c • P.e)
    (hdU : ∀ z ∈ P.perp, (d : V ≃ₗ[K] V) z = z) {u : V} (hu : u ∈ P.perp) :
    f (w183El Q P.e (c • u)) = (d : V ≃ₗ[K] V) (f (w183El Q P.e u)) := by
  have h1 : d * w183El Q P.e u * d⁻¹ = w183El Q P.e (c • u) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, w183El_coe]
    rw [eichler_conj (elementaryGroup_le_orthogonalGroup Q d.2), hdx, hdU u hu,
      eichler_smul_left]
  have h2 := Z1A_conj hf d (w183El Q P.e u)
  rw [h1, hd0, map_zero, add_zero, sub_zero] at h2
  exact h2

theorem w183_zero_of_roots {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {f : ↥(elementaryGroup Q) → V} (hf : f ∈ Z1A (w183ElemAct Q))
    (hT : ∀ u ∈ P.perp, f (w183El Q P.e u) = 0) (hR : ∀ u ∈ P.perp, f (w183El Q P.f u) = 0) :
    ∀ g, f g = 0 := by
  let Z : Subgroup ↥(elementaryGroup Q) :=
    { carrier := {g | f g = 0}
      one_mem' := Z1A_one hf
      mul_mem' := fun {g h} hg hh => by
        have hg' : f g = 0 := hg
        have hh' : f h = 0 := hh
        change f (g * h) = 0
        rw [mem_Z1A.mp hf, hg', hh', map_zero, add_zero]
      inv_mem' := fun {g} hg => by
        have hg' : f g = 0 := hg
        have h1 := mem_Z1A.mp hf g g⁻¹
        rw [mul_inv_cancel, Z1A_one hf, hg', zero_add, eq_comm] at h1
        change f g⁻¹ = 0
        exact (LinearEquiv.map_eq_zero_iff (g : V ≃ₗ[K] V)).mp h1 }
  have hle : elementaryGroup Q ≤ Z.map (elementaryGroup Q).subtype := by
    refine (rootGroup_sup_eq_elementaryGroup hQ P.Q_e P.Q_f
      (by rw [P.polar_ef]; exact one_ne_zero)).ge.trans (sup_le ?_ ?_)
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
      have h1 : polar Q w P.e = 0 := by rw [polar_comm]; exact hw
      have h2 : eichler Q P.e w = eichler Q P.e (P.proj w) := by
        have : w = P.proj w + polar Q w P.f • P.e := by
          conv_lhs => rw [P.eq_add_proj w]
          rw [h1, zero_smul, add_zero, add_comm]
        conv_lhs => rw [this]
        exact eichler_add_smul_self P.Q_e _ _
      exact ⟨w183El Q P.e (P.proj w), hT _ (P.proj_mem_perp w), h2.symm⟩
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
      have h1 : polar Q w P.f = 0 := by rw [polar_comm]; exact hw
      have h2 : eichler Q P.f w = eichler Q P.f (P.proj w) := by
        have : w = P.proj w + polar Q w P.e • P.f := by
          conv_lhs => rw [P.eq_add_proj w]
          rw [h1, zero_smul, zero_add, add_comm]
        conv_lhs => rw [this]
        exact eichler_add_smul_self P.Q_f _ _
      exact ⟨w183El Q P.f (P.proj w), hR _ (P.proj_mem_perp w), h2.symm⟩
  intro g
  obtain ⟨z, hz, hzg⟩ := hle g.2
  have : z = g := Subtype.ext hzg
  rw [← this]
  exact hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
