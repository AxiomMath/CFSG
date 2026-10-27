module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

theorem mem_zOf_iff {X : Subgroup G} {x : G} :
    x ∈ zOf X ↔ x ∈ X ∧ ∀ w ∈ X, w * x = x * w := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    exact ⟨hy, fun w hw => congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨w, hw⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩

theorem zOf_le (X : Subgroup G) : zOf X ≤ X := fun _ hx => (mem_zOf_iff.mp hx).1

theorem mem_normalizer_zOf {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (zOf X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ zOf X, g * x * g⁻¹ ∈ zOf X := by
    intro g hg x hx
    obtain ⟨hxX, hxc⟩ := mem_zOf_iff.mp hx
    refine mem_zOf_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) w).mp hw
    have hcomm := hxc _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx⟩

theorem mem_normalizer_commutator {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, X⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem mem_normalizer_centralizer_singleton {b z : G} (hz : z ∈ Subgroup.centralizer {b}) :
    z ∈ Subgroup.normalizer (Subgroup.centralizer {b} : Set G) := by
  have hzc : Commute z b := Subgroup.mem_centralizer_singleton_iff.mp hz
  have key : ∀ z : G, Commute z b → ∀ x ∈ Subgroup.centralizer {b},
      z * x * z⁻¹ ∈ Subgroup.centralizer {b} := by
    intro z hz x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hz.mul_left (Subgroup.mem_centralizer_singleton_iff.mp hx)).mul_left hz.inv_left)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key z hzc x hx, fun hx => by simpa [mul_assoc] using key z⁻¹ hzc.inv_left _ hx⟩

theorem pow_index_center_eq_one {W : Type*} [Group W] [Finite W] (hperf : commutator W = ⊤)
    (z : W) : z ^ (Subgroup.center W).index = 1 := by
  have hker : commutator W ≤ (MonoidHom.transferCenterPow W).ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have h1 : MonoidHom.transferCenterPow W z = 1 := by
    have : z ∈ (MonoidHom.transferCenterPow W).ker := hker (hperf ▸ Subgroup.mem_top z)
    exact this
  have h2 := congrArg Subtype.val h1
  simpa using h2

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
