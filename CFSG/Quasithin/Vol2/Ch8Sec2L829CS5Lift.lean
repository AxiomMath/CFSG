module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Star
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Cop

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_five_lift_star_cs5 {H A M₀ : Subgroup G} (hAH : A ≤ H) {c : E2.StarQuot M₀ H}
    (hc : c ∈ E2.star M₀ H A) (hc1 : c ≠ 1) {k : ℕ} (hck : c ^ 5 ^ k = 1) :
    ∃ (x : G) (hx : x ∈ A), x ≠ 1 ∧ (∃ a : ℕ, x ^ 5 ^ a = 1) ∧
      ∃ m : ℕ, (QuotientGroup.mk (⟨x, hAH hx⟩ : ↥H) : E2.StarQuot M₀ H) = c ^ m := by
  let f : ↥A →* E2.StarQuot M₀ H :=
    (QuotientGroup.mk' ((kerIn M₀ H).subgroupOf H)).comp (Subgroup.inclusion hAH)
  obtain ⟨a, ha, hac⟩ := mem_star_cs5.mp hc
  have hcf : c ∈ f.range := ⟨⟨a, ha⟩, hac⟩
  obtain ⟨x, hfx, a5, hx5, m, hfm⟩ := exists_five_power_lift_cs5 f hcf hc1 hck
  refine ⟨(x : G), x.2, ?_, ⟨a5, by simpa using congrArg Subtype.val hx5⟩, m, hfm⟩
  intro hx1
  apply hfx
  have : x = 1 := Subtype.ext hx1
  rw [this, map_one]

theorem commutator_mem_kerIn_of_star_commute_cs5 {H M₀ : Subgroup G} {x i : G} (hx : x ∈ H)
    (hi : i ∈ H)
    (hcomm : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : E2.StarQuot M₀ H) * QuotientGroup.mk ⟨i, hi⟩ =
      QuotientGroup.mk ⟨i, hi⟩ * QuotientGroup.mk ⟨x, hx⟩) :
    x * i * x⁻¹ * i⁻¹ ∈ kerIn M₀ H := by
  have h1 : (⟨x, hx⟩ * ⟨i, hi⟩ * ⟨x, hx⟩⁻¹ * ⟨i, hi⟩⁻¹ : ↥H) ∈ (kerIn M₀ H).subgroupOf H := by
    rw [← QuotientGroup.ker_mk' ((kerIn M₀ H).subgroupOf H), MonoidHom.mem_ker]
    show (QuotientGroup.mk (⟨x, hx⟩ * ⟨i, hi⟩ * ⟨x, hx⟩⁻¹ * ⟨i, hi⟩⁻¹ : ↥H) : E2.StarQuot M₀ H) = 1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm]
    group
  exact Subgroup.mem_subgroupOf.mp h1

end CFSG.Quasithin.H13
