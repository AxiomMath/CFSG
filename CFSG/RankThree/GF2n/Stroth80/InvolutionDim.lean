module

public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem range_le_ker_of_sq_eq_one [CharP K 2] (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT2 : T ∘ₗ T = LinearMap.id) :
    LinearMap.range (T - LinearMap.id) ≤ LinearMap.ker (T - LinearMap.id) := by
  have hT : ∀ x : M₀.E, T (T x) = x := fun x => by
    simpa using LinearMap.congr_fun hT2 x
  have h2 : ∀ y : M₀.E, y + y = 0 := fun y => by
    rw [← two_smul K y, CharTwo.two_eq_zero, zero_smul]
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hT]
  calc x - T x - (T x - x) = (x + x) - (T x + T x) := by abel
    _ = 0 := by rw [h2 x, h2 (T x), sub_zero]

theorem finrank_range_le_of_sq_eq_one [CharP K 2] (M₀ : QuadModel QF V K γ) {n : ℕ}
    (hdim : Module.finrank K M₀.E = 2 * n) {T : M₀.E →ₗ[K] M₀.E} (hT2 : T ∘ₗ T = LinearMap.id) :
    Module.finrank K (LinearMap.range (T - LinearMap.id)) ≤ n := by
  have h1 : Module.finrank K (LinearMap.range (T - LinearMap.id)) ≤
      Module.finrank K (LinearMap.ker (T - LinearMap.id)) :=
    Submodule.finrank_mono (range_le_ker_of_sq_eq_one M₀ hT2)
  have h3 : Module.finrank K (LinearMap.range (T - LinearMap.id)) +
      Module.finrank K (LinearMap.ker (T - LinearMap.id)) = Module.finrank K M₀.E :=
    LinearMap.finrank_range_add_finrank_ker _
  omega

end CFSG.RankThree.GF2n.Tim79.QuadModel
