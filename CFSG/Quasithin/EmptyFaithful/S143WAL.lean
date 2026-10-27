module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.DFinsupp

public section

namespace CFSG.Quasithin.S143W

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private theorem odd_nsmul_eq_self {n : ℕ} (hn : Odd n) (x : M) : n • x = x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hn.natCast_zmod_two, one_smul]

theorem coprime_decomp_of_odd (S : Subgroup (M ≃ₗ[ZMod 2] M)) (hS : Odd (Nat.card S)) :
    (∀ x : M, ∃ n ∈ Submodule.span (ZMod 2) {y : M | ∃ g ∈ S, ∃ w : M, y = g w - w},
        ∃ c : M, (∀ g ∈ S, g c = c) ∧ x = n + c) ∧
    ∀ x ∈ Submodule.span (ZMod 2) {y : M | ∃ g ∈ S, ∃ w : M, y = g w - w},
        (∀ g ∈ S, g x = x) → x = 0 := by
  have : Finite S := Nat.finite_of_card_ne_zero hS.pos.ne'
  have : Fintype S := Fintype.ofFinite S
  let P : M →ₗ[ZMod 2] M := ∑ g : S, ((g : M ≃ₗ[ZMod 2] M) : M →ₗ[ZMod 2] M)
  have hP : ∀ x, P x = ∑ g : S, (g : M ≃ₗ[ZMod 2] M) x := fun x => by
    simp [P, LinearMap.sum_apply]
  have hconst : ∀ x : M, ∑ _g : S, x = x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact odd_nsmul_eq_self hS x
  have h1 : ∀ h ∈ S, ∀ x, h (P x) = P x := fun h hh x => by
    rw [hP, map_sum]
    exact (Equiv.sum_comp (Equiv.mulLeft (⟨h, hh⟩ : S)) (fun g : S => (g : M ≃ₗ[ZMod 2] M) x))
  have h2 : ∀ x : M, (∀ g ∈ S, g x = x) → P x = x := fun x hx => by
    rw [hP]
    calc ∑ g : S, (g : M ≃ₗ[ZMod 2] M) x = ∑ _g : S, x := Finset.sum_congr rfl fun g _ => hx g g.2
      _ = x := hconst x
  have h3 : ∀ g ∈ S, ∀ x, P (g x) = P x := fun g hg x => by
    rw [hP, hP]
    exact (Equiv.sum_comp (Equiv.mulRight (⟨g, hg⟩ : S)) (fun h : S => (h : M ≃ₗ[ZMod 2] M) x))
  have h4 : ∀ x : M, x - P x ∈ Submodule.span (ZMod 2) {y : M | ∃ g ∈ S, ∃ w : M, y = g w - w} := by
    intro x
    rw [hP]
    nth_rewrite 1 [← hconst x]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun g _ => ?_
    have : x - (g : M ≃ₗ[ZMod 2] M) x = -((g : M ≃ₗ[ZMod 2] M) x - x) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨g, g.2, x, rfl⟩)
  refine ⟨fun x => ⟨x - P x, h4 x, P x, fun h hh => h1 h hh x, by abel⟩, fun x hx hfix => ?_⟩
  have hker : Submodule.span (ZMod 2) {y : M | ∃ g ∈ S, ∃ w : M, y = g w - w} ≤ LinearMap.ker P := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨g, hg, w, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, h3 g hg, sub_self]
  have h0 : P x = 0 := hker hx
  rw [← h2 x hfix]
  exact h0

theorem ker_eq_bot_of_odd_normal {Θ : Type*} [Group Θ] [Finite Θ] {Vt Vh : Type*} [AddCommGroup Vt]
    [Module (ZMod 2) Vt] [Finite Vt] [AddCommGroup Vh] [Module (ZMod 2) Vh]
    (ρ : Θ →* (Vt ≃ₗ[ZMod 2] Vt)) (σ : Θ →* (Vh ≃ₗ[ZMod 2] Vh)) (π : Vt →ₗ[ZMod 2] Vh)
    (hπρ : ∀ (θ : Θ) (x : Vt), π (ρ θ x) = σ θ (π x)) (K : Subgroup Θ) (hKn : K.Normal)
    (hodd : Odd (Nat.card (K.map ρ))) (hKZ : ∀ k ∈ K, ∀ z : Vt, π z = 0 → ρ k z = z)
    (hfix : ∀ w : Vh, (∀ k ∈ K, σ k w = w) → w = 0) (Y : Subgroup Θ)
    (hYZ : ∀ y ∈ Y, ∀ z : Vt, π z = 0 → ρ y z = z) (v : Vt)
    (hv : v ∈ Submodule.span (ZMod 2) {x : Vt | ∃ y ∈ Y, ∃ w : Vt, x = ρ y w - w})
    (hgen : Submodule.span (ZMod 2) (Set.range fun θ : Θ => ρ θ v) = ⊤) :
    ∀ z : Vt, π z = 0 → z = 0 := by
  obtain ⟨hdec, huniq⟩ := coprime_decomp_of_odd (K.map ρ) hodd
  set N := Submodule.span (ZMod 2) {y : Vt | ∃ g ∈ K.map ρ, ∃ w : Vt, y = g w - w} with hN
  have hinv : ∀ θ : Θ, ∀ x ∈ N, ρ θ x ∈ N := by
    intro θ x hx
    have hle : N ≤ N.comap (ρ θ : Vt →ₗ[ZMod 2] Vt) := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨g, hg, w, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨ρ (θ * k * θ⁻¹),
        Subgroup.mem_map_of_mem _ (hKn.conj_mem k hk θ), ρ θ w, ?_⟩
      simp [map_mul]
    exact hle hx
  have hker_of_fix : ∀ c : Vt, (∀ g ∈ K.map ρ, g c = c) → π c = 0 := by
    intro c hc
    refine hfix _ fun k hk => ?_
    rw [← hπρ, hc _ (Subgroup.mem_map_of_mem _ hk)]
  have hgenN : ∀ y ∈ Y, ∀ w, ρ y w - w ∈ N := by
    intro y hy w
    obtain ⟨n, hn, c, hc, rfl⟩ := hdec w
    have hπc : π c = 0 := hker_of_fix c hc
    have : ρ y (n + c) - (n + c) = ρ y n - n := by
      rw [map_add, hYZ y hy c hπc]; abel
    rw [this]
    exact N.sub_mem (hinv y n hn) hn
  have hvN : v ∈ N := by
    have : Submodule.span (ZMod 2) {x : Vt | ∃ y ∈ Y, ∃ w : Vt, x = ρ y w - w} ≤ N := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨y, hy, w, rfl⟩
      exact hgenN y hy w
    exact this hv
  have hNtop : N = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨θ, rfl⟩
    exact hinv θ v hvN
  intro z hz
  refine huniq z (by rw [hNtop]; trivial) ?_
  intro g hg
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
  exact hKZ k hk z hz

end CFSG.Quasithin.S143W
