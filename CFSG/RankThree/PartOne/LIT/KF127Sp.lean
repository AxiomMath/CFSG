module

public import CFSG.RankThree.PartOne.LIT.KF127Flag
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.RankThree.PartOne.LIT

section Symplectic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  (B : LinearMap.BilinForm K V)

private noncomputable def symplTransvection (hB : B.IsAlt) (x : V) (c : K) : V ≃ₗ[K] V :=
  LinearEquiv.transvection (f := c • B.flip x) (v := x) (by simp [hB.self_eq_zero x])

private theorem symplTransvection_apply (hB : B.IsAlt) (x : V) (c : K) (y : V) :
    symplTransvection B hB x c y = y + (c * B y x) • x := by
  simp [symplTransvection, LinearMap.transvection.apply]

private theorem symplTransvection_mem (hB : B.IsAlt) (T : Subgroup (V ≃ₗ[K] V))
    (hT : ∀ g : V ≃ₗ[K] V, g ∈ T ↔ ∀ x y, B (g x) (g y) = B x y) (x : V) (c : K) :
    symplTransvection B hB x c ∈ T := by
  rw [hT]
  intro y z
  have h1 : B x x = 0 := hB.self_eq_zero x
  have h2 : B x z = -B z x := (hB.neg_eq z x).symm
  simp only [symplTransvection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

private theorem exists_smul_of_proportional (hBnd : B.Nondegenerate)
    (B' : LinearMap.BilinForm K V) (h : ∀ x y z, B z x * B' y x = B y x * B' z x) :
    ∃ μ : K, ∀ y x, B' y x = μ * B y x := by
  have hloc : ∀ x, ∃ m : K, ∀ y, B' y x = m * B y x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun y => by simp [hx]⟩
    · obtain ⟨z, hz⟩ : ∃ z, B z x ≠ 0 := by
        by_contra hcon
        exact hx (hBnd.2 x (by simpa using hcon))
      refine ⟨B' z x / B z x, fun y => ?_⟩
      field_simp
      linear_combination h x y z
  choose m hm using hloc
  have hinj : ∀ a b : V, (∀ y, B y a = B y b) → a = b := fun a b hab =>
    sub_eq_zero.mp (hBnd.2 (a - b) (fun y => by rw [map_sub, hab y, sub_self]))
  have hfx : ∀ x y, B y (m x • x) = B' y x := fun x y => by
    rw [map_smul, smul_eq_mul, hm x y]
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[K] V, ∀ x, f x = m x • x :=
    ⟨{ toFun := fun x => m x • x
       map_add' := fun x x' => hinj _ _ fun y => by
         rw [hfx, map_add, map_add, hfx, hfx]
       map_smul' := fun c x => hinj _ _ fun y => by
         simp only [RingHom.id_apply]
         rw [hfx, map_smul, smul_eq_mul, map_smul, hfx, smul_eq_mul] },
      fun x => rfl⟩
  have hdep : ∀ x, ¬ LinearIndependent K ![x, f x] := fun x hli => by
    have := (LinearIndependent.pair_iff.1 hli) (m x) (-1) (by rw [hf]; simp)
    simp at this
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  refine ⟨a, fun y x => ?_⟩
  have hfa : m x • x = a • x := by
    have := LinearMap.congr_fun ha x
    simpa [hf] using this
  rw [← hfx x y, hfa, map_smul, smul_eq_mul]

private theorem exists_similitude (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (T : Subgroup (V ≃ₗ[K] V))
    (hT : ∀ g : V ≃ₗ[K] V, g ∈ T ↔ ∀ x y, B (g x) (g y) = B x y)
    (g : V ≃ₗ[K] V) (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) :
    ∃ μ : K, ∀ y z, B (g y) (g z) = μ * B y z := by
  obtain ⟨μ, hμ⟩ := exists_smul_of_proportional B hBnd
    (B.compl₁₂ (g : V →ₗ[K] V) (g : V →ₗ[K] V)) fun x y z => by
    have ht := (hT _).1 (hg _ (symplTransvection_mem B hB T hT x 1)) (g y) (g z)
    have e : ∀ w, g⁻¹ (g w) = w := fun w => by simp
    have h1 : B (g x) (g x) = 0 := hB.self_eq_zero (g x)
    have h2 : B (g x) (g z) = -B (g z) (g x) := (hB.neg_eq (g z) (g x)).symm
    simp only [LinearEquiv.mul_apply, e, symplTransvection_apply, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, one_mul, h1, h2] at ht
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    linear_combination ht
  exact ⟨μ, fun y z => by simpa using hμ y z⟩

private theorem stabilizer_preserves_orth {v : V} (hv : v ≠ 0) {g : V ≃ₗ[K] V} {μ : K}
    (hμ : ∀ y z, B (g y) (g z) = μ * B y z) (hgv : g v ∈ Submodule.span K {v}) {x : V}
    (hx : x ∈ LinearMap.ker (B.flip v)) : g x ∈ LinearMap.ker (B.flip v) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgv
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hv (g.injective (by rw [← hc, map_zero]))
  simp only [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply] at hx ⊢
  have h := hμ x v
  rw [← hc, map_smul, smul_eq_mul, hx, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hc0

private theorem exists_heisenberg (hB : B.IsAlt) (T : Subgroup (V ≃ₗ[K] V))
    (hT : ∀ g : V ≃ₗ[K] V, g ∈ T ↔ ∀ x y, B (g x) (g y) = B x y) (v : V) {x : V}
    (hx : B x v = 0) :
    ∃ q : V ≃ₗ[K] V, q ∈ T ∧ ∀ y, q y = y + B y v • (x + v) + B y x • v := by
  refine ⟨symplTransvection B hB (x + v) 1 * symplTransvection B hB x (-1),
    T.mul_mem (symplTransvection_mem B hB T hT _ _) (symplTransvection_mem B hB T hT _ _),
    fun y => ?_⟩
  have hxx : B x x = 0 := hB.self_eq_zero x
  simp only [LinearEquiv.mul_apply, symplTransvection_apply, map_add, map_smul, hxx, hx]
  module

private theorem heisenberg_mem_flagGroup (hB : B.IsAlt) (v : V) {x : V} (hx : B x v = 0)
    (h12 : Submodule.span K {v} ≤ LinearMap.ker (B.flip v)) (q : V ≃ₗ[K] V)
    (hq : ∀ y, q y = y + B y v • (x + v) + B y x • v) :
    q ∈ flagGroup (Submodule.span K {v}) (LinearMap.ker (B.flip v)) h12 := by
  have hvD : v ∈ LinearMap.ker (B.flip v) := by simpa using hB.self_eq_zero v
  have hxD : x ∈ LinearMap.ker (B.flip v) := by simpa using hx
  refine mem_flagGroup.2 ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have : q y - y = B y v • (x + v) + B y x • v := by rw [hq]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ hxD hvD))
      (Submodule.smul_mem _ _ hvD)
  · have hy' : B y v = 0 := by simpa using hy
    have : q y - y = B y x • v := by rw [hq, hy']; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h1 : B (a • v) v = 0 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero v, mul_zero]
    have h2 : B (a • v) x = 0 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hB.neg_eq x v, hx]
      simp
    rw [hq, h1, h2]
    simp

private theorem fixes_orthogonal_of_commuting (hBnd : B.Nondegenerate) (h2 : (2 : K) ≠ 0)
    {v : V} (hv : v ≠ 0) {l : V ≃ₗ[K] V} (hlv : l v = v) {μ : K}
    (hμ : ∀ y z, B (l y) (l z) = μ * B y z)
    (hcomm : ∀ x, B x v = 0 → ∀ y, l (y + B y v • (x + v) + B y x • v) =
      l y + B (l y) v • (x + v) + B (l y) x • v) :
    (∀ y, B (l y) v = B y v) ∧ ∀ x, B x v = 0 → l x = x := by
  have hC1 : ∀ y, B (l y) v = B y v := by
    intro y
    have h := hcomm 0 (by simp) y
    simp only [map_add, map_smul, hlv, zero_add, map_zero, zero_smul, add_zero] at h
    exact (smul_left_injective K hv (add_left_cancel h)).symm
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, B y₀ v = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, B y v ≠ 0 := by
      by_contra hcon
      exact hv (hBnd.2 v (by simpa using hcon))
    exact ⟨(B y v)⁻¹ • y, by simp [hy]⟩
  have hl1 : B (l y₀) v = 1 := by rw [hC1, hy₀]
  have hμ1 : μ = 1 := by
    have h := hμ y₀ v
    rw [hlv, hl1, hy₀, mul_one] at h
    exact h.symm
  refine ⟨hC1, fun x hx => ?_⟩
  have h := hcomm x hx y₀
  simp only [map_add, map_smul, hlv, hy₀, hl1, one_smul] at h
  have hF : l x = x + (B (l y₀) x - B y₀ x) • v := by
    rw [← sub_eq_zero]
    calc l x - (x + (B (l y₀) x - B y₀ x) • v)
        = (l y₀ + (l x + v) + B y₀ x • v) - (l y₀ + (x + v) + B (l y₀) x • v) := by module
      _ = 0 := sub_eq_zero.mpr h
  have hP : B (l y₀) (l x) = B y₀ x := by rw [hμ y₀ x, hμ1, one_mul]
  rw [hF, map_add, map_smul, smul_eq_mul, hl1, mul_one] at hP
  have hz : B (l y₀) x - B y₀ x = 0 := by
    have : (2 : K) * (B (l y₀) x - B y₀ x) = 0 := by linear_combination hP
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hF, hz, zero_smul, add_zero]

end Symplectic

theorem sp_final {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (T Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)) (hTΓ : T ≤ Γ)
    (hTn : ∀ g ∈ Γ, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hT : ∀ g : V ≃ₗ[ZMod p] V, g ∈ T ↔ ∀ x y, B (g x) (g y) = B x y)
    (hΛΓ : Λ ≤ Γ) (v : V) (hv : v ≠ 0)
    (hnorm : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hfix : ∀ l ∈ Λ, l v = v) (hO : CFSG.pCore p Λ = ⊥) :
    ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
  have hvD₂ : v ∈ LinearMap.ker (B.flip v) := by simpa using hB.self_eq_zero v
  have h12 : Submodule.span (ZMod p) {v} ≤ LinearMap.ker (B.flip v) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvD₂)
  have hD₁ : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} →
      ∀ x ∈ Submodule.span (ZMod p) {v}, g x ∈ Submodule.span (ZMod p) {v} := by
    intro g _ hgv x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hgv
  have hD₂ : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} →
      ∀ x ∈ LinearMap.ker (B.flip v), g x ∈ LinearMap.ker (B.flip v) := by
    intro g hg hgv x hx
    obtain ⟨μ, hμ⟩ := exists_similitude B hB hBnd T hT g (hTn g hg)
    exact stabilizer_preserves_orth B hv hμ hgv hx
  have hcomm : ∀ l ∈ Λ, ∀ x, B x v = 0 → ∀ y,
      l (y + B y v • (x + v) + B y x • v) = l y + B (l y) v • (x + v) + B (l y) x • v := by
    intro l hl x hx y
    obtain ⟨q, hqT, hq⟩ := exists_heisenberg B hB T hT v hx
    have hqf := heisenberg_mem_flagGroup B hB v hx h12 q hq
    have h := flag_comm (by omega) Γ Λ hΛΓ v hnorm hfix hO _ _ h12
      (Submodule.mem_span_singleton_self v) hD₁ hD₂ (hTΓ hqT) hqf hl
    have h' := DFunLike.congr_fun h y
    simp only [LinearEquiv.mul_apply, hq] at h'
    exact h'
  have hfixD : ∀ l ∈ Λ, (∀ y, B (l y) v = B y v) ∧ ∀ x, B x v = 0 → l x = x := by
    intro l hl
    obtain ⟨μ, hμ⟩ := exists_similitude B hB hBnd T hT l (hTn l (hΛΓ hl))
    exact fixes_orthogonal_of_commuting B hBnd h2 hv (hfix l hl) hμ (hcomm l hl)
  have key : ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ y, a (b y) = a y + (b y - y) := by
    intro a ha b hb y
    have hbD : B (b y - y) v = 0 := by
      change B.flip v (b y - y) = 0
      rw [map_sub]
      change B (b y) v - B y v = 0
      rw [(hfixD b hb).1, sub_self]
    have had : a (b y - y) = b y - y := (hfixD a ha).2 _ hbD
    calc a (b y) = a (y + (b y - y)) := congrArg a (by abel)
      _ = a y + a (b y - y) := map_add a _ _
      _ = a y + (b y - y) := by rw [had]
  intro a ha b hb
  ext y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, key a ha b hb, key b hb a ha]
  abel

end CFSG.RankThree.PartOne.LIT
