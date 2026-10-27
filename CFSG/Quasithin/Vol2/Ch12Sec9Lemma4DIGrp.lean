module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.Quasithin.H13.C1294

theorem sylow_odd_normal {N : Type} [Group N] [Finite N] (A S : Subgroup N) [A.Normal]
    (hS2 : IsPGroup 2 S) (hSyl : ¬ 2 ∣ S.index) (hSA : S ≤ A)
    (hodd : ∀ x : N, Odd (orderOf x) → x ∈ A) : A = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Sylow 2 N, (S' : Subgroup N) = S :=
    ⟨hS2.toSylow hSyl, rfl⟩
  haveI : Finite (Sylow 2 N) := Sylow.finite_of_finiteIndex S'
  have hsyl : ∀ y : N, (∃ k : ℕ, y ^ 2 ^ k = 1) → ∃ g s : N, s ∈ S ∧ y = g * s * g⁻¹ := by
    rintro y ⟨k, hk⟩
    have hZ : IsPGroup 2 (Subgroup.zpowers y) := by
      refine isPGroup_iff_pow_pow_eq_one.2 ?_
      rintro ⟨z, hz⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      refine ⟨k, Subtype.ext ?_⟩
      show (y ^ m) ^ 2 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S' Q
    have hyQ : y ∈ (Q : Subgroup N) := hQ (Subgroup.mem_zpowers y)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS'] at hyQ
    refine ⟨g, (MulAut.conj g)⁻¹ • y, hyQ, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    group
  have hdecomp : ∀ x : N, ∃ x₂ x₀ : N,
      x = x₂ * x₀ ∧ (∃ k : ℕ, x₂ ^ 2 ^ k = 1) ∧ Odd (orderOf x₀) := by
    intro x
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : IsCoprime ((2 : ℤ) ^ a) (b : ℤ) := by
      have h := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hb))
      exact_mod_cast h
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨x ^ (v * (b : ℤ)), x ^ (u * 2 ^ a), ?_, ⟨a, ?_⟩, ?_⟩
    · rw [← zpow_add, show v * (b : ℤ) + u * 2 ^ a = 1 by linarith, zpow_one]
    · rw [← zpow_natCast (x ^ (v * (b : ℤ))) (2 ^ a), ← zpow_mul]
      apply orderOf_dvd_iff_zpow_eq_one.1
      rw [hab]
      exact ⟨v, by push_cast; ring⟩
    · apply Odd.of_dvd_nat hb
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast (x ^ (u * 2 ^ a)) b, ← zpow_mul]
      apply orderOf_dvd_iff_zpow_eq_one.1
      rw [hab]
      exact ⟨u, by push_cast; ring⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨x₂, x₀, hx, h2, hodd0⟩ := hdecomp x
  obtain ⟨g, s, hs, hxs⟩ := hsyl x₂ h2
  have hx₂ : x₂ ∈ A := by
    rw [hxs]
    exact Subgroup.Normal.conj_mem inferInstance s (hSA hs) g
  rw [hx]
  exact A.mul_mem hx₂ (hodd x₀ hodd0)

theorem fixed_vector_GL {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (hM : 2 ≤ Module.finrank (ZMod 2) M) {v : M} (hv : v ≠ 0) :
    ∃ g : M ≃ₗ[ZMod 2] M, g v ≠ v := by
  haveI : Module.Finite (ZMod 2) M := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  obtain ⟨f, hfv⟩ : ∃ f : Module.Dual (ZMod 2) M, f v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) v).1 hcon)
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_self]
    omega
  obtain ⟨w, hwker, hw0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hfw : f w = 0 := LinearMap.mem_ker.1 hwker
  let g : M ≃ₗ[ZMod 2] M :=
    { toFun := fun x => x + f x • w
      invFun := fun x => x - f x • w
      map_add' := fun x y => by
        simp only [map_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul, smul_add]
      left_inv := fun x => by
        simp [map_add, map_smul, hfw]
      right_inv := fun x => by
        simp [map_sub, map_smul, hfw] }
  have hg : ∀ x, g x = x + f x • w := fun x => rfl
  refine ⟨g, ?_⟩
  rw [hg]
  intro h
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hf1 : f v = 1 := key _ hfv
  have h0 : f v • w = v + f v • w - v := by abel
  rw [h, sub_self, hf1, one_smul] at h0
  exact hw0 h0

end CFSG.Quasithin.H13.C1294
