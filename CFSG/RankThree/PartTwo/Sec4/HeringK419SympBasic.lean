module

public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.LieType.BorelTits

section Flags

variable {K V H : Type*} [Field K] [AddCommGroup V] [Module K V] [Group H]
  (ρ : H →* Module.End K V)

@[expose] def flag2 (A : Submodule K V) : ℕ → Submodule K V
  | 0 => ⊥
  | 1 => A
  | _ => ⊤

@[expose] def flag3 (A B : Submodule K V) : ℕ → Submodule K V
  | 0 => ⊥
  | 1 => A
  | 2 => B
  | _ => ⊤

theorem flag2_zero (A : Submodule K V) : flag2 A 0 = ⊥ := rfl

theorem flag2_two (A : Submodule K V) : flag2 A 2 = ⊤ := rfl

theorem flag3_zero (A B : Submodule K V) : flag3 A B 0 = ⊥ := rfl

theorem flag3_three (A B : Submodule K V) : flag3 A B 3 = ⊤ := rfl

theorem mem_flagStab_flag2 {A : Submodule K V} {g : H}
    (hA : ∀ w ∈ A, ρ g w ∈ A ∧ ρ g⁻¹ w ∈ A) : g ∈ flagStab ρ (flag2 A) := by
  intro i w hw
  match i with
  | 0 =>
    have h0 : w = 0 := by simpa [flag2] using hw
    subst h0
    simp [flag2]
  | 1 => exact hA w hw
  | i + 2 => simp [flag2]

theorem mem_flagKernel_flag2 {A : Submodule K V} {g : H} (hs : g ∈ flagStab ρ (flag2 A))
    (h1 : ∀ w ∈ A, ρ g w = w) (h2 : ∀ w, ρ g w - w ∈ A) : g ∈ flagKernel ρ (flag2 A) := by
  refine ⟨hs, fun i w hw => ?_⟩
  match i with
  | 0 =>
    have hwA : w ∈ A := by simpa [flag2] using hw
    simp [flag2, h1 w hwA]
  | 1 => simpa [flag2] using h2 w
  | i + 2 => simp [flag2]

theorem mem_flagStab_flag3 {A B : Submodule K V} {g : H}
    (hA : ∀ w ∈ A, ρ g w ∈ A ∧ ρ g⁻¹ w ∈ A) (hB : ∀ w ∈ B, ρ g w ∈ B ∧ ρ g⁻¹ w ∈ B) :
    g ∈ flagStab ρ (flag3 A B) := by
  intro i w hw
  match i with
  | 0 =>
    have h0 : w = 0 := by simpa [flag3] using hw
    subst h0
    simp [flag3]
  | 1 => exact hA w hw
  | 2 => exact hB w hw
  | i + 3 => simp [flag3]

theorem mem_flagKernel_flag3 {A B : Submodule K V} {g : H} (hs : g ∈ flagStab ρ (flag3 A B))
    (h1 : ∀ w ∈ A, ρ g w = w) (h2 : ∀ w ∈ B, ρ g w - w ∈ A) (h3 : ∀ w, ρ g w - w ∈ B) :
    g ∈ flagKernel ρ (flag3 A B) := by
  refine ⟨hs, fun i w hw => ?_⟩
  match i with
  | 0 =>
    have hwA : w ∈ A := by simpa [flag3] using hw
    simp [flag3, h1 w hwA]
  | 1 => simpa [flag3] using h2 w (by simpa [flag3] using hw)
  | 2 => simpa [flag3] using h3 w
  | i + 3 => simp [flag3]

theorem conj_mem_flagKernel {F : ℕ → Submodule K V} {k : H} (hk : k ∈ flagStab ρ F) {t : H}
    (ht : t ∈ flagKernel ρ F) : k * t * k⁻¹ ∈ flagKernel ρ F :=
  (Subgroup.mem_normalizer_iff.mp (flagStab_le_normalizer_flagKernel ρ F hk) t).mp ht

end Flags

structure SympData (K V H : Type*) [Field K] [AddCommGroup V] [Module K V] [Group H] where
  F : ReflForm K V
  σ_eq : F.σ = RingEquiv.refl K
  alt : ∀ v, F.β v v = 0
  ρ : H →* Module.End K V
  iso : IsIsometric F ρ
  inj : Function.Injective ρ
  trans : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x
  siegel : ∀ x y : V, F.β x y = 0 → ∃ h : H, ∀ v, ρ h v = v + F.β x v • y + F.β y v • x

namespace SympData

variable {K V H : Type*} [Field K] [AddCommGroup V] [Module K V] [Group H]
  (D : SympData K V H)

theorem β_smul_left (c : K) (u v : V) : D.F.β (c • u) v = c * D.F.β u v := by
  rw [D.F.smul_left, D.σ_eq]
  rfl

theorem β_swap [CharP K 2] (u v : V) : D.F.β v u = D.F.β u v := by
  rw [D.F.β_swap_of_alt D.alt]
  exact CharTwo.neg_eq _

theorem rep_inv_apply (g : H) (v : V) : D.ρ g⁻¹ (D.ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rep_apply_inv (g : H) (v : V) : D.ρ g (D.ρ g⁻¹ v) = v :=
  rep_apply_inv_apply D.ρ g v

theorem β_rep_left (g : H) (u v : V) : D.F.β (D.ρ g u) v = D.F.β u (D.ρ g⁻¹ v) := by
  have := D.iso g u (D.ρ g⁻¹ v)
  rwa [D.rep_apply_inv] at this

theorem β_rep_right (g : H) (u v : V) : D.F.β u (D.ρ g v) = D.F.β (D.ρ g⁻¹ u) v := by
  have := D.iso g (D.ρ g⁻¹ u) v
  rwa [D.rep_apply_inv] at this

theorem exists_β_ne_zero {v : V} (hv : v ≠ 0) : ∃ x, D.F.β v x ≠ 0 := by
  by_contra! h
  exact hv (D.F.nondeg v h)

theorem trans_sq [CharP K 2] {h : H} {x : V} (hh : ∀ w, D.ρ h w = w + D.F.β x w • x) (w : V) :
    D.ρ h (D.ρ h w) = w := by
  have e : D.ρ h (D.ρ h w) = w + (D.F.β x w + D.F.β x w) • x := by
    rw [hh (D.ρ h w), hh w, D.F.add_right, D.F.smul_right, D.alt x, mul_zero, add_zero]
    module
  rw [e, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem trans_mul_self [CharP K 2] {h : H} {x : V} (hh : ∀ w, D.ρ h w = w + D.F.β x w • x) :
    h * h = 1 :=
  D.inj (by
    refine LinearMap.ext fun w => ?_
    rw [map_mul, Module.End.mul_apply, D.trans_sq hh, map_one, Module.End.one_apply])

theorem trans_inv [CharP K 2] {h : H} {x : V} (hh : ∀ w, D.ρ h w = w + D.F.β x w • x) :
    h⁻¹ = h :=
  inv_eq_of_mul_eq_one_right (D.trans_mul_self hh)

theorem siegel_sq [CharP K 2] {h : H} {x y : V} (hxy : D.F.β x y = 0)
    (hh : ∀ w, D.ρ h w = w + D.F.β x w • y + D.F.β y w • x) (w : V) :
    D.ρ h (D.ρ h w) = w := by
  have hyx : D.F.β y x = 0 := D.F.refl _ _ hxy
  have e : D.ρ h (D.ρ h w) =
      w + (D.F.β x w + D.F.β x w) • y + (D.F.β y w + D.F.β y w) • x := by
    rw [hh (D.ρ h w), hh w]
    simp only [D.F.add_right, D.F.smul_right, D.alt, hxy, hyx, mul_zero, add_zero]
    module
  rw [e]
  simp only [CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem siegel_mul_self [CharP K 2] {h : H} {x y : V} (hxy : D.F.β x y = 0)
    (hh : ∀ w, D.ρ h w = w + D.F.β x w • y + D.F.β y w • x) : h * h = 1 :=
  D.inj (by
    refine LinearMap.ext fun w => ?_
    rw [map_mul, Module.End.mul_apply, D.siegel_sq hxy hh, map_one, Module.End.one_apply])

theorem siegel_inv [CharP K 2] {h : H} {x y : V} (hxy : D.F.β x y = 0)
    (hh : ∀ w, D.ρ h w = w + D.F.β x w • y + D.F.β y w • x) : h⁻¹ = h :=
  inv_eq_of_mul_eq_one_right (D.siegel_mul_self hxy hh)

end SympData

end CFSG.RankThree.PartTwo.Sec4.HeringK419
