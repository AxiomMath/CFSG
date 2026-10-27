module

public import CFSG.Quasithin.Background.SmithB42D4Coord

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

abbrev rA : WeylGroup TwistTag.D4.tag := TwistTag.D4.orbitReflection ⟨0, by decide⟩

abbrev rB : WeylGroup TwistTag.D4.tag := TwistTag.D4.orbitReflection ⟨1, by decide⟩

abbrev w0 : WeylGroup TwistTag.D4.tag := (rA * rB) ^ 3

theorem rA_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rA • v = reflect TwistTag.D4.tag ⟨0, by decide⟩ (reflect TwistTag.D4.tag ⟨1, by decide⟩
      (reflect TwistTag.D4.tag ⟨3, by decide⟩ v)) := by
  have hw : TwistTag.D4.orbitWord ⟨0, by decide⟩ =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
  change (coxeterSystem TwistTag.D4.tag).wordProd (TwistTag.D4.orbitWord ⟨0, by decide⟩) • v = _
  rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]

theorem rB_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rB • v = reflect TwistTag.D4.tag ⟨2, by decide⟩ v := by
  have hw : TwistTag.D4.orbitWord ⟨1, by decide⟩ = [⟨2, by decide⟩] := by decide
  change (coxeterSystem TwistTag.D4.tag).wordProd (TwistTag.D4.orbitWord ⟨1, by decide⟩) • v = _
  rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]

theorem w0_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    w0 • v = rA • rB • rA • rB • rA • rB • v := by
  rw [w0, pow_three, mul_smul, mul_smul, mul_smul, mul_smul, mul_smul]

section Mem


theorem rA_mem : rA ∈ relWeylTwist TwistTag.D4 := TwistTag.D4.orbitReflection_mem _

theorem rB_mem : rB ∈ relWeylTwist TwistTag.D4 := TwistTag.D4.orbitReflection_mem _

theorem w0_mem : w0 ∈ relWeylTwist TwistTag.D4 :=
  pow_mem (mul_mem rA_mem rB_mem) 3

end Mem

section Roots

theorem rA_C : rA • d4C = d4P := by rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_P : rA • d4P = d4C := by rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_H : rA • d4H = d4H := by rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_M0 : rA • d4M0 = d4N13 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_M1 : rA • d4M1 = d4N03 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_M3 : rA • d4M3 = d4N01 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_N13 : rA • d4N13 = d4M0 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_N03 : rA • d4N03 = d4M1 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rA_N01 : rA • d4N01 = d4M3 := by
  rw [rA_smul]; exact List.ofFn_injective (by decide +kernel)

theorem rB_E0 : rB • d4E0 = d4M0 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_E1 : rB • d4E1 = d4M1 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_E3 : rB • d4E3 = d4M3 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_M0 : rB • d4M0 = d4E0 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_M1 : rB • d4M1 = d4E1 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_M3 : rB • d4M3 = d4E3 := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_N13 : rB • d4N13 = d4N13 := by
  rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_N03 : rB • d4N03 = d4N03 := by
  rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_N01 : rB • d4N01 = d4N01 := by
  rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_P : rB • d4P = d4H := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_H : rB • d4H = d4P := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)
theorem rB_C : rB • d4C = -d4C := by rw [rB_smul]; exact List.ofFn_injective (by decide +kernel)

theorem w0_neg {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α = d4E0 ∨ α = d4E1 ∨ α = d4E3 ∨ α = d4C ∨ α = d4M0 ∨ α = d4M1 ∨ α = d4M3 ∨
      α = d4N13 ∨ α = d4N03 ∨ α = d4N01 ∨ α = d4P ∨ α = d4H) :
    w0 • α = -α := by
  rw [w0_smul, rA_smul, rA_smul, rA_smul, rB_smul, rB_smul, rB_smul]
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact List.ofFn_injective (by decide +kernel)

end Roots

section Conj

variable {G : Type*} [Group G]

theorem conj_mul3 (g x y z : G) :
    g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := by group

theorem conj_mul2 (g x y : G) : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

end Conj

theorem isRoot_of_d4 {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h : d4IsRootB α = true) : IsRoot TwistTag.D4.tag α :=
  d4IsRootB_iff.1 h

section Weyl

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

local notation "Xr" => pinnedX TwistTag.D4.tag K

variable (K) in
noncomputable abbrev nA : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K rA

variable (K) in
noncomputable abbrev nB : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K rB

variable (K) in
noncomputable abbrev nW0 : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K w0

theorem nA_conj {α : Fin TwistTag.D4.tag.rank → ℤ} (h : d4IsRootB α = true) (x : K) :
    nA K * Xr α x * (nA K)⁻¹ = Xr (rA • α) x :=
  canonicalRep_conj_charTwo' rA (isRoot_of_d4 h) x

theorem nB_conj {α : Fin TwistTag.D4.tag.rank → ℤ} (h : d4IsRootB α = true) (x : K) :
    nB K * Xr α x * (nB K)⁻¹ = Xr (rB • α) x :=
  canonicalRep_conj_charTwo' rB (isRoot_of_d4 h) x

theorem nW0_conj {α : Fin TwistTag.D4.tag.rank → ℤ} (h : d4IsRootB α = true) (x : K) :
    nW0 K * Xr α x * (nW0 K)⁻¹ = Xr (w0 • α) x :=
  canonicalRep_conj_charTwo' w0 (isRoot_of_d4 h) x

theorem nA_C (x : K) : nA K * Xr d4C x * (nA K)⁻¹ = Xr d4P x := by
  rw [nA_conj (by decide +kernel), rA_C]

theorem nA_P (x : K) : nA K * Xr d4P x * (nA K)⁻¹ = Xr d4C x := by
  rw [nA_conj (by decide +kernel), rA_P]

theorem nA_H (x : K) : nA K * Xr d4H x * (nA K)⁻¹ = Xr d4H x := by
  rw [nA_conj (by decide +kernel), rA_H]

theorem nA_ox₃ (c : K) : nA K * ox₃ σ c * (nA K)⁻¹ = ox₄ σ c := by
  rw [coe_ox₃_eq, coe_ox₄_eq, conj_mul3, nA_conj (by decide +kernel), nA_conj (by decide +kernel),
    nA_conj (by decide +kernel), rA_M0, rA_M1, rA_M3]

theorem nA_ox₄ (c : K) : nA K * ox₄ σ c * (nA K)⁻¹ = ox₃ σ c := by
  rw [coe_ox₃_eq, coe_ox₄_eq, conj_mul3, nA_conj (by decide +kernel), nA_conj (by decide +kernel),
    nA_conj (by decide +kernel), rA_N13, rA_N03, rA_N01]

theorem nB_ox₁ (c : K) : nB K * ox₁ σ c * (nB K)⁻¹ = ox₃ σ c := by
  rw [coe_ox₁_eq, coe_ox₃_eq, conj_mul3, nB_conj (by decide +kernel), nB_conj (by decide +kernel),
    nB_conj (by decide +kernel), rB_E0, rB_E1, rB_E3]

theorem nB_ox₃ (c : K) : nB K * ox₃ σ c * (nB K)⁻¹ = ox₁ σ c := by
  rw [coe_ox₁_eq, coe_ox₃_eq, conj_mul3, nB_conj (by decide +kernel), nB_conj (by decide +kernel),
    nB_conj (by decide +kernel), rB_M0, rB_M1, rB_M3]

theorem nB_ox₄ (c : K) : nB K * ox₄ σ c * (nB K)⁻¹ = ox₄ σ c := by
  rw [coe_ox₄_eq, conj_mul3, nB_conj (by decide +kernel), nB_conj (by decide +kernel),
    nB_conj (by decide +kernel), rB_N13, rB_N03, rB_N01]

theorem nB_P (x : K) : nB K * Xr d4P x * (nB K)⁻¹ = Xr d4H x := by
  rw [nB_conj (by decide +kernel), rB_P]

theorem nB_H (x : K) : nB K * Xr d4H x * (nB K)⁻¹ = Xr d4P x := by
  rw [nB_conj (by decide +kernel), rB_H]

theorem nB_C (x : K) : nB K * Xr d4C x * (nB K)⁻¹ = Xr (-d4C) x := by
  rw [nB_conj (by decide +kernel), rB_C]

omit [CharP K 2] in
theorem torA_ox₁ (hσ3 : σ.toRingHom ^ 3 = 1) (a : Kˣ) (s : K) :
    trialityTorusHom σ (a, 1) * ox₁ σ s * (trialityTorusHom σ (a, 1))⁻¹ =
      ox₁ σ ((a : K) ^ 2 * s) := by
  rw [torusHom_eq, torus_ox₁ (twistFixed_torus σ hσ3 a 1), map_one, inv_one, mul_one,
    Units.val_pow_eq_pow_val]

end Weyl

section Mem

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

theorem nA_mem : nA K ∈ C₀ := canonicalRep_mem_graphFixedRootGroup rA_mem

theorem nB_mem : nB K ∈ C₀ := canonicalRep_mem_graphFixedRootGroup rB_mem

theorem nW0_mem : nW0 K ∈ C₀ := canonicalRep_mem_graphFixedRootGroup w0_mem

theorem torus_mem (hσ3 : σ.toRingHom ^ 3 = 1) (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ p ∈ C₀ :=
  trialityTorusHom_mem_graphFixedRootGroup (pow_three_equiv σ hσ3) p

end Mem

end CFSG.Quasithin.B42D4
