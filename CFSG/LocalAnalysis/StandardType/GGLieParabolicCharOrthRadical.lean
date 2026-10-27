module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType

namespace GGOrthRad

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Subgroup
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def perp (Q : QuadraticForm K V) (W : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) W

@[expose] def stabE (Q : QuadraticForm K V) (W : Submodule K V) : Subgroup (elementaryGroup Q) :=
  MulAction.stabilizer (elementaryGroup Q) W

private theorem perp_mem_iff {Q : QuadraticForm K V} {W : Submodule K V} {y : V} :
    y ∈ perp Q W ↔ ∀ w ∈ W, polar Q w y = 0 := by
  rw [perp, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [polarBilin_apply_apply]

@[expose] def orthRadical (Q : QuadraticForm K V) (W : Submodule K V) :
    Subgroup (elementaryGroup Q) where
  carrier := {g | (∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) ∧
    ∀ y ∈ perp Q W, (g : V ≃ₗ[K] V) y - y ∈ W}
  one_mem' := ⟨fun w _ => by simp, fun y _ => by simp⟩
  mul_mem' := by
    rintro g g' ⟨hg1, hg2⟩ ⟨hg'1, hg'2⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hg'1 w hw, hg1 w hw]
    · intro y hy
      have h1 : (g' : V ≃ₗ[K] V) y - y ∈ W := hg'2 y hy
      have h2 : (g : V ≃ₗ[K] V) y - y ∈ W := hg2 y hy
      have h3 : (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) y - y) = (g' : V ≃ₗ[K] V) y - y :=
        hg1 _ h1
      have hsub : (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) y) - y =
          (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) y - y) + ((g : V ≃ₗ[K] V) y - y) := by
        rw [map_sub]
        abel
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hsub]
      exact W.add_mem (by rw [h3]; exact h1) h2
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hfix : ∀ w ∈ W, ((g : V ≃ₗ[K] V)⁻¹) w = w := by
      intro w hw
      have hgw : (g : V ≃ₗ[K] V) w = w := hg1 w hw
      calc ((g : V ≃ₗ[K] V)⁻¹) w = ((g : V ≃ₗ[K] V)⁻¹) ((g : V ≃ₗ[K] V) w) := by rw [hgw]
        _ = w := LinearEquiv.inv_apply_apply' _ _
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [Subgroup.coe_inv]
      exact hfix w hw
    · intro y hy
      have hgy : (g : V ≃ₗ[K] V) y - y ∈ W := hg2 y hy
      have hsub : ((g : V ≃ₗ[K] V)⁻¹) y - y =
          -((g : V ≃ₗ[K] V)⁻¹) ((g : V ≃ₗ[K] V) y - y) := by
        rw [map_sub, LinearEquiv.inv_apply_apply']
        abel
      rw [Subgroup.coe_inv, hsub]
      exact W.neg_mem (by rw [hfix _ hgy]; exact hgy)

theorem mem_stabE {Q : QuadraticForm K V} {W : Submodule K V} {g : elementaryGroup Q} :
    g ∈ stabE Q W ↔ W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = W :=
  Iff.rfl

private theorem map_mem_of_stabE {Q : QuadraticForm K V} {W : Submodule K V}
    {g : elementaryGroup Q} (hg : g ∈ stabE Q W) {w : V} (hw : w ∈ W) :
    (g : V ≃ₗ[K] V) w ∈ W := by
  rw [← mem_stabE.mp hg]
  exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩

private theorem inv_map_mem_of_stabE {Q : QuadraticForm K V} {W : Submodule K V}
    {g : elementaryGroup Q} (hg : g ∈ stabE Q W) {w : V} (hw : w ∈ W) :
    ((g : V ≃ₗ[K] V)⁻¹) w ∈ W := by
  have h := map_mem_of_stabE (g := g⁻¹) (Subgroup.inv_mem _ hg) hw
  rwa [Subgroup.coe_inv] at h

private theorem perp_map_mem {Q : QuadraticForm K V} {W : Submodule K V}
    {g : elementaryGroup Q} (hg : g ∈ stabE Q W) {y : V} (hy : y ∈ perp Q W) :
    (g : V ≃ₗ[K] V) y ∈ perp Q W := by
  rw [perp_mem_iff] at hy ⊢
  intro w hw
  have hiso : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2
  calc polar Q w ((g : V ≃ₗ[K] V) y)
      = polar Q ((g : V ≃ₗ[K] V) (((g : V ≃ₗ[K] V))⁻¹ w)) ((g : V ≃ₗ[K] V) y) := by
        rw [LinearEquiv.apply_inv_apply']
    _ = polar Q (((g : V ≃ₗ[K] V))⁻¹ w) y := polar_map_of_mem hiso _ _
    _ = 0 := hy _ (inv_map_mem_of_stabE hg hw)

private theorem sub_mem_perp_of_fixes {Q : QuadraticForm K V} {W : Submodule K V}
    {g : elementaryGroup Q} (hg : ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) (v : V) :
    (g : V ≃ₗ[K] V) v - v ∈ perp Q W := by
  rw [perp_mem_iff]
  intro w hw
  have hiso : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2
  have hstep : polar Q w ((g : V ≃ₗ[K] V) v) = polar Q w v := by
    calc polar Q w ((g : V ≃ₗ[K] V) v)
        = polar Q ((g : V ≃ₗ[K] V) w) ((g : V ≃ₗ[K] V) v) := by rw [hg w hw]
      _ = polar Q w v := polar_map_of_mem hiso w v
  rw [polar_sub_right, hstep, sub_self]

theorem orthRadical_le_stabE (Q : QuadraticForm K V) (W : Submodule K V) :
    orthRadical Q W ≤ stabE Q W := by
  intro g hg
  rw [mem_stabE]
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    change (g : V ≃ₗ[K] V) w ∈ W
    rwa [hg.1 w hw]
  · intro w hw
    rw [Submodule.mem_map]
    exact ⟨w, hw, hg.1 w hw⟩

theorem orthRadical_normal (Q : QuadraticForm K V) (W : Submodule K V) :
    ((orthRadical Q W).subgroupOf (stabE Q W)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (orthRadical_le_stabE Q W)]
  intro h k hh hk
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
    have hkw : ((k : V ≃ₗ[K] V)⁻¹) w ∈ W := inv_map_mem_of_stabE hk hw
    rw [hh.1 _ hkw]
    exact LinearEquiv.apply_inv_apply' (k : V ≃ₗ[K] V) w
  · intro y hy
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
    have hky : ((k : V ≃ₗ[K] V)⁻¹) y ∈ perp Q W :=
      perp_map_mem (g := k⁻¹) (Subgroup.inv_mem _ hk) hy
    have hh2 : (h : V ≃ₗ[K] V) (((k : V ≃ₗ[K] V)⁻¹) y) - ((k : V ≃ₗ[K] V)⁻¹) y ∈ W :=
      hh.2 _ hky
    have hsub : (k : V ≃ₗ[K] V) ((h : V ≃ₗ[K] V) (((k : V ≃ₗ[K] V)⁻¹) y)) - y =
        (k : V ≃ₗ[K] V) ((h : V ≃ₗ[K] V) (((k : V ≃ₗ[K] V)⁻¹) y) -
          ((k : V ≃ₗ[K] V)⁻¹) y) := by
      rw [map_sub, LinearEquiv.apply_inv_apply']
    rw [hsub]
    exact map_mem_of_stabE hk hh2

private theorem end_pow_apply_eq_iterate (S : Module.End K V) (n : ℕ) (v : V) :
    (S ^ n) v = S^[n] v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]

private theorem smul_pow_apply (c : K) (T : Module.End K V) (n : ℕ) (v : V) :
    ((c • T) ^ n) v = c ^ n • (T ^ n) v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul, smul_smul,
      pow_succ, pow_succ, Module.End.mul_apply]

private theorem cast_prime_end (p : ℕ) [CharP K p] : (p : Module.End K V) = 0 := by
  ext v
  rw [Module.End.natCast_apply, LinearMap.zero_apply, ← Nat.cast_smul_eq_nsmul K p v,
    CharP.cast_eq_zero K p, zero_smul]

private theorem end_pow_prime_sq_eq_one_of_cube_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    {S : Module.End K V} (h : (S - 1) ^ 3 = 0) : S ^ (p ^ 2) = 1 := by
  have hcube : (S - 1) ^ (p ^ 2) = 0 := by
    have hp2 : 3 ≤ p ^ 2 := by
      have := (Fact.out : Nat.Prime p).two_le
      nlinarith
    rw [← Nat.sub_add_cancel hp2, pow_add, h, mul_zero]
  have hS : S = 1 + (S - 1) := by abel
  rw [hS]
  obtain ⟨r, hr⟩ := (Commute.one_left (S - 1)).exists_add_pow_prime_pow_eq (p := p) Fact.out 2
  have hp0 : (p : Module.End K V) = 0 := cast_prime_end p
  simpa [hcube, hp0] using hr

private theorem linearEquiv_pow_eq_one_of_end {T : V ≃ₗ[K] V} {n : ℕ}
    (h : ((T : Module.End K V)) ^ n = 1) : T ^ n = 1 := by
  apply LinearEquiv.ext
  intro v
  have h1 : ((T : Module.End K V) ^ n) v = v := by
    rw [h]
    rfl
  have h2 : ((T : Module.End K V) ^ n) v = ((T : Module.End K V))^[n] v :=
    end_pow_apply_eq_iterate _ _ _
  rw [LinearEquiv.pow_apply]
  change (T : Module.End K V)^[n] v = v
  rw [← h2]
  exact h1

private theorem end_cube_zero_of_structure {Q : QuadraticForm K V} {W : Submodule K V}
    {T : V ≃ₗ[K] V}
    (hW : ∀ w ∈ W, T w = w)
    (hperp : ∀ y ∈ perp Q W, T y - y ∈ W)
    (hperp' : ∀ v, T v - v ∈ perp Q W) :
    ((T : Module.End K V) - 1) ^ 3 = 0 := by
  let N : Module.End K V := (T : Module.End K V) - 1
  have hN : ∀ v, N v = T v - v := by
    intro v
    rw [LinearMap.sub_apply, Module.End.one_apply]
    rfl
  have hNperp : ∀ v, N v ∈ perp Q W := by
    intro v
    rw [hN]
    exact hperp' v
  have hNW : ∀ y ∈ perp Q W, N y ∈ W := by
    intro y hy
    rw [hN]
    exact hperp y hy
  have hNW0 : ∀ w ∈ W, N w = 0 := by
    intro w hw
    rw [hN, hW w hw, sub_self]
  change N ^ 3 = 0
  apply LinearMap.ext
  intro v
  have h3 : (N ^ 3) v = N (N (N v)) := by
    simp only [pow_succ, pow_one, pow_zero, Module.End.mul_apply, Module.End.one_apply]
  rw [h3]
  exact hNW0 _ (hNW _ (hNperp v))

theorem isPGroup_orthRadical (p : ℕ) [Fact p.Prime] [CharP K p] (Q : QuadraticForm K V)
    (W : Submodule K V) : IsPGroup p (orthRadical Q W) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨2, ?_⟩
  have hW' : ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w := (g.2).1
  have hperp' : ∀ v, (g : V ≃ₗ[K] V) v - v ∈ perp Q W :=
    sub_mem_perp_of_fixes (g := g.1) (g.2).1
  have hcube := end_cube_zero_of_structure (Q := Q) (W := W) (T := (g : V ≃ₗ[K] V))
    hW' (g.2).2 hperp'
  have hend : ((g : V ≃ₗ[K] V) : Module.End K V) ^ (p ^ 2) = 1 :=
    end_pow_prime_sq_eq_one_of_cube_zero p hcube
  have hT : (g : V ≃ₗ[K] V) ^ (p ^ 2) = 1 := linearEquiv_pow_eq_one_of_end hend
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_pow, hT]
  rfl

private theorem end_cube_zero_of_structure_end {Q : QuadraticForm K V} {W : Submodule K V}
    {T : Module.End K V}
    (hW : ∀ w ∈ W, T w = w)
    (hperp : ∀ y ∈ perp Q W, T y - y ∈ W)
    (hperp' : ∀ v, T v - v ∈ perp Q W) :
    (T - 1) ^ 3 = 0 := by
  let N : Module.End K V := T - 1
  have hN : ∀ v, N v = T v - v := by
    intro v
    rw [LinearMap.sub_apply, Module.End.one_apply]
  have hNperp : ∀ v, N v ∈ perp Q W := by
    intro v
    rw [hN]
    exact hperp' v
  have hNW : ∀ y ∈ perp Q W, N y ∈ W := by
    intro y hy
    rw [hN]
    exact hperp y hy
  have hNW0 : ∀ w ∈ W, N w = 0 := by
    intro w hw
    rw [hN, hW w hw, sub_self]
  change N ^ 3 = 0
  apply LinearMap.ext
  intro v
  have h3 : (N ^ 3) v = N (N (N v)) := by
    simp only [pow_succ, pow_one, pow_zero, Module.End.mul_apply, Module.End.one_apply]
  rw [h3]
  exact hNW0 _ (hNW _ (hNperp v))

private theorem smul_pow_eq (c : K) (T : Module.End K V) (n : ℕ) :
    (c • T) ^ n = c ^ n • T ^ n := by
  apply LinearMap.ext
  intro v
  rw [smul_pow_apply, LinearMap.smul_apply]

private theorem exists_smul_eq_of_not_linearIndependent {Q : QuadraticForm K V}
    {s : elementaryGroup Q} {w : V}
    (hwne : w ≠ 0) (hnot : ¬ LinearIndependent K ![w, (s : V ≃ₗ[K] V) w]) :
    ∃ c : K, (s : V ≃ₗ[K] V) w = c • w := by
  by_contra hcon
  apply hnot
  rw [LinearIndependent.pair_iff' hwne]
  intro a ha
  exact hcon ⟨a, ha.symm⟩

private theorem three_le_finrank_perp [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hV : 5 ≤ Module.finrank K V) :
    3 ≤ Module.finrank K (perp Q W) := by
  have hf : Module.finrank K (perp Q W) = Module.finrank K V - Module.finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hQ W
  have hle : W ≤ perp Q W := by
    intro x hx
    rw [perp_mem_iff]
    intro y hy
    rw [QuadraticMap.polar, hW (y + x) (W.add_mem hy hx), hW y hy, hW x hx, sub_zero,
      sub_zero]
  have hmono : Module.finrank K W ≤ Module.finrank K (perp Q W) := Submodule.finrank_mono hle
  have hleV : Module.finrank K W ≤ Module.finrank K V := Submodule.finrank_le W
  omega

private noncomputable def eichlerRad (Q : QuadraticForm K V) (W : Submodule K V) (w y : V) :
    elementaryGroup Q :=
  ⟨eichler Q w y, eichler_mem_elementaryGroup Q w y⟩

private theorem eichlerRad_mem_orthRadical {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) {w y : V} (hw : w ∈ W) (hy : y ∈ perp Q W) :
    eichlerRad Q W w y ∈ orthRadical Q W := by
  have hQw : Q w = 0 := hW w hw
  have hpol : polar Q w y = 0 := (perp_mem_iff.mp hy) w hw
  refine ⟨?_, ?_⟩
  · intro w' hw'
    change eichler Q w y w' = w'
    rw [eichler_apply hQw hpol]
    have hp1 : polar Q w' w = 0 := by
      rw [QuadraticMap.polar, hW (w' + w) (W.add_mem hw' hw), hW w' hw', hW w hw, sub_zero,
        sub_zero]
    have hp2 : polar Q w' y = 0 := (perp_mem_iff.mp hy) w' hw'
    rw [hp1, hp2]
    simp
  · intro y' hy'
    change eichler Q w y y' - y' ∈ W
    rw [eichler_apply hQw hpol]
    have hp1 : polar Q y' w = 0 := by
      rw [polar_comm]
      exact (perp_mem_iff.mp hy') w hw
    rw [hp1, zero_smul, add_zero, mul_zero, add_zero]
    have hEq : y' - (polar Q y' y) • w - y' = (-(polar Q y' y)) • w := by
      rw [neg_smul]
      abel
    rw [hEq]
    exact W.smul_mem _ hw

private theorem eichler_conj_eq {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀ne : w₀ ≠ 0)
    {s : elementaryGroup Q} (hs : s ∈ stabE Q W)
    (hc : ∀ u ∈ orthRadical Q W,
      s * u * s⁻¹ * u⁻¹ ∈ (scalars K V).subgroupOf (elementaryGroup Q))
    {w y : V} (hw : w ∈ W) (hy : y ∈ perp Q W) :
    eichler Q ((s : V ≃ₗ[K] V) w) ((s : V ≃ₗ[K] V) y) = eichler Q w y := by
  let u : elementaryGroup Q := eichlerRad Q W w y
  have hu : u ∈ orthRadical Q W := eichlerRad_mem_orthRadical hW hw hy
  have hz : s * u * s⁻¹ * u⁻¹ ∈ (scalars K V).subgroupOf (elementaryGroup Q) := hc u hu
  obtain ⟨c, hc'⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hz)
  have hu_inv_w₀ : ((u : V ≃ₗ[K] V)⁻¹) w₀ = w₀ := by
    calc ((u : V ≃ₗ[K] V)⁻¹) w₀ = ((u : V ≃ₗ[K] V)⁻¹) ((u : V ≃ₗ[K] V) w₀) := by
          rw [hu.1 w₀ hw₀]
      _ = w₀ := LinearEquiv.inv_apply_apply' _ _
  have hfix0 : ((s * u * s⁻¹ * u⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) w₀ = w₀ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hu_inv_w₀]
    have hsw : ((s : V ≃ₗ[K] V)⁻¹) w₀ ∈ W := inv_map_mem_of_stabE hs hw₀
    rw [hu.1 _ hsw]
    exact LinearEquiv.apply_inv_apply' (s : V ≃ₗ[K] V) w₀
  have hc_eq : c = 1 := by
    have h1 : c • w₀ = w₀ := by rw [← hc' w₀, hfix0]
    have h2 : c • w₀ = 1 • w₀ := by rw [one_smul]; exact h1
    exact smul_left_injective K hw₀ne (by simpa using h2)
  have hz1 : (s * u * s⁻¹ * u⁻¹ : elementaryGroup Q) = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc' v, hc_eq]
    simp
  have hcomm : s * u = u * s := by
    have h1 : s * u * s⁻¹ = u := by
      have h := congrArg (fun x => x * u) hz1
      simpa [mul_assoc] using h
    have h := congrArg (fun x => x * s) h1
    simpa [mul_assoc] using h
  have hsu : (s : V ≃ₗ[K] V) * eichler Q w y = eichler Q w y * (s : V ≃ₗ[K] V) := by
    have h := congrArg (fun x : elementaryGroup Q => (x : V ≃ₗ[K] V)) hcomm
    simpa [u, eichlerRad, Subgroup.coe_mul] using h
  calc eichler Q ((s : V ≃ₗ[K] V) w) ((s : V ≃ₗ[K] V) y)
      = (s : V ≃ₗ[K] V) * eichler Q w y * (s : V ≃ₗ[K] V)⁻¹ := by
        rw [eichler_conj (elementaryGroup_le_orthogonalGroup Q s.2)]
    _ = eichler Q w y := by rw [hsu, mul_assoc, mul_inv_cancel, mul_one]

private theorem exists_polar_zero_and_one {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {w w' : V} (hwne : w ≠ 0)
    (hli : LinearIndependent K ![w, w']) :
    ∃ x, polar Q x w = 0 ∧ polar Q x w' = 1 := by
  obtain ⟨x₂, hx₂⟩ := exists_polar_ne_zero hQ hwne
  have hx₂w : polar Q x₂ w ≠ 0 := by rwa [polar_comm] at hx₂
  let x₂' : V := (polar Q x₂ w)⁻¹ • x₂
  have hx₂' : polar Q x₂' w = 1 := by
    rw [polar_smul_left_eq, inv_mul_cancel₀ hx₂w]
  have hex : ∃ x, polar Q x w = 0 ∧ polar Q x w' ≠ 0 := by
    by_contra! hcon
    have hzero : w' - (polar Q x₂' w') • w = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro x
      have h1 : polar Q (x - polar Q x w • x₂') w = 0 := by
        rw [polar_sub_left, polar_smul_left_eq, hx₂', mul_one, sub_self]
      have h2 : polar Q (x - polar Q x w • x₂') w' = 0 := hcon _ h1
      rw [polar_sub_left, polar_smul_left_eq] at h2
      rw [polar_comm, polar_sub_right, polar_smul_right_eq,
        mul_comm (polar Q x₂' w') (polar Q x w)]
      exact h2
    exact (LinearIndependent.pair_iff' hwne).mp hli (polar Q x₂' w') (sub_eq_zero.mp hzero).symm
  obtain ⟨x, hxw, hxw'⟩ := hex
  refine ⟨(polar Q x w')⁻¹ • x, ?_, ?_⟩
  · rw [polar_smul_left_eq, hxw, mul_zero]
  · rw [polar_smul_left_eq, inv_mul_cancel₀ hxw']

private theorem exists_polar_left_eq_one {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {w : V} (hwne : w ≠ 0) :
    ∃ x, polar Q x w = 1 := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hwne
  refine ⟨(polar Q w y)⁻¹ • y, ?_⟩
  rw [polar_smul_left_eq]
  rw [polar_comm Q y w]
  exact inv_mul_cancel₀ hy

private theorem smul_orbit_subset_span {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hQ : (polarBilin Q).Nondegenerate)
    {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀ne : w₀ ≠ 0)
    {s : elementaryGroup Q} (hs : s ∈ stabE Q W)
    (hc : ∀ u ∈ orthRadical Q W,
      s * u * s⁻¹ * u⁻¹ ∈ (scalars K V).subgroupOf (elementaryGroup Q))
    {w : V} (hw : w ∈ W) (hli : LinearIndependent K ![w, (s : V ≃ₗ[K] V) w]) :
    ∀ y ∈ perp Q W, (s : V ≃ₗ[K] V) y ∈
      Submodule.span K ({w, (s : V ≃ₗ[K] V) w} : Set V) := by
  intro y hy
  have hwne : w ≠ 0 := LinearIndependent.ne_zero 0 hli
  obtain ⟨x₁, hx₁w, hx₁sw⟩ := exists_polar_zero_and_one hQ hwne hli
  have hE1 := eichler_conj_eq hW hw₀ hw₀ne hs hc hw hy
  have hQsw : Q ((s : V ≃ₗ[K] V) w) = 0 := by
    rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2), hW w hw]
  have hpol : polar Q ((s : V ≃ₗ[K] V) w) ((s : V ≃ₗ[K] V) y) = 0 := by
    rw [polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2),
      (perp_mem_iff.mp hy) w hw]
  have h1 := DFunLike.congr_fun hE1 x₁
  rw [eichler_apply hQsw hpol x₁,
    eichler_apply (hW w hw) ((perp_mem_iff.mp hy) w hw) x₁] at h1
  rw [hx₁sw, hx₁w] at h1
  have hQy : Q ((s : V ≃ₗ[K] V) y) = Q y :=
    map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2) y
  rw [hQy] at h1
  simp only [one_smul, zero_smul, add_zero, mul_one, mul_zero] at h1
  let A : K := polar Q x₁ ((s : V ≃ₗ[K] V) y) + Q y
  let B : K := polar Q x₁ y
  have h1' : x₁ + ((s : V ≃ₗ[K] V) y - A • ((s : V ≃ₗ[K] V) w)) =
      x₁ + (-(B • w)) := by
    rw [← add_sub_assoc, ← sub_eq_add_neg]
    exact h1
  have h1'' : (s : V ≃ₗ[K] V) y - A • ((s : V ≃ₗ[K] V) w) = -(B • w) :=
    add_left_cancel h1'
  have hsy : (s : V ≃ₗ[K] V) y = A • ((s : V ≃ₗ[K] V) w) - B • w := by
    rw [sub_eq_iff_eq_add] at h1''
    rw [h1'']
    abel
  refine Submodule.mem_span_pair.mpr ⟨-B, A, ?_⟩
  calc (-B) • w + A • ((s : V ≃ₗ[K] V) w)
      = -(B • w) + A • ((s : V ≃ₗ[K] V) w) := by rw [neg_smul]
    _ = A • ((s : V ≃ₗ[K] V) w) - B • w := by rw [sub_eq_add_neg, add_comm]
    _ = (s : V ≃ₗ[K] V) y := hsy.symm

private theorem exists_scalar_on_W {Q : QuadraticForm K V} {W : Submodule K V}
    {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀ne : w₀ ≠ 0) {s : elementaryGroup Q}
    (hline : ∀ w ∈ W, ∃ c : K, (s : V ≃ₗ[K] V) w = c • w) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ w ∈ W, (s : V ≃ₗ[K] V) w = μ • w := by
  obtain ⟨μ, hμ⟩ := hline w₀ hw₀
  have hμne : μ ≠ 0 := by
    intro hμ0
    have h0 : (s : V ≃ₗ[K] V) w₀ = 0 := by rw [hμ, hμ0, zero_smul]
    exact hw₀ne ((s : V ≃ₗ[K] V).injective (by rw [h0, map_zero]))
  refine ⟨μ, hμne, ?_⟩
  intro w hw
  obtain ⟨c, hc⟩ := hline w hw
  obtain ⟨c', hc'⟩ := hline (w + w₀) (W.add_mem hw hw₀)
  have h1 : c • w + μ • w₀ = c' • w + c' • w₀ := by
    rw [← hc, ← hμ, ← map_add, hc', smul_add]
  have hEq : (c - c') • w + (μ - c') • w₀ = 0 := by
    have h1' : (c - c') • w + (μ - c') • w₀ =
        (c • w + μ • w₀) - (c' • w + c' • w₀) := by
      rw [sub_smul, sub_smul]
      abel
    rw [h1', h1, sub_self]
  by_cases hli : LinearIndependent K ![w, w₀]
  · have h2 := (LinearIndependent.pair_iff.mp hli) (c - c') (μ - c') hEq
    rw [hc, sub_eq_zero.mp h2.1, ← sub_eq_zero.mp h2.2]
  · have hnot' : ¬ LinearIndependent K ![w₀, w] := by
      intro h
      apply hli
      rw [LinearIndependent.pair_iff] at h ⊢
      intro a b hab
      have hba : b • w₀ + a • w = 0 := by rw [add_comm]; exact hab
      obtain ⟨hb0, ha0⟩ := h b a hba
      exact ⟨ha0, hb0⟩
    have hw' : ∃ a : K, a • w₀ = w := by
      by_contra! hc''
      exact hnot' ((LinearIndependent.pair_iff' hw₀ne).mpr hc'')
    obtain ⟨a, ha⟩ := hw'
    calc (s : V ≃ₗ[K] V) w = (s : V ≃ₗ[K] V) (a • w₀) := by rw [ha]
      _ = a • (s : V ≃ₗ[K] V) w₀ := map_smul _ _ _
      _ = a • (μ • w₀) := by rw [hμ]
      _ = μ • (a • w₀) := by rw [smul_smul, smul_smul, mul_comm]
      _ = μ • w := by rw [ha]

theorem exists_scalar_mul_mem_orthRadical (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (Q : QuadraticForm K V) [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    (hV : 5 ≤ Module.finrank K V) {W : Submodule K V} (h0 : W ≠ ⊥) (hW : ∀ w ∈ W, Q w = 0)
    {s : elementaryGroup Q} (hs : s ∈ stabE Q W)
    (hc : ∀ u ∈ orthRadical Q W,
      s * u * s⁻¹ * u⁻¹ ∈ (scalars K V).subgroupOf (elementaryGroup Q)) :
    ∃ z ∈ (scalars K V).subgroupOf (elementaryGroup Q), ∃ q ∈ orthRadical Q W, s = z * q := by
  obtain ⟨w₀, hw₀, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hSW : W ≤ perp Q W := by
    intro x hx
    rw [perp_mem_iff]
    intro y hy
    rw [QuadraticMap.polar, hW (y + x) (W.add_mem hy hx), hW y hy, hW x hx, sub_zero,
      sub_zero]
  have hdim : 3 ≤ Module.finrank K (perp Q W) := three_le_finrank_perp hQ hW hV
  have hspanW : K ∙ w₀ ≤ W := (Submodule.span_singleton_le_iff_mem w₀ W).mpr hw₀
  have hline : ∀ w ∈ W, ∃ c : K, (s : V ≃ₗ[K] V) w = c • w := by
    intro w hw
    by_cases hw0 : w = 0
    · exact ⟨0, by rw [hw0, map_zero, zero_smul]⟩
    · by_cases hli : LinearIndependent K ![w, (s : V ≃ₗ[K] V) w]
      · exfalso
        have hsubset := smul_orbit_subset_span hW hQ hw₀ hw₀ne hs hc hw hli
        have hmap : (perp Q W).map ((s : V ≃ₗ[K] V) : V →ₗ[K] V) ≤
            Submodule.span K ({w, (s : V ≃ₗ[K] V) w} : Set V) := by
          rw [Submodule.map_le_iff_le_comap]
          intro y hy
          exact hsubset y hy
        have h1 : Module.finrank K ((perp Q W).map ((s : V ≃ₗ[K] V) : V →ₗ[K] V)) =
            Module.finrank K (perp Q W) :=
          LinearEquiv.finrank_map_eq (s : V ≃ₗ[K] V) (perp Q W)
        have h2 : Module.finrank K ((perp Q W).map ((s : V ≃ₗ[K] V) : V →ₗ[K] V)) ≤
            Module.finrank K (Submodule.span K ({w, (s : V ≃ₗ[K] V) w} : Set V)) :=
          Submodule.finrank_mono hmap
        have h3 : Module.finrank K (Submodule.span K ({w, (s : V ≃ₗ[K] V) w} : Set V)) ≤ 2 := by
          classical
          have h := finrank_span_le_card (R := K) ({w, (s : V ≃ₗ[K] V) w} : Set V)
          have h4 : ({w, (s : V ≃ₗ[K] V) w} : Set V).toFinset.card ≤ 2 := by
            rw [Set.toFinset_insert, Set.toFinset_singleton]
            exact Finset.card_le_two
          omega
        omega
      · exact exists_smul_eq_of_not_linearIndependent hw0 hli
  obtain ⟨μ, hμne, hμw⟩ := exists_scalar_on_W hw₀ hw₀ne hline
  have hspan : ∀ y ∈ perp Q W, (s : V ≃ₗ[K] V) y - μ⁻¹ • y ∈ K ∙ w₀ := by
    intro y hy
    obtain ⟨x₁, hx₁⟩ := exists_polar_left_eq_one hQ hw₀ne
    have hE1 := eichler_conj_eq hW hw₀ hw₀ne hs hc hw₀ hy
    have hQsw : Q ((s : V ≃ₗ[K] V) w₀) = 0 := by
      rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2), hW w₀ hw₀]
    have hpol : polar Q ((s : V ≃ₗ[K] V) w₀) ((s : V ≃ₗ[K] V) y) = 0 := by
      rw [polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2),
        (perp_mem_iff.mp hy) w₀ hw₀]
    have h1 := DFunLike.congr_fun hE1 x₁
    rw [eichler_apply hQsw hpol x₁,
      eichler_apply (hW w₀ hw₀) ((perp_mem_iff.mp hy) w₀ hw₀) x₁] at h1
    have hQy : Q ((s : V ≃ₗ[K] V) y) = Q y :=
      map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2) y
    rw [hμw w₀ hw₀] at h1
    rw [polar_smul_right_eq, hx₁, hQy, mul_one, one_smul] at h1
    simp only [mul_one] at h1
    let A : K := polar Q x₁ ((s : V ≃ₗ[K] V) y) + Q y * μ
    let B : K := polar Q x₁ y + Q y
    have h1' : x₁ + (μ • ((s : V ≃ₗ[K] V) y) - A • (μ • w₀)) = x₁ + (y - B • w₀) := by
      simpa only [add_sub_assoc] using h1
    have h1'' : μ • ((s : V ≃ₗ[K] V) y) - A • (μ • w₀) = y - B • w₀ := add_left_cancel h1'
    have hμsy : μ • ((s : V ≃ₗ[K] V) y) = y + (A * μ - B) • w₀ := by
      rw [sub_eq_iff_eq_add] at h1''
      rw [smul_smul] at h1''
      rw [h1'']
      rw [sub_smul]
      abel
    have h4 : μ⁻¹ • (μ • ((s : V ≃ₗ[K] V) y)) = μ⁻¹ • (y + (A * μ - B) • w₀) := by rw [hμsy]
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hμne, one_smul] at h4
    refine Submodule.mem_span_singleton.mpr ⟨μ⁻¹ * (A * μ - B), ?_⟩
    rw [h4]
    abel
  have hWpos : 1 ≤ Module.finrank K W := by
    have h1 : Module.finrank K (K ∙ w₀) = 1 := finrank_span_singleton hw₀ne
    have h2 : Module.finrank K (K ∙ w₀) ≤ Module.finrank K W := Submodule.finrank_mono hspanW
    omega
  have hμ2 : μ ^ 2 = 1 := by
    by_cases hW1 : Module.finrank K W = 1
    · have hex2 : ∃ y ∈ perp Q W, Q y ≠ 0 := by
        by_contra! hcon
        have hle : perp Q W ≤ perp Q (perp Q W) := by
          intro z hz
          rw [perp_mem_iff]
          intro y hy
          rw [QuadraticMap.polar, hcon (y + z) ((perp Q W).add_mem hy hz), hcon y hy,
            hcon z hz, sub_zero, sub_zero]
        have hf1 : Module.finrank K (perp Q W) =
            Module.finrank K V - Module.finrank K W :=
          LinearMap.BilinForm.finrank_orthogonal hQ W
        have hf2 : Module.finrank K (perp Q (perp Q W)) =
            Module.finrank K V - Module.finrank K (perp Q W) :=
          LinearMap.BilinForm.finrank_orthogonal hQ (perp Q W)
        have hmono : Module.finrank K (perp Q W) ≤
            Module.finrank K (perp Q (perp Q W)) := Submodule.finrank_mono hle
        omega
      obtain ⟨y, hyperp, hyQ⟩ := hex2
      have hmem : (s : V ≃ₗ[K] V) y - μ⁻¹ • y ∈ K ∙ w₀ := hspan y hyperp
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hsy : (s : V ≃ₗ[K] V) y = μ⁻¹ • y + c • w₀ := by
        rw [hc]
        abel
      have hpy : polar Q y w₀ = 0 := by
        rw [polar_comm]
        exact (perp_mem_iff.mp hyperp) w₀ hw₀
      have hQcomp : Q (μ⁻¹ • y + c • w₀) = (μ⁻¹) ^ 2 * Q y := by
        rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hW w₀ hw₀,
          polar_smul_left_eq, polar_smul_right_eq, hpy]
        ring
      have hQy' : Q ((s : V ≃ₗ[K] V) y) = Q y :=
        map_of_mem (elementaryGroup_le_orthogonalGroup Q s.2) y
      have hmain : Q y = (μ⁻¹) ^ 2 * Q y := by
        calc Q y = Q ((s : V ≃ₗ[K] V) y) := hQy'.symm
          _ = Q (μ⁻¹ • y + c • w₀) := by rw [hsy]
          _ = (μ⁻¹) ^ 2 * Q y := hQcomp
      have hzero : (1 - (μ⁻¹) ^ 2) * Q y = 0 := by
        rw [sub_mul, one_mul]
        nth_rewrite 1 [hmain]
        exact sub_self _
      have hμinv2 : (μ⁻¹) ^ 2 = 1 := by
        have h := (mul_eq_zero.mp hzero).resolve_right hyQ
        exact (sub_eq_zero.mp h).symm
      have : (μ ^ 2)⁻¹ = 1 := by rw [← inv_pow, hμinv2]
      exact inv_injective (by rw [this, inv_one])
    · have hW2 : 2 ≤ Module.finrank K W := by omega
      have hex : ∃ y ∈ W, y ∉ K ∙ w₀ := by
        by_contra! hcon
        have hle : W ≤ K ∙ w₀ := fun y hy => hcon y hy
        have h1 : Module.finrank K W ≤ Module.finrank K (K ∙ w₀) :=
          Submodule.finrank_mono hle
        rw [finrank_span_singleton hw₀ne] at h1
        omega
      obtain ⟨y, hyW, hyK⟩ := hex
      have hyperp : y ∈ perp Q W := hSW hyW
      have hmem : (s : V ≃ₗ[K] V) y - μ⁻¹ • y ∈ K ∙ w₀ := hspan y hyperp
      rw [hμw y hyW] at hmem
      have hmem' : (μ - μ⁻¹) • y ∈ K ∙ w₀ := by
        rwa [← sub_smul] at hmem
      have hμeq : μ = μ⁻¹ := by
        by_contra hne
        have hscal : μ - μ⁻¹ ≠ 0 := sub_ne_zero.mpr hne
        have hy : y ∈ K ∙ w₀ := by
          have h := (K ∙ w₀).smul_mem (μ - μ⁻¹)⁻¹ hmem'
          rwa [smul_smul, inv_mul_cancel₀ hscal, one_smul] at h
        exact hyK hy
      have hμ2' : μ * μ = 1 := by
        have h := congrArg (fun x => μ * x) hμeq
        rw [mul_inv_cancel₀ hμne] at h
        exact h
      rw [pow_two]
      exact hμ2'
  have hμinv2 : (μ⁻¹) ^ 2 = 1 := by rw [inv_pow, hμ2, inv_one]
  have hμeq : μ = μ⁻¹ := by
    have h : μ⁻¹ = μ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hμ2)
    exact h.symm
  have hmemK_of : ∀ y ∈ perp Q W, (s : V ≃ₗ[K] V) y - μ • y ∈ W := by
    intro y hy
    apply hspanW
    have h := hspan y hy
    rwa [show μ⁻¹ • y = μ • y by rw [hμeq.symm]] at h
  let S' : Module.End K V := (μ⁻¹ : K) • ((s : V ≃ₗ[K] V) : Module.End K V)
  have hS'app : ∀ v, S' v = μ⁻¹ • (s : V ≃ₗ[K] V) v := by
    intro v
    rw [LinearMap.smul_apply]
    rfl
  have hcube : (S' - 1) ^ 3 = 0 := by
    apply end_cube_zero_of_structure_end (Q := Q) (W := W) (T := S')
    · intro w hw
      rw [hS'app, hμw w hw, smul_smul, inv_mul_cancel₀ hμne, one_smul]
    · intro y hy
      have hmemK : (s : V ≃ₗ[K] V) y - μ • y ∈ W := hmemK_of y hy
      have hEq : μ⁻¹ • (s : V ≃ₗ[K] V) y - y = μ⁻¹ • ((s : V ≃ₗ[K] V) y - μ • y) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hμne, one_smul]
      rw [hS'app, hEq]
      exact W.smul_mem _ hmemK
    · intro v
      rw [perp_mem_iff]
      intro w hw
      have hiso := elementaryGroup_le_orthogonalGroup Q s.2
      have hspol : polar Q w ((s : V ≃ₗ[K] V) v) = μ⁻¹ * polar Q w v := by
        have h := polar_map_of_mem hiso w v
        rw [hμw w hw, polar_smul_left_eq] at h
        rw [← h, ← mul_assoc, inv_mul_cancel₀ hμne, one_mul]
      rw [hS'app, polar_sub_right, polar_smul_right_eq, hspol, ← mul_assoc, ← pow_two,
        hμinv2, one_mul, sub_self]
  have hend : (S') ^ (p ^ 2) = 1 := end_pow_prime_sq_eq_one_of_cube_zero p hcube
  have hz_apply : ∀ v, ((s ^ (p ^ 2) : elementaryGroup Q) : V ≃ₗ[K] V) v = μ • v := by
    intro v
    have hS'pow : (S') ^ (p ^ 2) =
        ((μ⁻¹) ^ (p ^ 2)) • (((s : V ≃ₗ[K] V) : Module.End K V) ^ (p ^ 2)) := by
      rw [show S' = (μ⁻¹ : K) • ((s : V ≃ₗ[K] V) : Module.End K V) from rfl, smul_pow_eq]
    have h3 : ((μ⁻¹) ^ (p ^ 2)) •
        ((((s : V ≃ₗ[K] V) : Module.End K V) ^ (p ^ 2)) v) = v := by
      have h := congrArg (fun f : Module.End K V => f v) hend
      rw [hS'pow, LinearMap.smul_apply, Module.End.one_apply] at h
      exact h
    have h4 : (((s : V ≃ₗ[K] V) : Module.End K V) ^ (p ^ 2)) v = μ ^ (p ^ 2) • v := by
      have h5 : μ ^ (p ^ 2) * (μ⁻¹) ^ (p ^ 2) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hμne, one_pow]
      have h := congrArg (fun w => μ ^ (p ^ 2) • w) h3
      rw [smul_smul, h5, one_smul] at h
      exact h
    have hμpow : μ ^ (p ^ 2) = μ := by
      have hodd : Odd (p ^ 2) :=
        Odd.pow (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime p) hp)
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, hμ2, one_pow, one_mul]
    have hiter : (s : V ≃ₗ[K] V)^[p ^ 2] v =
        (((s : V ≃ₗ[K] V) : Module.End K V) ^ (p ^ 2)) v := by
      rw [end_pow_apply_eq_iterate]
      rfl
    rw [Subgroup.coe_pow, LinearEquiv.pow_apply, hiter, h4, hμpow]
  have hz_apply' : ∀ v, ((s : V ≃ₗ[K] V) ^ (p ^ 2)) v = μ • v := by
    intro v
    rw [← Subgroup.coe_pow]
    exact hz_apply v
  have hz_inv : ∀ v, (((s ^ (p ^ 2) : elementaryGroup Q) : V ≃ₗ[K] V)⁻¹) v = μ⁻¹ • v := by
    intro v
    have hcoe : (((s ^ (p ^ 2) : elementaryGroup Q) : V ≃ₗ[K] V)) =
        (s : V ≃ₗ[K] V) ^ (p ^ 2) := Subgroup.coe_pow (elementaryGroup Q) s (p ^ 2)
    rw [hcoe]
    apply ((s : V ≃ₗ[K] V) ^ (p ^ 2)).injective
    rw [LinearEquiv.apply_inv_apply', map_smul, hz_apply', smul_smul, inv_mul_cancel₀ hμne,
      one_smul]
  refine ⟨s ^ (p ^ 2), Subgroup.mem_subgroupOf.mpr (mem_scalars.mpr ⟨μ, hz_apply⟩),
    (s ^ (p ^ 2))⁻¹ * s, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro w hw
      rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, hz_inv, hμw w hw,
        smul_smul, inv_mul_cancel₀ hμne, one_smul]
    · intro y hy
      have hmemK : (s : V ≃ₗ[K] V) y - μ • y ∈ W := hmemK_of y hy
      have hEq : μ⁻¹ • (s : V ≃ₗ[K] V) y - y = μ⁻¹ • ((s : V ≃ₗ[K] V) y - μ • y) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hμne, one_smul]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, hz_inv, hEq]
      exact W.smul_mem _ hmemK
  · group

end GGOrthRad

end CFSG.StandardType
