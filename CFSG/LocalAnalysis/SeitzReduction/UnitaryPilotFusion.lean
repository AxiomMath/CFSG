module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreFusion

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem tvTransSU_mem_unitaryBlock {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ I)
    (hj : j ∈ I) : tvTransSU h hij ∈ unitaryBlock h I := by
  rw [mem_unitaryBlock]
  intro r s hrs
  have hv : ∀ k, k ∉ I → tvVec (K := K) i j k = 0 := fun k hk => by
    have hki : k ≠ i := by rintro rfl; exact hk hi
    have hkj : k ≠ j := by rintro rfl; exact hk hj
    simp [tvVec_apply, hki, hkj]
  rw [coe_tvTransSU, Matrix.add_apply, tvNil, vecMulVec_apply]
  rcases hrs with hr | hs
  · rw [hv r hr, zero_mul, add_zero]
  · rw [hv s hs, mul_zero, add_zero]

theorem stdTransvection_mem_blockSU {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ I)
    (hj : j ∈ I) : stdTransvection h hij ∈ blockSU h I :=
  unitaryProj_mem_blockSU h (tvTransSU_mem_unitaryBlock h hij hi hj)

theorem stdTransvection_ne_one {i j : Fin n} (hij : i ≠ j) : stdTransvection h hij ≠ 1 := by
  intro h1
  have hker : tvTransSU h hij ∈ unitaryScalars h n := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker]
    exact h1
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hker
  have h2 : (((tvTransSU h hij : unitarySU 2 f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := by
    rw [hc]
  rw [coe_tvTransSU, Matrix.add_apply, Matrix.one_apply_ne hij, tvNil, vecMulVec_apply,
    tvVec_left hij, tvVec_right hij, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_ne _ hij, zero_add, one_mul] at h2
  exact one_ne_zero h2

section Recentre

variable {G : Type} [Group G] {L : Subgroup G}

omit [Field K] in
theorem coe_conjugateMulEquiv_symm (x : G) (w : CFSG.conjugate L x) :
    (((conjugateMulEquiv L x).symm w : L) : G) = x * w * x⁻¹ := by
  have h1 := coe_conjugateMulEquiv L x ((conjugateMulEquiv L x).symm w)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1]
  group

omit [Field K] in
theorem recentre_twoSided {t : G} (htC : t ∈ centralizer (L : Set G)) {x z c : G} (hc : c ∈ L)
    (hz : z ∈ L ⊓ CFSG.conjugate L x) (hxz : x⁻¹ * t * x = t * z)
    (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹) :
    c * z * c⁻¹ ∈ L ⊓ CFSG.conjugate L (x * c⁻¹) ∧
      (x * c⁻¹)⁻¹ * t * (x * c⁻¹) = t * (c * z * c⁻¹) ∧
      x * c⁻¹ * (c * z * c⁻¹) * (x * c⁻¹)⁻¹ = x * z * x⁻¹ ∧
      ∀ l ∈ CFSG.conjugate L (x * c⁻¹),
        t * l * t⁻¹ = (c * z * c⁻¹) * l * (c * z * c⁻¹)⁻¹ := by
  have htc : c * t = t * c := mem_centralizer_iff.1 htC c hc
  have hmem : ∀ w ∈ CFSG.conjugate L x, c * w * c⁻¹ ∈ CFSG.conjugate L (x * c⁻¹) := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l, hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, _root_.mul_inv_rev]
    group
  have hmem' : ∀ w ∈ CFSG.conjugate L (x * c⁻¹), c⁻¹ * w * c ∈ CFSG.conjugate L x := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l, hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, _root_.mul_inv_rev]
    group
  refine ⟨⟨L.mul_mem (L.mul_mem hc hz.1) (L.inv_mem hc), hmem z hz.2⟩, ?_, by group, ?_⟩
  · calc (x * c⁻¹)⁻¹ * t * (x * c⁻¹) = c * (x⁻¹ * t * x) * c⁻¹ := by group
      _ = (c * t) * z * c⁻¹ := by rw [hxz]; group
      _ = t * (c * z * c⁻¹) := by rw [htc]; group
  · intro l hl
    have h1 := hact (c⁻¹ * l * c) (hmem' l hl)
    have ht' : t = c * t * c⁻¹ := by rw [htc]; group
    calc t * l * t⁻¹ = (c * t * c⁻¹) * l * (c * t * c⁻¹)⁻¹ := by rw [← ht']
      _ = c * (t * (c⁻¹ * l * c) * t⁻¹) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * l * c) * z⁻¹) * c⁻¹ := by rw [h1]
      _ = (c * z * c⁻¹) * l * (c * z * c⁻¹)⁻¹ := by group

end Recentre

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_stdTransvection (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {i j : Fin n}
    (hij : i ≠ j) :
    ∃ g : G, ∃ y ∈ L ⊓ CFSG.conjugate L g, g⁻¹ * t * g = t * y ∧
      (∃ hy : y ∈ L, e ⟨y, hy⟩ = stdTransvection h hij) ∧
      (∃ hy : y ∈ CFSG.conjugate L g,
        IsUnitaryTransvection h (((conjugateMulEquiv L g).symm.trans e) ⟨y, hy⟩)) ∧
      ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = y * l * y⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  obtain ⟨x, z, hz, hxz, ⟨hzL, hzT⟩, ⟨hzL', hzT'⟩, hact⟩ :=
    exists_conj_eq_mul_transvection_twoSided_of_six_le h hset e hn ht hKt
  obtain ⟨c₀, hc₀⟩ := exists_conj_eq_stdTransvection h (by omega) hzT hij
  have hcL : ((e.symm c₀ : L) : G) ∈ L := (e.symm c₀).2
  obtain ⟨hyLL, hg, hgy, hact'⟩ := recentre_twoSided htC hcL hz hxz hact
  refine ⟨x * ((e.symm c₀ : L) : G)⁻¹, _, hyLL, hg, ⟨hyLL.1, ?_⟩, ⟨hyLL.2, ?_⟩, hact'⟩
  ·
    have h1 : (⟨((e.symm c₀ : L) : G) * z * ((e.symm c₀ : L) : G)⁻¹, hyLL.1⟩ : L) =
        e.symm c₀ * ⟨z, hzL⟩ * (e.symm c₀)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₀]
  ·
    have h1 : ((conjugateMulEquiv L (x * ((e.symm c₀ : L) : G)⁻¹)).symm
        ⟨((e.symm c₀ : L) : G) * z * ((e.symm c₀ : L) : G)⁻¹, hyLL.2⟩ : L) =
        (conjugateMulEquiv L x).symm ⟨z, hzL'⟩ := by
      apply Subtype.ext
      rw [coe_conjugateMulEquiv_symm, coe_conjugateMulEquiv_symm]
      exact hgy
    rw [MulEquiv.trans_apply, h1]
    exact hzT'

end Setting

end CFSG.SeitzReduction.UnitaryPilot
