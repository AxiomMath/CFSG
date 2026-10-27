module

public import CFSG.Quasithin.Recognition.L34CIT.Config

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

namespace Config

variable {A : Type} [Group A]

theorem isConj_of_mem_Z (C : Config A) [Finite A] {z e : A} (hz : z ∈ C.Z) (hz1 : z ≠ 1)
    (he : e * e = 1) (he1 : e ≠ 1) : IsConj z e := by
  have he2 : e ^ 2 = 1 := by rwa [pow_two]
  have hP : IsPGroup 2 (Subgroup.zpowers e) :=
    (CFSG.Open.isElemAbelian_zpowers (p := 2) he2).isPGroup
  obtain ⟨P, hleP⟩ := hP.exists_le_sylow
  have heP : e ∈ (P : Subgroup A) := hleP (Subgroup.mem_zpowers e)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A C.T P
  obtain ⟨t, ht, hte⟩ : ∃ t ∈ (C.T : Subgroup A), MulAut.conj g t = e := by
    have heP' : e ∈ ((g • C.T : Sylow 2 A) : Subgroup A) := by
      rw [hg]
      exact heP
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at heP'
    exact Subgroup.mem_map.mp heP'
  let e' : A := g⁻¹ * e * g
  have he'T : e' ∈ C.T := by
    have hte' : e' = t := by
      dsimp [e']
      rw [← hte]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hte']
  have he'e : IsConj e' e := by
    rw [isConj_iff]
    exact ⟨g, by dsimp [e']; group⟩
  have he'1 : e' ≠ 1 := by
    intro h
    apply he1
    have : e = g * e' * g⁻¹ := by dsimp [e']; group
    rw [this, h, mul_one, mul_inv_cancel]
  have he'2 : e' * e' = 1 := by
    have hsq : e' * e' = g⁻¹ * (e * e) * g := by dsimp [e']; group
    rw [hsq, he]
    group
  rcases C.mem_or_mem e' he'T he'2 with hL | hM
  · obtain ⟨k, -, hk⟩ := C.exists_conj_L e' hL z (C.Z_le_L hz) he'1 hz1
    exact (isConj_iff.mpr ⟨k, hk⟩).symm.trans he'e
  · obtain ⟨k, -, hk⟩ := C.exists_conj_M e' hM z (C.Z_le_M hz) he'1 hz1
    exact (isConj_iff.mpr ⟨k, hk⟩).symm.trans he'e

theorem centralizer_eq_T (C : Config A) {z : A} (hz : z ∈ C.Z) (hz1 : z ≠ 1) :
    centralizer ({z} : Set A) = (C.T : Subgroup A) := by
  have hzT : z ∈ C.T := C.Z_le_T hz
  have hz2 : z * z = 1 := C.mul_self_eq_one_of_mem_Z hz
  have hP : IsPGroup 2 (centralizer ({z} : Set A)) := C.isPGroup_centralizer z hz2 hz1
  refine C.T.is_maximal' hP ?_
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact (Subgroup.mem_centralizer_iff.mp (C.inf_le_centralizer hz) t ht).symm

theorem centralizer_eq_of_mem_center (C : Config A) {e : A} (he : e * e = 1) (he1 : e ≠ 1)
    {P : Sylow 2 A} (heP : e ∈ P) (hc : ∀ y ∈ P, e * y = y * e) :
    centralizer ({e} : Set A) = (P : Subgroup A) := by
  have hP : IsPGroup 2 (centralizer ({e} : Set A)) := C.isPGroup_centralizer e he he1
  refine P.is_maximal' hP ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact hc y hy

theorem exists_sylow_eq_centralizer (C : Config A) [Finite A] {e : A} (he : e * e = 1)
    (he1 : e ≠ 1) : ∃ P : Sylow 2 A, centralizer ({e} : Set A) = (P : Subgroup A) := by
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ C.Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : C.Z = ⊥ := by
      rw [eq_bot_iff_forall]
      intro z hz
      simpa using h z hz
    have hZ4 : Nat.card C.Z = 4 := C.card_Z
    rw [hbot, Subgroup.card_bot] at hZ4
    norm_num at hZ4
  obtain ⟨g, hg⟩ := isConj_iff.mp (C.isConj_of_mem_Z hz hz1 he he1)
  let P : Sylow 2 A := g • C.T
  have hPcoe : (P : Subgroup A) = (C.T : Subgroup A).map (MulAut.conj g).toMonoidHom := by
    rw [show P = g • C.T from rfl, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨P, C.centralizer_eq_of_mem_center he he1 ?_ ?_⟩
  · change e ∈ (P : Subgroup A)
    rw [hPcoe]
    exact Subgroup.mem_map.mpr ⟨z, C.Z_le_T hz, hg⟩
  · intro y hy
    have hy' : y ∈ (P : Subgroup A) := hy
    rw [hPcoe] at hy'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy' 
    rw [← hg]
    have hzt : z * t = t * z :=
      (Subgroup.mem_centralizer_iff.mp (C.inf_le_centralizer hz) t ht).symm
    calc
      g * z * g⁻¹ * (g * t * g⁻¹) = g * (z * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hzt]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group

end Config

end CFSG.Quasithin.L34CIT
