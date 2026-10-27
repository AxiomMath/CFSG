module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Swap
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3Swap

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {Y T L₁ L₂ : Subgroup (LGL 2 V)} {a : LGL 2 V}

theorem exists_inner (c : SwapCfg Y T L₁ L₂ a) {D : Subgroup (LGL 2 V)}
    (hD : IsElemAbelian 2 D) (hDY : D ≤ Y) (haD : a ∈ D) (h3 : 2 < Nat.card ↥D) :
    ∃ b ∈ D, b ≠ 1 ∧ cj b L₁ = L₁ := by
  have hnotsub : ¬ (D : Set (LGL 2 V)) ⊆ ({1, a} : Set (LGL 2 V)) := by
    intro hsub
    have hle : (D : Set (LGL 2 V)).ncard ≤ 2 := by
      refine le_trans (Set.ncard_le_ncard hsub) ?_
      rw [show ({1, a} : Set (LGL 2 V)) = insert 1 ({a} : Set (LGL 2 V)) from rfl]
      calc (insert 1 ({a} : Set (LGL 2 V))).ncard ≤ ({a} : Set (LGL 2 V)).ncard + 1 :=
            Set.ncard_insert_le 1 {a}
        _ = 2 := by rw [Set.ncard_singleton]
    have hcard : Nat.card ↥D ≤ 2 := by
      change (D : Set (LGL 2 V)).ncard ≤ 2
      exact hle
    exact absurd h3 (not_lt.mpr hcard)
  obtain ⟨u, huD, hu⟩ := Set.not_subset.mp hnotsub
  have hu1 : u ≠ 1 := by rintro rfl; exact hu (by simp)
  have hua : u ≠ a := by rintro rfl; exact hu (by simp)
  rcases c.two.perm u (hDY huD) with ⟨huL, -⟩ | ⟨huL, -⟩
  · exact ⟨u, huD, hu1, huL⟩
  · refine ⟨a * u, D.mul_mem haD huD, ?_, ?_⟩
    · intro h
      have h2 : a * u = a * a := by rw [h, c.sq]
      exact hua (mul_left_cancel h2)
    · have haL₂ : cj a L₂ = L₁ := by
        rw [← c.swap, ← cj_mul, c.sq, cj_one]
      rw [cj_mul, huL, haL₂]

theorem zeta_fixes_of_inner (c : SwapCfg Y T L₁ L₂ a) {b : LGL 2 V} (hbY : b ∈ Y)
    (hba : b * a = a * b) (hbb : b * b = 1) (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) (U : Set V)
    (hU : ∀ l ∈ L₁, ∀ u ∈ U, zeta a l u ∈ U) (hbU : ∀ u ∈ U, b u = u) :
    ∀ l ∈ L₁, ∀ u ∈ U, zeta a l u = u := by
  let K : Subgroup ↥L₁ :=
    { carrier := {l | ∀ u ∈ U, zeta a (l : LGL 2 V) u = u}
      mul_mem' := by
        intro l l' hl hl' u hu
        show zeta a ((l * l' : ↥L₁) : LGL 2 V) u = u
        rw [show ((l * l' : ↥L₁) : LGL 2 V) = (l : LGL 2 V) * (l' : LGL 2 V) from rfl,
          zeta_mul c l.2 l'.2, LinearEquiv.mul_apply, hl' u hu, hl u hu]
      one_mem' := by
        intro u _
        show zeta a ((1 : ↥L₁) : LGL 2 V) u = u
        rw [show ((1 : ↥L₁) : LGL 2 V) = (1 : LGL 2 V) from rfl, zeta_one]
        rfl
      inv_mem' := by
        intro l hl u hu
        show zeta a ((l⁻¹ : ↥L₁) : LGL 2 V) u = u
        rw [show ((l⁻¹ : ↥L₁) : LGL 2 V) = (l : LGL 2 V)⁻¹ from rfl, zeta_inv c l.2]
        change (zeta a (l : LGL 2 V)).symm u = u
        exact (LinearEquiv.symm_apply_eq (zeta a (l : LGL 2 V))).mpr (hl u hu).symm }
  have hbconj_mem : ∀ l : ↥L₁, b * (l : LGL 2 V)⁻¹ * b⁻¹ ∈ L₁ := by
    intro l
    have hmem : b * (l : LGL 2 V)⁻¹ * b⁻¹ ∈ cj b L₁ := by
      rw [mem_cj]
      have h : b⁻¹ * (b * (l : LGL 2 V)⁻¹ * b⁻¹) * b = (l : LGL 2 V)⁻¹ := by group
      rw [h]
      exact L₁.inv_mem l.2
    rwa [hbL] at hmem
  have hnl_mem : ∀ l : ↥L₁,
      b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V) ∈ L₁ :=
    fun l => L₁.mul_mem (hbconj_mem l) l.2
  have hmemK : ∀ l : ↥L₁,
      (⟨b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V), hnl_mem l⟩ : ↥L₁) ∈ K := by
    intro l
    show ∀ u ∈ U, zeta a (b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V)) u = u
    intro u hu
    have hsplit : zeta a (b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V))
        = zeta a (b * (l : LGL 2 V)⁻¹ * b⁻¹) * zeta a (l : LGL 2 V) :=
      zeta_mul c (hbconj_mem l) l.2
    rw [hsplit, LinearEquiv.mul_apply]
    have hconj : zeta a (b * (l : LGL 2 V)⁻¹ * b⁻¹)
        = b * zeta a ((l : LGL 2 V)⁻¹) * b⁻¹ :=
      (zeta_conj hba ((l : LGL 2 V)⁻¹)).symm
    rw [hconj, zeta_inv c l.2]
    simp only [LinearEquiv.mul_apply]
    have hzu : zeta a (l : LGL 2 V) u ∈ U := hU (l : LGL 2 V) l.2 u hu
    have hb1u : b⁻¹ (zeta a (l : LGL 2 V) u) = zeta a (l : LGL 2 V) u := by
      change b.symm (zeta a (l : LGL 2 V) u) = zeta a (l : LGL 2 V) u
      exact (LinearEquiv.symm_apply_eq b).mpr (hbU _ hzu).symm
    rw [hb1u]
    have hinv : (zeta a (l : LGL 2 V))⁻¹ (zeta a (l : LGL 2 V) u) = u := by
      change (zeta a (l : LGL 2 V)).symm ((zeta a (l : LGL 2 V)) u) = u
      exact LinearEquiv.symm_apply_apply _ u
    rw [hinv]
    exact hbU u hu
  have hKnormal : K.Normal :=
    ⟨by
      intro n hn g
      show ∀ u ∈ U, zeta a ((g * n * g⁻¹ : ↥L₁) : LGL 2 V) u = u
      intro u hu
      have hcoe : ((g * n * g⁻¹ : ↥L₁) : LGL 2 V)
          = (g : LGL 2 V) * ((n : LGL 2 V) * (g : LGL 2 V)⁻¹) := by
        rw [show ((g * n * g⁻¹ : ↥L₁) : LGL 2 V)
              = (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ from rfl]
        group
      have hn' : ∀ u ∈ U, zeta a (n : LGL 2 V) u = u := hn
      rw [hcoe, zeta_mul c g.2 (L₁.mul_mem n.2 (L₁.inv_mem g.2)),
        zeta_mul c n.2 (L₁.inv_mem g.2), zeta_inv c g.2]
      simp only [LinearEquiv.mul_apply]
      have hgu : (zeta a (g : LGL 2 V))⁻¹ u ∈ U := by
        have h := hU ((g : LGL 2 V)⁻¹) (L₁.inv_mem g.2) u hu
        rwa [zeta_inv c g.2] at h
      rw [hn' _ hgu]
      change (zeta a (g : LGL 2 V)) ((zeta a (g : LGL 2 V)).symm u) = u
      exact LinearEquiv.apply_symm_apply _ u⟩
  have hmem₁L : ∀ l ∈ L₁, b * l * b⁻¹ ∈ L₁ := by
    intro l hl
    have hmem : b * l * b⁻¹ ∈ cj b L₁ := by
      rw [mem_cj]
      have h : b⁻¹ * (b * l * b⁻¹) * b = l := by group
      rw [h]
      exact hl
    rwa [hbL] at hmem
  have hKn : ∀ y ∈ L₁, ∀ k ∈ K.map L₁.subtype, y * k * y⁻¹ ∈ K.map L₁.subtype := by
    intro y hy k hk
    obtain ⟨k₀, hk₀, hk₀eq⟩ := Subgroup.mem_map.mp hk
    rw [← hk₀eq]
    simpa using Subgroup.mem_map_of_mem L₁.subtype (hKnormal.conj_mem k₀ hk₀ ⟨y, hy⟩)
  rcases quasi_normal_dichotomy c.two.quasi₁ (Subgroup.map_subtype_le K) hKn with hZ | htop
  ·
    exfalso
    have hmemZ : ∀ l : ↥L₁,
        b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V) ∈ quasiCentre L₁ :=
      fun l => hZ (Subgroup.mem_map_of_mem L₁.subtype (hmemK l))
    have hmem₁ : ∀ l ∈ L₁, b * l * b⁻¹ * l⁻¹ ∈ quasiCentre L₁ := by
      intro l hl
      have h := hmemZ ⟨l⁻¹, L₁.inv_mem hl⟩
      simpa using h
    have hcommL₁ : ∀ l ∈ L₁, b * l = l * b :=
      quasi_comm_of_comm_mod_centre c.two.quasi₁ hmem₁L hmem₁
    have hzeta : ∀ l ∈ L₁, b * zeta a l = zeta a l * b := by
      intro l hl
      have hbl : b * l * b⁻¹ = l := by rw [hcommL₁ l hl]; group
      have hconj : b * zeta a l * b⁻¹ = zeta a l := by rw [zeta_conj hba l, hbl]
      exact mul_inv_eq_iff_eq_mul.mp hconj
    exact hb1 (eq_one_of_comm_zeta c hbY hba hbb hbL hzeta)
  ·
    intro l hl u hu
    have hlK : (⟨l, hl⟩ : ↥L₁) ∈ K := by
      have hmem : l ∈ K.map L₁.subtype := by rw [htop]; exact hl
      obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
      have hk_eq : k = ⟨l, hl⟩ := Subtype.ext hkeq
      rw [← hk_eq]
      exact hk
    exact hlK u hu

end W183K3Swap

end CFSG.LocalAnalysis.WeakClosure81

end
