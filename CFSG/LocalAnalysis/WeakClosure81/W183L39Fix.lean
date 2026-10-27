module

public import CFSG.LocalAnalysis.WeakClosure81.W183L39Zeta
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183L39

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

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
    (hba : b * a = a * b) (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) (U : Set V)
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
  haveI := hKnormal
  have hKtop : K = ⊤ := by
    haveI := c.two.simple₁
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hbot | htop
    · exfalso
      have hcommBL₁ : ∀ l : ↥L₁, b * (l : LGL 2 V) = (l : LGL 2 V) * b := by
        intro l
        have hmem : (⟨b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V), hnl_mem l⟩ : ↥L₁) ∈ K :=
          hmemK l
        rw [hbot] at hmem
        have hnl_eq : b * (l : LGL 2 V)⁻¹ * b⁻¹ * (l : LGL 2 V) = 1 := by
          have := Subgroup.mem_bot.mp hmem
          simpa using congrArg (fun x : ↥L₁ => (x : LGL 2 V)) this
        have h3 : b * (l : LGL 2 V)⁻¹ * b⁻¹ = (l : LGL 2 V)⁻¹ :=
          mul_eq_one_iff_eq_inv.mp hnl_eq
        have h2 : b * (l : LGL 2 V)⁻¹ = (l : LGL 2 V)⁻¹ * b := by
          have h4 := congrArg (fun x => x * b) h3
          simpa [mul_assoc] using h4
        have hc : Commute b ((l : LGL 2 V)⁻¹) := h2
        simpa using (hc.inv_right).eq
      have hcomm_all : ∀ l ∈ L₁, b * l = l * b := fun l hl => hcommBL₁ ⟨l, hl⟩
      have hzeta : ∀ l ∈ L₁, b * zeta a l = zeta a l * b := by
        intro l hl
        have hbl : b * l * b⁻¹ = l := by rw [hcomm_all l hl]; group
        have hconj : b * zeta a l * b⁻¹ = zeta a l := by rw [zeta_conj hba l, hbl]
        exact mul_inv_eq_iff_eq_mul.mp hconj
      exact hb1 (eq_one_of_comm_zeta c hbY hba hbL hzeta)
    · exact htop
  intro l hl u hu
  have hlK : (⟨l, hl⟩ : ↥L₁) ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
  exact hlK u hu

end W183L39

end CFSG.LocalAnalysis.WeakClosure81

end
