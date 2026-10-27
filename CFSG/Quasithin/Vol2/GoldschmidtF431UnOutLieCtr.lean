module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem aut_mul_cj_mul_inv (k : MulAut (Xg h)) (d : Xg h) : k * cj h d * k⁻¹ = cj h (k d) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem orderOf_z1X : orderOf (z1X h) = 2 := by
  rw [← Subgroup.orderOf_coe, show ((z1X h : Xg h) : GL (Fin 4) K) = miyamotoZ1 K from rfl]
  exact orderOf_miyamotoZ1 h

theorem orderOf_z2X : orderOf (z2X h) = 2 := by
  rw [← Subgroup.orderOf_coe,
    show ((z2X h : Xg h) : GL (Fin 4) K) = LocalAnalysis.miyamotoZ2 K from rfl]
  exact orderOf_miyamotoZ2 h

theorem orderOf_cj_z1X : orderOf (cj h (z1X h)) = 2 := by
  rw [orderOf_injective (MulAut.conj : Xg h →* MulAut (Xg h)) (conj_hom_injective h) (z1X h),
    orderOf_z1X]

theorem orderOf_cj_z2X : orderOf (cj h (z2X h)) = 2 := by
  rw [orderOf_injective (MulAut.conj : Xg h →* MulAut (Xg h)) (conj_hom_injective h) (z2X h),
    orderOf_z2X]

theorem not_conj_z1X_z2X (k : MulAut (Xg h)) : k * cj h (z1X h) * k⁻¹ ≠ cj h (z2X h) := by
  intro e
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h k
  rw [aut_mul_cj_mul_inv, cj_inj, hs] at e
  have e2 : s * z1X h * s⁻¹ = z2X h := by
    rw [← e]
    simp [MulAut.mul_apply, MulAut.conj_apply, fa_z1X]
  apply miyamotoZ1_not_conj_Z2 (K := K) (((s : Xg h) : GL (Fin 4) K)⁻¹)
  have := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) e2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [inv_inv]
  exact this

theorem fix_of_comm_cj {w : MulAut (Xg h)} (hc : ∀ u ∈ Psy h, w * cj h u = cj h u * w)
    {u : Xg h} (hu : u ∈ Psy h) : w u = u := by
  have e : cj h (w u) = cj h u := by
    rw [← aut_mul_cj_mul_inv, hc u hu, mul_assoc, mul_inv_cancel, mul_one]
  exact (cj_inj h).1 e

theorem center_Ssd_le (_hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) (w : MulAut (Xg h))
    (hw : w ∈ Ssd h (Psy h) (fStab_Psy h) F₂)
    (hc : ∀ y ∈ Ssd h (Psy h) (fStab_Psy h) F₂, y * w = w * y) :
    w ∈ Ssd h (ZX h) (fStab_ZX h) ⊥ := by
  have hfix : ∀ u ∈ Psy h, w u = u :=
    fun u hu => fix_of_comm_cj h (fun u hu => (hc _ (cj_mem_Ssd h hu)).symm) hu
  obtain ⟨a, haA, rfl⟩ := (fixes_miyamotoZ2_iff h w).1 fun g hg =>
    hfix g (miyamotoA1_le_P h (miyamotoZ2_le_A1 h hg))
  have haP : (a : GL (Fin 4) K) ∈ miyamotoP h := miyamotoA1_le_P h haA
  have haZ : (a : GL (Fin 4) K) ∈ miyamotoZ h := by
    rw [← centerIn_miyamotoP]
    refine ⟨haP, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyX : y ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false false hy
    have e := hfix ⟨y, hyX⟩ hy
    have e2 : a * ⟨y, hyX⟩ = ⟨y, hyX⟩ * a := by
      rw [MulAut.conj_apply] at e
      have := congrArg (fun x => x * a) e
      simpa [mul_assoc] using this
    exact (congrArg Subtype.val e2).symm
  exact cj_mem_Ssd h haZ

theorem cj_z1X_mem_Ssd_ZX (F : Subgroup (K ≃+* K)) :
    cj h (z1X h) ∈ Ssd h (ZX h) (fStab_ZX h) F := cj_mem_Ssd h (z1X_mem_ZX h)

theorem sq_eq_one_of_mem_ZX {z : Xg h} (hz : z ∈ ZX h) : z * z = 1 := by
  obtain ⟨d, hd, e⟩ := (mem_Z h).1 (show (z : GL (Fin 4) K) ∈ miyamotoZ h from hz)
  apply Subtype.ext
  rw [Subgroup.coe_mul, e, miyamotoXGL_mul_self h (map_zero _)]
  simp [miyamotoXGL_zero h]

theorem Ssd_ZX_sq (x : MulAut (Xg h)) (hx : x ∈ Ssd h (ZX h) (fStab_ZX h) ⊥) : x ^ 2 = 1 := by
  obtain ⟨z, hz, φ, hφ, rfl⟩ := hx
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one, sq, ← cj_mul, sq_eq_one_of_mem_ZX h hz, cj_one]

end CFSG.Quasithin.H13.F431.Un.OL
