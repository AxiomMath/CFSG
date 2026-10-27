module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFusB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstD
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNst

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem IX_le_Ln : IX h ≤ Ln h := by
  intro g hg
  rw [Ln, Subgroup.mem_normalizer_iff]
  intro y
  have hn := miyamotoI_le_normalizer_unipotent h true false hg
  exact Subgroup.mem_normalizer_iff.1 hn (y : GL (Fin 4) K)

theorem normalizer_Psy_eq : Subgroup.normalizer (Psy h : Set (Xg h)) = Psy h ⊔ IX h := by
  have e := normalizer_miyamotoPG h (⊤ : Subgroup (Xg h)) (etaX h)
  rw [top_inf_eq] at e
  have h1 : Psy h = miyamotoPG h ⊤ (etaX h) := sg_eq_pull h _
  have h2 : IX h = miyamotoIG h ⊤ (etaX h) := sg_eq_pull h _
  rw [h1, h2]
  exact e

theorem normalizer_Psy_le_Pt : Subgroup.normalizer (Psy h : Set (Xg h)) ≤ Pt h := by
  rw [normalizer_Psy_eq]
  exact sup_le (Psy_le_Pt h) (IX_le_Pt h)

theorem normalizer_Psy_le_Ln : Subgroup.normalizer (Psy h : Set (Xg h)) ≤ Ln h := by
  rw [normalizer_Psy_eq]
  exact sup_le (Psy_le_Ln h) (IX_le_Ln h)

theorem xb_mem : miyamotoXGL h 0 1 0 0 ∈ miyamotoP h :=
  (miyamotoXGL_mem_P h).2 ⟨map_one _, by simp⟩

theorem xa_mem : miyamotoXGL h 1 0 0 0 ∈ miyamotoP h :=
  (miyamotoXGL_mem_P h).2 ⟨map_zero _, by simp⟩

theorem Pt_ne_top [IsSimpleGroup (Xg h)] : Pt h ≠ ⊤ := by
  intro e
  have : (A2X h).Normal := Subgroup.normalizer_eq_top_iff.1 e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A2X h) with h0 | h0
  · have hz : z1X h ∈ A2X h := z1X_mem_A2X h
    rw [h0, Subgroup.mem_bot] at hz
    have := orderOf_z1X h
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  · have hy : (⟨miyamotoXGL h 0 1 0 0, miyamotoUnipotent_le_SU h false false (xb_mem h)⟩ :
        Xg h) ∈ A2X h := by
      rw [h0]
      exact Subgroup.mem_top _
    have := ((miyamotoXGL_mem_A2 h).1 hy).1
    exact one_ne_zero this

theorem Ln_ne_top [IsSimpleGroup (Xg h)] : Ln h ≠ ⊤ := by
  intro e
  have : (A1X h).Normal := Subgroup.normalizer_eq_top_iff.1 e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A1X h) with h0 | h0
  · have hz : z1X h ∈ A1X h := z1X_mem_A1X h
    rw [h0, Subgroup.mem_bot] at hz
    have := orderOf_z1X h
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  · have hy : (⟨miyamotoXGL h 1 0 0 0, miyamotoUnipotent_le_SU h false false (xa_mem h)⟩ :
        Xg h) ∈ A1X h := by
      rw [h0]
      exact Subgroup.mem_top _
    have := ((miyamotoXGL_mem_A1 h).1 hy).1
    exact one_ne_zero this

theorem P_entry12 {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := by
  obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hg
  simp [miyamotoXGL, miyamotoX]

theorem P_entry01 {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := by
  obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hg
  simp [miyamotoXGL, miyamotoX]

theorem Pt_ne_normalizer : Pt h ≠ Subgroup.normalizer (Psy h : Set (Xg h)) := by
  intro e
  have hr : (⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ : Xg h) ∈ Subgroup.normalizer
      (Psy h : Set (Xg h)) := e ▸ fus_r2X_mem_Pt h
  have hy : (⟨miyamotoXGL h 0 1 0 0, miyamotoUnipotent_le_SU h false false (xb_mem h)⟩ :
      Xg h) ∈ Psy h := xb_mem h
  have hm := (Subgroup.mem_normalizer_iff.1 hr _).1 hy
  have h12 := P_entry12 h (show ((⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ : Xg h) *
    ⟨miyamotoXGL h 0 1 0 0, miyamotoUnipotent_le_SU h false false (xb_mem h)⟩ *
    (⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ : Xg h)⁻¹ : Xg h) ∈ Psy h from hm)
  have hinv : (miyamotoR2 K)⁻¹ = miyamotoR2 K := inv_eq_of_mul_eq_one_right miyamotoR2_mul_self
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hinv, Units.val_mul] at h12
  simp [miyamotoR2, miyamotoXGL, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at h12

theorem Ln_ne_normalizer : Ln h ≠ Subgroup.normalizer (Psy h : Set (Xg h)) := by
  intro e
  have hr1 : (⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : Xg h) ∈ Ln h :=
    mem_Ln_of_mem_N1 h (miyamotoR1_mem_N1 h)
  have hr : (⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : Xg h) ∈ Subgroup.normalizer
      (Psy h : Set (Xg h)) := e ▸ hr1
  have hy : (⟨miyamotoXGL h 1 0 0 0, miyamotoUnipotent_le_SU h false false (xa_mem h)⟩ :
      Xg h) ∈ Psy h := xa_mem h
  have hm := (Subgroup.mem_normalizer_iff.1 hr _).1 hy
  have h01 := P_entry01 h (show ((⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : Xg h) *
    ⟨miyamotoXGL h 1 0 0 0, miyamotoUnipotent_le_SU h false false (xa_mem h)⟩ *
    (⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : Xg h)⁻¹ : Xg h) ∈ Psy h from hm)
  have hinv : (miyamotoR1 K)⁻¹ = miyamotoR1 K := inv_eq_of_mul_eq_one_right miyamotoR1_mul_self
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hinv, Units.val_mul] at h01
  simp [miyamotoR1, miyamotoXGL, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at h01

theorem Pt_sup_Ln : Pt h ⊔ Ln h = ⊤ := by
  have e := miyamoto_generationG h (⊤ : Subgroup (Xg h)) (etaX h)
  have h1 : A1X h = miyamotoA1G h ⊤ (etaX h) := sg_eq_pull h _
  have h2 : A2X h = miyamotoA2G h ⊤ (etaX h) := sg_eq_pull h _
  have h3 : N1X h = miyamotoN1G h ⊤ (etaX h) := sg_eq_pull h _
  have h4 : N2X h = miyamotoN2G h ⊤ (etaX h) := sg_eq_pull h _
  rw [← h1, ← h2, ← h3, ← h4] at e
  rw [eq_top_iff, ← e]
  exact sup_le (le_sup_of_le_right (sup_le (A1X_le_Ln h) (fun n hn => mem_Ln_of_mem_N1 h hn)))
    (le_sup_of_le_left (sup_le (A2X_le_Pt h) (N2X_le_Pt h)))

theorem Pt_ne_Ln [IsSimpleGroup (Xg h)] : Pt h ≠ Ln h := by
  intro e
  apply Pt_ne_top h
  rw [← Pt_sup_Ln h, ← e, sup_idem]

end CFSG.Quasithin.H13.F431.Un.OL
