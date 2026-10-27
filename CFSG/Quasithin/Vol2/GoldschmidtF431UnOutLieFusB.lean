module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Parabolic
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSet

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem mem_Pt_of_normalizer {g : Xg h}
    (hg : (g : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoA2 h : Set (GL (Fin 4) K))) :
    g ∈ Pt h := by
  rw [Pt, Subgroup.mem_normalizer_iff]
  intro y
  exact Subgroup.mem_normalizer_iff.1 hg (y : GL (Fin 4) K)

theorem mem_Ln_of_normalizer {g : Xg h}
    (hg : (g : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoA1 h : Set (GL (Fin 4) K))) :
    g ∈ Ln h := by
  rw [Ln, Subgroup.mem_normalizer_iff]
  intro y
  exact Subgroup.mem_normalizer_iff.1 hg (y : GL (Fin 4) K)

theorem fus_r2X_mem_Pt : (⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ : Xg h) ∈ Pt h :=
  mem_Pt_of_normalizer h (miyamotoN2_le_normalizer_A2 h (miyamotoR2_mem_N2 h))

theorem mem_Ln_of_mem_N1 {g : Xg h} (hg : (g : GL (Fin 4) K) ∈ miyamotoN1 h) : g ∈ Ln h :=
  mem_Ln_of_normalizer h (miyamotoN1_le_normalizer_A1 h hg)

theorem mem_Ln_of_mem_I1_sup_N1 {g : Xg h}
    (hg : (g : GL (Fin 4) K) ∈ miyamotoI1 h ⊔ miyamotoN1 h) : g ∈ Ln h := by
  have : (g : GL (Fin 4) K) ∈ gramSU h (miyamotoJ4 K) ⊓
      Subgroup.normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) := by
    rw [normalizer_miyamotoA1 h]
    exact Subgroup.mem_sup_right hg
  exact mem_Ln_of_normalizer h this.2

theorem fus_step {B : Subgroup (Xg h)} {hB : FStab h B} (F : Subgroup (K ≃+* K)) {g a b : Xg h}
    (hg : g ∈ B) (e : g⁻¹ * a * g = b) :
    ∃ m ∈ Ssd h B hB F, m * cj h a * m⁻¹ = cj h b := by
  refine ⟨cj h g⁻¹, cj_mem_Ssd h (B.inv_mem hg), ?_⟩
  rw [← e, cj_mul, cj_mul, cj_inv h g, inv_inv]

theorem fus_step' {B : Subgroup (Xg h)} {hB : FStab h B} (F : Subgroup (K ≃+* K)) {g a b : Xg h}
    (hg : g ∈ B) (e : g * a * g⁻¹ = b) :
    ∃ m ∈ Ssd h B hB F, m * cj h a * m⁻¹ = cj h b := by
  refine ⟨cj h g, cj_mem_Ssd h hg, ?_⟩
  rw [← e, cj_mul, cj_mul, cj_inv]

end CFSG.Quasithin.H13.F431.Un.OL
