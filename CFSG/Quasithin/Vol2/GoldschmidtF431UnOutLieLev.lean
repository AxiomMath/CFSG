module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Generation
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSet

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

abbrev etaX : (⊤ : Subgroup (Xg h)) ≃* gramSU h (miyamotoJ4 K) := Subgroup.topEquiv

theorem sg_eq_pull (M : Subgroup (GL (Fin 4) K)) : sg h M = miyamotoPull h ⊤ (etaX h) M := by
  ext x
  rw [mem_miyamotoPull]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨g, hg, e⟩
    have : g = x := e
    rw [← this]
    exact hg

abbrev I1X : Subgroup (Xg h) := sg h (miyamotoI1 h)

abbrev I2X : Subgroup (Xg h) := sg h (miyamotoI2 h)

abbrev N1X : Subgroup (Xg h) := sg h (miyamotoN1 h)

abbrev N2X : Subgroup (Xg h) := sg h (miyamotoN2 h)

abbrev IX : Subgroup (Xg h) := sg h (miyamotoI h)

theorem Pt_eq : Pt h = A2X h ⊔ (I2X h ⊔ N2X h) := by
  have e := normalizer_miyamotoA2G h (⊤ : Subgroup (Xg h)) (etaX h)
  rw [top_inf_eq] at e
  have h1 : A2X h = miyamotoA2G h ⊤ (etaX h) := sg_eq_pull h _
  have h2 : I2X h = miyamotoI2G h ⊤ (etaX h) := sg_eq_pull h _
  have h3 : N2X h = miyamotoN2G h ⊤ (etaX h) := sg_eq_pull h _
  rw [Pt, h1, h2, h3]
  exact e

theorem Ln_eq : Ln h = A1X h ⊔ (I1X h ⊔ N1X h) := by
  have e := normalizer_miyamotoA1G h (⊤ : Subgroup (Xg h)) (etaX h)
  rw [top_inf_eq] at e
  have h1 : A1X h = miyamotoA1G h ⊤ (etaX h) := sg_eq_pull h _
  have h2 : I1X h = miyamotoI1G h ⊤ (etaX h) := sg_eq_pull h _
  have h3 : N1X h = miyamotoN1G h ⊤ (etaX h) := sg_eq_pull h _
  rw [Ln, h1, h2, h3]
  exact e

theorem Psy_le_A2X_sup_N2X : Psy h ≤ A2X h ⊔ N2X h := by
  have hP : miyamotoP h ≤ miyamotoA2 h ⊔ miyamotoN2 h := by
    rw [miyamotoA2_sup_N2_eq h]
    exact le_sup_left
  have e := miyamotoPull_sup h (⊤ : Subgroup (Xg h)) (etaX h)
    (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h)
  have := miyamotoPull_mono h (⊤ : Subgroup (Xg h)) (etaX h) hP
  rw [e] at this
  have h1 : Psy h = miyamotoPull h ⊤ (etaX h) (miyamotoP h) := sg_eq_pull h _
  have h2 : A2X h = miyamotoPull h ⊤ (etaX h) (miyamotoUnipotent h false true) := sg_eq_pull h _
  have h3 : N2X h = miyamotoPull h ⊤ (etaX h) (miyamotoN2 h) := sg_eq_pull h _
  rw [h1, h2, h3]
  exact this

theorem Psy_le_A1X_sup_N1X : Psy h ≤ A1X h ⊔ N1X h := by
  have hP : miyamotoP h ≤ miyamotoA1 h ⊔ miyamotoN1 h := by
    rw [miyamotoA1_sup_N1_eq h]
    exact le_sup_left
  have e := miyamotoPull_sup h (⊤ : Subgroup (Xg h)) (etaX h)
    (miyamotoUnipotent_le_SU h true false) (miyamotoN1_le_gramSU h)
  have := miyamotoPull_mono h (⊤ : Subgroup (Xg h)) (etaX h) hP
  rw [e] at this
  have h1 : Psy h = miyamotoPull h ⊤ (etaX h) (miyamotoP h) := sg_eq_pull h _
  have h2 : A1X h = miyamotoPull h ⊤ (etaX h) (miyamotoUnipotent h true false) := sg_eq_pull h _
  have h3 : N1X h = miyamotoPull h ⊤ (etaX h) (miyamotoN1 h) := sg_eq_pull h _
  rw [h1, h2, h3]
  exact this

theorem Psy_le_Pt : Psy h ≤ Pt h := by
  rw [Pt_eq]
  exact (Psy_le_A2X_sup_N2X h).trans (sup_le le_sup_left (le_sup_right.trans le_sup_right))

theorem Psy_le_Ln : Psy h ≤ Ln h := by
  rw [Ln_eq]
  exact (Psy_le_A1X_sup_N1X h).trans (sup_le le_sup_left (le_sup_right.trans le_sup_right))

theorem A2X_le_Pt : A2X h ≤ Pt h := Subgroup.le_normalizer

theorem A1X_le_Ln : A1X h ≤ Ln h := Subgroup.le_normalizer

theorem isSylowTwoOf_Psy : IsSylowTwoOf (Psy h) ⊤ := by
  have := finite_gramSU_miyamotoJ4 h
  obtain ⟨S, hS⟩ := exists_sylow_miyamotoP h
  have h2 := isSylowTwoOf_top_of_sylow (show Sylow 2 (Xg h) from S)
  rwa [show ((show Sylow 2 (Xg h) from S) : Subgroup (Xg h)) = Psy h from hS] at h2

end CFSG.Quasithin.H13.F431.Un.OL
