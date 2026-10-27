module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Background.F3Dihedral
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem vee_cj_of_mem_Ssd_bot {B : Subgroup (Xg h)} {hB : FStab h B} {α : MulAut (Xg h)}
    (hα : α ∈ Ssd h B hB ⊥) : ∃ s ∈ B, α = cj h s := by
  obtain ⟨s, hs, φ, hφ, rfl⟩ := hα
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  exact ⟨s, hs, by rw [fa_one, mul_one]⟩

theorem vee_A1X_comm {a b : Xg h} (ha : a ∈ A1X h) (hb : b ∈ A1X h) : a * b = b * a :=
  Subtype.ext (miyamotoA1_mul_comm h ha hb)

theorem vee_A1X_sq {a : Xg h} (ha : a ∈ A1X h) : a ^ 2 = 1 := by
  have := isElementaryAbelian_miyamotoA1 h
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := miyamotoA1 h)
    (a : GL (Fin 4) K) ha
  exact Subtype.ext (by simpa using this)

theorem Ssd_A1X_elemAb :
    (∀ a ∈ Ssd h (A1X h) (fStab_A1X h) ⊥, ∀ b ∈ Ssd h (A1X h) (fStab_A1X h) ⊥, a * b = b * a) ∧
      ∀ a ∈ Ssd h (A1X h) (fStab_A1X h) ⊥, a ^ 2 = 1 := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := vee_cj_of_mem_Ssd_bot h ha
    obtain ⟨t, ht, rfl⟩ := vee_cj_of_mem_Ssd_bot h hb
    rw [← cj_mul, ← cj_mul, vee_A1X_comm h hs ht]
  · obtain ⟨s, hs, rfl⟩ := vee_cj_of_mem_Ssd_bot h ha
    rw [sq, ← cj_mul, ← sq, vee_A1X_sq h hs, cj_one]

end CFSG.Quasithin.H13.F431.Un.OL
