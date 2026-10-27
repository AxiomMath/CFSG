module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCtr
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem normalizer_eq_of_isCoatom [IsSimpleGroup (Xg h)] {B : Subgroup (Xg h)}
    (hB : IsCoatom B) (hB1 : B ≠ ⊥) : Subgroup.normalizer (B : Set (Xg h)) = B := by
  rcases hB.le_iff.1 (Subgroup.le_normalizer (H := B)) with hN | hN
  · exfalso
    have : B.Normal := Subgroup.normalizer_eq_top_iff.1 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with e | e
    · exact hB1 e
    · exact hB.1 e
  · exact hN

theorem inf_autStab_eq_Ssd [IsSimpleGroup (Xg h)] {B : Subgroup (Xg h)} (hS : FStab h B)
    (hB : IsCoatom B) (hB1 : B ≠ ⊥) {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) :
    K₀ ⊓ autStab B = Ssd h B hS (FK h K₀) := by
  apply le_antisymm
  · rintro α ⟨hαK, hαS⟩
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφ
    have hsB : s ∈ B := by
      have hn : s ∈ Subgroup.normalizer (B : Set (Xg h)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        obtain ⟨x, rfl⟩ := (fa h φ).surjective y
        have h1 := hαS x
        have h2 : α x = s * fa h φ x * s⁻¹ := by
          rw [hs]
          simp [MulAut.mul_apply, MulAut.conj_apply]
        rw [h2] at h1
        rw [hS φ x] at *
        exact h1
      rwa [normalizer_eq_of_isCoatom h hB hB1] at hn
    refine ⟨s, hsB, φ, ?_, hs⟩
    rw [← cj_mul_fa_mem_iff h hinn s φ, ← hs]
    exact hαK
  · rintro _ ⟨s, hs, φ, hφ, rfl⟩
    refine ⟨Ssd_le (hB := hS) h hinn le_rfl ⟨s, hs, φ, hφ, rfl⟩, fun x => ?_⟩
    have e : (cj h s * fa h φ) x = s * fa h φ x * s⁻¹ := by
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [e, ← hS φ x]
    constructor
    · intro hx
      exact B.mul_mem (B.mul_mem hs hx) (B.inv_mem hs)
    · intro hx
      have := B.mul_mem (B.mul_mem (B.inv_mem hs) hx) hs
      simpa [mul_assoc] using this

theorem z1X_mem_A2X : z1X h ∈ A2X h :=
  miyamotoZ2_le_A2 h (miyamotoZ_le_Z2 h (z1X_mem_ZX h))

theorem Pt_ne_bot : Pt h ≠ ⊥ := by
  intro e
  have hz : z1X h ∈ Pt h := A2X_le_Pt h (z1X_mem_A2X h)
  rw [e, Subgroup.mem_bot] at hz
  have := orderOf_z1X h
  rw [hz, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Ln_ne_bot : Ln h ≠ ⊥ := by
  intro e
  have hz : z1X h ∈ Ln h := A1X_le_Ln h (z1X_mem_A1X h)
  rw [e, Subgroup.mem_bot] at hz
  have := orderOf_z1X h
  rw [hz, orderOf_one] at this
  exact absurd this (by norm_num)

theorem inf_autStab_Pt [IsSimpleGroup (Xg h)] (hPt : IsCoatom (Pt h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) :
    K₀ ⊓ autStab (Pt h) = Ssd h (Pt h) (fStab_Pt h) (FK h K₀) :=
  inf_autStab_eq_Ssd h (fStab_Pt h) hPt (Pt_ne_bot h) hinn

theorem inf_autStab_Ln [IsSimpleGroup (Xg h)] (hLn : IsCoatom (Ln h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) :
    K₀ ⊓ autStab (Ln h) = Ssd h (Ln h) (fStab_Ln h) (FK h K₀) :=
  inf_autStab_eq_Ssd h (fStab_Ln h) hLn (Ln_ne_bot h) hinn

end CFSG.Quasithin.H13.F431.Un.OL
