module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard
public import CFSG.Quasithin.Background.H156Main
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HLU24Inputs

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

private theorem bvec_255_apply (i : Fin 24) :
    bvec 24 255 i = if (i : ℕ) < 8 then 1 else 0 := by
  have htb : (255 : ℕ).testBit (i : ℕ) = decide ((i : ℕ) < 8) := by
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  simp only [bvec, htb]
  by_cases hi : (i : ℕ) < 8 <;> simp [hi]

theorem actM_liftCCols_three : actM liftCCols 3 = 255 := by
  rfl

theorem mem_octStab_of_fixes_three (γ : ↥AutPerm)
    (h : rhoC11 AutPerm le_rfl γ (toW 11 3) = toW 11 3) : (γ : S24) ∈ octStab octad0 := by
  set c : Fin 24 → ZMod 2 := liftC (Multiplicative.toAdd (toW 11 3)) with hc
  set c₂ : Fin 24 → ZMod 2 :=
    Multiplicative.toAdd (G6.permAct 24 (γ : S24) (Multiplicative.ofAdd c)) with hc₂
  have hrho : rhoC11 AutPerm le_rfl γ (toW 11 3) = Multiplicative.ofAdd (κC c₂) := by
    rw [hc₂, hc]
    rfl
  have hcb : c = bvec 24 255 := by
    rw [hc, toAdd_toW, liftC_bvec, actM_liftCCols_three]
  have hκc : κC c = bvec 11 3 := by
    rw [hc, κC_liftC, toAdd_toW]
  have h2 : κC c₂ = κC c := by
    have h1 : Multiplicative.ofAdd (κC c₂) = Multiplicative.ofAdd (κC c) := by
      calc Multiplicative.ofAdd (κC c₂) = rhoC11 AutPerm le_rfl γ (toW 11 3) := hrho.symm
        _ = toW 11 3 := h
        _ = Multiplicative.ofAdd (bvec 11 3) := rfl
        _ = Multiplicative.ofAdd (κC c) := by rw [hκc]
    simpa using congrArg Multiplicative.toAdd h1
  have hcC : c ∈ C := by rw [hc]; exact liftC_mem _
  have hc₂C : c₂ ∈ C := by
    rw [hc₂]
    have hmem : Multiplicative.ofAdd c ∈ golayC := (mem_golayC_iff _).2 (by simpa using hcC)
    exact (mem_golayC_iff _).1 ((preserves_code γ.2).1 _ hmem)
  have hsub : c₂ - c ∈ C := C.sub_mem hc₂C hcC
  have hker : κC (c₂ - c) = 0 := by
    rw [map_sub, h2]
    exact sub_self _
  have hcz : ∀ j : Fin 24, c j ≠ 0 ↔ (j : ℕ) < 8 := by
    intro j
    rw [hcb, bvec_255_apply]
    by_cases hj : (j : ℕ) < 8 <;> simp [hj]
  have hcc : c₂ = c := by
    rcases (κC_eq_zero_iff hsub).1 hker with h0 | hΩ
    · exact sub_eq_zero.1 h0
    · exfalso
      have hc₂eq : c₂ = c + Ω := by
        rw [add_comm c Ω]
        exact sub_eq_iff_eq_add.1 hΩ
      have hw₂ : hammingNorm c₂ = hammingNorm c := by
        rw [hc₂, toAdd_permAct]
        exact hammingNorm_comp_perm c ((γ : S24)⁻¹)
      have hw16 : hammingNorm (c + Ω) = 16 := by
        rw [hcb]
        decide +kernel
      have hw8 : hammingNorm c = 8 := by
        rw [hcb, hammingNorm_bvec]
        decide +kernel
      rw [hc₂eq, hw16, hw8] at hw₂
      omega
  have hci : ∀ i : Fin 24, c ((γ : S24)⁻¹ i) = c i := by
    intro i
    have h1 : c₂ i = c ((γ : S24)⁻¹ i) := by
      rw [hc₂]
      simpa using G6.permAct_apply 24 (γ : S24) (Multiplicative.ofAdd c) i
    rw [← h1, hcc]
  have hiff : ∀ i : Fin 24, (((γ : S24)⁻¹ i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
    intro i
    rw [← hcz ((γ : S24)⁻¹ i), ← hcz i, hci i]
  have hsmul : (γ : S24) • octad0 = octad0 := by
    ext i
    rw [smul_finset_eq_map, Finset.mem_map_equiv]
    simp only [octad0, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff i
  exact mem_octStab_iff.2 ⟨γ.2, hsmul⟩

end CFSG.ASVolI.H16
