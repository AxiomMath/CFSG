module

public import CFSG.Quasithin.Recognition.Stroth.W80Transport
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.ClassicalGroups.F2Fixed.SL2Fixed
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GroupTheory.ZPowersPGroup
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Unitary.SUExtras
  Matrix CFSG.Quasithin.Stroth.W80Model


variable {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  {k : ℕ}

private theorem root1_eq (hF : Nat.card F = (2 ^ k) ^ 2) :
    un5Oct (F := F) (p := 2) (f := k) hF 1 =
      rootGroup (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF) 5
        (Pi.single (0 : Fin 2) (1 : ℤ)) := by
  rw [un5Oct, octRootB_one,
    show (![(1 : ℤ), 0] : Fin 2 → ℤ) = Pi.single (0 : Fin 2) 1 by
      ext i; fin_cases i <;> rfl]
  rfl

private theorem rootneg1_eq (hF : Nat.card F = (2 ^ k) ^ 2) :
    un5Oct (F := F) (p := 2) (f := k) hF (-1) =
      rootGroup (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF) 5
        (-Pi.single (0 : Fin 2) (1 : ℤ)) := by
  rw [un5Oct, octRootB_neg_one,
    show (![(-1 : ℤ), 0] : Fin 2 → ℤ) = -Pi.single (0 : Fin 2) 1 by
      ext i; fin_cases i <;> rfl]
  rfl

private theorem root4_eq (hF : Nat.card F = (2 ^ k) ^ 2) :
    un5Oct (F := F) (p := 2) (f := k) hF 4 =
      rootGroup (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF) 5
        (Pi.single (1 : Fin 2) (1 : ℤ)) := by
  rw [un5Oct, octRootB_four,
    show (![(0 : ℤ), 1] : Fin 2 → ℤ) = Pi.single (1 : Fin 2) 1 by
      ext i; fin_cases i <;> rfl]
  rfl

private theorem rootneg4_eq (hF : Nat.card F = (2 ^ k) ^ 2) :
    un5Oct (F := F) (p := 2) (f := k) hF (-4) =
      rootGroup (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF) 5
        (-Pi.single (1 : Fin 2) (1 : ℤ)) := by
  rw [un5Oct, octRootB_neg_four,
    show (![(0 : ℤ), -1] : Fin 2 → ℤ) = -Pi.single (1 : Fin 2) 1 by
      ext i; fin_cases i <;> rfl]
  rfl

private theorem shortWeyl_mem (hF : Nat.card F = (2 ^ k) ^ 2)
    (hk : (0 : Fin (5 / 2)).val + 1 < 5 / 2) (c : F) :
    shortWeyl (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩) c ∈
      un5Oct (F := F) (p := 2) (f := k) hF 1 ⊔
        un5Oct (F := F) (p := 2) (f := k) hF (-1) := by
  rw [root1_eq (F := F) (k := k) hF, rootneg1_eq (F := F) (k := k) hF]
  rw [shortWeyl_def]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (rootHom_mem (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ 0)
      (toStd_short hk).symm (Multiplicative.ofAdd c))
  · exact Subgroup.mem_sup_right (rootHom_mem (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk).symm (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩)
      (lowIdx_ne_rev (n := 5) (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) (0 : Fin (5 / 2)) ⟨0 + 1, hk⟩)
      (toStd_short_neg hk).symm (Multiplicative.ofAdd (-c⁻¹)))
  · exact Subgroup.mem_sup_left (rootHom_mem (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ 0)
      (toStd_short hk).symm (Multiplicative.ofAdd c))

private theorem shortTorus_mem (hF : Nat.card F = (2 ^ k) ^ 2)
    (hk : (0 : Fin (5 / 2)).val + 1 < 5 / 2) (c : F) :
    shortTorus (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩) c ∈
      un5Oct (F := F) (p := 2) (f := k) hF 1 ⊔
        un5Oct (F := F) (p := 2) (f := k) hF (-1) := by
  rw [shortTorus_def]
  exact mul_mem (shortWeyl_mem (F := F) (k := k) hF hk c)
    (shortWeyl_mem (F := F) (k := k) hF hk (-1))

private theorem levelTorus_zero_le_oct_one_sup_neg_one
    (hF : Nat.card F = (2 ^ k) ^ 2) :
    levelTorus (unitaryInvolution F 2 k) (0 : Fin (5 / 2)) ≤
      un5Oct (F := F) (p := 2) (f := k) hF 1 ⊔
        un5Oct (F := F) (p := 2) (f := k) hF (-1) := by
  have hk : (0 : Fin (5 / 2)).val + 1 < 5 / 2 := by decide
  unfold levelTorus
  rw [dite_eq_left hk, Subgroup.closure_le]
  rintro g ⟨c, hc⟩
  have hg : g = shortTorus (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev (0 : Fin (5 / 2)) 0)
      (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ ⟨0 + 1, hk⟩) (c : F) :=
    Subtype.ext (Units.ext (by
      rw [hc, coe_shortTorus (unitaryInvolution F 2 k) (unitaryInvolution_involutive hF)
        _ _ _ (lowIdx_ne_rev (n := 5) ⟨0 + 1, hk⟩ 0) c.ne_zero]
      rfl))
  rw [hg]
  exact shortTorus_mem (F := F) (k := k) hF hk (c : F)

private theorem levelTorus_one_le_oct_four_sup_neg_four
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (ζ : traceZero (unitaryInvolution F 2 k)) (hζ : (ζ : F) ≠ 0) :
    levelTorus (unitaryInvolution F 2 k) (1 : Fin (5 / 2)) ≤
      un5Oct (F := F) (p := 2) (f := k) hF 4 ⊔
        un5Oct (F := F) (p := 2) (f := k) hF (-4) := by
  have hk : ¬(1 : Fin (5 / 2)).val + 1 < 5 / 2 := by decide
  have hn : ¬Even (5 : ℕ) := by decide
  have hnorm : ∀ x, unitaryInvolution F 2 k x = x →
      ∃ a, unitaryInvolution F 2 k a * a = x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, by simp⟩
    · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0
  rw [root4_eq (F := F) (k := k) hF, rootneg4_eq (F := F) (k := k) hF]
  unfold levelTorus
  rw [dite_eq_right hk, ite_eq_right hn, Subgroup.closure_le]
  rintro g ⟨t, hg⟩
  obtain ⟨w, hw, hwm⟩ := exists_heisGen_mem_rankOne
    (σ := unitaryInvolution F 2 k) (hσ := unitaryInvolution_involutive hF)
    hζ hnorm hk hn t
  have hgw : g = w := Subtype.ext (Units.ext (hg.trans hwm.symm))
  rw [hgw]
  simpa [CFSG.LieType.CurtisTits.rankOne] using hw

theorem un5BorelResidualSplit : Un5BorelResidualSplit := by
  intro k F _ _ _ _ hF ζ hζfact hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := un5Proj (F := F) (f := k)
  let D := un5System hF ζ
  let P1 := D.P₁
  let P2 := D.P₂
  let X := CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 ⊓ P2
  let Y := CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 ⊓ P1
  have hU2 : IsPGroup 2 D.U := (isSylowTwoOf_un5System hF ζ).2.1
  have hUB : D.U ≤ D.B := D.U_le_B
  have hBP1 : D.B ≤ P1 := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_true] using
      CFSG.Quasithin.H13.F431.BN.B_le_P D true
  have hBP2 : D.B ≤ P2 := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using
      CFSG.Quasithin.H13.F431.BN.B_le_P D false
  have hU_P1 : D.U ≤ P1 := hUB.trans hBP1
  have hU_P2 : D.U ≤ P2 := hUB.trans hBP2
  have hU_X : D.U ≤ X := le_inf
    (le_twoPrimeResidualOf_of_isPGroup hU_P1 hU2) hU_P2
  have hU_Y : D.U ≤ Y := le_inf
    (le_twoPrimeResidualOf_of_isPGroup hU_P2 hU2) hU_P1
  have hroot1 : D.root 1 ≤ P1 :=
    (D.root_le_B (k := 1) (by norm_num) (by omega)).trans hBP1
  have hrootm1 : D.root (-1) ≤ P1 := rankTwo_root_neg_one_le_P1 D
  have hroot4 : D.root 4 ≤ P2 :=
    (D.root_le_B (k := 4) (by norm_num) (by omega)).trans hBP2
  have hrootm4 : D.root (-4) ≤ P2 := by
    have h := rankTwo_root_neg_n_le_P2 D
    simpa using h
  have hU1 : IsPGroup 2 (un5Oct (F := F) (p := 2) (f := k) hF 1) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots
        (octRootB_mem_roots' (isRoot_four_of (by norm_num) (by norm_num))))
  have hUm1 : IsPGroup 2 (un5Oct (F := F) (p := 2) (f := k) hF (-1)) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots
        (octRootB_mem_roots' (isRoot_four_of_neg (by norm_num) (by norm_num))))
  have hU4 : IsPGroup 2 (un5Oct (F := F) (p := 2) (f := k) hF 4) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots
        (octRootB_mem_roots' (isRoot_four_of (by norm_num) (by norm_num))))
  have hUm4 : IsPGroup 2 (un5Oct (F := F) (p := 2) (f := k) hF (-4)) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots
        (octRootB_mem_roots' (isRoot_four_of_neg (by norm_num) (by norm_num))))
  have hroot1_2 : IsPGroup 2 (D.root 1) := by
    show IsPGroup 2 ((un5Oct (F := F) (p := 2) (f := k) hF 1).map π)
    exact hU1.map π
  have hrootm1_2 : IsPGroup 2 (D.root (-1)) := by
    show IsPGroup 2 ((un5Oct (F := F) (p := 2) (f := k) hF (-1)).map π)
    exact hUm1.map π
  have hroot4_2 : IsPGroup 2 (D.root 4) := by
    show IsPGroup 2 ((un5Oct (F := F) (p := 2) (f := k) hF 4).map π)
    exact hU4.map π
  have hrootm4_2 : IsPGroup 2 (D.root (-4)) := by
    show IsPGroup 2 ((un5Oct (F := F) (p := 2) (f := k) hF (-4)).map π)
    exact hUm4.map π
  have hroot1_O2 : D.root 1 ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 :=
    le_twoPrimeResidualOf_of_isPGroup hroot1 hroot1_2
  have hrootm1_O2 : D.root (-1) ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 :=
    le_twoPrimeResidualOf_of_isPGroup hrootm1 hrootm1_2
  have hroot4_O2 : D.root 4 ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 :=
    le_twoPrimeResidualOf_of_isPGroup hroot4 hroot4_2
  have hrootm4_O2 : D.root (-4) ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 :=
    le_twoPrimeResidualOf_of_isPGroup hrootm4 hrootm4_2
  have hT0_map : (levelTorus (unitaryInvolution F 2 k) (0 : Fin (5 / 2))).map π ≤
      D.root 1 ⊔ D.root (-1) := by
    refine (Subgroup.map_mono
      (levelTorus_zero_le_oct_one_sup_neg_one (F := F) (k := k) hF)).trans ?_
    rw [Subgroup.map_sup]
    exact le_rfl
  have hT0_O2 : (levelTorus (unitaryInvolution F 2 k) (0 : Fin (5 / 2))).map π ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 :=
    hT0_map.trans (sup_le hroot1_O2 hrootm1_O2)
  have hBN : D.B ⊓ D.N =
      (unT (F := F) (p := 2) (f := k) 5).map (un5Proj (F := F) (f := k)) :=
    un5System_B_inf_N hF ζ
  have hT0_B : (levelTorus (unitaryInvolution F 2 k) (0 : Fin (5 / 2))).map π ≤ D.B := by
    refine (Subgroup.map_mono
      (le_iSup (fun i : Fin (5 / 2) => levelTorus (unitaryInvolution F 2 k) i) 0)).trans ?_
    simp only [π]
    change Subgroup.map (un5Proj (F := F) (f := k))
      (unT (F := F) (p := 2) (f := k) 5) ≤ D.B
    rw [← hBN]
    exact inf_le_left
  have hT0_P2 : (levelTorus (unitaryInvolution F 2 k) (0 : Fin (5 / 2))).map π ≤ P2 :=
    hT0_B.trans hBP2
  have hT1_map : (levelTorus (unitaryInvolution F 2 k) (1 : Fin (5 / 2))).map π ≤
      D.root 4 ⊔ D.root (-4) := by
    refine (Subgroup.map_mono
      (levelTorus_one_le_oct_four_sup_neg_four (F := F) (k := k) hF ζ
        (Fact.out : ((ζ : F) ≠ 0)))).trans ?_
    rw [Subgroup.map_sup]
    exact le_rfl
  have hT1_O2 : (levelTorus (unitaryInvolution F 2 k) (1 : Fin (5 / 2))).map π ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 :=
    hT1_map.trans (sup_le hroot4_O2 hrootm4_O2)
  have hT1_B : (levelTorus (unitaryInvolution F 2 k) (1 : Fin (5 / 2))).map π ≤ D.B := by
    refine (Subgroup.map_mono
      (le_iSup (fun i : Fin (5 / 2) => levelTorus (unitaryInvolution F 2 k) i) 1)).trans ?_
    simp only [π]
    change Subgroup.map (un5Proj (F := F) (f := k))
      (unT (F := F) (p := 2) (f := k) 5) ≤ D.B
    rw [← hBN]
    exact inf_le_left
  have hT1_P1 : (levelTorus (unitaryInvolution F 2 k) (1 : Fin (5 / 2))).map π ≤ P1 :=
    hT1_B.trans hBP1
  have hH : D.B ⊓ D.N ≤ X ⊔ Y := by
    rw [hBN]
    rw [show unT (F := F) (p := 2) (f := k) 5 =
      ⨆ i : Fin (5 / 2), levelTorus (unitaryInvolution F 2 k) i from rfl,
      Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact (le_inf hT0_O2 hT0_P2).trans le_sup_left
    · exact (le_inf hT1_O2 hT1_P1).trans le_sup_right
  have hBsplit : D.B ≤ (D.B ⊓ D.N) ⊔ D.U := by
    rw [← SetLike.coe_subset_coe, D.isSplit.2]
    exact Subgroup.mul_subset (fun x hx => Subgroup.mem_sup_left hx)
      (fun x hx => Subgroup.mem_sup_right hx)
  have hB : D.B ≤ X ⊔ Y :=
    hBsplit.trans (sup_le hH (hU_X.trans le_sup_left))
  change D.B ≤ X ⊔ Y
  exact hB

end CFSG.Quasithin.Stroth
