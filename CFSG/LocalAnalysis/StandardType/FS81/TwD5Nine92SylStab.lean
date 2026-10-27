module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OE6

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem filter_normOne_card :
    (Finset.univ.filter
      (fun v : Fin 6 → ZMod 3 => v 0 = 0 ∧ ∑ i, v i ^ 2 = 1)).card = 90 := by
  decide +kernel

theorem card_normOne_coords :
    Nat.card {v : Fin 6 → ZMod 3 // v 0 = 0 ∧ ∑ i, v i ^ 2 = 1} = 90 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact filter_normOne_card

private theorem wt_eq_one_or_four (w : Fin 6 → ZMod 3) (h0 : w 0 = 0)
    (hsum : ∑ i, w i ^ 2 = 1) : wt w = 1 ∨ wt w = 4 := by
  revert w
  decide +kernel

private theorem oE6_smul_eq_mulVec (A : ↥(oE6 1)) (v : Fin 6 → ZMod 3) :
    A • v = ((A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v := by
  rw [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]

private theorem wt_single_two : wt (Pi.single 2 1 : Fin 6 → ZMod 3) = 1 := by
  simpa using wt_smul_single (k := 6) (c := (1 : ZMod 3)) one_ne_zero 2

private theorem rE6_one_mulVec_e_two :
    (rE6 1 *ᵥ (Pi.single 2 1 : Fin 6 → ZMod 3)) = ![0, -1, 0, -1, -1, -1] := by
  decide +kernel

private theorem wt_rE6_one_mulVec_e_two :
    wt (rE6 1 *ᵥ (Pi.single 2 1 : Fin 6 → ZMod 3)) = 4 := by
  rw [rE6_one_mulVec_e_two]
  decide +kernel

private theorem zero_rE6_one_mulVec_e_two :
    (rE6 1 *ᵥ (Pi.single 2 1 : Fin 6 → ZMod 3)) 0 = 0 := by
  rw [rE6_one_mulVec_e_two]
  decide

private theorem exists_spMat_mulVec_eq_fix_prod {k : ℕ} {v w : Fin k → ZMod 3} {p : Fin k}
    (hwt : wt v = wt w) (hv : v p = 0) (hw : w p = 0) :
    ∃ σ s, IsSign s ∧ σ p = p ∧ ∏ i, s i = 1 ∧ spMat σ s *ᵥ v = w := by
  classical
  obtain ⟨σ, s, hs, hσp, hmap⟩ := exists_spMat_mulVec_eq_fix hwt hv hw
  set d : ZMod 3 := ∏ i, s i with hd
  set s' : Fin k → ZMod 3 := Function.update s p (s p * d) with hs'def
  have hs_ne : ∀ i, s i ≠ 0 := by
    intro i
    rcases hs i with h | h <;> rw [h] <;> decide
  have hd_ne : d ≠ 0 := by
    rw [hd]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs_ne i
  have hs'_sign : IsSign s' := by
    intro i
    by_cases hi : i = p
    · rw [hi, hs'def, Function.update_self]
      exact eq_one_or_of_ne_zero (mul_ne_zero (hs_ne p) hd_ne)
    · rw [hs'def, Function.update_of_ne hi]
      exact hs i
  have hE : (∏ x ∈ Finset.univ.erase p, s x) * s p = d := by
    rw [hd]
    conv_rhs => rw [← Finset.insert_erase (Finset.mem_univ p)]
    rw [Finset.prod_insert (Finset.notMem_erase p Finset.univ), mul_comm]
  have hd2 : d * d = 1 := by
    rw [hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_self_of_ne_zero (hs_ne i)
  have hprod : ∏ i, s' i = 1 := by
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin k)) s' (Finset.mem_univ p)]
    have hErase : (∏ x ∈ Finset.univ.erase p, s' x) =
        ∏ x ∈ Finset.univ.erase p, s x := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [hs'def, Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [hErase, show s' p = s p * d from by rw [hs'def, Function.update_self]]
    calc (∏ x ∈ Finset.univ.erase p, s x) * (s p * d)
        = ((∏ x ∈ Finset.univ.erase p, s x) * s p) * d := by ring
      _ = d * d := by rw [hE]
      _ = 1 := hd2
  refine ⟨σ, s', hs'_sign, hσp, hprod, ?_⟩
  have hact : spMat σ s' *ᵥ v = spMat σ s *ᵥ v := by
    rw [spMat_mulVec, spMat_mulVec]
    funext i
    by_cases hi : σ.symm i = p
    · rw [hi, hs'def, Function.update_self, hv, mul_zero, mul_zero]
    · rw [hs'def, Function.update_of_ne hi]
  rw [hact, hmap]

private theorem orbit_subset_normOne :
    MulAction.orbit ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3) ⊆
      {v : Fin 6 → ZMod 3 | v 0 = 0 ∧ ∑ i, v i ^ 2 = 1} := by
  intro v hv
  rw [MulAction.mem_orbit_iff] at hv
  obtain ⟨⟨A, hA⟩, hAe⟩ := hv
  rw [oE6_smul_eq_mulVec] at hAe
  obtain ⟨hrow, hquad, -⟩ := oE6RecOut_holds 1 (Or.inl rfl)
  constructor
  · rw [← hAe, Matrix.mulVec_single_one, Matrix.col_apply]
    exact hrow A hA 2 (by decide)
  · rw [← hAe]
    rw [hquad A hA (Pi.single 2 1) (by simp)]
    rw [Finset.sum_eq_single 2]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ 2) h

private theorem normOne_subset_orbit :
    {v : Fin 6 → ZMod 3 | v 0 = 0 ∧ ∑ i, v i ^ 2 = 1} ⊆
      MulAction.orbit ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3) := by
  intro w hw
  obtain ⟨hw0, hsum⟩ := hw
  have mem_spMat : ∀ (σ : Equiv.Perm (Fin 6)) (s : Fin 6 → ZMod 3) (hs : IsSign s),
      σ 0 = 0 → ∏ i, s i = 1 → spMatGL σ s hs ∈ oE6 1 := by
    intro σ s hs hσ0 hprod
    apply Subgroup.subset_closure
    left
    exact ⟨σ, s, hs, ⟨hσ0, hprod⟩, spMatGL_val σ s hs⟩
  have mem_rE6 : rE6GL 1 det_rE6_one ∈ oE6 1 := by
    apply Subgroup.subset_closure
    right
    exact rE6GL_val 1 det_rE6_one
  rcases wt_eq_one_or_four w hw0 hsum with h1 | h4
  · obtain ⟨σ, s, hs, hσ0, hprod, hmap⟩ :=
      exists_spMat_mulVec_eq_fix_prod (v := (Pi.single 2 1 : Fin 6 → ZMod 3)) (w := w)
        (p := 0) (by rw [wt_single_two, h1]) (by simp) hw0
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨spMatGL σ s hs, mem_spMat σ s hs hσ0 hprod⟩, ?_⟩
    rw [oE6_smul_eq_mulVec, spMatGL_val, hmap]
  · obtain ⟨σ, s, hs, hσ0, hprod, hmap⟩ :=
      exists_spMat_mulVec_eq_fix_prod
        (v := (rE6 1 *ᵥ (Pi.single 2 1 : Fin 6 → ZMod 3))) (w := w) (p := 0)
        (by rw [wt_rE6_one_mulVec_e_two, h4]) zero_rE6_one_mulVec_e_two hw0
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨spMatGL σ s hs * rE6GL 1 det_rE6_one,
        (oE6 1).mul_mem (mem_spMat σ s hs hσ0 hprod) mem_rE6⟩, ?_⟩
    rw [oE6_smul_eq_mulVec, gl_mul_mulVec, spMatGL_val, rE6GL_val, hmap]

theorem orbit_oE6_one_e_two :
    MulAction.orbit ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3) =
      {v : Fin 6 → ZMod 3 | v 0 = 0 ∧ ∑ i, v i ^ 2 = 1} :=
  Set.Subset.antisymm orbit_subset_normOne normOne_subset_orbit

private theorem ncard_normOne :
    {v : Fin 6 → ZMod 3 | v 0 = 0 ∧ ∑ i, v i ^ 2 = 1}.ncard = 90 := by
  rw [← Nat.card_coe_set_eq]
  exact card_normOne_coords

theorem card_stabilizer_oE6_one_e_two (hcard : Nat.card ↥(oE6 1) = 103680) :
    Nat.card ↥(MulAction.stabilizer ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3)) = 1152 := by
  have h1 := Subgroup.card_mul_index
    (MulAction.stabilizer ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3))
  rw [MulAction.index_stabilizer, orbit_oE6_one_e_two, ncard_normOne, hcard] at h1
  omega

theorem card_le_nine_of_isPGroup_of_mulVec_e_two (hcard : Nat.card ↥(oE6 1) = 103680)
    {P : Subgroup (GL (Fin 6) (ZMod 3))} (hP : IsPGroup 3 P) (hPX : P ≤ oE6 1)
    (hfix : ∀ A ∈ P, (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 2 1 =
      Pi.single 2 1) :
    Nat.card P ≤ 9 := by
  let S : Subgroup ↥(oE6 1) :=
    MulAction.stabilizer ↥(oE6 1) (Pi.single 2 1 : Fin 6 → ZMod 3)
  have hle : P.subgroupOf (oE6 1) ≤ S := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    rw [oE6_smul_eq_mulVec]
    exact hfix (g : GL (Fin 6) (ZMod 3)) (Subgroup.mem_subgroupOf.mp hg)
  have hcardP' : Nat.card ↥(P.subgroupOf (oE6 1)) = Nat.card P := by
    have hcs := Subgroup.card_subtype (oE6 1) (P.subgroupOf (oE6 1))
    rw [Subgroup.map_subgroupOf_eq_of_le hPX] at hcs
    exact hcs.symm
  have hdvd : Nat.card P ∣ Nat.card ↥S := by
    rw [← hcardP']
    exact Subgroup.card_dvd_of_le hle
  have hS : Nat.card ↥S = 1152 := card_stabilizer_oE6_one_e_two hcard
  rw [hS] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd3 : 3 ^ k ∣ 1152 := by
    rw [← hk]
    exact hdvd
  rw [show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 from by norm_num] at hdvd3
  have hcop : Nat.Coprime (3 ^ k) (2 ^ 7) :=
    (Nat.Coprime.pow_left k (by decide : Nat.Coprime 3 2)).pow_right 7
  have h32 : 3 ^ k ∣ 3 ^ 2 := hcop.dvd_of_dvd_mul_left hdvd3
  have hk2 : k ≤ 2 :=
    (pow_dvd_pow_iff (a := (3 : ℕ)) (n := k) (m := 2) (by norm_num)
      (by simp)).mp h32
  calc Nat.card P = 3 ^ k := hk
    _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end CFSG.StandardType.FrameRoute.FS81

end
