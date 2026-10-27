module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL43Mat
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Item434RemL43 (PSL43 projSLEquivPSL43
  not_three_dvd_card_outer_PSL43)

theorem l43_card_Q : Nat.card (projUnitriangular 4 (ZMod 3)) = 3 ^ 6 := by
  rw [card_projUnitriangular (K := ZMod 3), Nat.card_zmod] <;> norm_num

theorem l43_not_dvd_PSL43 : ¬ 3 ^ (6 + 1) ∣ Nat.card PSL43 := by
  intro h
  have hsplit : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) =
      Nat.card PSL43 * Nat.card (scalars 4 (ZMod 3)) :=
    (scalars 4 (ZMod 3)).card_eq_card_quotient_mul_card_subgroup
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) = 3 ^ 6 * 16640 := by
    rw [card_SL_eq (K := ZMod 3) (by norm_num : 1 ≤ 4), Nat.card_zmod]
    first
    | decide
    | rfl
    | norm_num [Finset.prod_Icc_succ_top]
  have h3 : 3 ^ (6 + 1) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) := by
    rw [hsplit]
    exact Dvd.dvd.mul_right h _
  rw [hSL] at h3
  norm_num at h3

theorem l43RG01_val : ((l43RG01 : l43SL) : l43Mat) = l43G01 := rfl

theorem l43RG12_val : ((l43RG12 : l43SL) : l43Mat) = l43G12 := rfl

theorem l43RG23_val : ((l43RG23 : l43SL) : l43Mat) = l43G23 := rfl

theorem l43_hw : ∀ u ∈ projUnitriangular 4 (ZMod 3), orderOf u = 3 →
    (∀ q ∈ projUnitriangular 4 (ZMod 3), q * u = u * q) →
    ∃ g : PSL43, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  intro u hu huo hcomm
  obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hu
  have hpow : proj 4 (ZMod 3) M ^ 3 = 1 := by
    have := pow_orderOf_eq_one (proj 4 (ZMod 3) M)
    rwa [huo] at this
  have hM3 : M ^ 3 = 1 := by
    have h1 : proj 4 (ZMod 3) (M ^ 3) = 1 := by rw [map_pow, hpow]
    have h3 : M ^ 3 ∈ unitriangular 4 (ZMod 3) ⊓ scalars 4 (ZMod 3) :=
      ⟨(unitriangular 4 (ZMod 3)).pow_mem hM 3, proj_eq_one_iff.mp h1⟩
    rw [unitriangular_inf_scalars, Subgroup.mem_bot] at h3
    exact h3
  have hcen : ∀ h ∈ unitriangular 4 (ZMod 3), h * M = M * h := fun h hh =>
    Item434RemL43.mul_comm_of_proj_mul_comm hM3
      (hcomm _ (Subgroup.mem_map_of_mem (proj 4 (ZMod 3)) hh))
  have hR01 : l43G01 * (M : l43Mat) = (M : l43Mat) * l43G01 := by
    have h := congrArg (fun A : l43SL => (A : l43Mat)) (hcen _ l43RG01_mem)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, l43RG01_val] using h
  have hR12 : l43G12 * (M : l43Mat) = (M : l43Mat) * l43G12 := by
    have h := congrArg (fun A : l43SL => (A : l43Mat)) (hcen _ l43RG12_mem)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, l43RG12_val] using h
  have hR23 : l43G23 * (M : l43Mat) = (M : l43Mat) * l43G23 := by
    have h := congrArg (fun A : l43SL => (A : l43Mat)) (hcen _ l43RG23_mem)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, l43RG23_val] using h
  obtain ⟨h01, h02, h12, h13, h23⟩ := upper_of_comm_roots (M : l43Mat) hR01 hR12 hR23
  have hlow : ∀ i j : Fin 4, j < i → (M : l43Mat) i j = 0 := (mem_unitriangular.mp hM).1
  have hdiag : ∀ i : Fin 4, (M : l43Mat) i i = 1 := (mem_unitriangular.mp hM).2
  obtain ⟨c, hMc⟩ : ∃ c : ZMod 3, (M : l43Mat) = l43Z c :=
    ⟨(M : l43Mat) 0 3, eq_l43Z_of (M : l43Mat) (hlow 1 0 (by decide)) (hlow 2 0 (by decide))
      (hlow 2 1 (by decide)) (hlow 3 0 (by decide)) (hlow 3 1 (by decide))
      (hlow 3 2 (by decide)) (hdiag 0) (hdiag 1) (hdiag 2) (hdiag 3) h01 h02 h12 h13 h23⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hM1 : M = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one, hMc, l43Z_zero])
    rw [hM1, map_one, orderOf_one] at huo
    exact absurd huo (by decide)
  have hSS : l43SSL * l43SiSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, l43SSL_val, l43SiSL_val,
      Matrix.SpecialLinearGroup.coe_one]
    exact l43S_mul_Si
  have hinv : l43SSL⁻¹ = l43SiSL := inv_eq_of_mul_eq_one_right hSS
  have hconjSL : l43SSL * M * l43SSL⁻¹ = l43NSL c := by
    rw [hinv]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, l43SSL_val,
      l43SiSL_val, hMc, l43NSL_val]
    exact l43S_mul_Z c
  have hNM : l43NSL c * M = M * l43NSL c := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hMc, l43NSL_val]
    exact l43N_mul_Z c
  have hkey : proj 4 (ZMod 3) l43SSL * proj 4 (ZMod 3) M * (proj 4 (ZMod 3) l43SSL)⁻¹ =
      proj 4 (ZMod 3) (l43NSL c) := by
    rw [← hconjSL]
    simp only [map_mul, map_inv]
  refine ⟨proj 4 (ZMod 3) l43SSL, ?_, ?_⟩
  · rw [hkey, ← map_mul, ← map_mul, hNM]
  · intro hmem
    rw [hkey] at hmem
    rcases mem_zpowers_cases_of_pow_three hpow hmem with h1 | h2 | h3
    · have hN0 := scalar_entry_zero _ (proj_eq_one_iff.mp h1)
      rw [l43NSL_val] at hN0
      simp [l43N] at hN0
      exact hc0 ((by decide : ∀ x : ZMod 3, -x = 0 → x = 0) c hN0)
    · have hs := proj_eq_proj_iff.mp h2
      rw [inv_l43NSL] at hs
      have hN0 := scalar_entry_zero _ hs
      rw [Matrix.SpecialLinearGroup.coe_mul, l43NSL_val, hMc] at hN0
      simp [l43N, l43Z, Matrix.mul_apply, Fin.sum_univ_four] at hN0
      exact hc0 ((by decide : ∀ x : ZMod 3, - -x = 0 → x = 0) c hN0)
    · have hs : proj 4 (ZMod 3) (l43NSL c * M) = 1 := by
        rw [map_mul, h3, inv_mul_cancel]
      have hN0 := scalar_entry_zero _ (proj_eq_one_iff.mp hs)
      rw [Matrix.SpecialLinearGroup.coe_mul, l43NSL_val, hMc] at hN0
      simp [l43N, l43Z, Matrix.mul_apply, Fin.sum_univ_four] at hN0
      exact hc0 ((by decide : ∀ x : ZMod 3, -x = 0 → x = 0) c hN0)

theorem l43_listRow_PSL43 : ListRow PSL43 :=
  listRow_of_sylow_center 6 (projUnitriangular 4 (ZMod 3)) l43_card_Q l43_not_dvd_PSL43 l43_hw

theorem l43_listRow_proj [Finite (projSL 4 (GaloisField 3 1))] :
    ListRow (projSL 4 (GaloisField 3 1)) :=
  ListRow.of_mulEquiv projSLEquivPSL43.symm l43_listRow_PSL43

theorem l43_outerRow_proj [Finite (projSL 4 (GaloisField 3 1))] :
    OuterRow (projSL 4 (GaloisField 3 1)) :=
  OuterRow.of_mulEquiv projSLEquivPSL43.symm
    (outerRow_of_not_three_dvd_outer not_three_dvd_card_outer_PSL43)

theorem row_l43 : RowOf (projSL 4 (GaloisField 3 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSL 4 (GaloisField 3 1)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv e.symm ⟨l43_listRow_proj, l43_outerRow_proj⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
