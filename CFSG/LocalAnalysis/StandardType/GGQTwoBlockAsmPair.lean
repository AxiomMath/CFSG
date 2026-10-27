module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmChart
import CFSG.LocalAnalysis.StandardType.GGQTwoSixWin
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m N : ℕ} {G : Type} [Group G]
  {H : Subgroup G}

theorem natCard_coordBlockSU {n : ℕ} (J : Finset (Fin n)) :
    Nat.card ↥(coordBlockSU K 2 1 J) = Nat.card (Su K 2 1 J.card) := by
  change Nat.card ↥((blockSUOn K 2 1 J).range) = Nat.card (Su K 2 1 J.card)
  rw [← Subgroup.map_top (blockSUOn K 2 1 J),
    Subgroup.card_map_of_injective (blockSUOn_injective J), Subgroup.card_top]

private theorem qTwoChartPair_map_coordBlockSU {m : ℕ} (hm : 3 ≤ m) (J : Finset (Fin 3)) :
    (coordBlockSU K 2 1 J).map (blockEmb K 2 1 m 3 0 (by omega)) =
      coordBlockSU K 2 1 (J.map (Fin.castLEEmb hm)) := by
  have he : SixPoint.qTwoSixWinEmb (m := m) (k := 3) (i := 0) (by omega) =
      Fin.castLEEmb hm := by
    ext a
    simp [SixPoint.qTwoSixWinEmb]
  simpa only [he] using
    SixPoint.qTwoSix_map_win_coordBlock (K := K) (m := m) (k := 3) (i := 0) (by omega) J

theorem B12_eq_coordBlockSU :
    B12 K 2 1 = coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
  rw [B12, embSUid_two_eq_blockEmb]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨A, rfl⟩
    refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1)
      (J := ({0, 1} : Finset (Fin 3)))).mpr ?_
    intro i j hij
    rw [coe_coe_blockEmb, blockMat_apply]
    fin_cases i <;> fin_cases j <;> simp_all
  · have hcard : Nat.card ↥(coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))) =
        Nat.card ↥((blockEmb K 2 1 3 2 0 (by omega)).range) := by
      rw [natCard_coordBlockSU (J := ({0, 1} : Finset (Fin 3))),
        ← Subgroup.map_top (blockEmb K 2 1 3 2 0 (by omega)),
        Subgroup.card_map_of_injective (blockEmb_injective (by omega)), Subgroup.card_top]
      norm_num
    exact hcard.le

theorem B23_eq_coordBlockSU :
    B23 K 2 1 = coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
  rw [B23, embSUid_zero_eq_blockEmb]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨A, rfl⟩
    refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1)
      (J := ({1, 2} : Finset (Fin 3)))).mpr ?_
    intro i j hij
    rw [coe_coe_blockEmb, blockMat_apply]
    fin_cases i <;> fin_cases j <;> simp_all
  · have hcard : Nat.card ↥(coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))) =
        Nat.card ↥((blockEmb K 2 1 3 2 1 (by omega)).range) := by
      rw [natCard_coordBlockSU (J := ({1, 2} : Finset (Fin 3))),
        ← Subgroup.map_top (blockEmb K 2 1 3 2 1 (by omega)),
        Subgroup.card_map_of_injective (blockEmb_injective (by omega)), Subgroup.card_top]
      norm_num
    exact hcard.le

private theorem qTwoChartPair_coordBlockSU_three :
    coordBlockSU K 2 1 ({0, 1, 2} : Finset (Fin 3)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1)
    (J := ({0, 1, 2} : Finset (Fin 3)))).mpr ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem qTwoChartPair_ker_le_center {m : ℕ} (hm : 3 ≤ m) {φ : Su K 2 1 m →* G}
    (hker : φ.ker ≤ Subgroup.center (Su K 2 1 m))
    (hιinj : Function.Injective (blockEmb K 2 1 m 3 0 (by omega))) :
    (φ.comp (blockEmb K 2 1 m 3 0 (by omega))).ker ≤ Subgroup.center (Su K 2 1 3) := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have hx' : blockEmb K 2 1 m 3 0 (by omega) x ∈ Subgroup.center (Su K 2 1 m) := hker hx
  rw [Subgroup.mem_center_iff] at hx' ⊢
  intro y
  apply hιinj
  rw [map_mul, map_mul]
  exact hx' (blockEmb K 2 1 m 3 0 (by omega) y)

namespace QTwoCanonBlocks

theorem unitaryBlockStandardPair (B : QTwoCanonBlocks K m N H) (hmN : m ≤ N) (hm : 3 ≤ m)
    {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UnitaryBlockStandardPair K 2 1 (B.blk {a, b, c}) (B.blk {a, b}) (B.blk {b, c}) := by
  classical
  let g : Fin 3 ↪ Fin N := ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hg0 : g 0 = a := rfl
  have hg1 : g 1 = b := rfl
  have hg2 : g 2 = c := rfl
  have huniv : ({0, 1, 2} : Finset (Fin 3)).map g = {a, b, c} := by
    simp [hg0, hg1, hg2]
  have h01 : ({0, 1} : Finset (Fin 3)).map g = {a, b} := by simp [hg0, hg1]
  have h12 : ({1, 2} : Finset (Fin 3)).map g = {b, c} := by simp [hg1, hg2]
  obtain ⟨φ, hker, hφ⟩ := B.exists_chart_of_embedding hm hmN g
  let ι : Su K 2 1 3 →* Su K 2 1 m := blockEmb K 2 1 m 3 0 (by omega)
  have hιinj : Function.Injective ι := blockEmb_injective (by omega)
  have hPuniv := hφ ({0, 1, 2} : Finset (Fin 3)) (by simp) (by simp)
  have hP01 := hφ ({0, 1} : Finset (Fin 3)) (by simp) (by simp)
  have hP12 := hφ ({1, 2} : Finset (Fin 3)) (by simp) (by simp)
  have hiota : ι.range = coordBlockSU K 2 1
      (({0, 1, 2} : Finset (Fin 3)).map (Fin.castLEEmb hm)) := by
    rw [← Subgroup.map_top ι, ← qTwoChartPair_coordBlockSU_three (K := K),
      qTwoChartPair_map_coordBlockSU (K := K) (m := m) hm ({0, 1, 2} : Finset (Fin 3))]
  have hrange : (φ.comp ι).range = B.blk {a, b, c} := by
    rw [MonoidHom.range_comp, hiota, ← hPuniv, huniv]
  have hconj : (MulAut.conj ((1 : Su K 2 1 3))⁻¹).toMonoidHom = MonoidHom.id _ := by
    rw [inv_one, map_one]
    ext x
    rfl
  have hB12 : ((B12 K 2 1).map (MulAut.conj ((1 : Su K 2 1 3))⁻¹).toMonoidHom).map
      (φ.comp ι) = B.blk {a, b} := by
    rw [hconj, Subgroup.map_id, B12_eq_coordBlockSU, ← Subgroup.map_map,
      qTwoChartPair_map_coordBlockSU (K := K) (m := m) hm ({0, 1} : Finset (Fin 3)),
      ← hP01, h01]
  have hB23 : ((B23 K 2 1).map (MulAut.conj ((1 : Su K 2 1 3))⁻¹).toMonoidHom).map
      (φ.comp ι) = B.blk {b, c} := by
    rw [hconj, Subgroup.map_id, B23_eq_coordBlockSU, ← Subgroup.map_map,
      qTwoChartPair_map_coordBlockSU (K := K) (m := m) hm ({1, 2} : Finset (Fin 3)),
      ← hP12, h12]
  refine ⟨φ.comp ι, 1, hrange, qTwoChartPair_ker_le_center hm hker hιinj, Or.inl ⟨hB12, hB23⟩⟩

end QTwoCanonBlocks

end CFSG.StandardType.QTwo

end
