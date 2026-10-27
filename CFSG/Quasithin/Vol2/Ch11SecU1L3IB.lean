module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Syl
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.E1
open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def rowU (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) :=
  (lineBlk p).ker.map (linePar p).subtype

@[expose] noncomputable def colU (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) :=
  (rowU p).map (slTau p).toMonoidHom

theorem mem_rowU_iff {g : SL(3, ZMod p)} : g ∈ rowU p ↔ ∃ s : Fin 2 → ZMod p, g = uMat s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (lineBlk_eq_one_iff y).mp hy
  · rintro ⟨s, rfl⟩
    exact ⟨⟨uMat s, uMat_mem_linePar s⟩, (lineBlk_eq_one_iff _).mpr ⟨s, rfl⟩, rfl⟩

theorem linePar_le_normalizer_rowU : linePar p ≤ Subgroup.normalizer (rowU p : Set _) := by
  have hle : rowU p ≤ linePar p := Subgroup.map_subtype_le _
  have hsub : (rowU p).subgroupOf (linePar p) = (lineBlk p).ker :=
    Subgroup.comap_map_eq_self_of_injective (linePar p).subtype_injective _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp ?_
  rw [hsub]
  infer_instance

theorem leviBlock_le_normalizer_rowU : leviBlock p ≤ Subgroup.normalizer (rowU p : Set _) :=
  leviBlock_le_linePar.trans linePar_le_normalizer_rowU

theorem mem_colU_iff {g : SL(3, ZMod p)} : g ∈ colU p ↔ slTau p g ∈ rowU p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [slTau_slTau] using hx
  · intro h
    exact ⟨slTau p g, h, slTau_slTau g⟩

theorem leviBlock_le_normalizer_colU : leviBlock p ≤ Subgroup.normalizer (colU p : Set _) := by
  intro b hb
  have hb' := leviBlock_le_normalizer_rowU (slTau_mem_leviBlock hb)
  rw [Subgroup.mem_normalizer_iff] at hb' ⊢
  intro x
  rw [mem_colU_iff, mem_colU_iff, map_mul, map_mul, map_inv]
  exact hb' (slTau p x)

theorem rowU_comm {x y : SL(3, ZMod p)} (hx : x ∈ rowU p) (hy : y ∈ rowU p) : x * y = y * x := by
  obtain ⟨s, rfl⟩ := mem_rowU_iff.mp hx
  obtain ⟨t, rfl⟩ := mem_rowU_iff.mp hy
  exact uMat_comm s t

theorem colU_comm {x y : SL(3, ZMod p)} (hx : x ∈ colU p) (hy : y ∈ colU p) : x * y = y * x := by
  apply (slTau p).injective
  rw [map_mul, map_mul]
  exact rowU_comm (mem_colU_iff.mp hx) (mem_colU_iff.mp hy)

theorem transvection_two_zero_mem (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ rowU p := by
  refine mem_rowU_iff.mpr ⟨![c, 0], Subtype.ext ?_⟩
  rw [CFSG.LinearGroups.coe_transvection, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem transvection_two_one_mem (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ rowU p := by
  refine mem_rowU_iff.mpr ⟨![0, c], Subtype.ext ?_⟩
  rw [CFSG.LinearGroups.coe_transvection, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem transvection_zero_two_mem (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ colU p := by
  refine mem_colU_iff.mpr (mem_rowU_iff.mpr ⟨![-c, 0], Subtype.ext ?_⟩)
  rw [slTau_apply, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.coe_transpose, CFSG.LinearGroups.coe_transvection, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem transvection_one_two_mem (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ colU p := by
  refine mem_colU_iff.mpr (mem_rowU_iff.mpr ⟨![0, -c], Subtype.ext ?_⟩)
  rw [slTau_apply, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.coe_transpose, CFSG.LinearGroups.coe_transvection, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sup_rowU_colU : rowU p ⊔ colU p = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3)
    (K := ZMod p), Subgroup.closure_le]
  have hR : ∀ {x}, x ∈ rowU p → x ∈ rowU p ⊔ colU p := fun hx => Subgroup.mem_sup_left hx
  have hC : ∀ {x}, x ∈ colU p → x ∈ rowU p ⊔ colU p := fun hx => Subgroup.mem_sup_right hx
  have hcomm : ∀ {x y}, x ∈ rowU p ⊔ colU p → y ∈ rowU p ⊔ colU p →
      ⁅x, y⁆ ∈ rowU p ⊔ colU p := fun hx hy => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  ·
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 2 by decide) (show (2 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 1 by decide) c 1
    rw [mul_one] at h
    exact h ▸ hcomm (hC (transvection_zero_two_mem c)) (hR (transvection_two_one_mem 1))
  · exact hC (transvection_zero_two_mem c)
  ·
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (1 : Fin 3) ≠ 2 by decide) (show (2 : Fin 3) ≠ 0 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) c 1
    rw [mul_one] at h
    exact h ▸ hcomm (hC (transvection_one_two_mem c)) (hR (transvection_two_zero_mem 1))
  · exact absurd rfl hij
  · exact hC (transvection_one_two_mem c)
  · exact hR (transvection_two_zero_mem c)
  · exact hR (transvection_two_one_mem c)
  · exact absurd rfl hij

theorem isSolvable_map_rowU : Group.IsSolvable ↥((rowU p).map (piL p)) :=
  Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, rowU_comm hx hy]

theorem isSolvable_map_colU : Group.IsSolvable ↥((colU p).map (piL p)) :=
  Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, colU_comm hx hy]

theorem leviC_le_normalizer_rowU :
    leviC p ≤ Subgroup.normalizer ((rowU p).map (piL p) : Set (PSL3 p)) :=
  (Subgroup.map_mono leviBlock_le_normalizer_rowU).trans (Subgroup.le_normalizer_map _)

theorem leviC_le_normalizer_colU :
    leviC p ≤ Subgroup.normalizer ((colU p).map (piL p) : Set (PSL3 p)) :=
  (Subgroup.map_mono leviBlock_le_normalizer_colU).trans (Subgroup.le_normalizer_map _)

theorem nParam_psl3_le_one (hp2 : p ≠ 2) : nParam (⊤ : Subgroup (PSL3 p)) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, -, -, hU, hUB, -⟩ := exists_special_sylow hp2
  have hUs : Group.IsSolvable ↥U := by
    have := hU.2.1.isNilpotent
    infer_instance
  refine nParam_le_one_of_solvable_pair (T := U) hU le_sup_right le_sup_right
    (CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer
      (hUB.trans leviC_le_normalizer_rowU) isSolvable_map_rowU hUs)
    (CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer
      (hUB.trans leviC_le_normalizer_colU) isSolvable_map_colU hUs) ?_
  refine eq_top_iff.mpr (le_trans ?_ (sup_le_sup le_sup_left le_sup_left))
  rw [← Subgroup.map_sup, sup_rowU_colU, Subgroup.map_top_of_surjective _ piL_surjective]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
