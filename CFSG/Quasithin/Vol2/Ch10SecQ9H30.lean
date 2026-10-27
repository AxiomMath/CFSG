module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H25
public import CFSG.Quasithin.Vol2.Ch10SecQ9H27

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem sl1_eq_one : ∀ g : Matrix.SpecialLinearGroup (Fin 1) (ZMod 2), g = 1 := by decide

theorem topB_eq_one_of_one (g : ↥(stabStd 1 k)) :
    topB ((g : Matrix.SpecialLinearGroup (Fin (1 + k)) (ZMod 2)) :
      Matrix (Fin (1 + k)) (Fin (1 + k)) (ZMod 2)) = 1 :=
  congrArg Subtype.val (sl1_eq_one (topH 1 k g))

theorem botB_eq_one_of_one (g : ↥(stabStd m 1)) :
    botB ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 :=
  congrArg Subtype.val (sl1_eq_one (botH m 1 g))

theorem mem_pCore_iff {G : Type*} [Group G] {X : Subgroup G} (w : ↥X) :
    w ∈ CFSG.pCore 2 ↥X ↔ w.1 ∈ o2G X := by
  refine ⟨fun h => ⟨w, h, rfl⟩, fun ⟨w', hw', h⟩ => ?_⟩
  rwa [show w = w' from Subtype.ext h.symm]

theorem exists_invStd_four {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (φ : ↥X →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hconj : ∀ u ∈ uniSL 4, ∀ x : ↥X, ∃ x' : ↥X, φ x' = u * φ x * u⁻¹ ∧
      (x ∈ CFSG.pCore 2 ↥X → x' ∈ CFSG.pCore 2 ↥X)) :
    ∃ m', 1 ≤ m' ∧ m' < 4 ∧ InvStd φ.range m' := by
  have hU1 : uniSL 4 ≤ Subgroup.normalizer
      (φ.range : Set (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) := by
    refine le_normalizer_of_conj ?_
    rintro u hu _ ⟨x, rfl⟩
    obtain ⟨x', hx', -⟩ := hconj u hu x
    exact ⟨x', hx'⟩
  have hU2 : uniSL 4 ≤ Subgroup.normalizer (((CFSG.pCore 2 ↥X).map φ :
      Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :
        Set (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) := by
    refine le_normalizer_of_conj ?_
    rintro u hu _ ⟨x, hxP, rfl⟩
    obtain ⟨x', hx', hP⟩ := hconj u hu x
    exact ⟨x', hP hxP, hx'⟩
  have hUp : IsPGroup 2 (uniSL 4) :=
    IsPGroup.of_card (n := 6) (by rw [card_uniSL_four]; norm_num)
  obtain ⟨A, hAp, hA1, hXA, hUA⟩ :=
    exists_twoSubgroup e φ hφ hUp (by rw [card_uniSL_four]; norm_num) hU1 hU2
  exact exists_invStd (by norm_num) hAp hA1 hXA fun i j h =>
    hUA (trvE_mem_uniSL i j (by rw [Fin.lt_def]; omega))

theorem mem_stabStd_of_normalizer {X : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + k)) (ZMod 2))}
    (hX : X ≤ stabStd 3 k) (himg : (X.subgroupOf (stabStd 3 k)).map (topH 3 k) = ⊤)
    (hbot : ∀ x : ↥(stabStd 3 k), x.1 ∈ X → botH 3 k x = 1)
    {y : Matrix.SpecialLinearGroup (Fin (3 + k)) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin (3 + k)) (ZMod 2)))) :
    y ∈ stabStd 3 k := by
  refine presStd_of_smul_mem fun j => ?_
  obtain ⟨j', hj'⟩ : ∃ j' : Fin 3, j ≠ j' := ⟨j + 1, by fin_cases j <;> decide⟩
  have hg : trvE j j' hj' ∈ (X.subgroupOf (stabStd 3 k)).map (topH 3 k) := by
    rw [himg]; trivial
  obtain ⟨x, hx, hxt⟩ := hg
  have hxX : x.1 ∈ X := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨w, hw⟩ : ∃ w : Fin (3 + k) → ZMod 2, w = Pi.single (Fin.castAdd k j') 1 := ⟨_, rfl⟩
  have hej : Pi.single (Fin.castAdd k j) (1 : ZMod 2) = x.1 • w + w := by
    rw [hw, smul_single_of_topH hj' hxt, add_add_cancel_vec]
  have hz : y * x.1 * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hyN _).mp hxX
  rw [hej, smul_add, show y • x.1 • w = (y * x.1 * y⁻¹) • y • w by
    rw [smul_smul, smul_smul, inv_mul_cancel_right]]
  obtain ⟨z, hzd⟩ : ∃ z : ↥(stabStd 3 k), z.1 = y * x.1 * y⁻¹ := ⟨⟨_, hX hz⟩, rfl⟩
  have hb1 := congrArg Subtype.val (hbot z (hzd ▸ hz))
  rw [coe_botH, hzd] at hb1
  exact smul_add_mem_of_botB_one (hX hz) hb1 _

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
