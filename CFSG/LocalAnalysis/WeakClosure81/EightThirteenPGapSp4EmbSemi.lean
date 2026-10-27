module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbDef
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbSemiAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem sp4_emb_semi {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (b : F) (hb : b ≠ 0)
    {A : Subgroup (StatedSp 2 F)} (hA : ∀ g, g ∈ A ↔ ∃ s : F, g = sp4Z s (b * s ^ 2)) :
    Sp4Sl2Emb A := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  let hb' : StatedSp 2 F := wcgapesHb b hb
  let ι : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 2 F :=
    (MulAut.conj hb').toMonoidHom.comp wcgapesIota1Hom
  have hmap : (unitriangular 2 F).map ι =
      ((unitriangular 2 F).map wcgapesIota1Hom).map (MulAut.conj hb').toMonoidHom := by
    dsimp only [ι]
    rw [Subgroup.map_map]
  refine ⟨ι, ?_, ?_, ?_⟩
  · intro x y hxy
    apply wcgapesIota1_injective hF
    have h2 := (MulAut.conj hb').injective (by simpa [ι] using hxy)
    simpa [wcgapesIota1Hom] using h2
  · ext g
    rw [hA, hmap]
    constructor
    · rintro ⟨s, rfl⟩
      refine Subgroup.mem_map.mpr ⟨sp4Z s (s ^ 2), ?_, ?_⟩
      · rw [wcgapes_mem_map_unitriangular hF]; exact ⟨s, rfl⟩
      · change hb' * sp4Z s (s ^ 2) * hb'⁻¹ = sp4Z s (b * s ^ 2)
        exact wcgapes_conj_sp4Z b hb s
    · intro hg
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
      rw [wcgapes_mem_map_unitriangular hF] at hx
      obtain ⟨s, rfl⟩ := hx
      refine ⟨s, ?_⟩
      rw [← hxg]
      change hb' * sp4Z s (s ^ 2) * hb'⁻¹ = sp4Z s (b * s ^ 2)
      exact wcgapes_conj_sp4Z b hb s
  · intro l
    have hB : borelSubgroup 2 F ≤ normalizer (unipotent 2 F : Set (StatedSp 2 F)) :=
      (normal_subgroupOf_iff_le_normalizer unipotent_le_borelSubgroup).mp
        unipotent_subgroupOf_borelSubgroup_normal
    have hbB : hb' ∈ borelSubgroup 2 F :=
      mem_borelSubgroup_of_coe_eq_blockMat (A := !![1, 0; 0, b]) (C := 0)
        (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
        (by
          rw [Matrix.det_fin_two_of]
          simpa using isUnit_iff_ne_zero.mpr hb)
        (by rw [wcgapesHb_coe_blockMat])
    have hXB : wcgapesIota1 (slTwoDiag l) ∈ borelSubgroup 2 F :=
      mem_borelSubgroup_of_coe_eq_blockMat (A := !![(l : F) ^ 2, 0; 0, 1]) (C := 0)
        (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
        (by
          rw [Matrix.det_fin_two_of]
          simp only [mul_one, mul_zero, sub_zero]
          exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (Units.ne_zero l)))
        (by rw [wcgapesIota1_coe, wcgapesM_diag])
    show ((MulAut.conj hb') (wcgapesIota1Hom (slTwoDiag l)) : StatedSp 2 F) ∈
      normalizer (unipotent 2 F : Set (StatedSp 2 F))
    rw [MulAut.conj_apply]
    exact (normalizer (unipotent 2 F : Set (StatedSp 2 F))).mul_mem
      ((normalizer _).mul_mem (hB hbB) (hB hXB)) ((normalizer _).inv_mem (hB hbB))

end CFSG.LocalAnalysis.WeakClosure81

end
