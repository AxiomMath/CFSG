module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddGroup
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReducePSL
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Subgroup

theorem orderOf_le_of_outer_involution_psl_even {J : Type} [Group J] [Finite J] {f : ℕ}
    (hq : 2 ^ f % 3 = 2) (hL : LieModel J .PSL 3 2 f) {α : MulAut J} (hα : α ^ 2 = 1)
    (hαout : α ∉ (MulAut.conj : J →* MulAut J).range) {y : J} (hy : α y = y) :
    orderOf y ≤ 2 ^ f + 1 := by
  classical
  obtain ⟨K, _, hFin, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  haveI : Finite K := hFin
  have hadm := hL.admissible
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fintype K := Fintype.ofFinite K
  haveI hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  have hnd : ¬ 3 ∣ Nat.card K - 1 := by omega
  have hinj : Function.Injective (LinearFlag.proj 3 K) :=
    CFSG.AGLEmbedding.ToralReduce.proj_injective_of_not_dvd hnd
  set β : MulAut (LinearFlag.projectiveSL 3 K) := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, hα, map_one]
  have hβout : β ∉ (MulAut.conj : LinearFlag.projectiveSL 3 K →* _).range := fun h =>
    hαout (CFSG.RankThree.PartTwo.Sec20.L3OddGroup.mem_range_conj_of_congr e h)
  have hfodd : Odd f :=
    CFSG.RankThree.PartTwo.Sec20.L3OddGroup.odd_of_pow_mod_three_eq_two hq
  have hnotEven : ¬ Even f := Nat.not_even_iff_odd.mpr hfodd
  obtain ⟨γ, hγ⟩ :
      ∃ γ : MulAut (LinearFlag.projectiveSL 3 K),
        β = γ * LinearFlag.dualAut 3 K * γ⁻¹ := by
    rcases CFSG.LocalAnalysis.EvenBN.LinearThree.exists_conj_canonical_of_not_mem_range
        (K := K) hf hK hβ2 hβout with ⟨hfe, -⟩ | hmid | ⟨hfe, -⟩
    · exact absurd hfe hnotEven
    · exact hmid
    · exact absurd hfe hnotEven
  set x : LinearFlag.projectiveSL 3 K := e y with hxdef
  have hβx : β x = x := by
    rw [hβdef, hxdef, CFSG.RankThree.PartTwo.Sec20.L3OddGroup.congr_apply_apply, hy]
  set z : LinearFlag.projectiveSL 3 K := (γ⁻¹ : MulAut _) x with hzdef
  have hδz : LinearFlag.dualAut 3 K z = z := by
    show LinearFlag.dualAut 3 K ((γ⁻¹ : MulAut _) x) = (γ⁻¹ : MulAut _) x
    have h1 : (γ * LinearFlag.dualAut 3 K * γ⁻¹) x = x := by rw [← hγ]; exact hβx
    have h2 := congrArg (fun w => (γ⁻¹ : MulAut (LinearFlag.projectiveSL 3 K)) w) h1
    simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h2
  obtain ⟨g, hg⟩ := LinearFlag.proj_surjective 3 K z
  have hδg : LinearFlag.dualAut 3 K (LinearFlag.proj 3 K g) = LinearFlag.proj 3 K g := by
    rw [hg]; exact hδz
  rw [LinearFlag.dualAut_proj] at hδg
  have hgt : (g⁻¹).transpose = g := hinj hδg
  set G : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL g with hGdef
  have hGinv : Matrix.GeneralLinearGroup.inverseTranspose G = G := by
    rw [hGdef, ← CFSG.ComponentClassification.CatalogueBGraphForm.toGL_slGraphAut]
    exact congrArg Matrix.SpecialLinearGroup.toGL hgt
  have hcoe : (G : Matrix (Fin 3) (Fin 3) K)ᵀ =
      ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc (G : Matrix (Fin 3) (Fin 3) K)ᵀ
        = ((Matrix.GeneralLinearGroup.inverseTranspose G : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [hGinv]
      _ = (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ)ᵀ := by
            rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := Matrix.transpose_transpose _
  have hmem : G ∈ FourGroupEvenCanonical.matrixIsometryGroup
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [FourGroupEvenCanonical.mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one,
      hcoe, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨E⟩ :=
    CFSG.ComponentClassification.RankTwoHypIIL3.nonempty_matrixIsometryGroup_one_mulEquiv_SL2
      (K := K)
  let e2 := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)
  let m : ↥(FourGroupEvenCanonical.matrixIsometryGroup
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := ⟨G, hmem⟩
  have hGle : orderOf G ≤ Nat.card K + 1 := by
    calc orderOf G = orderOf m := Subgroup.orderOf_coe m
      _ = orderOf (E m) := (MulEquiv.orderOf_eq E m).symm
      _ = orderOf (e2.symm (E m)) := (MulEquiv.orderOf_eq e2.symm (E m)).symm
      _ ≤ Nat.card K + 1 :=
        CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le K _
  calc orderOf y = orderOf x := (MulEquiv.orderOf_eq e y).symm
    _ = orderOf z := (MulEquiv.orderOf_eq (γ⁻¹ : MulAut _) x).symm
    _ = orderOf g := by rw [← hg]; exact orderOf_injective (LinearFlag.proj 3 K) hinj g
    _ = orderOf G :=
        (orderOf_injective Matrix.SpecialLinearGroup.toGL
          Matrix.SpecialLinearGroup.toGL_injective g).symm
    _ ≤ Nat.card K + 1 := hGle
    _ = 2 ^ f + 1 := by rw [hK]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
