module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeSpecial
import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section UniCubeIsComp

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator

private theorem uni_cube_eigBlock_isComponent_aux {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg n K q)} (hδ : IsConjBy d δ') {μ : K} (hμ : μ ^ 3 = 1) (hQS : CubeBlockQS q d μ) :
    CFSG.Assembly.IsComponentOf (eigBlock q d μ) (ggAutFixedSubgroup δ') := by
  classical
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  let h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  have hd' : d ∈ primeFormUnitary h (idGram K n) := uni_cube_mem_primeFormUnitary h rfl hd
  have H : UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin d) :=
    uni_cube_unitaryPrimaryData h hd' hd3
  have hn1 : 1 ≤ n := by omega
  have hk2 : 2 ≤ Module.finrank K (cubeEigen d μ) := by
    rcases hQS with ⟨h2, _⟩ | h4 <;> omega
  have htoLin : (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K)) =
      Matrix.toLin' (d : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_toLin]
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K)) μ := by
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hk : 2 ≤ Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K)) μ) := hk2
    rw [hbot] at hk
    simp at hk
  have hmem' : (Polynomial.X - Polynomial.C μ : Polynomial K) ∈
      CFSG.RankThree.PartOne.KCPrimary.primaryFactors
        (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K)) :=
    CFSG.RankThree.PartOne.KCUnitaryScalar.X_sub_C_mem_primaryFactors heig
  have hmem : (Polynomial.X - Polynomial.C μ : Polynomial K) ∈
      CFSG.RankThree.PartOne.KCPrimary.primaryFactors
        (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K)) := by
    rw [htoLin]
    exact hmem'
  have hcomp_eq : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K))
        (Polynomial.X - Polynomial.C μ) = cubeEigen d μ := by
    have h1 : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
          (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K))
          (Polynomial.X - Polynomial.C μ) =
        Module.End.eigenspace (↑(Matrix.GeneralLinearGroup.toLin d)) μ := by
      ext v
      rw [CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C,
        Module.End.mem_eigenspace_iff]
    rw [h1, htoLin]
  have hm : 2 ≤ Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
      (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K))
      (Polynomial.X - Polynomial.C μ)) := by
    rw [hcomp_eq]
    exact hk2
  have hexc : (Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (↑(Matrix.GeneralLinearGroup.toLin d) : Module.End K (Fin n → K))
        (Polynomial.X - Polynomial.C μ)), 2 ^ f) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
    rw [hcomp_eq]
    have hq4 : 4 ≤ 2 ^ f ∨ 4 ≤ Module.finrank K (cubeEigen d μ) := by
      rcases hQS with ⟨_, h4⟩ | h4
      · exact Or.inl h4
      · exact Or.inr h4
    intro hmem2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hq4 with h4q | h4k
    · rcases hmem2 with ⟨hk1, hq1⟩ | ⟨hk1, hq1⟩ | ⟨hk1, hq1⟩ <;> omega
    · rcases hmem2 with ⟨hk1, _⟩ | ⟨hk1, _⟩ | ⟨hk1, _⟩ <;> omega
  have hgood : IsGoodBlock h (Matrix.GeneralLinearGroup.toLin d)
      ⟨Polynomial.X - Polynomial.C μ, hmem⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryScalar.isGoodBlock_X_sub_C
      (x := Matrix.GeneralLinearGroup.toLin d) hmem hm hexc
  have hcompP : CFSG.Open.IsComponentOf
      (((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin d)
          (Polynomial.X - Polynomial.C μ)).comap
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6psuh_toLinSU h n)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
      (fixSubgroup (primeFormConjHom h (idGram K n) ⟨d, hd'⟩)) :=
    uni_cube_primeForm_t6psub_block_isComponent h ⟨d, hd'⟩ H
      ⟨⟨Polynomial.X - Polynomial.C μ, hmem⟩, hgood⟩
  have hiii := uni_cube_specialBlock_eq_eigBlock h hn1 hd' hd3 hq3 H hμ
  let e := CFSG.StandardType.InndiagSU.projEquiv h hn1
  have hiii' : (eigBlock (2 ^ f) d μ).map e.toMonoidHom =
      ((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin d)
          (Polynomial.X - Polynomial.C μ)).comap
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6psuh_toLinSU h n)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := hiii
  have hcompA : CFSG.Assembly.IsComponentOf
      ((((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin d)
          (Polynomial.X - Polynomial.C μ)).comap
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6psuh_toLinSU h n)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))))
      (fixSubgroup (primeFormConjHom h (idGram K n) ⟨d, hd'⟩)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr hcompP
  have htrans := CFSG.StandardType.isComponentOf_map_mulEquiv' e.symm hcompA
  have hfix : ggAutFixedSubgroup δ' =
      (fixSubgroup (primeFormConjHom h (idGram K n) ⟨d, hd'⟩)).comap e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_comap]
    exact uni_cube_fixSubgroup_projEquiv h hn1 hδ hd' x
  have hBmap : ((((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin d)
          (Polynomial.X - Polynomial.C μ)).comap
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6psuh_toLinSU h n)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))).map
          e.symm.toMonoidHom = eigBlock (2 ^ f) d μ := by
    rw [← hiii']
    rw [Subgroup.map_map]
    rw [show (e.symm.toMonoidHom).comp (e.toMonoidHom) = MonoidHom.id (PSUg n K (2 ^ f)) by
      ext x
      simp]
    rw [Subgroup.map_id]
  have hKmap : (fixSubgroup (primeFormConjHom h (idGram K n) ⟨d, hd'⟩)).map e.symm.toMonoidHom
      = (fixSubgroup (primeFormConjHom h (idGram K n) ⟨d, hd'⟩)).comap e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨k, hk, hky⟩
      rw [← hky]
      simpa using hk
    · intro hy
      exact ⟨e y, hy, by simp⟩
  rw [hBmap, hKmap, ← hfix] at htrans
  exact htrans

end UniCubeIsComp

theorem uni_cube_eigBlock_isComponent {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg n K q)} (hδ : IsConjBy d δ') {μ : K} (hμ : μ ^ 3 = 1) (hQS : CubeBlockQS q d μ) :
    IsComponentOf (eigBlock q d μ) (ggAutFixedSubgroup δ') :=
  uni_cube_eigBlock_isComponent_aux hK hq3 hn hd hd3 hδ hμ hQS

end CFSG.StandardType.TablePThreeKG

end
