module

public import CFSG.RankThree.PartOne.KF4.B2SpFacts
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.PresentationLocal
open CFSG.Assembly.LowTwoRank CFSG.Monster.Existence.Compat
open CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne


@[expose] def f4SpGroup_mulEquiv_sympFour {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    f4SpGroup k ≃* sympFour :=
  (f4SpGroup_mulEquiv_statedSp k).trans
    ((statedProjEquivOfBot (StatedSp 2 k) (statedScalars_eq_bot hk)).symm.trans
      (statedProjEquivSympFour hk))

theorem f4SpGroup_center_eq_one {L : Type} [Field L] [CharP L 2] (M : f4SpGroup L)
    (hM : ∀ Y : f4SpGroup L, Y * M = M * Y) : M = 1 := by
  obtain ⟨c, hc⟩ := scalar_of_commutes_f4SpGroup (K := L) (L := L)
    ((M : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) (fun Y hY => by
      have h := congrArg (fun A : f4SpGroup L => ((A : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L))
        (hM ⟨Y, hY⟩)
      simp only [Subgroup.coe_mul, Units.val_mul] at h
      simp only [Algebra.algebraMap_self]
      exact h.symm)
  have hmem := M.2
  rw [mem_f4SpGroup, hc, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hmem
  have h03 := congrFun (congrFun hmem 0) 3
  simp [f4B2J0, Matrix.smul_apply] at h03
  have hc1 : c = 1 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (c - 1) ^ 2 = 0 := by linear_combination h03 + (1 - c) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1, one_smul]
  rfl

theorem f4SpGroup_derived {k : Type} [Field k] [Finite k] [CharP k 2]
    (hkc : Nat.card k = 2 ∨ 4 ≤ Nat.card k) :
    CFSG.IsQuasisimple ↥(commutator (f4SpGroup k)) ∧
      ∀ s : f4SpGroup k, (∀ a ∈ commutator (f4SpGroup k), s * a = a * s) → s = 1 := by
  rcases hkc with h2 | h4
  · set e := f4SpGroup_mulEquiv_sympFour h2 with he
    have hmap : (commutator (f4SpGroup k)).map e.toMonoidHom = commutator sympFour := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 e.surjective]
    refine ⟨(derived_of_mulEquiv_sympFour e).1, fun s hs => ?_⟩
    have hs' : e s ∈ Subgroup.centralizer (commutator sympFour : Set sympFour) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hmap] at hh
      obtain ⟨a, ha, rfl⟩ := hh
      have := congrArg e (hs a ha)
      simp only [map_mul] at this
      exact this.symm
    rw [centralizer_commutator_sympFour, Subgroup.mem_bot] at hs'
    exact (map_eq_one_iff e e.injective).1 hs'
  · have hq : CFSG.IsQuasisimple (f4SpGroup k) := f4SpGroup_isQuasisimple k (Or.inl h4)
    have hperf : commutator (f4SpGroup k) = ⊤ := Group.isPerfect_def.1 hq.1
    refine ⟨?_, fun s hs => ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv).symm hq
    · refine f4SpGroup_center_eq_one s fun Y => ?_
      have := hs Y (by rw [hperf]; exact Subgroup.mem_top Y)
      exact this.symm

end CFSG.RankThree.PartOne.KF4
