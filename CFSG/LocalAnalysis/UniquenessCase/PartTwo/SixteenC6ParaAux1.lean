module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

theorem s16c6_derInf_fixes {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q : Subgroup (GL ι F)) (v : ι → F) (hv : v ≠ 0)
    (hQv : ∀ g ∈ Q, (g : Matrix ι ι F) *ᵥ v ∈ Submodule.span F {v}) :
    ∀ g ∈ F07.DerInf Q, (g : Matrix ι ι F) *ᵥ v = v := by
  classical
  have hline : ∀ g : Q, ∃ cc : F, ((g : GL ι F) : Matrix ι ι F) *ᵥ v = cc • v :=
    fun g => (Submodule.mem_span_singleton.mp (hQv g g.2)).imp (fun cc hcc => hcc.symm)
  choose cc hcc using hline
  have hccmul : ∀ g h : Q, cc (g * h) = cc g * cc h := by
    intro g h
    have e : cc (g * h) • v = (cc g * cc h) • v := by
      rw [← hcc (g * h)]
      rw [show (((g * h : Q) : GL ι F) : Matrix ι ι F) =
          ((g : GL ι F) : Matrix ι ι F) * ((h : GL ι F) : Matrix ι ι F) from by
        simp [Subgroup.coe_mul, Units.val_mul]]
      rw [← Matrix.mulVec_mulVec, hcc h, Matrix.mulVec_smul, hcc g, smul_smul, mul_comm]
    exact smul_left_injective F hv e
  have hcc1 : cc 1 = 1 := by
    have e : cc (1 : Q) • v = (1 : F) • v := by
      rw [← hcc 1]
      rw [show (((1 : Q) : GL ι F) : Matrix ι ι F) = 1 from by simp [Subgroup.coe_one],
        Matrix.one_mulVec, one_smul]
    exact smul_left_injective F hv e
  let χ : Q →* F := { toFun := cc, map_one' := hcc1, map_mul' := hccmul }
  have hDerQ : F07.DerInf Q ≤ Q := by
    rw [F07.DerInf]
    exact Subgroup.map_subtype_le _
  have hfixQ : ∀ g : Q, (g : GL ι F) ∈ F07.DerInf Q → cc g = 1 := by
    intro g hg
    let χD : ↥(F07.DerInf Q) →* F := χ.comp (Subgroup.inclusion hDerQ)
    haveI : Group.IsPerfect ↥(F07.DerInf Q) :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect Q
    have hsub : Subsingleton χD.toHomUnits.range := by
      have : Group.IsPerfect χD.toHomUnits.range := Group.IsPerfect.range χD.toHomUnits
      infer_instance
    have h1 : (⟨χD.toHomUnits ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ : χD.toHomUnits.range) = 1 :=
      Subsingleton.elim _ _
    have h2 : χD.toHomUnits ⟨g, hg⟩ = 1 := congrArg Subtype.val h1
    have h3 := congrArg Units.val h2
    simpa [χD, χ, Subgroup.inclusion] using h3
  intro g hg
  have hgQ : (g : GL ι F) ∈ Q := hDerQ hg
  rw [hcc ⟨g, hgQ⟩, hfixQ ⟨g, hgQ⟩ hg, one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
