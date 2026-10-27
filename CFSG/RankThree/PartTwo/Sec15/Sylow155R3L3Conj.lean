module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiField
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.KFacts.K72SLPiInndiag

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (StatedScalars)

variable {π : Bool} {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def slPiConj (hK : PiField π 2 f K) :
    glPi π 3 (2 ^ f) K →* MulAut (slPi π 3 (2 ^ f) K) where
  toFun y := (conjSL (fun h => by subst h; exact hK.unitary) y.2).symm
  map_one' := MulEquiv.ext fun s => Subtype.ext (by
    show (1 : GL (Fin 3) K) * s * (1 : GL (Fin 3) K)⁻¹ = s
    group)
  map_mul' y z := MulEquiv.ext fun s => Subtype.ext (by
    show ((y * z : glPi π 3 (2 ^ f) K) : GL (Fin 3) K) * s *
      ((y * z : glPi π 3 (2 ^ f) K) : GL (Fin 3) K)⁻¹ =
        (y : GL (Fin 3) K) * ((z : GL (Fin 3) K) * s * (z : GL (Fin 3) K)⁻¹) *
          (y : GL (Fin 3) K)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem coe_slPiConj_apply (hK : PiField π 2 f K) (y : glPi π 3 (2 ^ f) K)
    (s : slPi π 3 (2 ^ f) K) :
    ((slPiConj hK y s : slPi π 3 (2 ^ f) K) : GL (Fin 3) K) =
      (y : GL (Fin 3) K) * s * (y : GL (Fin 3) K)⁻¹ :=
  rfl

theorem slPiConj_eq_of_semiAct (hK : PiField π 2 f K) {ζ : MulAut (slPi π 3 (2 ^ f) K)}
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K) (h : KFacts.SemiAct ζ 1 y) :
    ζ = slPiConj hK ⟨y, hy⟩ :=
  MulEquiv.ext fun s => Subtype.ext ((KFacts.semiAct_one_iff.mp h s).trans
    (coe_slPiConj_apply hK ⟨y, hy⟩ s).symm)

theorem conj_eq_slPiConj (hK : PiField π 2 f K) (j : slPi π 3 (2 ^ f) K) :
    MulAut.conj j = slPiConj hK ⟨j, slPi_le_glPi (fun h => by subst h; exact hK.unitary) j.2⟩ :=
  MulEquiv.ext fun s => Subtype.ext (by
    rw [MulAut.conj_apply, coe_slPiConj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv])

theorem exists_scalar_of_slPiConj_eq_one (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    {y : glPi π 3 (2 ^ f) K} (hy : slPiConj hK y = 1) :
    ∃ ℓ : Kˣ, (y : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) ℓ := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (2 ^ f) := fun h => by subst h; exact hq
  have hsc : (y : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
    mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => by
      have h1 := congrArg (fun z : MulAut (slPi π 3 (2 ^ f) K) =>
        ((z ⟨s, hs⟩ : slPi π 3 (2 ^ f) K) : GL (Fin 3) K)) hy
      simp only [coe_slPiConj_apply, MulAut.one_apply] at h1
      calc (y : GL (Fin 3) K) * s = ((y : GL (Fin 3) K) * s * (y : GL (Fin 3) K)⁻¹) * y := by
            group
        _ = s * y := by rw [h1]
  obtain ⟨ℓ, hℓ⟩ := hsc
  exact ⟨ℓ, hℓ.symm⟩

theorem commutator_le_range_slPiConj (hK : PiField π 2 f K) (hq2 : 2 < 2 ^ f) :
    commutator (MulAut (slPi π 3 (2 ^ f) K)) ≤ (slPiConj hK).range := by
  intro ζ hζ
  have := hK.finite
  cases π
  · have h := hK.unitary
    have hmem := KFacts.map_mem_commutator
      ((MulAut.congr (KFacts.suCenterEquiv h hq2)).toMonoidHom.comp
        ((KFacts.centerDescend _).comp (MulAut.congr (slPiFalseEquiv 2 f K)).toMonoidHom)) hζ
    obtain ⟨y, hy, hsa⟩ := KFacts.exists_conj_of_psuConj_mem h hq2
      (KFacts.commutator_le_psuConj_range h hq2 hmem)
    exact ⟨⟨y, hy⟩, (slPiConj_eq_of_semiAct hK hy hsa).symm⟩
  · have hmem := KFacts.map_mem_commutator
      ((descendAut 3 K).comp (MulAut.congr (slPiTrueEquiv (2 ^ f) K)).toMonoidHom) hζ
    obtain ⟨y, hsa⟩ := KFacts.exists_conj_of_descendAut_mem
      (KFacts.commutator_le_linearAutGroup hmem)
    exact ⟨⟨y, mem_glPi_true _ _⟩, (slPiConj_eq_of_semiAct hK (mem_glPi_true _ _) hsa).symm⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
