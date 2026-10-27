module

public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofSignal

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 suConj psuConj mem_unitaryIsom3 coe_suConj
  stdPinnedPSL stdPinnedPSL_stable stdPinnedPSU3 stdPinnedPSU3_stable)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

namespace Proof142Res

variable {K : Type} [Field K]

theorem mem_inndiagPi_true_iff {q : ℕ} (β : MulAut (projImage (slPi true 3 q K))) :
    β ∈ inndiagPi true q K ↔ MulAut.congr (pslEquivProjective q K) β ∈ linearAutGroup 3 K := by
  set Φ := pslEquivProjective q K with hΦ
  have key : ∀ (g : GL (Fin 3) K) (s : Matrix.SpecialLinearGroup (Fin 3) K),
      ((slToPsl q K (slConjugation 3 K g s) : projImage (slPi true 3 q K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk g * (slToPsl q K s : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk g)⁻¹ := by
    intro g s
    rw [coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul, map_mul, map_inv]
  have hΦs : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K,
      Φ.symm (proj 3 K s) = slToPsl q K s := fun s => by
    rw [MulEquiv.symm_apply_eq, hΦ, pslEquivProjective_slToPsl]
  constructor
  · rintro ⟨g, -, hβ⟩
    refine (mem_linearAutGroup_iff (n := 3) (K := K)).mpr ⟨g, ?_⟩
    ext x
    obtain ⟨s, rfl⟩ := proj_surjective 3 K x
    rw [conjAut_proj, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hΦs,
      ← pslEquivProjective_slToPsl (q := q)]
    congr 1
    apply Subtype.ext
    rw [hβ, key]
  · intro hβ
    obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hβ
    refine ⟨A, mem_glPi_true _ _, fun t => ?_⟩
    obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) q t
    have h1 : Φ (β (slToPsl q K s)) = Φ (slToPsl q K (slConjugation 3 K A s)) := by
      have := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K s)) hA
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hΦs] at this
      rw [← this, conjAut_proj, hΦ, pslEquivProjective_slToPsl]
    rw [Φ.injective h1, key]

theorem mem_inndiagPi_false_iff {p f : ℕ} (h : UnitaryFieldData p f K)
    (β : MulAut (projImage (slPi false 3 (p ^ f) K))) :
    β ∈ inndiagPi false (p ^ f) K ↔ MulAut.congr (psuEquivUnitary h) β ∈ (psuConj h).range := by
  set Φ := psuEquivUnitary h with hΦ
  have key : ∀ (A : unitaryIsom3 h) (s : unitarySU p f K 3),
      ((suToPsu p f K (suConj h A s) : projImage (slPi false 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A : GL (Fin 3) K) * (suToPsu p f K s : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk (A : GL (Fin 3) K))⁻¹ := by
    intro A s
    rw [coe_suToPsu, coe_suToPsu, coe_suConj, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  have hmem : ∀ g : GL (Fin 3) K, g ∈ glPi false 3 (p ^ f) K ↔ g ∈ unitaryIsom3 h :=
    fun g => by rw [mem_glPi_false h, mem_unitaryIsom3]
  have hΦs : ∀ s : unitarySU p f K 3, Φ.symm (unitaryProj h 3 s) = suToPsu p f K s := fun s => by
    rw [MulEquiv.symm_apply_eq, hΦ, psuEquivUnitary_suToPsu]
  constructor
  · rintro ⟨g, hg, hβ⟩
    refine ⟨⟨g, (hmem g).mp hg⟩, ?_⟩
    ext x
    obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
    rw [psuConj_unitaryProj, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      hΦs, ← psuEquivUnitary_suToPsu h]
    congr 1
    apply Subtype.ext
    rw [hβ, key]
  · rintro ⟨A, hA⟩
    refine ⟨A, (hmem A).mpr A.2, fun t => ?_⟩
    obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) t
    have h1 : Φ (β (suToPsu p f K s)) = Φ (suToPsu p f K (suConj h A s)) := by
      have := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ (unitaryProj h 3 s)) hA
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hΦs] at this
      rw [← this, psuConj_unitaryProj, hΦ, psuEquivUnitary_suToPsu]
    rw [Φ.injective h1, key]

end Proof142Res

open Proof142Res

theorem ks142InndiagNormal : KS142InndiagNormal := by
  intro π p f K _ hK _ hq2
  have := hK.finite
  cases π
  · have h := hK.unitary
    have hN : ((psuConj h).range).Normal := (stdPinnedPSU3_stable (h := h) hq2).normal
    have heq : inndiagPi false (p ^ f) K =
        ((psuConj h).range).comap (MulAut.congr (psuEquivUnitary h)).toMonoidHom := by
      ext β
      exact mem_inndiagPi_false_iff h β
    rw [heq]
    exact hN.comap _
  · have hN : (linearAutGroup 3 K).Normal := (stdPinnedPSL_stable (n := 3) (K := K) le_rfl).normal
    have heq : inndiagPi true (p ^ f) K =
        (linearAutGroup 3 K).comap (MulAut.congr (pslEquivProjective (p ^ f) K)).toMonoidHom := by
      ext β
      exact mem_inndiagPi_true_iff β
    rw [heq]
    exact hN.comap _

end CFSG.RankThree.PartTwo.Sec14
