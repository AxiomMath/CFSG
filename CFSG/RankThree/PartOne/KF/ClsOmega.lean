module

public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem quadPlusPolar_eq_spForm (u v : Fin n ⊕ Fin n → K) :
    quadPlusPolar n K u v = (spForm n K).β u v := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [spForm_β, dotProduct_spJ_mulVec]
  unfold quadPlusPolar
  simp only [dotProduct, Function.comp_apply]
  rw [Finset.sum_add_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (v (Sum.inl i) * u (Sum.inr i)) * h2

theorem statedOmega_quadPlus_le_statedSp :
    StatedOmega (StatedQuadPlus n K) ≤ StatedSp n K := by
  intro A hA
  have hiso := isIsometric_natRep_statedOmega (quadPlusForm n K) ⟨A, hA⟩
  obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry n K
    (Matrix.mulVecLin (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) (fun u v => by
      have h := hiso u v
      rw [natRep_apply, natRep_apply] at h
      change quadPlusPolar n K _ _ = quadPlusPolar n K _ _ at h
      rw [quadPlusPolar_eq_spForm, quadPlusPolar_eq_spForm] at h
      simpa using h)
  have hgA : (g : GL (Fin n ⊕ Fin n) K) = A := by
    apply Units.ext
    ext i j
    have := congrFun (hg (Pi.single j 1)) i
    rw [natRep_apply] at this
    simpa [Matrix.mulVec_single_one] using this
  rw [← hgA]
  exact g.2

noncomputable def equivProjOfScalarsBot {ι : Type} [Fintype ι] [DecidableEq ι] {K' : Type}
    [Field K'] (H : Subgroup (GL ι K')) (h : (StatedScalars ι K').subgroupOf H = ⊥) :
    ↥H ≃* StatedProj H :=
  MulEquiv.ofBijective (QuotientGroup.mk' ((StatedScalars ι K').subgroupOf H))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']; exact h,
      QuotientGroup.mk'_surjective _⟩

theorem statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxSp : (x : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K :=
    statedOmega_quadPlus_le_statedSp x.2
  have h1 : (⟨x, hxSp⟩ : StatedSp n K) ∈
      (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) := hx
  rw [statedScalars_subgroupOf_statedSp_eq_bot hn, Subgroup.mem_bot] at h1
  refine Subgroup.mem_bot.mpr (Subtype.ext ?_)
  exact congrArg (fun y : StatedSp n K => (y : GL (Fin n ⊕ Fin n) K)) h1

theorem localRank_statedProj_statedOmega_quadPlus_le [Finite K] (hn : 1 ≤ n) {p : ℕ}
    (hp : p.Prime) :
    localRank p (StatedProj (StatedOmega (StatedQuadPlus n K))) ≤ localRank p ↥(StatedSp n K) := by
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (equivProjOfScalarsBot _ (statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot (K := K) hn)) hp]
  exact CFSG.RankThree.PartOne.PlaneAux.localRank_le_of_injective hp
    (Subgroup.inclusion statedOmega_quadPlus_le_statedSp) (Subgroup.inclusion_injective _)

end CFSG.RankThree.PartOne.KFU
