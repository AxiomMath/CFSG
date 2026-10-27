module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Bridge
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135c2_psl_cover
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L) (hirr : IsIrrOn L ⊤ ⊥) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K), CharP K 2 ∧ Fintype.card K = 2 ^ f ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L, Function.Surjective φ ∧
        φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ∧
        Odd (Nat.card φ.ker) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun a b h => MulEquiv.ext (congr_fun h))
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hperf : Group.IsPerfect ↥L := hQ.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hW'
      (fun U hU => hirr.2.2.2 U hU bot_le le_top)
  have hsc : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f :=
    hlie.statedClassicalModel (by decide)
  have hf : 1 ≤ f := hsc.1.2.1
  obtain ⟨K, hKfield, hKfinite, hKcard, hKchar, hm2, φ', hφ', hker, _⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.exists_cover_of_psl_model
      (L := ↥L) hperf hodd hf hsc
  letI : Field K := hKfield
  haveI : Finite K := hKfinite
  let fK : Fintype K := Fintype.ofFinite K
  letI : Fintype K := fK
  haveI : CharP K 2 := hKchar
  have hKcardF : Fintype.card K = 2 ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact hKcard
  have hker_center : φ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    hker.trans (le_of_eq (LinearFlag.scalars_eq_center n K))
  have hoddker : Odd (Nat.card φ'.ker) :=
    Odd.of_dvd_nat CFSG.StandardType.AutPSL.odd_card_scalars
      (Subgroup.card_dvd_of_le hker)
  exact ⟨hm2, K, hKfield, fK, hKchar, hKcardF, φ', hφ', hker_center, hoddker⟩

theorem w135c2_psl_rep_irreducible {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} (hIrr : IsIrrOn L ⊤ ⊥)
    {G : Type} [Group G] (φ : G →* ↥L) (hφ : Function.Surjective φ) :
    (pslRep φ).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  refine ⟨?_, ?_⟩
  · haveI : Nontrivial W := by
      have hne : (⊤ : Subgroup W) ≠ ⊥ := (ne_of_lt hIrr.1).symm
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      exact ⟨(a : W), 1, fun h => ha (Subtype.ext h)⟩
    infer_instance
  · intro U hU
    let U' : Subgroup W :=
      { carrier := {w | Additive.ofMul w ∈ U}
        one_mem' := U.zero_mem
        mul_mem' := fun ha hb => U.add_mem ha hb
        inv_mem' := fun ha => U.neg_mem ha }
    have hst : StableUnder L U' := by
      intro x hx u hu
      obtain ⟨g, hg⟩ := hφ ⟨x, hx⟩
      have h := hU g (Additive.ofMul u) hu
      rw [pslRep_apply, hg, mulAutLinear_apply] at h
      exact h
    rcases hIrr.2.2.2 U' hst bot_le le_top with h0 | h1
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : Additive.toMul v ∈ U' := by
        change Additive.ofMul (Additive.toMul v) ∈ U
        rwa [ofMul_toMul]
      rw [h0, Subgroup.mem_bot] at hv'
      rw [← ofMul_toMul v, hv']
      rfl
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hv' : Additive.toMul v ∈ U' := by rw [h1]; trivial
      change Additive.ofMul (Additive.toMul v) ∈ U at hv'
      rwa [ofMul_toMul] at hv'

theorem w135c2_psl_rep_ne_one {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L)
    {G : Type} [Group G] (φ : G →* ↥L) (hφ : Function.Surjective φ) :
    ∃ x : G, pslRep φ x ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := hQ.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hne : x' * y' ≠ y' * x' := by
    intro h
    exact hxy (by
      have := congrArg (QuotientGroup.mk' (Subgroup.center ↥L)) h
      simpa using this)
  have hx'1 : x' ≠ 1 := by
    intro h
    exact hne (by rw [h, one_mul, mul_one])
  obtain ⟨g, hg⟩ := hφ x'
  refine ⟨g, ?_⟩
  intro h
  apply hx'1
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have h1 := congrArg (fun (f : Additive W →ₗ[ZMod 2] Additive W) =>
    f (Additive.ofMul w)) h
  simp only [pslRep_apply, hg, mulAutLinear_apply, Module.End.one_apply] at h1
  apply Additive.ofMul.injective
  simpa using h1

end CFSG.LocalAnalysis.WeakClosure81
