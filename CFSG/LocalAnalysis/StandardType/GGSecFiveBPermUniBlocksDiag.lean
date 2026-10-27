module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrameClass

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.SpecialLinear Matrix
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Transport

variable {K : Type} [Field K] {f d : ℕ}

private theorem blockExt_diagonal (S : Finset (Fin d)) (t : Fin S.card → Kˣ) :
    TableBUE.blockExt S (diagonal fun a => (t a : K)) =
      diagonal fun i => ((if hi : i ∈ S then t (S.equivFin ⟨i, hi⟩) else 1 : Kˣ) : K) := by
  ext i j
  change (if hi : i ∈ S then (if hj : j ∈ S then
      diagonal (fun a => (t a : K)) (S.equivFin ⟨i, hi⟩) (S.equivFin ⟨j, hj⟩) else 0)
    else (1 : Matrix (Fin d) (Fin d) K) i j) = _
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ S
    · simp only [dif_pos hi, diagonal_apply_eq]
    · simp only [dif_neg hi, one_apply_eq, diagonal_apply_eq, Units.val_one]
  · rw [diagonal_apply_ne _ hij]
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
      by_cases hj : j ∈ S
      · rw [dif_pos hj, diagonal_apply_ne _ fun h =>
          hij (congrArg Subtype.val (S.equivFin.injective h))]
      · rw [dif_neg hj]
    · rw [dif_neg hi, one_apply_ne hij]

theorem TableBUE.map_blockSU_le_commutator_diagGLHom_range (h : UnitaryFieldData 2 f K)
    (S : Finset (Fin d))
    (hJ : unitarySU 2 f K S.card ≤ ⁅unitarySU 2 f K S.card, (diagGLHom S.card K).range⁆) :
    (TableBUE.blockSU (K := K) (n := f) S).map (unitarySU 2 f K d).subtype ≤
      ⁅(TableBUE.blockSU (K := K) (n := f) S).map (unitarySU 2 f K d).subtype,
        (diagGLHom d K).range⁆ := by
  let Φ : GL (Fin S.card) K →* GL (Fin d) K := Units.map (TableBUE.blockExtHom S)
  have hmap : (TableBUE.blockSU (K := K) (n := f) S).map (unitarySU 2 f K d).subtype =
      (unitarySU 2 f K S.card).map Φ := by
    rw [← TableBUE.range_blockExtSU S h, MonoidHom.range_eq_map, Subgroup.map_map]
    have hcomp : (unitarySU 2 f K d).subtype.comp (TableBUE.blockExtSU S h) =
        Φ.comp (unitarySU 2 f K S.card).subtype := rfl
    rw [hcomp, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hdiag : (diagGLHom S.card K).range.map Φ ≤ (diagGLHom d K).range := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨fun i => if hi : i ∈ S then t (S.equivFin ⟨i, hi⟩) else 1, Units.ext ?_⟩
    change (diagGLHom d K _ : Matrix (Fin d) (Fin d) K) =
      TableBUE.blockExt S (diagGLHom S.card K t : Matrix (Fin S.card) (Fin S.card) K)
    rw [coe_diagGLHom, coe_diagGLHom, blockExt_diagonal]
  rw [hmap]
  calc (unitarySU 2 f K S.card).map Φ
      ≤ (⁅unitarySU 2 f K S.card, (diagGLHom S.card K).range⁆).map Φ := Subgroup.map_mono hJ
    _ = ⁅(unitarySU 2 f K S.card).map Φ, (diagGLHom S.card K).range.map Φ⁆ :=
      Subgroup.map_commutator _ _ _
    _ ≤ ⁅(unitarySU 2 f K S.card).map Φ, (diagGLHom d K).range⁆ :=
      Subgroup.commutator_mono le_rfl hdiag

end Transport

section Frame

variable {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K] {Bs X : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
  {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

theorem GGSecFiveBPermUniLFrame.map_blockSU_le_ggBlockComm_of_le_commutator
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hχ : Function.Surjective χ)
    {S : Finset (Fin n)}
    (hS : (TableBUE.blockSU (K := K) (n := f) S).map (unitarySU 2 f K n).subtype ≤
      ⁅(TableBUE.blockSU (K := K) (n := f) S).map (unitarySU 2 f K n).subtype,
        (diagGLHom n K).range⁆) :
    (TableBUE.blockSU (K := K) (n := f) S).map σ ≤
      ggBlockComm Bs eta (π '' (S : Set (Fin n))) := by
  have hcent : ∀ s ∈ TableBUE.blockSU (K := K) (n := f) S,
      σ s ∈ Subgroup.centralizer (ggBsCoordZeroOn Bs eta (π '' (S : Set (Fin n))) : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨hbB, hco⟩ := mem_ggBsCoordZeroOn.1 hb
    have hconst : ∀ i ∈ S, ∀ j ∈ S, eta ⟨b, hbB⟩ (π i) = eta ⟨b, hbB⟩ (π j) := fun i hi j hj => by
      rw [hco (π i) (Set.mem_image_of_mem π (Finset.mem_coe.2 hi)),
        hco (π j) (Set.mem_image_of_mem π (Finset.mem_coe.2 hj))]
    exact ((Subgroup.mem_centralizer_iff.mp
      (hF.mem_centralizer_map_blockSU_of_const ⟨b, hbB⟩ hconst)) (σ s) ⟨s, hs, rfl⟩).symm
  rw [Subgroup.map_le_iff_le_comap,
    ← Subgroup.map_le_map_iff_of_injective (unitarySU 2 f K n).subtype_injective]
  refine hS.trans (Subgroup.commutator_le.mpr ?_)
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, rfl⟩
  choose c hc using fun k => hχ (t k)
  let b : ↥Bs := eta.symm fun j => c (π.symm j)
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 b
  have hDt : D = diagGLHom n K t := by
    refine Units.ext ?_
    rw [hDm, coe_diagGLHom]
    congr 1
    funext k
    simp only [b, MulEquiv.apply_symm_apply, Equiv.symm_apply_apply, hc]
  subst hDt
  refine ⟨s * (LineU.conjN _ hD s)⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, ← hconj s]
    have hcomm : σ s * ((b : G) * σ s * (b : G)⁻¹)⁻¹ = ⁅σ s, (b : G)⁆ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator (hcent s hs) b.2
  · rw [commutatorElement_def]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
    group

theorem GGSecFiveBPermUniLFrame.surjective_of_card_eq_four
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : Nat.card K = 4) (hp : p.Prime) :
    Function.Surjective χ := by
  have : Fact p.Prime := ⟨hp⟩
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hcardp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hdvd : p ∣ 3 := by
    rw [← hcardp, ← hunits]
    exact Subgroup.card_dvd_of_injective χ hF.2.2.1
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  exact (hF.2.2.1.bijective_of_nat_card_le (by rw [hunits, hcardp, hp3])).2

end Frame

end CFSG.StandardType

end
