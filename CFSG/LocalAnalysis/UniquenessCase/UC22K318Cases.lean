module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Flag
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.RankThree.SubgroupLists.SymplecticRegulus
import CFSG.RankThree.SubgroupLists.SymplecticInvolutionPairs
import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup Module
open CFSG.RankThree.SubgroupLists (spForm IsIrreducibleOn lagInl mem_lagInl eq_mkV spForm_mkV tGL
  coe_tGL tGL_mulVec tGL_mem tGL_add tGL_zero finrank_lagInl neg_one_mem_statedSp_two)
open CFSG.RankThree.CentralCover (sl2Diag sl2Upper sl2DiagHom sl2UpperHom sl2DiagHom_apply
  sl2UpperHom_apply sl2Diag_mul sl2Diag_one sl2Diag_injective sl2UpperHom_injective
  sl2Diag_conj_upper sl2Diag_neg_one_commute)
open scoped Matrix MatrixGroups

variable {L : Type} [Group L] [Finite L] {q : ℕ} [Fact q.Prime]

theorem isPGroup_not_isCyclic_range {A G : Type} [Group A] [Group G] {φ : A →* G}
    (hφ : Function.Injective φ) (hA : Nat.card A = q ^ 2) (hAq : ∀ a : A, a ^ q = 1) :
    IsPGroup q φ.range ∧ ¬ IsCyclic φ.range ∧ φ.range ≠ ⊥ := by
  have hq : q.Prime := Fact.out
  have h2 := hq.two_le
  have hcard : Nat.card φ.range = q ^ 2 := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  refine ⟨IsPGroup.of_card hcard, fun hcyc => ?_, fun hbot => ?_⟩
  · have hexp : Monoid.exponent φ.range ∣ q := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      change φ a ^ q = 1
      rw [← map_pow, hAq, map_one]
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    have := Nat.le_of_dvd hq.pos hexp
    nlinarith
  · rw [hbot, Subgroup.card_bot] at hcard
    nlinarith

theorem three_lt_pRank_of_sp4 {X : Subgroup L} (hq2 : q ≠ 2)
    {ψ : L →* GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hD : SympSection X q ψ)
    (hP : ψ.range = CFSG.Open.StatedSp 2 (ZMod q)) : 3 < CFSG.Open.pRank q (⊤ : Subgroup L) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Multiplicative (Fin 2 → ZMod q) →* GL (Fin 2 ⊕ Fin 2) (ZMod q),
      ∀ d, φ d = tGL (Matrix.diagonal (Multiplicative.toAdd d)) :=
    ⟨{ toFun := fun d => tGL (Matrix.diagonal (Multiplicative.toAdd d))
       map_one' := by
         change tGL (Matrix.diagonal (Multiplicative.toAdd (1 : Multiplicative (Fin 2 → ZMod q)))) =
           1
         rw [toAdd_one, Matrix.diagonal_zero', tGL_zero]
       map_mul' := fun a b => by
         change tGL (Matrix.diagonal (Multiplicative.toAdd (a * b))) =
           tGL (Matrix.diagonal (Multiplicative.toAdd a)) *
             tGL (Matrix.diagonal (Multiplicative.toAdd b))
         rw [tGL_add]
         exact congrArg tGL (Matrix.diagonal_add _ _).symm }, fun _ => rfl⟩
  have hφi : Function.Injective φ := by
    intro a b hab
    rw [hφ, hφ] at hab
    have h := congrArg Units.val hab
    rw [coe_tGL, coe_tGL] at h
    exact Multiplicative.toAdd.injective
      (Matrix.diagonal_injective (Matrix.fromBlocks_inj.1 h).2.1)
  have hA : Nat.card (Multiplicative (Fin 2 → ZMod q)) = q ^ 2 := by
    change Nat.card (Fin 2 → ZMod q) = q ^ 2
    simp [Nat.card_fun]
  have hAq : ∀ a : Multiplicative (Fin 2 → ZMod q), a ^ q = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨hFq, hFc, -⟩ := isPGroup_not_isCyclic_range hφi hA hAq
  have hFψ : φ.range ≤ ψ.range := by
    rintro _ ⟨d, rfl⟩
    rw [hP, hφ]
    exact tGL_mem (Matrix.diagonal_transpose _)
  have hneg : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ ψ.range := by
    rw [hP]
    exact neg_one_mem_statedSp_two
  have hW : Nat.card (lagInl : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q)) = q ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod, finrank_lagInl]
  have hWi : ∀ v ∈ (lagInl : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q)), ∀ w ∈ lagInl,
      spForm 2 (ZMod q) v w = 0 := by
    intro v hv w hw
    have hv0 : (fun i => v (Sum.inr i)) = 0 := funext (mem_lagInl.1 hv)
    have hw0 : (fun i => w (Sum.inr i)) = 0 := funext (mem_lagInl.1 hw)
    rw [eq_mkV v, eq_mkV w, spForm_mkV, hv0, hw0, dotProduct_zero, zero_dotProduct, sub_zero]
  have hFW : ∀ f ∈ φ.range, ∀ w ∈ (lagInl : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q)),
      (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ w = w := by
    rintro _ ⟨d, rfl⟩ w hw
    have hw0 : (fun i => w (Sum.inr i)) = 0 := funext (mem_lagInl.1 hw)
    rw [hφ, eq_mkV w, tGL_mulVec, hw0, Matrix.mulVec_zero, add_zero]
  exact three_lt_pRank_of_flag hq2 hD hneg hFψ hFq hFc hW hWi hFW

theorem three_lt_pRank_of_sl2 {X : Subgroup L} (hq2 : q ≠ 2)
    {ψ : L →* GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hD : SympSection X q ψ)
    (hPS : ψ.range ≤ CFSG.Open.StatedSp 2 (ZMod q)) (hirr : IsIrreducibleOn ψ.range)
    (e : ψ.range ≃* SL(2, GaloisField q 2)) : 3 < CFSG.Open.pRank q (⊤ : Subgroup L) := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hK : ringChar (GaloisField q 2) ≠ 2 := by
    rw [ringChar.eq (GaloisField q 2) q]
    exact hq2
  have hKcard : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card q 2 (by norm_num)]
  obtain ⟨ι, hιe⟩ : ∃ ι : SL(2, GaloisField q 2) →* GL (Fin 2 ⊕ Fin 2) (ZMod q),
      ∀ s, ι s = ((e.symm s : ψ.range) : GL (Fin 2 ⊕ Fin 2) (ZMod q)) :=
    ⟨ψ.range.subtype.comp e.symm.toMonoidHom, fun _ => rfl⟩
  have hιi : Function.Injective ι := by
    intro a b hab
    rw [hιe, hιe] at hab
    exact e.symm.injective (Subtype.ext hab)
  have hιP : ∀ s, ι s ∈ ψ.range := fun s => by
    rw [hιe]
    exact (e.symm s).2
  have hz : ι (sl2Diag (-1)) = -1 := by
    refine eq_neg_one_of_commute hirr (fun g hg => ?_) ?_ ?_
    · have hg' : ι (e ⟨g, hg⟩) = g :=
        (hιe _).trans (congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩))
      rw [← hg', ← map_mul, ← map_mul, (sl2Diag_neg_one_commute (e ⟨g, hg⟩)).eq]
    · rw [← map_mul, ← sl2Diag_mul, neg_one_mul, neg_neg, sl2Diag_one, map_one]
    · intro h1
      rw [← map_one ι] at h1
      have h2 := hιi h1
      rw [← sl2Diag_one] at h2
      have h3 := congrArg Units.val (sl2Diag_injective h2)
      rw [Units.val_neg, Units.val_one] at h3
      exact Ring.neg_one_ne_one_of_char_ne_two hK h3
  obtain ⟨μ, hμN⟩ : ∃ μ : (GaloisField q 2)ˣ, μ ^ (q ^ 2 / 2) = -1 := by
    obtain ⟨lam, hlam⟩ := FiniteField.exists_nonsquare hK
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      exact hlam ⟨0, (mul_zero 0).symm⟩
    have hlamN : lam ^ (q ^ 2 / 2) = -1 := by
      rcases FiniteField.pow_dichotomy hK hlam0 with h1 | h1
      · exact absurd ((FiniteField.isSquare_iff hK hlam0).2 h1) hlam
      · rwa [hKcard] at h1
    refine ⟨Units.mk0 lam hlam0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hlamN, Units.val_neg, Units.val_one]
  have hhN : ι (sl2Diag μ) ^ (q ^ 2 / 2) = -1 := by
    rw [← map_pow, ← sl2DiagHom_apply, ← map_pow, hμN, sl2DiagHom_apply, hz]
  have hA : Nat.card (Multiplicative (GaloisField q 2)) = q ^ 2 := by
    change Nat.card (GaloisField q 2) = q ^ 2
    exact GaloisField.card q 2 (by norm_num)
  have hAq : ∀ a : Multiplicative (GaloisField q 2), a ^ q = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero (GaloisField q 2) q, zero_mul]
  have hUi : Function.Injective (ι.comp (sl2UpperHom (GaloisField q 2))) := by
    intro a b hab
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hab
    exact sl2UpperHom_injective (hιi hab)
  obtain ⟨hFq, hFc, hF1⟩ := isPGroup_not_isCyclic_range hUi hA hAq
  have hFψ : (ι.comp (sl2UpperHom (GaloisField q 2))).range ≤ ψ.range := by
    rintro _ ⟨c, rfl⟩
    exact hιP _
  have hconjF : ∀ (ν : (GaloisField q 2)ˣ) (c : GaloisField q 2),
      ι (sl2Diag ν) * ι (sl2Upper c) * (ι (sl2Diag ν))⁻¹ ∈
        (ι.comp (sl2UpperHom (GaloisField q 2))).range := by
    intro ν c
    refine ⟨Multiplicative.ofAdd ((ν : GaloisField q 2) ^ 2 * c), ?_⟩
    rw [MonoidHom.comp_apply, sl2UpperHom_apply, toAdd_ofAdd, ← sl2Diag_conj_upper, map_mul,
      map_mul, map_inv]
  have hinvd : (sl2Diag μ)⁻¹ = sl2Diag μ⁻¹ := by
    rw [← sl2DiagHom_apply, ← sl2DiagHom_apply, map_inv]
  have hhF : ι (sl2Diag μ) ∈ normalizer
      ((ι.comp (sl2UpperHom (GaloisField q 2))).range : Set (GL (Fin 2 ⊕ Fin 2) (ZMod q))) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨c, rfl⟩
      exact hconjF μ (Multiplicative.toAdd c)
    · rintro ⟨c, hc⟩
      have hc' : ι (sl2Upper (Multiplicative.toAdd c)) =
          ι (sl2Diag μ) * g * (ι (sl2Diag μ))⁻¹ := hc
      have hg : g = ι (sl2Diag μ⁻¹) * ι (sl2Upper (Multiplicative.toAdd c)) *
          (ι (sl2Diag μ⁻¹))⁻¹ := by
        rw [hc', ← hinvd, map_inv, inv_inv]
        group
      rw [hg]
      exact hconjF μ⁻¹ (Multiplicative.toAdd c)
  obtain ⟨W, hW, hWi, hFW⟩ :=
    exists_flag hq2 (hFψ.trans hPS) hFq hF1 (hPS (hιP (sl2Diag μ))) hhF hhN
  have hneg : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ ψ.range := by
    rw [← hz]
    exact hιP _
  exact three_lt_pRank_of_flag hq2 hD hneg hFψ hFq hFc hW hWi hFW

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
