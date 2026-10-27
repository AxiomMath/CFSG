module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Fix
import CFSG.RankThree.PartOne.KC.IrreducibleCentralizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesBasis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Polynomial
open scoped Matrix MatrixGroups

private noncomputable def ggF4TWP_glToLinearEquiv (F : Type) [Field F] :
    GL (Fin 6) F ≃* ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 6 → F))

theorem ggF4TWP_no_commute_thirteen_seventeen {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (A U : GL (Fin 6) F) (hA : A ^ 13 = 1) (hA1 : A ≠ 1)
    (hU : U ^ 17 = 1) (hU1 : U ≠ 1) (hAU : A * U = U * A) : False := by
  classical
  let e := ggF4TWP_glToLinearEquiv F
  have hV : Module.finrank F (Fin 6 → F) = 6 := Module.finrank_fin_fun F
  have ha : e A ^ 13 = 1 := by rw [← map_pow e A 13, hA, map_one]
  have ha1 : e A ≠ 1 := fun h => hA1 (e.injective (h.trans (map_one e).symm))
  have hu : e U ^ 17 = 1 := by rw [← map_pow e U 17, hU, map_one]
  have hu1 : e U ≠ 1 := fun h => hU1 (e.injective (h.trans (map_one e).symm))
  have hau : (e A : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) *
      (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) =
      (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) *
        (e A : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) := by
    have h : e A * e U = e U * e A := by rw [← map_mul, hAU, map_mul]
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, h]
  set W : Submodule F (Fin 6 → F) :=
    LinearMap.ker ((e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) - 1) with hW
  have hfix : Module.finrank F W = 2 :=
    ggF4H4Psl64_fixed_finrank_two hF hV (e U) hu hu1
  have hinv : ∀ w ∈ W, e A w ∈ W := by
    intro w hw
    have huw : (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w = w := sub_eq_zero.mp hw
    have h1 : (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) ((e A :
        (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w) = (e A : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w := by
      have h3 : (e A : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) ((e U :
          (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w) =
          (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) ((e A :
            (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w) := by
        simpa using congrArg (fun f : (Fin 6 → F) →ₗ[F] (Fin 6 → F) => f w) hau
      rw [← h3, huw]
    show (e U : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) ((e A :
      (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w) - (e A : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) w = 0
    rw [h1, sub_self]
  rcases ggF4H4Psl64_invariant_bot_or_top hF hV (e A) ha ha1 W hinv with h | h
  · rw [h, finrank_bot] at hfix
    omega
  · rw [h, finrank_top, hV] at hfix
    omega

section Image

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem ggF4TWP_minpoly_irreducible (hF : Nat.card F = 4)
    (hV : Module.finrank F V = 6) (a x : V ≃ₗ[F] V) (ha : a ^ 13 = 1) (ha1 : a ≠ 1)
    (hax : a * x = x * a) (hx : x ^ 15 = 1) :
    Irreducible (minpoly F x.toLinearMap) := by
  classical
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
  have hT15 : (x : V →ₗ[F] V) ^ 15 = 1 := by
    have h := (map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) x 15).symm
    rwa [hx, map_one] at h
  have hdvd : minpoly F x.toLinearMap ∣ X ^ 15 - 1 :=
    minpoly.dvd F x.toLinearMap (by simp [hT15])
  have hm0 : minpoly F x.toLinearMap ≠ 0 := minpoly.ne_zero_of_finite F x.toLinearMap
  have hnat : 0 < (minpoly F x.toLinearMap).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x.toLinearMap)
  obtain ⟨q, hqirr, hqdvd⟩ := Polynomial.exists_irreducible_of_natDegree_pos hnat
  obtain ⟨r, hr⟩ := hqdvd
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hm0 hr
  have hrdeg : r.natDegree < (minpoly F x.toLinearMap).natDegree := by
    rw [hr, natDegree_mul hqirr.ne_zero hr0]
    have h := hqirr.natDegree_pos
    omega
  have haevr : (aeval x.toLinearMap) r ≠ 0 := by
    intro h0
    have hd : minpoly F x.toLinearMap ∣ r := minpoly.dvd F x.toLinearMap h0
    have hle := natDegree_le_of_dvd hd hr0
    omega
  have hmem : ∀ v : V, (aeval x.toLinearMap) r v ∈
      CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap q := by
    intro v
    rw [CFSG.RankThree.PartOne.KCPrimary.mem_primaryComponent]
    have h1 : (aeval x.toLinearMap) q ((aeval x.toLinearMap) r v) =
        (aeval x.toLinearMap) (q * r) v := by
      rw [map_mul]
      rfl
    rw [h1, ← hr, minpoly.aeval]
    rfl
  have hWne : CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap q ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp haevr
    have hmem' := hmem v
    rw [hbot] at hmem'
    exact hv (by simpa using hmem')
  have hax' : Commute (a : V →ₗ[F] V) x.toLinearMap := by
    have h : (a : V →ₗ[F] V) * x.toLinearMap = x.toLinearMap * a.toLinearMap := by
      rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hax]
    exact h
  have hinv : ∀ w ∈ CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap q,
      a w ∈ CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap q :=
    fun w hw => CFSG.RankThree.PartOne.KCPrimary.apply_mem_primaryComponent hax' hw
  rcases ggF4H4Psl64_invariant_bot_or_top hF hV a ha ha1
    (CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap q) hinv with h | h
  · exact absurd h hWne
  · have haevq : (aeval x.toLinearMap) q = 0 := by
      rw [CFSG.RankThree.PartOne.KCPrimary.primaryComponent] at h
      exact LinearMap.ker_eq_top.mp h
    have hm_dvd_q : minpoly F x.toLinearMap ∣ q := minpoly.dvd F x.toLinearMap haevq
    have hm_notunit : ¬ IsUnit (minpoly F x.toLinearMap) := by
      intro hu
      have hdeg : (minpoly F x.toLinearMap).degree = 0 := degree_eq_zero_of_isUnit hu
      rw [degree_eq_natDegree hm0] at hdeg
      have hz : (minpoly F x.toLinearMap).natDegree = 0 := by simpa using hdeg
      omega
    have hassoc : Associated q (minpoly F x.toLinearMap) :=
      (hqirr.dvd_iff.mp hm_dvd_q).resolve_left hm_notunit
    exact hassoc.irreducible hqirr

theorem ggF4TWP_minpoly_natDegree_dvd_two (hF : Nat.card F = 4)
    (hV : Module.finrank F V = 6) (a x : V ≃ₗ[F] V) (ha : a ^ 13 = 1) (ha1 : a ≠ 1)
    (hax : a * x = x * a) (hx : x ^ 15 = 1) :
    (minpoly F x.toLinearMap).natDegree ∣ 2 := by
  classical
  have hirr : Irreducible (minpoly F x.toLinearMap) :=
    ggF4TWP_minpoly_irreducible hF hV a x ha ha1 hax hx
  have hT15 : (x : V →ₗ[F] V) ^ 15 = 1 := by
    have h := (map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) x 15).symm
    rwa [hx, map_one] at h
  have hdvd : minpoly F x.toLinearMap ∣ X ^ 15 - 1 :=
    minpoly.dvd F x.toLinearMap (by simp [hT15])
  have hdd : minpoly F x.toLinearMap ∣ X ^ (Nat.card F) ^ 2 - X := by
    have h16 : (X : F[X]) ^ (Nat.card F) ^ 2 - X = X ^ 16 - X := by
      rw [hF]
      norm_num
    have hsplit : (X : F[X]) ^ 16 - X = X * (X ^ 15 - 1) := by ring
    rw [h16, hsplit]
    exact dvd_mul_of_dvd_right hdvd X
  exact Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hirr hdd

end Image

theorem ggF4TWP_seventeen_dvd_card_GL_six (E : Type) [Field E] [Finite E]
    (hE : Nat.card E = 4) : 17 ∣ Nat.card (GL (Fin 6) E) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  rw [Matrix.card_GL_field (𝔽 := E) (n := 6), ← Nat.card_eq_fintype_card, hE]
  have hfac : 17 ∣ (4 ^ 6 - 4 ^ 2) := by norm_num
  exact hfac.trans
    (Finset.dvd_prod_of_mem (fun i : Fin 6 => (4 ^ 6 - 4 ^ (i : ℕ))) (Finset.mem_univ 2))

theorem ggF4TWP_seventeen_dvd_card_GL_three (E : Type) [Field E] [Finite E]
    (hE : Nat.card E = 16) : 17 ∣ Nat.card (GL (Fin 3) E) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  rw [Matrix.card_GL_field (𝔽 := E) (n := 3), ← Nat.card_eq_fintype_card, hE]
  have hfac : 17 ∣ (16 ^ 3 - 16 ^ 1) := by norm_num
  exact hfac.trans
    (Finset.dvd_prod_of_mem (fun i : Fin 3 => (16 ^ 3 - 16 ^ (i : ℕ))) (Finset.mem_univ 1))

theorem ggF4TWP_exists_seventeen_commute {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (A X : GL (Fin 6) F) (hA : A ^ 13 = 1) (hA1 : A ≠ 1)
    (hX : X ^ 15 = 1) (hAX : A * X = X * A) :
    ∃ U : GL (Fin 6) F, U ^ 17 = 1 ∧ U ≠ 1 ∧ X * U = U * X ∧
      U ∈ LargeEvenSLGroup (Fin 6) F := by
  classical
  let e := ggF4TWP_glToLinearEquiv F
  have hV : Module.finrank F (Fin 6 → F) = 6 := Module.finrank_fin_fun F
  have ha : e A ^ 13 = 1 := by rw [← map_pow e A 13, hA, map_one]
  have ha1 : e A ≠ 1 := fun h => hA1 (e.injective (h.trans (map_one e).symm))
  have hx : e X ^ 15 = 1 := by rw [← map_pow e X 15, hX, map_one]
  have hax : e A * e X = e X * e A := by rw [← map_mul, hAX, map_mul]
  let m : F[X] := minpoly F (e X).toLinearMap
  have hirr : Irreducible m :=
    ggF4TWP_minpoly_irreducible hF hV (e A) (e X) ha ha1 hax hx
  have hdvd2 : m.natDegree ∣ 2 :=
    ggF4TWP_minpoly_natDegree_dvd_two hF hV (e A) (e X) ha ha1 hax hx
  haveI hFact : Fact (Irreducible m) := ⟨hirr⟩
  have hm0 : m ≠ 0 := minpoly.ne_zero_of_finite F (e X).toLinearMap
  haveI : Module.Finite F (AdjoinRoot m) := (AdjoinRoot.powerBasis hm0).finite
  haveI : Finite (AdjoinRoot m) := Module.finite_of_finite F
  have hdim : Module.finrank F (Fin 6 → F) =
      m.natDegree * Module.finrank (AdjoinRoot m)
        (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m) :=
    CFSG.RankThree.PartOne.KCPrimary.finrank_eq_natDegree_minpoly_mul_finrank_primaryComponent
      (e X).toLinearMap
  have hcardE : Nat.card (AdjoinRoot m) = 4 ^ m.natDegree := by
    have h := CFSG.RankThree.PartOne.KCPrimary.natCard_adjoinRoot_minpoly (K := F)
      (V := Fin 6 → F) (e X).toLinearMap
    rw [hF] at h
    exact h
  let ec : ↥(Subgroup.centralizer ({e X} : Set ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)))) ≃*
      Matrix.GeneralLinearGroup (Fin (Module.finrank (AdjoinRoot m)
        (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m)))
        (AdjoinRoot m) :=
    (CFSG.RankThree.PartOne.KCPrimary.centralizerEquivGeneralLinearGroupOfIrreducibleMinpoly
      (e X) hirr).trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot m)
        (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m)).trans
        (CFSG.ComponentClassification.CatalogueBProjectiveCoordinates.automorphismMatrixEquiv
          (AdjoinRoot m)
          (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m)))
  have h17card : 17 ∣
      Nat.card ↥(Subgroup.centralizer ({e X} : Set ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)))) := by
    rw [Nat.card_congr ec.toEquiv]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h1 | h2
    · have hn : Module.finrank (AdjoinRoot m)
          (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m) = 6 := by
        have h := hdim
        rw [h1, hV] at h
        omega
      have hE4 : Nat.card (AdjoinRoot m) = 4 := by rw [hcardE, h1]; norm_num
      rw [hn]
      exact ggF4TWP_seventeen_dvd_card_GL_six (AdjoinRoot m) hE4
    · have hn : Module.finrank (AdjoinRoot m)
          (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (e X).toLinearMap m) = 3 := by
        have h := hdim
        rw [h2, hV] at h
        omega
      have hE16 : Nat.card (AdjoinRoot m) = 16 := by rw [hcardE, h2]; norm_num
      rw [hn]
      exact ggF4TWP_seventeen_dvd_card_GL_three (AdjoinRoot m) hE16
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  haveI : Finite ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) :=
    Finite.of_equiv (GL (Fin 6) F) e.toEquiv
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({e X} : Set ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F))))) 17 h17card
  have hu17 : (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) ^ 17 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa using congrArg (fun w : ↥(Subgroup.centralizer
      ({e X} : Set ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)))) =>
      (w : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F))) h
  have hu1 : (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) ≠ 1 := by
    intro h1
    have h2 : u = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hu
    omega
  have hucomm : (e X : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) *
      (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) =
      (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) * e X :=
    (Subgroup.mem_centralizer_iff.mp u.2) (e X) (Set.mem_singleton _)
  let U : GL (Fin 6) F := e.symm (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F))
  have hU17 : U ^ 17 = 1 := by
    rw [show U = e.symm (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) from rfl,
      ← map_pow e.symm (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) 17, hu17, map_one]
  have hU1 : U ≠ 1 := by
    intro h
    apply hu1
    have h2 : e U = 1 := by rw [h, map_one]
    simpa [U] using h2
  have hXU : X * U = U * X := by
    have h : e.symm ((e X) * (u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F))) =
        e.symm ((u : (Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) * e X) := by rw [hucomm]
    simpa [U] using h
  have hcardF : Nat.card Fˣ = 3 := by
    have h := Nat.card_units F
    rw [hF] at h
    simpa using h
  have hdet17 : (Matrix.GeneralLinearGroup.det U) ^ 17 = 1 := by
    rw [← map_pow, hU17, map_one]
  have hdet3 : (Matrix.GeneralLinearGroup.det U) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := Matrix.GeneralLinearGroup.det U)
    rwa [hcardF] at h
  have hdet1 : Matrix.GeneralLinearGroup.det U = 1 := by
    have hg : (Matrix.GeneralLinearGroup.det U) ^ (Nat.gcd 17 3) = 1 :=
      pow_gcd_eq_one.mpr ⟨hdet17, hdet3⟩
    rwa [show Nat.gcd 17 3 = 1 by norm_num, pow_one] at hg
  have hdetmat : ((U : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply U, hdet1, Units.val_one]
  exact ⟨U, hU17, hU1, hXU, CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff.mpr hdetmat⟩

end CFSG.StandardType
