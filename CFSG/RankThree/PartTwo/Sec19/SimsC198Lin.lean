module

public import CFSG.Open.PGLModelDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.KFacts.KS21SylowL44
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL62
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL72
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG.PGLModel (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.KFacts.KS21 (SylowModel wreathHom wreathHom_injective)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (rot3)
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (equivSL card_M_eq sylowModel_projSL)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecHom vecHom_injective conj_vecElt)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
  (slEquivProjSL not_three_dvd_card_outer_projSL_gf2)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L62 (card_SL6 factorization_card_SL6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L72 (card_SL7 factorization_card_SL7)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

private theorem wreath_central_card {A Q : Type} [Group A] [Group Q] [Finite A] [Nontrivial A]
    (D : Subgroup (A ≀ᵣ Q)) (hc : ∀ x ∈ D, ∀ y : A ≀ᵣ Q, x * y = y * x) :
    Nat.card D ≤ Nat.card A := by
  classical
  have key : ∀ x : A ≀ᵣ Q, (∀ y : A ≀ᵣ Q, x * y = y * x) →
      x.right = 1 ∧ ∀ k, x.left k = x.left 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hq : x.right = 1 := by
      by_contra hq
      have h := congrArg (fun w : A ≀ᵣ Q => w.left 1)
        (hx ⟨fun k => if k = 1 then a else 1, 1⟩)
      simp only [RegularWreathProduct.mul_left, Pi.mul_apply, inv_one, mul_one, one_mul,
        inv_eq_one, hq, if_true, if_false] at h
      exact ha (by simpa using h.symm)
    refine ⟨hq, fun k => ?_⟩
    have h := congrArg (fun w : A ≀ᵣ Q => w.left 1) (hx ⟨1, k⁻¹⟩)
    simpa [hq] using h.symm
  refine Nat.card_le_card_of_injective (fun d : D => (d : A ≀ᵣ Q).left 1) fun d₁ d₂ h => ?_
  obtain ⟨hr₁, hl₁⟩ := key d₁ (hc d₁ d₁.2)
  obtain ⟨hr₂, hl₂⟩ := key d₂ (hc d₂ d₂.2)
  refine Subtype.ext (RegularWreathProduct.ext (funext fun k => ?_) (hr₁.trans hr₂.symm))
  rw [hl₁ k, hl₂ k]
  exact h

private abbrev Wr3 : Type := Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

private theorem card_wr3 : Nat.card Wr3 = 81 := by
  rw [RegularWreathProduct.card]
  simp

private theorem card_le_three_of_mulEquiv {Q : Type} [Group Q] (e : Q ≃* Wr3) (D : Subgroup Q)
    (hc : ∀ x ∈ D, ∀ y : Q, x * y = y * x) : Nat.card D ≤ 3 := by
  have hD : ∀ x ∈ D.map e.toMonoidHom, ∀ y : Wr3, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hc x hx y]
  have h := wreath_central_card (D.map e.toMonoidHom) hD
  rw [Subgroup.card_map_of_injective e.injective] at h
  simpa using h

private theorem card_le_three_of_sylowModel {S : Type} [Group S] [Finite S]
    (hS : SylowModel S Wr3) (P D : Subgroup S) (hP : Nat.card P = 81) (hDP : D ≤ P)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW : Nat.card Wr3 = 3 ^ (Nat.card S).factorization 3 := by
    obtain ⟨Φ, -, hW⟩ := hS
    exact hW
  have hP' : Nat.card P = 3 ^ (Nat.card S).factorization 3 := by
    rw [hP, ← hW, card_wr3]
  obtain ⟨e⟩ := hS.nonempty_mulEquiv (Sylow.ofCard P hP')
  have e' : P ≃* Wr3 := (MulEquiv.subgroupCongr (Sylow.coe_ofCard P hP').symm).trans e
  have hc' : ∀ x ∈ D.subgroupOf P, ∀ y : P, x * y = y * x := by
    intro x hx y
    apply Subtype.ext
    exact hc x hx y y.2
  have h := card_le_three_of_mulEquiv e' (D.subgroupOf P) hc'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv] at h

private theorem sylowModel_of_wreathFacts {X : Type} [Group X] {z : Fin 3 → X} {t : X}
    (hf : WreathFacts z t) (hcard : Nat.card Wr3 = 3 ^ (Nat.card X).factorization 3) :
    SylowModel X Wr3 := by
  have hwτ : ∀ v : Fin 3 → ZMod 3, t * vecHom hf (Multiplicative.ofAdd v) =
      vecHom hf (Multiplicative.ofAdd (rot3 v)) * t := fun v => by
    have h := conj_vecElt hf v
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  refine ⟨wreathHom (vecHom hf) t hf.pow_t hwτ,
    wreathHom_injective (vecHom_injective hf) hf.pow_t hwτ ⟨![1, 0, 0], ?_⟩, hcard⟩
  intro h
  exact one_ne_zero (congrFun h 0).symm

theorem l44_not_three_dvd_outer :
    ¬ 3 ∣ Nat.card (Outer (projSL 4 (GaloisField 2 2))) := by
  intro h3
  have hd := higher_linear_outer_order_divides_field_gcd_bound (k := GaloisField 2 2) (p := 2)
    (f := 2) (n := 4) Nat.prime_two (by norm_num) (by norm_num)
    (GaloisField.card 2 2 (by norm_num))
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 (GaloisField 2 2))).toEquiv] at h3
  have h := h3.trans hd
  norm_num at h

theorem l44_not_dvd_243 : ¬ 243 ∣ Nat.card (projSL 4 (GaloisField 2 2)) := by
  rw [Nat.card_congr equivSL.toEquiv, card_M_eq]
  norm_num

theorem l44_sylow_center (P D : Subgroup (projSL 4 (GaloisField 2 2))) (hP : IsPGroup 3 P)
    (hP81 : Nat.card P = 81) (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 :=
  card_le_three_of_sylowModel sylowModel_projSL P D hP81 hDP hc

theorem l62_not_three_dvd_outer :
    ¬ 3 ∣ Nat.card (Outer (projSL 6 (GaloisField 2 1))) :=
  not_three_dvd_card_outer_projSL_gf2 (by norm_num)

theorem l62_not_dvd_243 : ¬ 243 ∣ Nat.card (projSL 6 (GaloisField 2 1)) := by
  rw [← Nat.card_congr (slEquivProjSL (by norm_num : 1 ≤ 6)).toEquiv, card_SL6]
  norm_num

theorem l62_sylow_center (P D : Subgroup (projSL 6 (GaloisField 2 1))) (hP : IsPGroup 3 P)
    (hP81 : Nat.card P = 81) (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 := by
  haveI : Finite (projSL 6 (GaloisField 2 1)) :=
    Finite.of_equiv _ (slEquivProjSL (by norm_num : 1 ≤ 6)).toEquiv
  have hS : SylowModel (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) Wr3 :=
    sylowModel_of_wreathFacts CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L62.wreathFacts
      (by rw [factorization_card_SL6, card_wr3]; norm_num)
  exact card_le_three_of_sylowModel (hS.of_mulEquiv (slEquivProjSL (by norm_num : 1 ≤ 6))) P D
    hP81 hDP hc

theorem l72_not_three_dvd_outer :
    ¬ 3 ∣ Nat.card (Outer (projSL 7 (GaloisField 2 1))) :=
  not_three_dvd_card_outer_projSL_gf2 (by norm_num)

theorem l72_not_dvd_243 : ¬ 243 ∣ Nat.card (projSL 7 (GaloisField 2 1)) := by
  rw [← Nat.card_congr (slEquivProjSL (by norm_num : 1 ≤ 7)).toEquiv, card_SL7]
  norm_num

theorem l72_sylow_center (P D : Subgroup (projSL 7 (GaloisField 2 1))) (hP : IsPGroup 3 P)
    (hP81 : Nat.card P = 81) (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 := by
  haveI : Finite (projSL 7 (GaloisField 2 1)) :=
    Finite.of_equiv _ (slEquivProjSL (by norm_num : 1 ≤ 7)).toEquiv
  have hS : SylowModel (Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1)) Wr3 :=
    sylowModel_of_wreathFacts CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L72.wreathFacts
      (by rw [factorization_card_SL7, card_wr3]; norm_num)
  exact card_le_three_of_sylowModel (hS.of_mulEquiv (slEquivProjSL (by norm_num : 1 ≤ 7))) P D
    hP81 hDP hc

end CFSG.RankThree.PartTwo.Sec19.SimsC198
