module

public import CFSG.Open.PGLModelDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.KFacts.KS21SylowCore
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434OmegaMinus
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG.PGLModel (projSp projOmegaMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.KFacts.KS21 (SylowModel wreathHom wreathHom_injective)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (rot3)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecHom vecHom_injective conj_vecElt)

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

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  (sp62Equiv card_outer_H6 wreathFacts_zH factorization_card_H6)

theorem sp62_not_three_dvd_outer :
    ¬ 3 ∣ Nat.card (Outer (projSp 3 (GaloisField 2 1))) := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    sp62Equiv).toEquiv, card_outer_H6]
  norm_num

theorem sp62_not_dvd_243 : ¬ 243 ∣ Nat.card (projSp 3 (GaloisField 2 1)) := by
  rw [CFSG.PGLModel.card_projSp_three_two]
  norm_num

theorem sp62_sylow_center
    (P D : Subgroup (projSp 3 (GaloisField 2 1))) (hP : IsPGroup 3 P)
    (hP81 : Nat.card P = 81) (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 := by
  haveI : Finite (projSp 3 (GaloisField 2 1)) := Finite.of_equiv _ sp62Equiv.symm.toEquiv
  have hS : SylowModel CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 Wr3 :=
    sylowModel_of_wreathFacts wreathFacts_zH (by rw [factorization_card_H6, card_wr3]; norm_num)
  exact card_le_three_of_sylowModel (hS.of_mulEquiv sp62Equiv.symm) P D hP81 hDP hc

open CFSG.EvenSmallLie.OmegaEightMinus (omegaT nonempty_mulEquiv_omegaT card_outer_omegaT)
open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus
  (statedClassicalModel_of_mulEquiv wreathFacts_omegaT factorization_card_omegaT)

private theorem nonempty_mulEquiv_omegaT_of_irreducible
    {b c : GaloisField 2 1} (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (projOmegaMinus 3 (GaloisField 2 1) b c ≃* omegaT) :=
  nonempty_mulEquiv_omegaT
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      statedClassicalModel_of_mulEquiv hbc (MulEquiv.refl _)⟩)

theorem om8m_not_three_dvd_outer {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ¬ 3 ∣ Nat.card (Outer (projOmegaMinus 3 (GaloisField 2 1) b c)) := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_omegaT_of_irreducible hbc
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv,
    card_outer_omegaT]
  norm_num

theorem om8m_not_dvd_243 {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ¬ 243 ∣ Nat.card (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  rw [Sec19.Step1911Proof.card_projOmegaMinus hbc]
  have h : CFSG.Open.ordTwistedD 4 (2 ^ 1) = 3 ^ 4 * 2437120 := by
    simp [CFSG.Open.ordTwistedD, Finset.prod_Icc_succ_top]
  rw [h]
  norm_num

theorem om8m_sylow_center
    {b c : GaloisField 2 1} (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (P D : Subgroup (projOmegaMinus 3 (GaloisField 2 1) b c)) (hP : IsPGroup 3 P)
    (hP81 : Nat.card P = 81) (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hc : ∀ x ∈ D, ∀ y ∈ P, x * y = y * x) : Nat.card D ≤ 3 := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_omegaT_of_irreducible hbc
  haveI : Finite (projOmegaMinus 3 (GaloisField 2 1) b c) := Finite.of_equiv _ θ.symm.toEquiv
  have hS : SylowModel omegaT Wr3 :=
    sylowModel_of_wreathFacts wreathFacts_omegaT
      (by rw [factorization_card_omegaT, card_wr3]; norm_num)
  exact card_le_three_of_sylowModel (hS.of_mulEquiv θ.symm) P D hP81 hDP hc

end CFSG.RankThree.PartTwo.Sec19.SimsC198
