module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.Statements
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.MinusFacts
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusFacts
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusCover
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusFour
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.CaseA
import CFSG.OddTranspositions.PartFour.Fourteen.FiveReflectionList
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
import CFSG.OddTranspositions.PartFour.SeventeenFourSp
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Main

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81

theorem false_of_o4CaseAFacts_orthogonalPlus {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsMem : s ∈ imageClass hC) {f : ℕ} (hf : 3 ≤ f) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = 2 ^ f)
    (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      ↥(CFSG.PGLModel.orthogonalPlus 2 F))
    (hs : s * s = 1) (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hprim : ∀ B : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      B ⊆ {x | IsConj s x} → B.Nonempty →
      (∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
        (fun y => g * y * g⁻¹) '' B = B ∨
          Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x | IsConj s x}) : False := by
  have hchar : CharP F 2 := by
    have hFintype : Fintype F := Fintype.ofFinite F
    have hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcover := sl2_prod_cover_of_two_pow hf hcard
  have hfacts := o4CaseAFacts_of_mulEquiv_orthogonalPlus hF4 e hs hgen hcover hprim
  have hfacts' : O4CaseAFacts _ (imageClass hC) := by
    rwa [← imageClass_eq_setOf_isConj hC hsMem] at hfacts
  exact false_of_o4CaseAFacts hC hMZ hfacts'

theorem ascList_of_isOrthReflection_orthogonalPlus_four
    {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsMem : s ∈ imageClass hC) {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 4)
    (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      ↥(CFSG.PGLModel.orthogonalPlus 2 F))
    (hs : s * s = 1) (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hW : CFSG.OddTranspositions.PartThree.WongPSp4Five) : AscList G D := by
  have hchar : CharP F 2 := by
    have hFintype : Fintype F := Fintype.ofFinite F
    have hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨π, hπ⟩ :=
    exists_isFiveReflectionModel_of_mulEquiv_orthogonalPlus_four hcard e hs hgen
  have hmod : ∃ π, PartThree.IsFiveReflectionModel 3 true π (imageClass hC) :=
    ⟨π, by rwa [imageClass_eq_setOf_isConj hC hsMem]⟩
  have h11 := PartThree.theorem11_1_holds hW G D hC hrad
    (solvableRadical_eq_center_of_le_center hMZ) hmod
  exact ascList_of_isFiveReflectionModel (n := 4) (by norm_num) h11

theorem false_of_o4CaseAFacts_orthogonalMinus {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsMem : s ∈ imageClass hC) {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = 2 ^ f) {b c : F}
    (hirr : ∀ t : F, t ^ 2 + b * t + c ≠ 0)
    (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      ↥(CFSG.PGLModel.orthogonalMinus 1 F b c))
    (hs : s * s = 1) (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hprim : ∀ B : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      B ⊆ {x | IsConj s x} → B.Nonempty →
      (∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
        (fun y => g * y * g⁻¹) '' B = B ∨
          Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x | IsConj s x}) : False := by
  have hchar : CharP F 2 := by
    have hFintype : Fintype F := Fintype.ofFinite F
    have hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hfacts := o4CaseAFacts_of_mulEquiv_orthogonalMinus hf hcard hirr e hs hgen hprim
  have hfacts' : O4CaseAFacts _ (imageClass hC) := by
    rwa [← imageClass_eq_setOf_isConj hC hsMem] at hfacts
  exact false_of_o4CaseAFacts hC hMZ hfacts'

theorem theorem4OFour_holds
    (hW : CFSG.OddTranspositions.PartThree.WongPSp4Five) : Theorem4OFour := by
  intro G _ _ D hC hrad hMZ hO
  let X := Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)
  obtain ⟨s, hsMem, f, hf, hO⟩ := hO
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_quotient_H hC
  let φ : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hgen : Subgroup.closure {x : X | IsConj s x} = ⊤ := by
    rw [← imageClass_eq_setOf_isConj hC hsMem]
    exact imageClass_gen hC
  have hs : s * s = 1 := by
    obtain ⟨y, hy, rfl⟩ := hsMem
    have hy2 : y * y = 1 := by
      have h := (DstarH_isOddTransp hC).1 y hy
      have h' := pow_orderOf_eq_one y
      rw [h] at h'
      simpa [pow_two] using h'
    show QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y *
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y = 1
    rw [← map_mul, hy2, map_one]
  have hprim : ∀ B : Set X, B ⊆ {x : X | IsConj s x} → B.Nonempty →
      (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨
        Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x : X | IsConj s x} := by
    intro B hB hBne hBst
    exact (subsingleton_or_eq_of_isOrthReflection (E := {x : X | IsConj s x})
      ⟨s, rfl⟩ hZ (IsConj.refl s) (m := 4) (f := f) (le_refl 4) (Or.inr hf) hO)
      B hB hBne hBst
  rcases hO with ⟨k, hk, hm, F, hFld, hFin, hcard, e₀, -⟩ |
      ⟨k, hk, hm, F, hFld, hFin, hcard, b, c, hirr, e₀, -⟩
  · have hk2 : k = 2 := by omega
    subst hk2
    let e : X ≃* ↥(CFSG.PGLModel.orthogonalPlus 2 F) := φ.trans e₀
    by_cases hf3 : 3 ≤ f
    · exact (false_of_o4CaseAFacts_orthogonalPlus hC hMZ hsMem hf3 hcard e hs hgen
        hprim).elim
    · have hf2 : f = 2 := by omega
      subst hf2
      exact ascList_of_isOrthReflection_orthogonalPlus_four hC hrad hMZ hsMem
        (by simpa using hcard) e hs hgen hW
  · have hk1 : k = 1 := by omega
    subst hk1
    let e : X ≃* ↥(CFSG.PGLModel.orthogonalMinus 1 F b c) := φ.trans e₀
    exact (false_of_o4CaseAFacts_orthogonalMinus hC hMZ hsMem hf hcard hirr e hs hgen
      hprim).elim

end CFSG.OddTranspositions.PartFour
