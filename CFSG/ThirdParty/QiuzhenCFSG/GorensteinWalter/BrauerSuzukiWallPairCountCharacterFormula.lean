module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.formula_1_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The involution-pair character formula

Bender's function `i(x)` counts ordered pairs of involutions with product
`x`.  Suzuki VI.(1.15) expands it in the irreducible-character basis and
therefore gives its scalar product with every signed irreducible character.
-/

namespace CFSG.GorensteinWalter

noncomputable section

open BenderSuzuki.External

universe u

/-- Bender's involution-pair count, regarded as a complex-valued function. -/
@[expose] public noncomputable def bswPairCountClassFunction
    (G : Type u) [Group G] (x : G) : ℂ :=
  bswPairCount G x

/-- The involution-pair count is a class function, and its scalar product
with a signed irreducible character is the corresponding coefficient in
Bender's character expansion. -/
public theorem BrauerSuzukiWallHypotheses.pairCount_character_formula
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Section1.IsClassFunction (bswPairCountClassFunction G) ∧
      ∀ chi : Section1.ClassFunction G,
        Section3.IsSignedIrreducibleCharacter chi →
          Section1.scalarProduct G chi (bswPairCountClassFunction G) =
            ((Nat.card G : ℂ) / (Nat.card h.H : ℂ) ^ 2) *
              (chi h.t ^ 2 / chi 1) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, xi, hxi, _b, _hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let mu : ι → Section1.ClassFunction G :=
    fun j => Section1.ofConjClassFunction (xi j)
  let Ct : ConjClasses G := ConjClasses.mk h.t
  let C1 : ConjClasses G := ConjClasses.mk (1 : G)
  let a : ι → ℂ := fun j => xi j Ct * xi j Ct / xi j C1
  let omega : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun j => star (a j)) mu
  let factor : ℂ :=
    (Nat.card G : ℂ) / (Nat.card h.H : ℂ) ^ 2
  have hmuClass : ∀ j, Section1.IsClassFunction (mu j) := by
    intro j
    exact Section1.ofConjClassFunction_isClassFunction (xi j)
  have homegaClass : Section1.IsClassFunction omega := by
    intro x g
    unfold omega Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [hmuClass j x g]
  have hCtCarrier : Ct.carrier = bswInvolutions G := by
    calc
      Ct.carrier = MulAction.orbit (ConjAct G) h.t := by
        simpa [Ct] using (ConjAct.orbit_eq_carrier_conjClasses h.t).symm
      _ = bswInvolutions G := (bswInvolutions_eq_orbit h).symm
  have hCtCard : Nat.card Ct.carrier = h.H.index := by
    rw [hCtCarrier, Nat.card_coe_set_eq]
    exact bswInvolutions_ncard_eq_index_H h
  have hHCard : (Nat.card h.H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := h.H)).ne'
  have hIndexCard : (h.H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := h.H))
  have hGroupCardCast :
      (Nat.card G : ℂ) = (Nat.card h.H : ℂ) * (h.H.index : ℂ) := by
    exact_mod_cast h.H.card_mul_index.symm
  have hfactorEq :
      (h.H.index : ℂ) * (h.H.index : ℂ) / (Nat.card G : ℂ) =
        factor := by
    dsimp [factor]
    rw [hGroupCardCast]
    field_simp [hHCard, hIndexCard]
  have hsumOmega (x : G) :
      star (omega x) =
        ∑ j : ι,
          xi j Ct * xi j Ct * star (xi j (ConjClasses.mk x)) /
            xi j C1 := by
    simp [omega, Section1.weightedFamilySum, a, mu, mul_assoc]
    rw [show @Finset.univ ι (Fintype.ofFinite ι) =
      @Finset.univ ι hι by ext; simp]
    apply Finset.sum_congr rfl
    intro j _hj
    change xi j Ct * xi j Ct / xi j C1 *
        star (xi j (ConjClasses.mk x)) =
      xi j Ct * (xi j Ct * star (xi j (ConjClasses.mk x))) / xi j C1
    ring
  have hcountStar (x : G) :
      (bswPairCount G x : ℂ) = factor * star (omega x) := by
    have hformula := Suzuki.VI.suzuki_ch6_formula_1_15
      xi hxi Ct Ct (ConjClasses.mk x) x
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
    rw [hCtCarrier] at hformula
    have hpairCast : (bswPairCount G x : ℂ) =
        (Nat.card
          {p : (bswInvolutions G) × (bswInvolutions G) |
            (p.1 : G) * (p.2 : G) = x} : ℂ) := by
      exact_mod_cast bswPairCount_eq_card_pair_subtype x
    have hformula' : (bswPairCount G x : ℂ) =
        ((Nat.card (bswInvolutions G) : ℂ) *
            (Nat.card (bswInvolutions G) : ℂ) / (Nat.card G : ℂ)) *
          (∑ j : ι,
            xi j Ct * xi j Ct * star (xi j (ConjClasses.mk x)) /
              xi j C1) := by
      simpa [C1] using hpairCast.trans hformula
    rw [Nat.card_coe_set_eq, bswInvolutions_ncard_eq_index_H h,
      hfactorEq, ← hsumOmega x] at hformula'
    exact hformula'
  have hcount (x : G) :
      (bswPairCount G x : ℂ) = factor * omega x := by
    have hs := congrArg star (hcountStar x)
    simpa [factor] using hs
  have hpairCountEq :
      bswPairCountClassFunction G = factor • omega := by
    ext x
    simpa [bswPairCountClassFunction] using hcount x
  have hpairCountClass :
      Section1.IsClassFunction (bswPairCountClassFunction G) := by
    rw [hpairCountEq]
    exact Section1.isClassFunction_smul factor omega homegaClass
  have hmuOrth : ∀ i j : ι,
      Section1.scalarProduct G (mu i) (mu j) =
        if i = j then 1 else 0 := by
    intro i j
    calc
      Section1.scalarProduct G (mu i) (mu j) =
          Theory.Character.classFunctionInner (xi i) (xi j) := by
        symm
        simpa [mu, Section1.toConjClassFunction_ofConjClassFunction] using
          (Section1.classFunctionInner_toConjClassFunction
            (mu i) (mu j) (hmuClass i) (hmuClass j))
      _ = if i = j then 1 else 0 :=
        Section1.representation_completeFamily_orthonormal hxi i j
  have hspMu : ∀ j : ι,
      Section1.scalarProduct G (mu j) omega = a j := by
    intro j
    unfold omega
    rw [Section1.scalarProduct_weightedFamilySum_right]
    simp [hmuOrth, a]
  refine ⟨hpairCountClass, ?_⟩
  intro chi hchi
  rcases hchi with ⟨epsilon, hepsilon, nu, hnu, rfl⟩
  have hnuClass : Section1.IsClassFunction nu :=
    Section1.isCharacter_isClassFunction nu
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hnu)
  have hnuConjIrr :=
    Section1.toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      hnuClass hnu
  obtain ⟨j, hj⟩ := hxi.2.1
    (Section1.toConjClassFunction nu hnuClass) hnuConjIrr
  have hmuj : mu j = nu := by
    ext x
    have hx := congrFun hj (ConjClasses.mk x)
    change xi j (ConjClasses.mk x) = nu x
    exact hx
  have hjt : xi j Ct = nu h.t := by
    change mu j h.t = nu h.t
    rw [hmuj]
  have hjone : xi j C1 = nu 1 := by
    change mu j 1 = nu 1
    rw [hmuj]
  have haj : a j = nu h.t ^ 2 / nu 1 := by
    simp [a, hjt, hjone, pow_two]
  have hnuOne : nu 1 ≠ 0 := by
    simpa [Section1.degree_apply] using
      Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup nu hnu
  have hspNu :
      Section1.scalarProduct G nu omega = nu h.t ^ 2 / nu 1 := by
    calc
      Section1.scalarProduct G nu omega =
          Section1.scalarProduct G (mu j) omega := by rw [hmuj]
      _ = a j := hspMu j
      _ = nu h.t ^ 2 / nu 1 := haj
  rw [hpairCountEq, Section1.scalarProduct_smul_right,
    Section1.scalarProduct_smul_left, hspNu]
  rcases hepsilon with rfl | rfl
  · simp [factor]
  · simp [factor]
    field_simp [hnuOne]

end

end CFSG.GorensteinWalter
