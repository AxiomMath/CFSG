
module

public import CFSG.Sporadic.Schreier.J4SElevenBase1

public import CFSG.Sporadic.Schreier.J4SElevenCheck
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.Schreier.J4SRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix commutatorElement

theorem card_Q11_sylow :
    Nat.card Q11 = 11 ^ (Nat.card J).factorization 11 := by
  rw [card_Q11, card_J_eq]
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  have h29 : Nat.Prime 29 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h43 : Nat.Prime 43 := by norm_num
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization_pow h11,
    Nat.Prime.factorization h23, Nat.Prime.factorization h29, Nat.Prime.factorization h31,
    Nat.Prime.factorization h37, Nat.Prime.factorization h43, Finsupp.single_apply]
  norm_num

@[expose] def Q11Sylow :
    Sylow 11 J :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  Sylow.ofCard Q11 card_Q11_sylow

theorem Q11Sylow_coe :
    (Q11Sylow : Subgroup J) = Q11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact Sylow.coe_ofCard _ _

theorem R3E_J4_eleven_normalizer_transitivity_and_fixed_dimensions :
    ∃ x y z h₁ h₂ c : J,
      (∃ P : Sylow 11 J, (P : Subgroup J) = Subgroup.closure {x, y}) ∧
      IsExtraspecialPGroup 11 (Subgroup.closure ({x, y} : Set J)) ∧
      Nat.card (Subgroup.closure ({x, y} : Set J)) = 11 ^ 3 ∧
      Monoid.exponent (Subgroup.closure ({x, y} : Set J)) = 11 ∧ z = ⁅x, y⁆ ∧
      (Subgroup.center (Subgroup.closure ({x, y} : Set J))).map
        (Subgroup.closure ({x, y} : Set J)).subtype = Subgroup.zpowers z ∧
      h₁ ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set J) : Set J) ∧
      h₂ ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set J) : Set J) ∧
      h₁ * x * h₁⁻¹ = x ^ 7 * y ^ 3 * z ^ 2 ∧ h₁ * y * h₁⁻¹ = x ^ 3 * y ^ 3 * z ^ 9 ∧
      h₁ * z * h₁⁻¹ = z ∧ h₂ * x * h₂⁻¹ = x ^ 8 * y ^ 6 * z ^ 3 ∧
      h₂ * y * h₂⁻¹ = x ^ 10 * y ^ 5 * z ^ 8 ∧ h₂ * z * h₂⁻¹ = z ^ 2 ∧
      (∀ v w : Fin 2 → ZMod 11, v ≠ 0 → w ≠ 0 →
        ∃ g ∈ Submonoid.closure ({!![7, 3; 3, 3], !![8, 10; 6, 5]} :
          Set (Matrix (Fin 2) (Fin 2) (ZMod 11))), g *ᵥ v = w) ∧
      Nat.card {v : Fin 2 → ZMod 11 // v ≠ 0} = 120 ∧
      Module.finrank (ZMod 2) (rowFix ((x : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2))) = 12 ∧
      Module.finrank (ZMod 2) (rowFix ((y : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2))) = 12 ∧
      Module.finrank (ZMod 2) (rowFix ((z : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2))) = 2 ∧
      orderOf c = 23 ∧
      Module.finrank (ZMod 2) (rowFix ((c : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2))) = 2 :=
  ⟨qx, qy, qz, nrm₁, nrm₂, q23Elt, ⟨Q11Sylow, Q11Sylow_coe⟩, isExtraspecial_Q11, card_Q11,
    exponent_Q11, rfl, center_Q11, nrm₁_mem_normalizer, nrm₂_mem_normalizer, nrm₁_qx, nrm₁_qy,
    nrm₁_qz, nrm₂_qx, nrm₂_qy, nrm₂_qz, matAB_transitive, card_nonzero_eleven, finrank_rowFix_qx,
    finrank_rowFix_qy, finrank_rowFix_qz, orderOf_q23Elt, finrank_rowFix_q23⟩

end CFSG.Sporadic.J4Schreier
