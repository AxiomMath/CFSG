module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace AutOm

section Roots

variable {K : Type} [Field K] {n : ℕ}

@[expose] def PlusRootElt (hn : 3 ≤ n) (r : matrixDerived (coordinateQuadPlus n K)) : Prop :=
  ∃ (i j : Fin n) (hij : i ≠ j) (s t : Bool) (a : K) (u : spinGroup (quadPlus n K)),
    r = spinModelPlus hn (u * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * u⁻¹)

theorem plusRootElt_of_modelRoot (hn : 3 ≤ n) {r : matrixDerived (coordinateQuadPlus n K)}
    (hr : GGModelRoot (plusDatum n K hn) .POmegaPlus (spinModelPlus hn) r) :
    PlusRootElt hn r := by
  obtain ⟨-, γ, ⟨hγ, -⟩, u, z, hz, rfl⟩ := hr
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  have hz' : z ∈ ((plusFrame n K hn).longRoot hij s t).range := by
    rw [← hX]
    exact hz
  obtain ⟨c₀, rfl⟩ := hz'
  exact ⟨i, j, hij, s, t, Multiplicative.toAdd c₀, u, rfl⟩

end Roots

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem autModel_plus (hn5 : 5 ≤ n) (R : matrixDerived (coordinateQuadPlus n K) → Prop)
    (hρ : ∀ r, R r → GGGoodAut r (plusRefl (by omega)))
    (hφ : ∀ σ : K ≃+* K, σ * σ = 1 → σ ≠ 1 → ∀ r, R r →
      GGGoodAut r (fieldAutP n σ) ∧ GGGoodAut r (plusRefl (by omega) * fieldAutP n σ)) :
    GGAutModel (matrixDerived (coordinateQuadPlus n K)) R := by
  refine ⟨inner _, plusCompl (by omega), inner_normal _, le_rfl, ?_,
    fun σ => exists_inner_mul_plusCompl hn5 σ, inner_inf_plusCompl (by omega),
    fun r hr c hc hc2 hc1 e he => AutSt.goodAut_conj_inner ?_ he⟩
  · rw [show inner (matrixDerived (coordinateQuadPlus n K)) =
        (MulAut.conj : matrixDerived (coordinateQuadPlus n K) →* _).range from rfl,
      Subgroup.relIndex_self]
    exact odd_one
  · rcases involution_plusCompl (by omega) hc hc2 hc1 with rfl | ⟨σ, hσσ, hσ1, rfl | rfl⟩
    · exact hρ r hr
    · exact (hφ σ hσσ hσ1 r hr).1
    · exact (hφ σ hσσ hσ1 r hr).2

end Model

end AutOm

section Family

@[expose] def GGAutModelPlusFourInput : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    ∃ (C : Type) (_ : Group C) (π : (ggU .POmegaPlus 4 f).K →* C), Function.Surjective π ∧
      π.ker = Subgroup.center (ggU .POmegaPlus 4 f).K ∧
      GGAutModel C (GGModelRoot (ggU .POmegaPlus 4 f).D .POmegaPlus π)

@[expose] def PlusGoodInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn5 : 5 ≤ n),
    (∀ r, AutOm.PlusRootElt (K := K) (by omega : 3 ≤ n) r →
      GGGoodAut r (AutOm.plusRefl (K := K) (by omega : 1 ≤ n))) ∧
    ∀ σ : K ≃+* K, σ * σ = 1 → σ ≠ 1 → ∀ r, AutOm.PlusRootElt (K := K) (by omega : 3 ≤ n) r →
      GGGoodAut r (AutOm.fieldAutP n σ) ∧
        GGGoodAut r (AutOm.plusRefl (K := K) (by omega : 1 ≤ n) * AutOm.fieldAutP n σ)

theorem ggAutModelAt_POmegaPlus_of_inputs (h4 : GGAutModelPlusFourInput)
    (hgood : PlusGoodInput) : GGAutModelAt .POmegaPlus := by
  intro n f hadm _ _
  obtain ⟨-, hf, hn4⟩ := hadm
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · exact h4 f hf
  · have hn : 3 ≤ n := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    obtain ⟨hρ, hφ⟩ := hgood (GaloisField 2 f) n hn5
    refine ⟨matrixDerived (coordinateQuadPlus n (GaloisField 2 f)), inferInstance,
      AutOm.spinModelPlus hn, AutOm.spinModelPlus_surjective hn, AutOm.ker_spinModelPlus hn,
      AutOm.autModel_plus hn5 _ (fun r hr => hρ r (AutOm.plusRootElt_of_modelRoot hn hr))
        fun σ hσσ hσ1 r hr => hφ σ hσσ hσ1 r (AutOm.plusRootElt_of_modelRoot hn hr)⟩

theorem ggAutStructureAt_POmegaPlus_of_inputs (h4 : GGAutModelPlusFourInput)
    (hgood : PlusGoodInput) : GGAutStructureAt .POmegaPlus :=
  ggAutStructureAt_of_autModelAt (ggAutModelAt_POmegaPlus_of_inputs h4 hgood)

end Family

end CFSG.StandardType
