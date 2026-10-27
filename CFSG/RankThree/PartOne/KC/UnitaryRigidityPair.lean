module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPair

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryScalar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem not_exceptional_of_three_lt {m : ℕ} (hq : 3 < ℓ ^ f) :
    (m, ℓ ^ f) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
  omega

theorem two_le_finrank_of_pair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Submodule K V} {u v : V} (hu : u ∈ W) (hv : v ∈ W) (hind : LinearIndependent K ![u, v]) :
    2 ≤ Module.finrank K W := by
  have h1 : LinearIndependent K ![(⟨u, hu⟩ : W), ⟨v, hv⟩] := by
    refine LinearIndependent.of_comp W.subtype ?_
    convert hind using 1
    ext i
    fin_cases i <;> rfl
  have := h1.fintype_card_le_finrank
  simpa using this

theorem torus_comm_of_good_eigenpair (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) {μ : K} (hμ : h.bar μ * μ = 1) {b₁ b₂ : Fin n → K}
    (hb : IsONPair h b₁ b₂)
    (hx₁ : ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₁ = μ • b₁)
    (hx₂ : ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₂ = μ • b₂)
    (hexc : (Module.finrank K (primaryComponent ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C μ)), ℓ ^ f) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)))
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hβ : ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    ∀ c : Kˣ, h.norm (c : K) = 1 →
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h b₁ b₂ c).map τ =
        torusMat h b₁ b₂ c * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have H := (S.planeData hx).primaryData
  have hμ' : h.norm μ = 1 := by
    change μ * h.bar μ = 1
    rw [mul_comm]
    exact hμ
  have hev : Module.End.HasEigenvalue ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hx₁, hb.ne_zero_left⟩
  have hmem := X_sub_C_mem_primaryFactors hev
  have hm : 2 ≤ Module.finrank K (primaryComponent ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C μ)) :=
    two_le_finrank_of_pair (mem_primaryComponent_X_sub_C.mpr hx₁)
      (mem_primaryComponent_X_sub_C.mpr hx₂) hb.linearIndependent
  have hgood := isGoodBlock_X_sub_C (hK := h) hmem hm hexc
  have hF := isPerfect_idSpecialBlock S hx ⟨⟨X - C μ, hmem⟩, hgood⟩
  intro c hc
  exact matrix_comm_of_perfect S.three_le S.ne hF M τ (hβ ⟨⟨X - C μ, hmem⟩, hgood⟩) _
    (torusUnitary_mem_idSpecialBlock h x H hμ hmem hb hx₁ hx₂ c hc)

end CFSG.RankThree.PartOne.KCUnitaryPair
