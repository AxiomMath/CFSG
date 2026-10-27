module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggNbrLSideSp_inn {ℓ n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) (LargeEvenGSpSet K ℓ) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSpGroup K ℓ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rwa [← Nat.card_eq_fintype_card])
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro φ hφ
  obtain ⟨A, hA, hAut⟩ := hφ
  obtain ⟨z, P₀, hP₀mem, hAeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_gspSet_decomp (s := ℓ) h2 hA
  let P : ↥(LargeEvenSpGroup K ℓ) := ⟨P₀, hP₀mem⟩
  refine ⟨LargeEvenProjMk (LargeEvenSpGroup K ℓ) P, ?_⟩
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin ℓ ⊕ Fin ℓ) K).subgroupOf (LargeEvenSpGroup K ℓ)) x
  have hmem' : P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹ ∈ LargeEvenSpGroup K ℓ :=
    (LargeEvenSpGroup K ℓ).mul_mem
      ((LargeEvenSpGroup K ℓ).mul_mem hP₀mem h.2)
      ((LargeEvenSpGroup K ℓ).inv_mem hP₀mem)
  let h' : ↥(LargeEvenSpGroup K ℓ) := ⟨P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹, hmem'⟩
  have hh' : h' = P * h * P⁻¹ := Subtype.ext rfl
  have hcomm := Matrix.GeneralLinearGroup.scalar_commute (n := Fin ℓ ⊕ Fin ℓ) z
    (P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹)
  have hrel : (h' : GL (Fin ℓ ⊕ Fin ℓ) K) = A * h * A⁻¹ := by
    change P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹ = A * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * A⁻¹
    rw [hAeq]
    calc P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹
        = Matrix.GeneralLinearGroup.scalar (Fin ℓ ⊕ Fin ℓ) z *
            (P₀ * (h : GL (Fin ℓ ⊕ Fin ℓ) K) * P₀⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin ℓ ⊕ Fin ℓ) z)⁻¹ := by
          rw [hcomm]; group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin ℓ ⊕ Fin ℓ) z * P₀) *
            (h : GL (Fin ℓ ⊕ Fin ℓ) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin ℓ ⊕ Fin ℓ) z * P₀)⁻¹ := by group
  have h1 : φ (LargeEvenProjMk (LargeEvenSpGroup K ℓ) h) =
      LargeEvenProjMk (LargeEvenSpGroup K ℓ) h' := hAut h h' hrel
  have h2' : MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K ℓ) P)
        (LargeEvenProjMk (LargeEvenSpGroup K ℓ) h) =
      LargeEvenProjMk (LargeEvenSpGroup K ℓ) h' := by
    simp only [MulAut.conj_apply, hh', map_mul, map_inv]
  exact h2'.trans h1.symm

end CFSG.StandardType
