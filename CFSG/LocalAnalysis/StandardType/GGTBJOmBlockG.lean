module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.LocalAnalysis.StandardType.GGTBJOmClass
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.LocalAnalysis.StandardType.GGTBJOmOrbit
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGClass
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGSupp
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGAct
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGMove

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem TBJOmData.blockG_pieces [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ a : ZMod p, a ≠ 0 ∧
      (∃ i, toAdd (f₀ i) ≠ 0 ∧ Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h) ∧
      (∀ i, toAdd (f₀ i) ≠ 0 → Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h →
        toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a) ∧
      (∀ i k : Fin r, i ≠ k → toAdd (f₀ i) ≠ 0 →
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ k) ≠ 0 →
        Δ.F.U k ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ i) = toAdd (f₀ k) →
        ∃ n ∈ specialBlock Q (Δ.τ f₀) h ⊓ orthDerived Q,
          ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) f)) ∧
      (∀ i k : Fin r, toAdd (f₀ i) ≠ 0 →
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ k) ≠ 0 →
        Δ.F.U k ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f₀ i) = a →
        toAdd (f₀ k) = -a →
        ∃ n ∈ specialBlock Q (Δ.τ f₀) h ⊓ orthDerived Q,
          ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) (dinv i k f))) ∧
      (∀ f : Fin r → Multiplicative (ZMod p),
        (∃ m : ZMod p, ∀ i, toAdd (f₀ i) ≠ 0 →
          Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h → toAdd (f i) = m * toAdd (f₀ i)) →
          ∀ j ∈ specialBlock Q (Δ.τ f₀) h, Δ.τ f * j = j * Δ.τ f) := by
  classical
  have hy : OddOrderIsometry Q p (Δ.τ f₀) := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have h0 : h.coeff 0 ≠ 0 := hy.coeff_zero_ne hh
  have horb := Δ.orbitSpace_eq hp2 hQ hA f₀ hh hX
  obtain ⟨i₀, hi₀, hU₀⟩ := Δ.exists_piece hp2 hQ hA f₀ hh hX
  refine ⟨toAdd (f₀ i₀), hi₀, ⟨i₀, hi₀, hU₀⟩, ?_, ?_, ?_, ?_⟩
  · intro i hi hUi
    exact eq_or_eq_neg_of_ker_or_reciprocal_ker hp2 Δ.c Δ.finrank_D Δ.c_pow Δ.c_fix Δ.c_twist
      Δ.c_roots hirr hX h0 hi₀ hi (Δ.piece_ker hp2 hQ hA f₀ hh hX i₀ hi₀ hU₀)
      (Δ.piece_ker hp2 hQ hA f₀ hh hX i hi hUi)
  · intro i k hik hi hUi hk hUk hik'
    obtain ⟨w, hw, hsupp, hconj⟩ := Δ.swapMove i k hik
    exact Δ.exists_mem_specialBlock_conj hy hh hUi hUk hw hsupp
      (fun f => permAut (Equiv.swap i k) f) hconj (permAut_swap_swap i k)
      (permAut_swap_eq_self (toAdd.injective hik'))
  · intro i k hi hUi hk hUk hia hka
    have hik : i ≠ k := ne_of_toAdd_eq_neg hp2 hi₀ hia hka
    obtain ⟨w₁, hw₁, hs₁, hc₁⟩ := Δ.swapMove i k hik
    obtain ⟨w₂, hw₂, hs₂, hc₂⟩ := Δ.dinvMove i k hik
    refine Δ.exists_mem_specialBlock_conj hy hh hUi hUk (mul_mem hw₁ hw₂) ?_
      (fun f => permAut (Equiv.swap i k) (dinv i k f)) ?_ (permAut_swap_dinv_involutive i k)
      (permAut_swap_dinv_eq_self hik ?_)
    · intro v hv₁ hv₂
      rw [LinearEquiv.mul_apply, hs₂ v hv₁ hv₂, hs₁ v hv₁ hv₂]
    · intro f
      rw [show w₁ * w₂ * Δ.τ f * (w₁ * w₂)⁻¹ = w₁ * (w₂ * Δ.τ f * w₂⁻¹) * w₁⁻¹ by group,
        hc₂, hc₁]
    · rw [hia, hka]
  · intro f ⟨m, hm⟩ j hj
    refine commute_of_eq_pow_on_orbitSpace hy hh (z := Δ.τ f) ?_ (n := m.val) ?_
      (specialBlock_le_supportedBlock h hj)
    · rw [← map_mul, ← map_mul, mul_comm]
    · exact Δ.τ_apply_eq_pow_of_orbit horb fun i hUi =>
        hm i (Δ.active_of_le_orbitSpace hp2 hQ hA f₀ hh hX i hUi) hUi

theorem TBJOmData.blockG [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ (a : ZMod p) (P : Fin r → Prop), a ≠ 0 ∧ (∃ i, P i) ∧
      (∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a) ∧
      (∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
        ∃ n ∈ specialBlock Q (Δ.τ f₀) h ⊓ orthDerived Q,
          ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) f)) ∧
      (∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
        ∃ n ∈ specialBlock Q (Δ.τ f₀) h ⊓ orthDerived Q,
          ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) (dinv i k f))) ∧
      (∀ f : Fin r → Multiplicative (ZMod p),
        (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
          ∀ j ∈ specialBlock Q (Δ.τ f₀) h, Δ.τ f * j = j * Δ.τ f) := by
  obtain ⟨a, ha, hne, hval, hswap, hmixed, hcent⟩ :=
    Δ.blockG_pieces hp2 hQ hA f₀ hh hX
  refine ⟨a, fun i => toAdd (f₀ i) ≠ 0 ∧ Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h,
    ha, hne, ?_, ?_, ?_, ?_⟩
  · rintro i ⟨hi, hUi⟩
    exact hval i hi hUi
  · rintro i k hik ⟨hi, hUi⟩ ⟨hk, hUk⟩ he
    exact hswap i k hik hi hUi hk hUk he
  · rintro i k ⟨hi, hUi⟩ ⟨hk, hUk⟩ hia hka
    exact hmixed i k hi hUi hk hUk hia hka
  · rintro f ⟨m, hm⟩ j hj
    refine hcent f ⟨m, fun i hi hUi => hm i (And.intro hi hUi)⟩ j hj

end OrthTorus

end CFSG.StandardType

end
