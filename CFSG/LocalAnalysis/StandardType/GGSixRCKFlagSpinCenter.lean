module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmGen
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem rckFlagSC_eq_one_of_central_involution {K : Type} [Field K] [CharP K 2]
    {σ : Type} [Fintype σ] [DecidableEq σ] (Q : QuadraticForm K (σ → K))
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hirr : ∀ P : Submodule K (σ → K),
      (∀ g : spinGroup Q, ∀ x ∈ P, (Spin.spinAction Q g) x ∈ P) → P = ⊥ ∨ P = ⊤)
    {z : spinGroup Q} (hz : z * z = 1)
    (hcent : ∀ g : spinGroup Q, g * z = z * g) : z = 1 := by
  let S : (σ → K) ≃ₗ[K] (σ → K) := Spin.spinAction Q z
  let N : (σ → K) →ₗ[K] (σ → K) := (S : (σ → K) →ₗ[K] (σ → K)) - 1
  have hSS : S * S = 1 := by
    change Spin.spinAction Q z * Spin.spinAction Q z = 1
    rw [← map_mul, hz, map_one]
  have hSS' : ∀ x : σ → K,
      (↑S : (σ → K) →ₗ[K] (σ → K)) ((↑S : (σ → K) →ₗ[K] (σ → K)) x) = x := fun x => by
    have := congrArg (fun e : (σ → K) ≃ₗ[K] (σ → K) => e x) hSS
    simpa using this
  have hN2 : ∀ x : σ → K, N (N x) = 0 := by
    intro x
    have hx2 : x + x = 0 := by rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
    have hSx2 : S x + S x = 0 := by rw [← two_smul K (S x), CharTwo.two_eq_zero, zero_smul]
    have h : N (N x) = (x + x) - (S x + S x) := by
      simp only [N, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [hSS' x]
      module
    rw [h, hx2, hSx2, sub_zero]
  have hcomm : ∀ (g : spinGroup Q) (x : σ → K),
      N ((Spin.spinAction Q g) x) = (Spin.spinAction Q g) (N x) := by
    intro g x
    have hmul : S * (Spin.spinAction Q g) = (Spin.spinAction Q g) * S := by
      change Spin.spinAction Q z * Spin.spinAction Q g =
        Spin.spinAction Q g * Spin.spinAction Q z
      rw [← map_mul, ← map_mul, hcent g]
    have happ : (↑S : (σ → K) →ₗ[K] (σ → K)) ((Spin.spinAction Q g) x) =
        (Spin.spinAction Q g) ((↑S : (σ → K) →ₗ[K] (σ → K)) x) := by
      change S ((Spin.spinAction Q g) x) = (Spin.spinAction Q g) (S x)
      have h := congrArg (fun e : (σ → K) ≃ₗ[K] (σ → K) => e x) hmul
      simpa only [LinearEquiv.mul_apply] using h
    simp only [N, LinearMap.sub_apply, Module.End.one_apply, map_sub, happ]
  by_cases hN0 : N = 0
  · have hS1 : (S : (σ → K) →ₗ[K] (σ → K)) = 1 := sub_eq_zero.mp hN0
    have hmat : Spin.spinMatrix Q z = 1 := by
      apply Units.ext
      apply Matrix.mulVec_injective
      funext v
      show (↑(Spin.spinMatrix Q z) : Matrix σ σ K).mulVec v =
        (1 : Matrix σ σ K).mulVec v
      rw [Matrix.one_mulVec, Spin.spinMatrix_mulVec]
      have hSv : S v = v := by
        have := congrArg (fun L : (σ → K) →ₗ[K] (σ → K) => L v) hS1
        simpa using this
      simpa using hSv
    exact hinj (hmat.trans (map_one (Spin.spinMatrix Q)).symm)
  · have hNne : N ≠ 0 := hN0
    have hrange_le_ker : N.range ≤ N.ker := by
      rintro x ⟨y, rfl⟩
      exact hN2 y
    have hkerInv : ∀ g : spinGroup Q, ∀ x ∈ N.ker, (Spin.spinAction Q g) x ∈ N.ker := by
      intro g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hcomm g x, hx, map_zero]
    have hrange_ne : N.range ≠ ⊥ := fun h => hNne (LinearMap.range_eq_bot.mp h)
    have hker_ne_top : N.ker ≠ ⊤ := fun h => hNne (by
      apply LinearMap.ext
      intro x
      have : x ∈ N.ker := by rw [h]; trivial
      simpa using this)
    have hker_ne_bot : N.ker ≠ ⊥ := by
      intro hbot
      exact hrange_ne (le_bot_iff.mp (hbot ▸ hrange_le_ker))
    rcases hirr N.ker hkerInv with h | h
    · exact absurd h hker_ne_bot
    · exact absurd h hker_ne_top

theorem rckFlagSC_odd_center_of_irred {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : Type} [Fintype σ] [DecidableEq σ] (Q : QuadraticForm K (σ → K))
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hirr : ∀ P : Submodule K (σ → K),
      (∀ g : spinGroup Q, ∀ x ∈ P, (Spin.spinAction Q g) x ∈ P) → P = ⊥ ∨ P = ⊤) :
    Odd (Nat.card (Subgroup.center (spinGroup Q))) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have : Finite (spinGroup Q) := Finite.of_injective (Spin.spinMatrix Q) hinj
  have : Fintype (Subgroup.center (spinGroup Q)) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Fintype.card (Subgroup.center (spinGroup Q)) := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.mp heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card 2 h2dvd
  have hzsq : z * z = 1 := by
    rw [← pow_two, ← hzord]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzU : (z : spinGroup Q) * (z : spinGroup Q) = 1 := by
    simpa using congrArg Subtype.val hzsq
  have hcent : ∀ g : spinGroup Q, g * (z : spinGroup Q) = (z : spinGroup Q) * g :=
    fun g => Subgroup.mem_center_iff.mp z.2 g
  exact hz1 (Subtype.ext (rckFlagSC_eq_one_of_central_involution Q hinj hirr hzU hcent))

theorem rckFlagSC_irred_spinAction {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hE : elementaryGroup Q ≤ (Spin.spinAction Q).range)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∀ P : Submodule K V,
      (∀ g : spinGroup Q, ∀ x ∈ P, (Spin.spinAction Q g) x ∈ P) → P = ⊥ ∨ P = ⊤ := by
  intro P hPinv
  refine submodule_eq_bot_or_top_of_elementaryGroup_invariant hQ hP P ?_
  intro g hg x hx
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp (hE hg)
  exact hPinv u x hx

theorem rckFlagSC_oddCenter_quadPlus_zero (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadPlus 0 (GaloisField 2 g))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus 0 (GaloisField 2 g))) :=
    (MonoidHom.ker_eq_bot_iff _).1 (Spin.ker_spinMatrix_quadPlus_eq_bot h2)
  have : Subsingleton (spinGroup (Spin.quadPlus 0 (GaloisField 2 g))) :=
    hinj.subsingleton
  unfold OddCenterOf
  have hcard : Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 0 (GaloisField 2 g)))) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  rw [hcard]
  exact odd_one

theorem rckFlagSC_oddCenter_quadMinus_three (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadMinus 3 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  unfold OddCenterOf
  refine rckFlagSC_odd_center_of_irred _ ?_ ?_
  · exact (MonoidHom.ker_eq_bot_iff _).1
      (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 g) h2)
  · let F := GaloisField 2 g
    let b := (minusCoeffs 2 g).1
    let c := (minusCoeffs 2 g).2
    let Q : QuadraticForm F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := Spin.quadMinus 3 F b c
    have hQ : (polarBilin Q).Nondegenerate :=
      Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F (minusCoeffs_irr 2 g)
    have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) :=
      ⟨fun i => minusPair F b c i, fun i j hij => minusPair_orth hij⟩
    have hV : 5 ≤ Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      norm_num
    have hrange : (Spin.spinAction Q).range = elementaryGroup Q :=
      Spin.range_spinAction_eq_elementaryGroup hQ hV
        (minusPair_orth (K := F) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
          (by simp))
    exact rckFlagSC_irred_spinAction hQ (le_of_eq hrange.symm) hP

end CFSG.StandardType.RCKFlag
