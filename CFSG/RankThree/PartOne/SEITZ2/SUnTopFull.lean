module

public import CFSG.RankThree.PartOne.SEITZ2.SUnBlocks
public import CFSG.RankThree.PartOne.SEITZ2.SUnMain

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan
open CFSG.LieType.BorelTits (unitaryInvolution)

section TopFull

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Subfield K}
  {σ₀ : k ≃+* k}

theorem su_pair_top_of_full (hσ : IsUnitaryInvolution (unitaryInvolution K 2 f))
    (hσ₀ : IsUnitaryInvolution σ₀)
    (hσk : ∀ c : k, unitaryInvolution K 2 f (c : K) = ((σ₀ c : k) : K)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hK : Nat.card (fixSub (unitaryInvolution K 2 f)) =
      Nat.card (ratFix (unitaryInvolution K 2 f) k) ^ p)
    {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1) (hωn : unitaryInvolution K 2 f ω * ω = 1)
    (hKsq : Nat.card K = (2 ^ f) ^ 2) (hq2 : 2 ^ f ≠ 2) {n : ℕ} (hn : 3 ≤ n + 1)
    (A : GL (Fin (n + 1)) K)
    (hA : conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1)
    (hfull : ∃ e : Fin (n + 1) → K, IsRat k e ∧ e ≠ 0 ∧
      herm (unitaryInvolution K 2 f) e e = 0 ∧ ∀ b : fixSub (unitaryInvolution K 2 f),
        ∃ t ∈ (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA),
          IsTv (unitaryInvolution K 2 f) t e (b : K)) :
    (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA) = ⊤ := by
  classical
  set σ := unitaryInvolution K 2 f with hσdef
  have hσi := hσ.invol
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set M := (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA) with hM
  have hRM : (phiN hσk).range ≤ M := le_sup_left
  have hu : σ (1 : K) * 1 = -1 := by
    rw [map_one, mul_one]
    linear_combination h2
  let W : WittData σ := ⟨1, ω, hu, hωn, hω1⟩
  have ha₂ : herm σ (W.hypA 0 : Fin 2 → K) (W.hypA 0) = 0 := W.herm_hypA_hypA
  have hb₂ : herm σ (W.hypB 0 : Fin 2 → K) (W.hypB 0) = 0 := W.herm_hypB_hypB
  have hab₂ : herm σ (W.hypA 0 : Fin 2 → K) (W.hypB 0) = 1 := W.herm_hypA_hypB
  have hexp : ∀ v : Fin 2 → K, v = herm σ (W.hypB 0 : Fin 2 → K) v • (W.hypA 0 : Fin 2 → K) +
      herm σ (W.hypA 0 : Fin 2 → K) v • (W.hypB 0 : Fin 2 → K) := W.eq_hyp_expansion hσi
  have ha₂r : ∀ x, (W.hypA 0 : Fin 2 → K) x ∈ k := by
    intro x
    rw [WittData.hypA, Pi.add_apply]
    exact k.add_mem (pi_single_mem _ _ k.one_mem) (pi_single_mem _ _ k.one_mem)
  have hb₂r : ∀ x, (W.hypB 0 : Fin 2 → K) x ∈ k := by
    intro x
    rw [WittData.hypB, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    exact k.mul_mem (k.inv_mem (k.sub_mem k.one_mem hωk))
      (k.add_mem (pi_single_mem _ _ k.one_mem)
        (pi_single_mem _ _ (k.mul_mem k.one_mem hωk)))
  have hfr : ∀ i : Fin n, (i : ℕ) + 2 ≤ n + 1 := fun i => by omega
  have haI : ∀ i : Fin n, herm σ (embVec (n + 1) i (W.hypA 0 : Fin 2 → K))
      (embVec (n + 1) i (W.hypA 0 : Fin 2 → K)) = 0 := fun i => by
    rw [herm_embVec_embVec (hfr i)]; exact ha₂
  have hbI : ∀ i : Fin n, herm σ (embVec (n + 1) i (W.hypB 0 : Fin 2 → K))
      (embVec (n + 1) i (W.hypB 0 : Fin 2 → K)) = 0 := fun i => by
    rw [herm_embVec_embVec (hfr i)]; exact hb₂
  have habI : ∀ i : Fin n, herm σ (embVec (n + 1) i (W.hypA 0 : Fin 2 → K))
      (embVec (n + 1) i (W.hypB 0 : Fin 2 → K)) = 1 := fun i => by
    rw [herm_embVec_embVec (hfr i)]; exact hab₂
  obtain ⟨e, he, he0, heiso, hefull⟩ := hfull
  have hM_rat : ∀ a : Fin (n + 1) → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c := by
    intro a ha' hiso c hc hσc
    obtain ⟨t, htR, ht⟩ := exists_phiN_isTv hσ₀.invol hσk ha' hiso hc hσc
    exact ⟨t, hRM htR, ht⟩
  have hne0 : ∀ i : Fin n, embVec (n + 1) i (W.hypA 0 : Fin 2 → K) ≠ 0 := fun i h => by
    have := habI i
    rw [h, herm_zero_left] at this
    exact zero_ne_one this
  have hblock : ∀ i : Fin n, (blockEmb2 K 2 f n i).range ≤ M := by
    intro i
    have hfull_i : ∀ b : fixSub σ, ∃ t ∈ M,
        IsTv σ t (embVec (n + 1) i (W.hypA 0 : Fin 2 → K)) (b : K) := by
      intro b
      obtain ⟨r, hrR, hr⟩ := exists_phiN_smul_eq hn hσ₀ hσk he (embVec_isRat ha₂r) he0
        (hne0 i) heiso (haI i)
      obtain ⟨t₀, ht₀M, ht₀⟩ := hefull b
      refine ⟨r * t₀ * r⁻¹, M.mul_mem (M.mul_mem (hRM hrR) ht₀M) (M.inv_mem (hRM hrR)), ?_⟩
      have := ht₀.conj r
      rwa [hr] at this
    have hplane := range_planeSUN_le hσ hp hp2 hK (haI i) (hbI i) (habI i)
      (embVec_isRat hb₂r) hM_rat hfull_i
    exact range_blockEmb2_le hσ i ha₂ hb₂ hab₂ hexp (haI i) (hbI i) (habI i) hplane
  exact eq_top_of_blocks hKsq hq2 hblock

end TopFull

end CFSG.RankThree.PartOne.SEITZ2
