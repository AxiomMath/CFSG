module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairSumC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_pair_comm_mul_mem (hc : Nine3Choice V T A K S X p g x) {Z J : Subgroup G}
    (hJZ : J ≤ Z) (hZW : Z ≤ nineW V S) {i a b : G} (ha : a ∈ Z) (haJ : ⁅i, a⁆ ∈ J)
    (hbJ : ⁅i, b⁆ ∈ J) : ⁅i, a * b⁆ ∈ J := by
  have hbZ : ⁅i, b⁆ ∈ Z := hJZ hbJ
  have hcomm : a * ⁅i, b⁆ * a⁻¹ = ⁅i, b⁆ := by
    rw [hc.core.nineW_mul_comm (hZW ha) (hZW hbZ)]
    group
  have hcomm' : ⁅i, a⁆ * a * ⁅i, b⁆ * a⁻¹ = ⁅i, a⁆ * ⁅i, b⁆ := by
    calc ⁅i, a⁆ * a * ⁅i, b⁆ * a⁻¹
        = ⁅i, a⁆ * (a * ⁅i, b⁆ * a⁻¹) := by group
      _ = ⁅i, a⁆ * ⁅i, b⁆ := by rw [hcomm]
  rw [commutatorElement_mul_right_eq_mul_conj, hcomm']
  exact J.mul_mem haJ hbJ

theorem nine3_pair_five_delta (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {B : Fin (4 + 1) → Subgroup G} {σ : Equiv.Perm (Fin (4 + 1))} {bb : Fin (4 + 1) → G}
    (he : Nine3PairEnum V K S A g 4 B σ bb) (hcard : Nat.card ↥(nineDelta V S) = 5) :
    ∀ i ∈ nineI V K, ⁅i, bb 1 * bb 2 * bb 3 * bb 4⁆ = 1 := by
  classical
  let J : Subgroup G := ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K
  have hJZ : J ≤ nineZ V K S :=
    iSup₂_le fun B hB => inf_le_left.trans (le_iSup₂_of_le B hB le_rfl)
  have hZW : nineZ V K S ≤ nineW V S := by
    rw [hc.core.nineW_eq]
    exact le_sup_right
  have hbbZ : ∀ k, k ≠ 0 → bb k ∈ nineZ V K S := fun k hk =>
    (le_iSup₂_of_le (B k) (he.Ω k hk) le_rfl : B k ≤ nineZ V K S) (he.bb_mem k hk).1
  have hbbK : ∀ k, k ≠ 0 → bb k ∈ K := fun k hk =>
    hc.core.S_le_K ((he.Ω k hk).2 (he.bb_mem k hk).1)
  have hcK : bb 1 * bb 2 * bb 3 * bb 4 ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem (hbbK 1 (by decide)) (hbbK 2 (by decide)))
      (hbbK 3 (by decide))) (hbbK 4 (by decide))
  have hcommJ : ∀ {i : G}, i ∈ nineI V K → ∀ k, k ≠ 0 → ⁅i, bb k⁆ ∈ J := by
    intro i hi k hk
    have hmem : ⁅i, bb k⁆ ∈ ⁅nineI V K, B k⁆ :=
      Subgroup.commutator_mem_commutator hi (he.bb_mem k hk).1
    rw [hI.comm (B k) (he.Ω k hk)] at hmem
    exact (le_iSup₂_of_le (B k) (he.Ω k hk) le_rfl : B k ⊓ pCoreOf 2 K ≤ J) hmem
  have hcJ : ∀ i ∈ nineI V K, ⁅i, bb 1 * bb 2 * bb 3 * bb 4⁆ ∈ J := by
    intro i hi
    have h1 : ⁅i, bb 1⁆ ∈ J := hcommJ hi 1 (by decide)
    have h2 : ⁅i, bb 2⁆ ∈ J := hcommJ hi 2 (by decide)
    have h3 : ⁅i, bb 3⁆ ∈ J := hcommJ hi 3 (by decide)
    have h4 : ⁅i, bb 4⁆ ∈ J := hcommJ hi 4 (by decide)
    have ha1 : bb 1 ∈ nineZ V K S := hbbZ 1 (by decide)
    have ha2 : bb 1 * bb 2 ∈ nineZ V K S :=
      (nineZ V K S).mul_mem ha1 (hbbZ 2 (by decide))
    have ha3 : bb 1 * bb 2 * bb 3 ∈ nineZ V K S :=
      (nineZ V K S).mul_mem ha2 (hbbZ 3 (by decide))
    have hp1 : ⁅i, bb 1 * bb 2⁆ ∈ J :=
      nine3_pair_comm_mul_mem hc hJZ hZW ha1 h1 h2
    have hp2 : ⁅i, bb 1 * bb 2 * bb 3⁆ ∈ J :=
      nine3_pair_comm_mul_mem hc hJZ hZW ha2 hp1 h3
    have hp3 : ⁅i, (bb 1 * bb 2 * bb 3) * bb 4⁆ ∈ J :=
      nine3_pair_comm_mul_mem hc hJZ hZW ha3 hp2 h4
    simpa only [mul_assoc] using hp3
  exact nine3_delta_zero hc hI hcK (nine3_pair_five_central hc hI he hcard) hcJ

end CFSG.LocalAnalysis.WeakClosure81
