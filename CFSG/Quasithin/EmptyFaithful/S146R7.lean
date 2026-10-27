module

public import CFSG.Quasithin.EmptyFaithful.S146R6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_of_secIso_dihedral {A Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : SecIso A Q (DihedralGroup p)) : ∃ z ∈ A, z ∉ Q ∧ Odd (orderOf z) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h
  have hord : orderOf (e.symm (DihedralGroup.r 1)) = p := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm (DihedralGroup.r 1))
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow (y : G)
  have hzA : (y : G) ^ 2 ^ k ∈ A := A.pow_mem y.2 _
  refine ⟨(y : G) ^ 2 ^ k, hzA, fun hzQ => ?_, hk⟩
  have hone : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzA⟩ : ↥A) : ↥A ⧸ Q.subgroupOf A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
  have hpow : (e.symm (DihedralGroup.r 1)) ^ 2 ^ k = 1 := by
    rw [← hy, ← QuotientGroup.mk_pow]
    exact hone
  have hdvd : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hpow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

@[expose] def Stage14612Part : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      (p = 3 ∨ p = 5) ∧ ∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDec12 T M H p H₀ H₁ H₂ t

theorem stage14612_of_part (h5 : Stage1461Five) (h : Stage14612Part) : Stage14612 := by
  intro G _ _ T M S H PQ p hred
  obtain ⟨hp, hex⟩ := h G T M S H PQ p hred
  refine ⟨hp, hex, fun H₀ H₁ H₂ t hdec => ?_⟩
  have hH : IsHTM T M H := hred.isHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have key : ∀ Hi : Subgroup G, Hi ≤ H → pCoreOf 2 H ≤ Hi →
      (∃ z ∈ Hi, z ∉ pCoreOf 2 H ∧ Odd (orderOf z)) →
      quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper Hi⁆ := by
    rintro Hi hHiH hQHi ⟨z, hz1, hzQ, hzodd⟩
    have hX1 : oTwoUpper Hi ≠ ⊥ := by
      intro hbot
      have hzX : z ∈ oTwoUpper Hi := mem_oTwoUpper_of_odd hz1 hzodd
      rw [hbot, Subgroup.mem_bot] at hzX
      exact hzQ (hzX ▸ (pCoreOf 2 H).one_mem)
    have hXF : oTwoUpper Hi ≤ oTwoFstarIn H :=
      (((oTwoUpper_mono hHiH).trans (hred.oTwoUpper_le_pq hT2)).trans hred.le_oTwoPIn).trans
        (oTwoPIn_le_oTwoFstarIn hred.prime H)
    exact S.lemma_14_6_2 hH (h5 G T M S H hH) hX1 (S146A.oTwoUpper_idem Hi) hXF
      (hQHi.trans (le_normalizer_oTwoUpper Hi))
  exact ⟨key H₁ (hdec.le₁.trans hdec.le) hdec.Q₁
      (exists_odd_of_secIso_dihedral hred.prime hred.odd hdec.dihedral₁),
    key H₂ (hdec.le₂.trans hdec.le) hdec.Q₂
      (exists_odd_of_secIso_dihedral hred.prime hred.odd hdec.dihedral₂)⟩

theorem stageSection146_of_inputs_seven (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612Part) (h15 : Stage14615) (h17 : Stage14617)
    (h20 : Stage14620) (h21 : Stage14621) (h22 : Stage14622)
    (h23 : Stage14623) (hD4 : Stage146D4) (h24 : Stage14624)
    (hF1 : Stage146FRank) (hF2 : Stage146FH2) (hF3 : Stage146FFour)
    (h9 : Stage1469) (h105 : Stage14610Five) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs_six h1413 h11 h113 hedge h2 h3 h5 (stage14612_of_part h5 h12) h15 h17
    h20 h21 h22 h23 hD4 h24 hF1 hF2 hF3 h9 h105 h634

end CFSG.Quasithin
