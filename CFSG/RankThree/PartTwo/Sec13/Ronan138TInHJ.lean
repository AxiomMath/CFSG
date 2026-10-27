module

public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Ronan138SNorm
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_range_conj_of_pow_three_pow_j2
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {σ : MulAut X} {k : ℕ}
    (hσ : σ ^ 3 ^ k = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  set φ : CFSG.ComponentClassification.OuterAutomorphisms.Outer X ≃* Multiplicative (ZMod 2) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).trans f with hφ
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 1 := by
    have h3 : φ (σ : CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ^ 3 ^ k = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h3
    exact h3
  have h2 : (σ : CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 1 :=
    φ.injective (h1.trans (map_one φ).symm)
  have h4 : σ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    (QuotientGroup.eq_one_iff σ).mp h2
  exact h4

variable {G : Type} [Group G] [Finite G]

theorem false_of_hj_torus
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) {E K : Subgroup G} {e d n : G}
    (hD : Sec13Data G E e K)
    (hφ : Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2))
    (hdΩ : Subgroup.zpowers d ∉ omegaA E) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hdE : d ∈ E)
    (hnC : n ∈ Subgroup.centralizer (E : Set G)) (hnk : ∃ k : ℕ, n ^ 3 ^ k = 1)
    (hn3 : n ^ 3 ∈ Subgroup.zpowers d) (hn31 : n ^ 3 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hφ
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := hspor
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hJ2p φ
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    center_eq_bot_of_mulEquiv φK hJ2z
  have heK : e ∉ K := not_mem_of_center_inf_commutator hD φ (by rw [hJ2z, bot_inf_eq])
  have hEK9 : Nat.card (E ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hD hJ2p φ
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hD.isElemAbelian.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  obtain ⟨b, hbEK, hb1⟩ : ∃ b ∈ E ⊓ K, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E ⊓ K = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at hEK9
    norm_num at hEK9
  have hnE : n ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hnC
  have hne : n * e = e * n := (Subgroup.mem_centralizer_iff.mp hnC e heE).symm
  have hnN : n ∈ Subgroup.normalizer (K : Set G) :=
    Ronan138S.mem_normalizer_of_mem_lA hD.mem_lA he3 heK (Subgroup.mem_inf.mp hbEK).1
      (Subgroup.mem_inf.mp hbEK).2 hb1 hnE hne
  set σ := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨n, hnN⟩) with hσ
  obtain ⟨k, hk⟩ := hnk
  have hσk : σ ^ 3 ^ k = 1 := by
    rw [hσ, ← map_pow, ← map_pow]
    have : (⟨n, hnN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one, map_one]
  obtain ⟨kb, hkb⟩ := mem_range_conj_of_pow_three_pow_j2 ⟨φK⟩ hσk
  have hkbk : kb ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (kb ^ 3 ^ k) = 1 := by rw [map_pow, hkb, hσk]
    have hmem : kb ^ 3 ^ k ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun τ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => τ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * kb ^ 3 ^ k = kb ^ 3 ^ k * g * (kb ^ 3 ^ k)⁻¹ * kb ^ 3 ^ k := by rw [h2]
        _ = kb ^ 3 ^ k * g := by group
    rw [hZK, Subgroup.mem_bot] at hmem
    exact hmem
  have hkb3 : kb ^ 3 = 1 := by
    have hP : IsPGroup 3 (Subgroup.zpowers kb) := by
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      change (kb ^ i) ^ 3 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkbk, one_zpow]
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    obtain ⟨⟨hHeis, -⟩, -⟩ := h415 _ ⟨φK⟩ Q _ rfl _ rfl
    have hkbQ : kb ∈ (Q : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
      hQ (Subgroup.mem_zpowers kb)
    have h1 := Monoid.pow_exponent_eq_one
      (⟨kb, hkbQ⟩ : (Q : Subgroup (K ⧸ aschbacherSolvableCore 3 K)))
    rw [hHeis.2.2] at h1
    exact congrArg Subtype.val h1
  have hσ3 : σ ^ 3 = 1 := by rw [← hkb, ← map_pow, hkb3, map_one]
  have hn3C : n ^ 3 ∈ Sec4.thetaQuotCentralizer K := by
    refine Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨pow_mem hnN 3, ?_⟩
    have h1 : (⟨n ^ 3, pow_mem hnN 3⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨n, hnN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 := Subtype.ext (by simp)
    rw [h1, map_pow, map_pow]
    exact hσ3
  have hn3E : n ^ 3 ∈ E := Subgroup.zpowers_le.mpr hdE hn3
  have hCE := sectionCentralizer_eq_inf hD.mem_lA.2.1
  rw [hD.mem_lA.2.2.1] at hCE
  have hn3' : n ^ 3 ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hn3E, hn3C⟩
  rw [← hCE] at hn3'
  have hn33 : (n ^ 3) ^ 3 = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hn3
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have h1 := Ronan138S.zpowers_eq_of_mem hn33 hn31 he3 he1 hn3'
  have h2 := Ronan138S.zpowers_eq_of_mem hn33 hn31 hd3 hd1 hn3
  apply hdΩ
  rw [← h2, h1]
  exact hD.zpowers_mem_omegaA

end CFSG.RankThree.PartTwo.Sec13.Ronan138T
