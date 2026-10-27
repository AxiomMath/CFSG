module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
import CFSG.Quasithin.EmptyFaithful.T1521SSp4Act

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p2214_bor_card_normalizer {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X)
    (Q : Sylow 2 X) :
    Nat.card (normalizer ((Q : Subgroup X) : Set X)) * (Nat.card (Q : Subgroup X) + 1) = Nat.card X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, -, hBor⟩ := CFSG.QuasithinUnique.Unc25G2.BenderBorel.exists_borel_of_bender hB
  obtain ⟨-, ⟨D, hDcyc, -, -, hsup⟩, -⟩ := hBor Q
  have hsolvN := CFSG.QuasithinUnique.Unc25G2.BenderBorel.isSolvable_normalizer_of_sup_cyclic Q.isPGroup'
    hDcyc hsup
  have hreg := CFSG.QuasithinUnique.Unc25G2.BenderBorel.regular_of_borel
    (CFSG.QuasithinUnique.Unc25G2.BenderBorel.isSimpleBenderGroup_of_fusion hB) Q hsolvN
  set N := normalizer ((Q : Subgroup X) : Set X) with hN
  have hNtop : N ≠ ⊤ := uc22p2214_bor_ne_top_of_bender hB hsolvN
  have hα : ∃ β : X ⧸ N, β ≠ ((1 : X) : X ⧸ N) := by
    by_contra hall
    push_neg at hall
    apply hNtop
    rw [eq_top_iff]
    intro x _
    have hx := hall (x : X ⧸ N)
    rw [QuotientGroup.eq, mul_one] at hx
    exact inv_mem_iff.mp hx
  have hfix : (Q : Subgroup X) ≤ MulAction.stabilizer X ((1 : X) : X ⧸ N) := by
    rw [MulAction.stabilizer_quotient]
    exact Subgroup.le_normalizer
  have h1 := CFSG.BenderSuzuki.IsRegularOn.natCard_compl_point hreg hfix hα
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Nat.card (X ⧸ N) := Nat.card_pos
  rw [h2, h1, Nat.sub_add_cancel hpos, mul_comm]

theorem uc22p2214_bor_dvd_of_dvd_mul {r n m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r ∣ 2 ^ n * m) : r ∣ m := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1)) hr2
  · exact h1

theorem uc22p2214_borel_prime_L2 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsL2 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ Nat.card ↥(normalizer (S : Set X))) : r ∣ 2 ^ n - 1 := by
  obtain ⟨Q, rfl⟩ := uc22p2214_bor_sylow hS
  have h1 := uc22p22r_L2_card_normalizer hX Q
  rw [uc22p22r_L2_card hX] at h1
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have hsq : (2 ^ n) ^ 2 - 1 = m * (m + 2) := by
    rw [hm, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [hsq, hm, show m + 1 + 1 = m + 2 by ring, show (m + 1) * (m * (m + 2)) = (m + 1) * m * (m + 2) by ring]
    at h1
  have hN : Nat.card ↥(normalizer ((Q : Subgroup X) : Set X)) = (m + 1) * m :=
    Nat.eq_of_mul_eq_mul_right (by omega) h1
  rw [hN, ← hm] at hrN
  rw [show 2 ^ n - 1 = m by omega]
  exact uc22p2214_bor_dvd_of_dvd_mul hr hr2 hrN

theorem uc22p2214_borel_prime_Sz {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSz X n) {S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrN : r ∣ Nat.card ↥(normalizer (S : Set X))) : r ∣ 2 ^ n - 1 := by
  obtain ⟨Q, rfl⟩ := uc22p2214_bor_sylow hS
  have h1 := uc22p2214_bor_card_normalizer (uc22p2214_bor_bender_Sz hX) Q
  rw [(CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_twistedB2 hX Q).2.2.2.2,
    CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hX,
    show (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) by ring]
    at h1
  have hN := Nat.eq_of_mul_eq_mul_right (by omega) h1
  rw [hN, ← pow_mul] at hrN
  exact uc22p2214_bor_dvd_of_dvd_mul hr hr2 hrN

theorem uc22p2214_borel_prime_U3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ Nat.card ↥(normalizer (S : Set X))) : r ∣ 2 ^ n - 1 ∨ r ∣ 2 ^ n + 1 := by
  obtain ⟨Q, rfl⟩ := uc22p2214_bor_sylow hS
  have h1 := uc22p2214_bor_card_normalizer (uc22p2214_bor_bender_U3 hX) Q
  rw [(CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_PSU3 hX Q).2.2.2.2] at h1
  have h2 := CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hX
  rw [← h1] at h2
  set N := Nat.card ↥(normalizer ((Q : Subgroup X) : Set X))
  set d := Nat.gcd 3 (2 ^ n + 1)
  have h3 : N * d * ((2 ^ n) ^ 3 + 1) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    rw [show N * d * ((2 ^ n) ^ 3 + 1) = N * ((2 ^ n) ^ 3 + 1) * d by ring, h2]
    ring
  have h4 := Nat.eq_of_mul_eq_mul_right (by positivity) h3
  have h5 : r ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := h4 ▸ dvd_mul_of_dvd_left hrN d
  rw [← pow_mul] at h5
  have h6 := uc22p2214_bor_dvd_of_dvd_mul hr hr2 h5
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring, Nat.add_sub_cancel]
  rw [hsq] at h6
  exact (Nat.Prime.dvd_mul hr).mp h6

theorem uc22p2214_borel_prime_Sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ Nat.card ↥(normalizer (S : Set X))) : r ∣ 2 ^ n - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hcl, -⟩ := uc22p2214_bor_sp4_model hX
  obtain ⟨K, _, _, _, φ, hK, hφS, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hcl
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hS)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrN
  have hg : φ (x : X) ∈ normalizer
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K : Subgroup _) : Set _) := by
    rw [← hφS, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, x.2, rfl⟩
  have hgo : orderOf (φ (x : X)) = r := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_projUnipotent (r := 2) (K := K) 2
    (by norm_num)] at hg
  obtain ⟨b, hb, hbg⟩ := hg
  have hbo : orderOf b = r := by
    rw [← hgo, ← hbg]
    exact (orderOf_injective _ CFSG.Quasithin.Sp4.proj_injective b).symm
  have hbo' : orderOf (⟨b, hb⟩ : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 K) = r := by
    rw [Subgroup.orderOf_mk, hbo]
  set d := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.diagHom 2 K ⟨b, hb⟩ with hd
  have hdr : d ^ r = 1 := by rw [hd, ← map_pow, ← hbo', pow_orderOf_eq_one, map_one]
  by_cases hd1 : d = 1
  ·
    exfalso
    have hker : (⟨b, hb⟩ : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 K) ∈
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.diagHom 2 K).ker :=
      MonoidHom.mem_ker.mpr (by rw [← hd]; exact hd1)
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.ker_diagHom, Subgroup.mem_subgroupOf] at hker
    have hgU : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K b ∈
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K := ⟨b, hker, rfl⟩
    rw [hbg, ← hφS] at hgU
    obtain ⟨y, hyS, hyx⟩ := hgU
    have hyx' : y = (x : X) := φ.injective hyx
    obtain ⟨k, hk⟩ := (hS.isPGroup) ⟨y, hyS⟩
    have hyo : orderOf y = r := by rw [hyx', Subgroup.orderOf_coe, hx]
    have hdvd : r ∣ 2 ^ k := by
      rw [← hyo, ← Subgroup.orderOf_mk y hyS]
      exact orderOf_dvd_of_pow_eq_one hk
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hd1
    have hio : orderOf (d i) = r := orderOf_eq_prime (by rw [← Pi.pow_apply, hdr, Pi.one_apply]) hi
    have h1 := orderOf_dvd_natCard (d i)
    rwa [hio, Nat.card_units, hK] at h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
