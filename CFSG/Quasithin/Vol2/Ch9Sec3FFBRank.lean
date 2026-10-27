module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2EvenRank
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBBar

public section

namespace CFSG.Quasithin.H13.Ch9.FFB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.RankThree.PartTwo.Census.Carrier (ThreeRankLeOne)

section SL2

variable {K : Type*} [Field K]

theorem sq_add_self_add_one_eq_zero_of_pow_three {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) K) ^ 2 + (g : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = g := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨t, ht⟩ : ∃ t : K, t = M 0 0 + M 1 1 := ⟨_, rfl⟩
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hM]
    exact g.2
  have hCH : M * M = t • M - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;>
      first | linear_combination (-1 : K) * hdet | ring
  have hM3 : M ^ 3 = 1 := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
  have h3 : M ^ 3 = (t * t - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [pow_succ', pow_two, hCH, mul_sub, mul_one, Matrix.mul_smul, hCH, smul_sub, smul_smul,
      sub_smul, one_smul]
    abel
  have hlin : (t * t - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := h3.symm.trans hM3
  by_cases ht1 : t = -1
  · rw [pow_two, hCH, ht1, neg_one_smul]
    abel
  exfalso
  have ht1' : t + 1 ≠ 0 := fun h => ht1 (eq_neg_of_add_eq_zero_left h)
  have htt : t * t - 1 ≠ 0 := by
    intro h
    rw [h, zero_smul, zero_sub] at hlin
    have h00 := congrFun (congrFun hlin 0) 0
    simp at h00
    exact ht1 (by linear_combination -h00)
  have hfac : t * t - 1 = (t - 1) * (t + 1) := by ring
  have htm : t - 1 ≠ 0 := fun h => htt (by rw [hfac, h, zero_mul])
  have hscal : M = (t - 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : (t * t - 1) • M = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [add_smul, one_smul, add_comm]
      exact eq_add_of_sub_eq hlin
    calc M = ((t * t - 1)⁻¹ * (t * t - 1)) • M := by rw [inv_mul_cancel₀ htt, one_smul]
      _ = (t * t - 1)⁻¹ • ((t + 1) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [← smul_smul, h1]
      _ = (t - 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [smul_smul, hfac, mul_inv, mul_assoc, inv_mul_cancel₀ ht1', mul_one]
  obtain ⟨c, hc⟩ : ∃ c : K, c = (t - 1)⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hscal
  have hc2 : c * c = 1 := by
    have h := hdet
    rw [hscal] at h
    simpa using h
  have hc3 : c ^ 3 = 1 := by
    have h := hM3
    rw [hscal, smul_pow, one_pow] at h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  have hc1 : c = 1 := by
    have e : c ^ 3 = c * (c * c) := by ring
    rw [hc2, mul_one] at e
    rw [← e, hc3]
  apply hg1
  ext i j
  have h := congrFun (congrFun hscal i) j
  rw [hc1, one_smul, hM] at h
  simpa using h

theorem threeRankLeOne_SL2_of_three_ne_zero (h3 : (3 : K) ≠ 0) :
    ThreeRankLeOne (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro a b ha hb hab ha1
  by_cases hb1 : b = 1
  · rw [hb1]
    exact Subgroup.one_mem _
  by_cases hab1 : a * b = 1
  · rw [eq_inv_of_mul_eq_one_right hab1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hc : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hc.mul_pow, ha, hb, one_mul]
  have hA := sq_add_self_add_one_eq_zero_of_pow_three ha ha1
  have hB := sq_add_self_add_one_eq_zero_of_pow_three hb hb1
  have hAB := sq_add_self_add_one_eq_zero_of_pow_three hab3 hab1
  set A : Matrix (Fin 2) (Fin 2) K := (a : Matrix (Fin 2) (Fin 2) K)
  set B : Matrix (Fin 2) (Fin 2) K := (b : Matrix (Fin 2) (Fin 2) K)
  have hcAB : Commute A B := by
    change A * B = B * A
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hab]
  rw [Matrix.SpecialLinearGroup.coe_mul, hcAB.mul_pow] at hAB
  have hA2 : A ^ 2 = -A - 1 := by
    rw [← sub_eq_zero, ← hA]
    abel
  have hB2 : B ^ 2 = -B - 1 := by
    rw [← sub_eq_zero, ← hB]
    abel
  rw [hA2, hB2] at hAB
  have hS : 2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [← hAB]
    noncomm_ring
  have hAA : A * A = -A - 1 := by rw [← pow_two]; exact hA2
  have key : (2 • A + 1) * (2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K)) =
      3 • (A - B) := by
    have e1 : (2 • A + 1) * (2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K)) =
        4 • (A * A * B) + 2 • (A * A) + 4 • (A * B) + 5 • A + B +
          2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
      noncomm_ring
    rw [e1, hAA]
    noncomm_ring
  rw [hS, mul_zero] at key
  have hAB0 : A - B = 0 := by
    have h' : (3 : K) • (A - B) = 0 := by
      have e : (3 : K) • (A - B) = 3 • (A - B) := by
        rw [← Nat.cast_smul_eq_nsmul K]
        norm_num
      rw [e]
      exact key.symm
    exact (smul_eq_zero.mp h').resolve_left h3
  rw [show b = a from Subtype.ext (sub_eq_zero.mp hAB0).symm]
  exact Subgroup.mem_zpowers a

end SL2

section Hom

variable {X : Type} [Group X]

theorem eq_one_of_pow_three_of_coprime {N : Subgroup X} [Finite N]
    (hN : Nat.Coprime 3 (Nat.card N)) {x : X} (hx : x ∈ N) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : N) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hN) h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)

theorem threeRankLeOne_of_hom {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hker : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) : ThreeRankLeOne X := by
  intro a b ha hb hab ha1
  have hψa1 : ψ a ≠ 1 := fun h => ha1 (hker a h ha)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (threeRankLeOne_SL2_of_three_ne_zero h3 (ψ a) (ψ b) (by rw [← map_pow, ha, map_one])
      (by rw [← map_pow, hb, map_one]) (by rw [← map_mul, ← map_mul, hab]) hψa1)
  have hmem : b * (a ^ k)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have hcomm : Commute b ((a ^ k)⁻¹) := (Commute.zpow_left (hab : Commute a b) k).symm.inv_right
  have hc3 : (b * (a ^ k)⁻¹) ^ 3 = 1 := by
    rw [hcomm.mul_pow, hb, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ha, one_zpow, inv_one]
  have h1 := hker _ hmem hc3
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact Subgroup.zpow_mem_zpowers a k

variable [Finite X]

theorem threeRankLeOne_of_case3 (h : A36Case3 X) : ThreeRankLeOne X := by
  obtain ⟨p, hp, hp3, -, ⟨eF⟩, e, ψ, -, hψk, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1
    omega
  refine threeRankLeOne_of_hom h3 ψ fun x hx hx3 => ?_
  rw [hψk] at hx
  have hcard : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card]
    simp
  have : Finite ↥(CFSG.fittingSubgroup X) := inferInstance
  refine eq_one_of_pow_three_of_coprime ?_ hx hx3
  rw [hcard]
  exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))

theorem threeRankLeOne_of_case4 (h : A36Case4 X) : ThreeRankLeOne X := by
  obtain ⟨-, -, ⟨e⟩, hprimes⟩ := h
  have h3 : (3 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup X)) with hψ
  refine threeRankLeOne_of_hom h3 ψ fun x hx hx3 => ?_
  have hxF : x ∈ CFSG.fittingSubgroup X := by
    rw [hψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  refine eq_one_of_pow_three_of_coprime ?_ hxF hx3
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3F
  have := (hprimes 3 Nat.prime_three h3F).1
  omega

theorem isQuasisimple_of_mem_cComp {Q : Type} [Group Q] [Finite Q] (h36 : A36Statement Q)
    {L : Subgroup Q} (hL : L ∈ cComp (⊤ : Subgroup Q)) (h3 : ¬ ThreeRankLeOne ↥L) :
    CFSG.IsQuasisimple ↥L := by
  obtain ⟨hconc, -, -⟩ := h36 L hL
  rcases hconc with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3' | h4'
  · exact hcomp.1
  · exact hcomp.1
  · exact absurd (threeRankLeOne_of_case3 h3') h3
  · exact absurd (threeRankLeOne_of_case4 h4') h3

end Hom

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_o2q (h36 : A36ForSQTK) {Y KY : Subgroup G} (hSQ : SQTKGroup ↥Y)
    (hKYc : KY ∈ cComp Y) (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) {a b : G} (haK : a ∈ KY)
    (hbK : b ∈ KY) (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) : CFSG.IsQuasisimple (O2Q KY) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQbar := SQTKHyp.of_sqtkGroup ↥Y hSQ
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have h2 : ∀ x : ↥Y, π x = 1 → (x : G) ^ 3 = 1 → (x : G) = 1 := by
    intro x hx hx3
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have h := CFSG.RankThree.PartTwo.Census.Carrier.eq_one_of_mem_of_pow_three
      CFSG.pCore_isPGroup hx (Subtype.ext (by simpa using hx3))
    exact congrArg Subtype.val h
  set a' : ↥(modO2Image Y KY) := ⟨π ⟨a, hKYY haK⟩, ⟨a, hKYY haK⟩,
    Subgroup.mem_subgroupOf.mpr haK, rfl⟩ with ha'
  set b' : ↥(modO2Image Y KY) := ⟨π ⟨b, hKYY hbK⟩, ⟨b, hKYY hbK⟩,
    Subgroup.mem_subgroupOf.mpr hbK, rfl⟩ with hb'
  have hnot : ¬ ThreeRankLeOne ↥(modO2Image Y KY) := by
    intro h
    have ha3 : a' ^ 3 = 1 := Subtype.ext (by
      simp only [ha', Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      rw [show (⟨a, hKYY haK⟩ : ↥Y) ^ 3 = 1 from Subtype.ext (by simpa using ha), map_one])
    have hb3 : b' ^ 3 = 1 := Subtype.ext (by
      simp only [hb', Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      rw [show (⟨b, hKYY hbK⟩ : ↥Y) ^ 3 = 1 from Subtype.ext (by simpa using hb), map_one])
    have hab' : a' * b' = b' * a' := Subtype.ext (by
      simp only [ha', hb', Subgroup.coe_mul, ← map_mul]
      congr 1
      exact Subtype.ext hab)
    have ha'1 : a' ≠ 1 := by
      intro h1
      apply ha1
      exact h2 ⟨a, hKYY haK⟩ (congrArg Subtype.val h1) ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h a' b' ha3 hb3 hab' ha'1)
    apply hba
    have hk' : π (⟨b, hKYY hbK⟩⁻¹ * ⟨a, hKYY haK⟩ ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simp only [ha', hb', Subgroup.coe_zpow] at this
      rw [map_mul, map_inv, map_zpow, this, inv_mul_cancel]
    have hcomm : Commute b⁻¹ (a ^ k) := ((Commute.zpow_left hab k).symm).inv_left
    have h3 : (b⁻¹ * a ^ k) ^ 3 = 1 := by
      rw [hcomm.mul_pow, inv_pow, hb, inv_one, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, ha, one_zpow]
    have h1 := h2 _ hk' (by simpa using h3)
    have h1' : b⁻¹ * a ^ k = 1 := by simpa using h1
    rw [inv_mul_eq_one] at h1'
    rw [h1']
    exact Subgroup.zpow_mem_zpowers a k
  have hqL := isQuasisimple_of_mem_cComp (h36 _ hQbar) (modO2Image_mem_cComp hKYc) hnot
  obtain ⟨e⟩ := nonempty_o2q_equiv hSQ hKYc hYKY
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqL

end CFSG.Quasithin.H13.Ch9.FFB
