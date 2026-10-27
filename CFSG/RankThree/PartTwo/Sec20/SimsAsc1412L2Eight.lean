module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Skel
public import CFSG.CharacterTheory.PSL2Table.Classes
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.CharacterTheory.PSL2Table.Halves
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.PSL2Table
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem relIndex_centralizer_conj_eight {I : Subgroup X} (hI : I.Normal) (g x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex I =
      (centralizer ({x} : Set X)).relIndex I := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.normal_iff_map_conj_eq.mp hI g).symm

theorem noSmallEight1412_of_dvd_orderOf (h : Hyp1411 X L S)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    {t ℓ : X} (htt : t * t = 1) (hℓ : ℓ ∈ L) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (h6 : ∀ e : ℕ, 1 ≤ e → e ≤ 6 → ¬ r ^ k ∣ 2 ^ e - 1)
    (hdvd : r ^ k ∣ orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) (t * (ℓ * t * ℓ⁻¹)))) :
    NoSmallEight1412 X L t := by
  intro I hIn hI hLI
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hbot := map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  have hun : ∀ u : X, u ∈ normalizer (I : Set X) := fun u => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have hc : (centralizer ({ℓ * t * ℓ⁻¹} : Set X)).relIndex I ≤ 8 := by
    rw [relIndex_centralizer_conj_eight hIn]
    exact hle
  obtain ⟨N, -, hpow, hN⟩ := exists_pow_mem_centralizer_prime_pow hI (hun t) (hun (ℓ * t * ℓ⁻¹))
    hle hc
  have hyL : t * (ℓ * t * ℓ⁻¹) ∈ L := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have : t * (ℓ * t * ℓ⁻¹) = t * ℓ * t⁻¹ * ℓ⁻¹ := by rw [htinv]; group
    rw [this]
    exact L.mul_mem (h.2.1.conj_mem ℓ hℓ t) (L.inv_mem hℓ)
  have h1 : (π (t * (ℓ * t * ℓ⁻¹))) ^ (2 * N) = 1 := by
    have hmem : π ((t * (ℓ * t * ℓ⁻¹)) ^ (2 * N)) ∈
        (centralizer (I : Set X)).map π ⊓ L.map π :=
      ⟨mem_map_of_mem π hpow, mem_map_of_mem π (L.pow_mem hyL _)⟩
    rw [hbot, Subgroup.mem_bot, map_pow] at hmem
    exact hmem
  have hdvd' : r ^ k ∣ N * 2 := by
    rw [mul_comm]
    exact hdvd.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (r ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  obtain ⟨e, he1, he64, hediv⟩ := hN r k hr hr2 hk (hcop.dvd_of_dvd_mul_right hdvd')
  have he6 : e ≤ 6 := by
    by_contra h7
    push Not at h7
    have : 2 ^ 7 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h7
    omega
  exact h6 e he1 he6 hediv

private theorem eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have ha1 : a ≠ 1 := by rintro rfl; rw [orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by rintro rfl; rw [orderOf_one] at hb; norm_num at hb
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [← ha]; exact pow_orderOf_eq_one x
    · rw [← hb]; exact pow_orderOf_eq_one x
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ha1.symm, hb1.symm]),
      Finset.card_pair hab]
  have := Finset.card_le_card hsub
  omega

theorem exists_orderOf_mul_conj_eq_of_orderOf_eq_two {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) (h1 : IsSquare (-1 : F))
    {z : PSL(2, F)} (hz : orderOf z = 2) :
    ∃ g : PSL(2, F), orderOf (z * (g * z * g⁻¹)) = (Fintype.card F + 1) / 2 := by
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨w, hwS, hww, hinv, -⟩ :=
    CFSG.Glauberman.Dickson.MaxStructure.normalizer_nonsplitTorus_eq hF hq hν
  have hw1 : w ≠ 1 := fun h => hwS (h ▸ (nonsplitTorus ν).one_mem)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
  obtain ⟨a, haT, hza⟩ := (involution_conj_torus hF hq hν hz).1 h1
  obtain ⟨b, hbT, hwb⟩ := (involution_conj_torus hF hq hν hw2).1 h1
  have hao : orderOf a = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hza
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  have hbo : orderOf b = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hwb
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hw2
  have := splitTorus_isCyclic (F := F)
  have hab : (⟨a, haT⟩ : splitTorus F) = ⟨b, hbT⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic (by rw [Subgroup.orderOf_mk]; exact hao)
      (by rw [Subgroup.orderOf_mk]; exact hbo)
  have hab' : a = b := congrArg Subtype.val hab
  have hzw : IsConj w z := hwb.trans (by rw [← hab']; exact hza.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hzw
  have := CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := nonsplitTorus ν)
  have hycard : Nat.card (nonsplitTorus ν) = (Fintype.card F + 1) / 2 :=
    CFSG.Glauberman.Dickson.MaxStructure.card_nonsplitTorus_eq hF hν
  have hyo : orderOf (y : PSL(2, F)) = (Fintype.card F + 1) / 2 := by
    rw [Subgroup.orderOf_coe, hy, hycard]
  have hq4 : Fintype.card F % 4 = 1 := by
    have h3 := FiniteField.isSquare_neg_one_iff.mp h1
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
    omega
  have hodd : ¬ 2 ∣ (Fintype.card F + 1) / 2 := by omega
  refine ⟨c * y * c⁻¹, ?_⟩
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hww).symm
  have hwy : w * (y : PSL(2, F)) * w = (y : PSL(2, F))⁻¹ := by
    have := hinv y y.2
    rwa [hwinv] at this
  have key : z * (c * y * c⁻¹ * z * (c * y * c⁻¹)⁻¹) = c * ((y : PSL(2, F))⁻¹ ^ 2) * c⁻¹ := by
    rw [← hc]
    calc c * w * c⁻¹ * (c * y * c⁻¹ * (c * w * c⁻¹) * (c * y * c⁻¹)⁻¹)
        = c * ((w * y * w) * (y : PSL(2, F))⁻¹) * c⁻¹ := by group
      _ = c * ((y : PSL(2, F))⁻¹ ^ 2) * c⁻¹ := by rw [hwy, sq]
  rw [key, show c * ((y : PSL(2, F))⁻¹ ^ 2) * c⁻¹ = MulAut.conj c ((y : PSL(2, F))⁻¹ ^ 2) from rfl,
    MulEquiv.orderOf_eq, orderOf_pow' _ (by norm_num), orderOf_inv, hyo]
  have hg : Nat.gcd ((Fintype.card F + 1) / 2) 2 = 1 := by
    rcases Nat.coprime_or_dvd_of_prime Nat.prime_two ((Fintype.card F + 1) / 2) with h | h
    · exact Nat.Coprime.symm h
    · exact absurd h hodd
  rw [hg, Nat.div_one]

theorem exists_primePow_dvd_sq_add_one_div_two {r : ℕ} (hr : Odd r) (hr5 : 5 ≤ r) :
    ∃ ℓ k : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ k ∧ ℓ ^ k ∣ (r ^ 2 + 1) / 2 ∧
      ∀ e : ℕ, 1 ≤ e → e ≤ 6 → ¬ ℓ ^ k ∣ 2 ^ e - 1 := by
  obtain ⟨m, rfl⟩ := hr
  have hm : 2 ≤ m := by omega
  have hN : ((2 * m + 1) ^ 2 + 1) / 2 = 2 * m * m + 2 * m + 1 := by
    have : (2 * m + 1) ^ 2 + 1 = 2 * (2 * m * m + 2 * m + 1) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hN]
  set N := 2 * m * m + 2 * m + 1 with hNdef
  have hN13 : 13 ≤ N := by nlinarith
  have hN2 : N = 2 * (m * m + m) + 1 := by rw [hNdef]; ring
  have hNodd : ¬ 2 ∣ N := by rw [hN2]; omega
  have hcast : ∀ n : ℕ, ((N : ℕ) : ZMod n) = 2 * (m : ZMod n) * m + 2 * m + 1 := fun n => by
    rw [hNdef]; push_cast; ring
  have h3 : ¬ 3 ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff, hcast]
    generalize (m : ZMod 3) = x
    revert x
    decide
  have h7 : ¬ 7 ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff, hcast]
    generalize (m : ZMod 7) = x
    revert x
    decide
  have h31 : ¬ 31 ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff, hcast]
    generalize (m : ZMod 31) = x
    revert x
    decide
  by_cases hex : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ ℓ ≠ 5
  · obtain ⟨ℓ, hℓ, hℓN, hℓ5⟩ := hex
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact hNodd hℓN
    refine ⟨ℓ, 1, hℓ, hℓ2, le_rfl, by rw [pow_one]; exact hℓN, fun e he1 he6 hdvd => ?_⟩
    rw [pow_one] at hdvd
    have hp : ∀ n : ℕ, n.Prime → ℓ ∣ n → ℓ = n := fun n hn h =>
      (Nat.prime_dvd_prime_iff_eq hℓ hn).mp h
    have h3' : ℓ ≠ 3 := by rintro rfl; exact h3 hℓN
    have h7' : ℓ ≠ 7 := by rintro rfl; exact h7 hℓN
    have h31' : ℓ ≠ 31 := by rintro rfl; exact h31 hℓN
    interval_cases e
    · norm_num at hdvd
      exact hℓ.one_lt.ne' hdvd
    · exact h3' (hp 3 (by norm_num) (by simpa using hdvd))
    · exact h7' (hp 7 (by norm_num) (by simpa using hdvd))
    · have h15 : ℓ ∣ 3 * 5 := by simpa using hdvd
      rcases (Nat.Prime.dvd_mul hℓ).mp h15 with h | h
      · exact h3' (hp 3 (by norm_num) h)
      · exact hℓ5 (hp 5 (by norm_num) h)
    · exact h31' (hp 31 (by norm_num) (by simpa using hdvd))
    · have h63 : ℓ ∣ 7 * (3 * 3) := by simpa using hdvd
      rcases (Nat.Prime.dvd_mul hℓ).mp h63 with h | h
      · exact h7' (hp 7 (by norm_num) h)
      · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h <;> exact h3' (hp 3 (by norm_num) h)
  · push Not at hex
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : N ≠ 0)
      (fun {d} hd hdN => hex d hd hdN)
    have h25 : 25 ∣ N := by
      rw [hpow]
      have hlen : 2 ≤ N.primeFactorsList.length := by
        by_contra hlen
        push Not at hlen
        have : 5 ^ N.primeFactorsList.length ≤ 5 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact (Nat.pow_dvd_pow 5 hlen).trans (by rw [← hpow])
    refine ⟨5, 2, by norm_num, by norm_num, by norm_num, by simpa using h25, fun e he1 he6 => ?_⟩
    interval_cases e <;> norm_num

end CFSG.RankThree.PartTwo.Sec20
