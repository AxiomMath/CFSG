module

public import CFSG.LocalAnalysis.UniquenessCase.UCSingerL3a
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3L
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UG
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Group

variable {G : Type*} [Group G]

theorem l3_mem_normalizer_of_conj {x : G} {H : Subgroup G} (hx3 : x ^ 3 = 1)
    (hmap : ∀ h ∈ H, x * h * x⁻¹ ∈ H) : x ∈ normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨hmap h, fun hh => ?_⟩
  have h2 := hmap _ (hmap _ hh)
  have h3' : x * x * x = 1 := by rw [← hx3, pow_succ, pow_two]
  have e : x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = h := by
    calc x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * h * (x * x * x)⁻¹ := by group
      _ = h := by rw [h3', one_mul, inv_one, mul_one]
  rw [← e]
  exact h2

theorem l3_singer_of_conj {x σ : G} {m N : ℕ} (hx3 : x ^ 3 = 1) (hconj : x * σ * x⁻¹ = σ ^ m)
    (hσ : orderOf σ = N) (hm : 1 ≤ m) (hcop : Nat.Coprime (m - 1) N) :
    ∃ C : Subgroup G, IsCyclic C ∧ Nat.card C = N ∧ x ∈ normalizer (C : Set G) ∧
      ∀ c ∈ C, x * c * x⁻¹ = c → c = 1 := by
  have hpow : ∀ n : ℤ, x * σ ^ n * x⁻¹ = σ ^ ((m : ℤ) * n) := by
    intro n
    rw [← conj_zpow, hconj, ← zpow_natCast, ← _root_.zpow_mul]
  refine ⟨zpowers σ, inferInstance, by rw [Nat.card_zpowers, hσ], ?_, ?_⟩
  · refine l3_mem_normalizer_of_conj hx3 fun h hh => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [hpow]
    exact Subgroup.zpow_mem _ (mem_zpowers σ) _
  · intro c hc hfix
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [hpow] at hfix
    have h1 : σ ^ (((m - 1 : ℕ) : ℤ) * n) = 1 := by
      have e : ((m - 1 : ℕ) : ℤ) * n = (m : ℤ) * n - n := by
        rw [Nat.cast_sub hm]
        ring
      rw [e, _root_.zpow_sub, hfix, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hσ] at h1
    rw [← orderOf_dvd_iff_zpow_eq_one, hσ]
    exact (Nat.isCoprime_iff_coprime.2 hcop.symm).dvd_of_dvd_mul_left h1

end Group

theorem l3_coprime_coxeter {q : ℕ} (hq : q % 3 = 1) (hq2 : 2 ≤ q) :
    Nat.Coprime (q ^ 2 - 1) (q ^ 2 - q + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  have e1 : (k + 2) ^ 2 - 1 = (k + 1) * (k + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (k + 2) ^ 2 - (k + 2) + 1 = k ^ 2 + 3 * k + 3 := by
    have : (k + 2) ^ 2 = k ^ 2 + 3 * k + 2 + (k + 2) := by ring
    omega
  rw [e1, e2]
  refine Nat.Coprime.mul_left ?_ ?_
  · rw [show k ^ 2 + 3 * k + 3 = 1 + (k + 2) * (k + 1) by ring, Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right _
  · rw [show k ^ 2 + 3 * k + 3 = 3 + k * (k + 3) by ring, Nat.coprime_add_mul_right_right]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).symm

theorem l3Singer_psl {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 3 p f) (hq : p ^ f % 3 = 2) (x : K) (hx : orderOf x = 3) :
    ∃ C : Subgroup K, IsCyclic C ∧ Nat.card C = (p ^ f) ^ 2 + p ^ f + 1 ∧
      x ∈ Subgroup.normalizer (C : Set K) ∧ ∀ c ∈ C, x * c * x⁻¹ = c → c = 1 := by
  obtain ⟨hadm, F, hFf, hFfin, hF, ⟨e⟩⟩ := hK
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hq' : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  let e' : K ≃* SL(3, F) := (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq (center_SL3_eq_bot (cube_roots_trivial hq'))).trans
      QuotientGroup.quotientBot)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  obtain ⟨z, hz, hdz⟩ := l3_exists_singer_L hf hF hq' (d := e' x)
    (by rw [← map_pow, hx3, map_one]) (fun h => hx1 (e'.injective (h.trans (map_one e').symm)))
  have hσ : x * e'.symm z * x⁻¹ = (e'.symm z) ^ Nat.card F := by
    apply e'.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_pow, MulEquiv.apply_symm_apply, hdz]
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ := l3_singer_of_conj hx3 hσ
    ((MulEquiv.orderOf_eq e'.symm z).trans hz) (by omega) (l3_coprime_singer hq')
  rw [hF] at hC2
  exact ⟨C, hC1, hC2, hC3, hC4⟩

theorem l3Singer_psu {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSU 3 p f) (hq : p ^ f % 3 = 1) (x : K) (hx : orderOf x = 3) :
    ∃ C : Subgroup K, IsCyclic C ∧ Nat.card C = (p ^ f) ^ 2 - p ^ f + 1 ∧
      x ∈ Subgroup.normalizer (C : Set K) ∧ ∀ c ∈ C, x * c * x⁻¹ = c → c = 1 := by
  obtain ⟨hadm, F, hFf, hFfin, hF, ⟨e⟩⟩ := hK
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  let e₁ : K ≃* StatedSU 3 (p ^ f) F :=
    (e.trans (QuotientGroup.quotientMulEquivOfEq
      (scalars_subgroupOf_statedSU_eq_bot hF hq))).trans QuotientGroup.quotientBot
  let e' : K ≃* SU (unitaryInvolution F p f) 3 := e₁.trans (equivStatedSU hF 3).symm
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  obtain ⟨z, hz, hdz⟩ := l3_exists_singer_U (unitaryInvolution F p f) (unitaryInvolution_apply F p f)
    (unitaryInvolution_involutive hF) hf hF hq (d := e' x) (by rw [← map_pow, hx3, map_one])
    (fun h => hx1 (e'.injective (h.trans (map_one e').symm)))
  have hσ : x * e'.symm z * x⁻¹ = (e'.symm z) ^ Nat.card F := by
    apply e'.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_pow, MulEquiv.apply_symm_apply, hdz]
  have hQ2 : 2 ≤ p ^ f := two_le_of_card_eq_sq hF
  have hq2 : 1 ≤ Nat.card F := Nat.card_pos
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ := l3_singer_of_conj hx3 hσ
    ((MulEquiv.orderOf_eq e'.symm z).trans hz) hq2 (by rw [hF]; exact l3_coprime_coxeter hq hQ2)
  exact ⟨C, hC1, hC2, hC3, hC4⟩

theorem l3SingerFact_holds : CFSG.RankThree.PartTwo.Sec3.L3SingerFact :=
  ⟨fun _ _ _ _ _ hK hq x hx => l3Singer_psl hK hq x hx,
    fun _ _ _ _ _ hK hq x hx => l3Singer_psu hK hq x hx⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
