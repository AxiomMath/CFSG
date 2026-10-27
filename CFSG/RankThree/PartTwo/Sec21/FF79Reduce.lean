module

public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog IsCharTwoType)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem exists_isSylowOf [Finite G] (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    ∃ B : Subgroup G, IsSylowOf p B H := by
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (P.not_dvd_index)

theorem exists_involution_of_odd [Finite G] {B : Subgroup G} (hodd : Odd (Nat.card (CenS B)))
    {n : G} (hn : ∀ x ∈ B, n * (n * x * n⁻¹) * n⁻¹ = x) {b : G} (hb : b ∈ B) (hb1 : b⁻¹ ≠ b)
    (hnb : n * b * n⁻¹ = b⁻¹) :
    ∃ m : ℕ, Odd m ∧ orderOf (n ^ m) = 2 := by
  have hn2 : n ^ 2 ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hn x hx
    rw [pow_two]
    calc x * (n * n) = (n * (n * x * n⁻¹) * n⁻¹) * (n * n) := by rw [this]
      _ = n * n * x := by group
  have hpos : 0 < orderOf n := orderOf_pos n
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨m, hm, ?_⟩
  have hc : (n ^ m) ^ 2 ∈ CenS B := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Subgroup.pow_mem _ hn2 m
  have hord : orderOf (n ^ m) = 2 ^ a := by
    rw [orderOf_pow' n hm.pos.ne', hnm, Nat.gcd_mul_left_left]
    simp [hm.pos.ne']
  have h2 : (n ^ m) ^ 2 = 1 := by
    have hdvd : orderOf ((⟨(n ^ m) ^ 2, hc⟩ : CenS B)) ∣ Nat.card (CenS B) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have hp : orderOf ((n ^ m) ^ 2) ∣ 2 ^ a := by
      rw [← hord]; exact orderOf_pow_dvd _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hp
    rcases k with _ | k
    · simpa using hk
    · exfalso
      rw [hk] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
        ((Dvd.intro _ (pow_succ' 2 k).symm).trans hdvd))
  have hne : n ^ m ≠ 1 := by
    intro h1
    apply hb1
    have hact : ∀ k : ℕ, n ^ k * b * (n ^ k)⁻¹ = if Even k then b else b⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_inv_rev, show n * n ^ k * b * ((n ^ k)⁻¹ * n⁻¹) =
          n * (n ^ k * b * (n ^ k)⁻¹) * n⁻¹ by group, ih]
        by_cases hk : Even k
        · simp [hk, hnb, Nat.even_add_one]
        · have := hn b hb
          rw [hnb] at this
          simp [hk, Nat.even_add_one, this]
    have := hact m
    rw [h1] at this
    simpa [Nat.not_even_iff_odd.mpr hm] using this.symm
  exact orderOf_eq_prime h2 hne

theorem sq_conj_eq_of_diag {B : Subgroup G} {b b₁ b₂ n : G}
    (hB : B = Subgroup.closure {b, b₁, b₂}) (hnb : n * b * n⁻¹ = b⁻¹) (hn1 : n * b₁ * n⁻¹ = b₁)
    (hn2 : n * b₂ * n⁻¹ = b₂) : ∀ x ∈ B, n * (n * x * n⁻¹) * n⁻¹ = x := by
  intro x hx
  rw [hB] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    · rw [hnb, show n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ by group, hnb, inv_inv]
    · rw [hn1, hn1]
    · rw [hn2, hn2]
  | one => group
  | mul y z _ _ hy hz =>
    calc n * (n * (y * z) * n⁻¹) * n⁻¹
        = (n * (n * y * n⁻¹) * n⁻¹) * (n * (n * z * n⁻¹) * n⁻¹) := by group
      _ = y * z := by rw [hy, hz]
  | inv y _ hy =>
    rw [show n * (n * y⁻¹ * n⁻¹) * n⁻¹ = (n * (n * y * n⁻¹) * n⁻¹)⁻¹ by
      simp only [mul_inv_rev, inv_inv, mul_assoc], hy]

theorem conj_pow_odd_eq {n x : G} (h : n * (n * x * n⁻¹) * n⁻¹ = x) {m : ℕ} (hm : Odd m) :
    n ^ m * x * (n ^ m)⁻¹ = n * x * n⁻¹ := by
  obtain ⟨j, rfl⟩ := hm
  have hc : Commute (n ^ 2) x := by
    rw [Commute, SemiconjBy, pow_two]
    calc n * n * x = (n * n * x * (n * n)⁻¹) * (n * n) := by group
      _ = (n * (n * x * n⁻¹) * n⁻¹) * (n * n) := by group
      _ = x * (n * n) := by rw [h]
  have hcj : Commute (n ^ (2 * j)) x := by rw [pow_mul]; exact hc.pow_left j
  rw [pow_succ, mul_inv_rev]
  calc n ^ (2 * j) * n * x * (n⁻¹ * (n ^ (2 * j))⁻¹)
      = n ^ (2 * j) * (n * x * n⁻¹) * (n ^ (2 * j))⁻¹ := by group
    _ = n * (n ^ (2 * j) * x * (n ^ (2 * j))⁻¹) * n⁻¹ := by
        rw [show n ^ (2 * j) = n * n ^ (2 * j) * n⁻¹ by
          rw [← pow_succ', pow_succ, mul_inv_cancel_right]]
        group
    _ = n * x * n⁻¹ := by rw [hcj.eq, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec21.FF79
