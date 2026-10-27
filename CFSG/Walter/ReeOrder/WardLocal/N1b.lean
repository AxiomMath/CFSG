module

public import CFSG.Walter.ReeOrder.WardLocal.N1
public import CFSG.Walter.ReeOrder.WardLocal.P1d

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {k : ℕ} (hq : q = 3 ^ (2 * k + 1))
  (hK : Fintype.card K = q) (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) (hA : (AA S).card = q - 1)
  (hC1 : ∀ x : G, Odd (orderOf x) → 3 ∣ orderOf x →
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 3)

@[expose] noncomputable def NN1 (S : WardSetup G PSL(2, K) q (-1)) : Subgroup G :=
  Subgroup.normalizer (PP1 S : Set G)

include hq hK hcT hG hA hC1 in
theorem card_NN1 : ∃ b : ℕ, Nat.card (NN1 S) = (q - 1) * 3 ^ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  obtain ⟨x, hx⟩ : (AA S).Nonempty := by
    rw [← Finset.card_pos, hA]; omega
  have h := card_N1 hq hK hcT hG hA hx
  have hp : IsPGroup 3 (NN1 S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
    (centralizer_AA hq hK hcT hG hA hC1 hx).1.to_le inf_le_right
  obtain ⟨b, hb⟩ := hp.exists_card_eq
  exact ⟨b, by rw [NN1, h]; rw [NN1] at hb; rw [hb]⟩

omit [Fintype G] in
theorem commute_zpowers {n ρ x : G} (h : n * ρ = ρ * n) (hx : x ∈ Subgroup.zpowers ρ) :
    n * x = x * n := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ((Commute.zpow_right h z)).eq

include hq hK hcT in
theorem burnside_NN1 {b : ℕ} (hb : Nat.card (NN1 S) = (q - 1) * 3 ^ b) (r : ℕ) (hr : r.Prime)
    (hrq : r ∣ q - 1) : ∃ R : Subgroup G, R ≤ NN1 S ∧ IsPGroup r R ∧
      Nat.card R = r ^ (Nat.card (NN1 S)).factorization r ∧
      ∀ n ∈ NN1 S, (∀ x ∈ R, n * x * n⁻¹ ∈ R) → ∀ x ∈ R, n * x = x * n := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k', hk', hodd⟩ := Block.q_half hq
  have hq1 : q - 1 = 2 * k' := by omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    have h3 : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
    omega
  have hfac : (Nat.card (NN1 S)).factorization r = (q - 1).factorization r := by
    rw [hb, Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr
        Nat.prime_three).mp (hr.dvd_of_dvd_pow h))), add_zero]
  rcases hr.eq_two_or_odd' with rfl | hrodd
  ·
    refine ⟨Subgroup.zpowers S.J, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]; exact J_mem_normalizer_PP1 hq hcT
    · apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, S.orderOf_J, pow_one]
    · rw [Nat.card_zpowers, S.orderOf_J, hfac, hq1, Nat.factorization_mul (by norm_num)
        (by omega), Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (fun h => by
          obtain ⟨t, ht⟩ := hodd; omega), add_zero, pow_one]
    · intro n hn hnR x hx
      have hJ := hnR S.J (Subgroup.mem_zpowers _)
      have hJ' : n * S.J * n⁻¹ = S.J := by
        rcases (mem_zpowers_of_orderOf_eq_two S.orderOf_J).mp hJ with h | h
        · exfalso
          apply S.J_ne
          have := congrArg (fun t => n⁻¹ * t * n) h
          simpa [mul_assoc] using this
        · exact h
      have hnJ : n * S.J = S.J * n := by
        calc n * S.J = n * S.J * n⁻¹ * n := by group
          _ = S.J * n := by rw [hJ']
      exact commute_zpowers hnJ hx
  ·
    have hrk : r ∣ k' := by
      rw [hq1] at hrq
      rcases (Nat.Prime.dvd_mul hr).mp hrq with h | h
      · exfalso
        have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
        rw [this] at hrodd; exact absurd hrodd (by decide)
      · exact h
    set e := k'.factorization r with he
    have hdvd : r ^ e ∣ k' := Nat.ordProj_dvd k' r
    set m' := k' / r ^ e with hm'
    have hk'pos : 0 < k' := hodd.pos
    have hdgen : orderOf (S.κ (dgen K)) = k' := by
      rw [S.orderOf_κ, orderOf_dgen (hK.trans hk')]
    set ρ := S.κ (dgen K) ^ m' with hρ
    have hρord : orderOf ρ = r ^ e := by
      rw [hρ, orderOf_pow' _ (by
        intro h0
        rw [hm'] at h0
        exact (Nat.div_pos (Nat.le_of_dvd hk'pos hdvd) (pow_pos hr.pos e)).ne' h0), hdgen,
        Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd), Nat.div_div_self hdvd hk'pos.ne']
    have hρRR : ρ ∈ RR S := mem_RR.mpr ⟨m', by rw [map_pow]⟩
    have he1 : 1 ≤ e := by
      rw [he]; exact (hr.dvd_iff_one_le_factorization hk'pos.ne').mp hrk
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, orderOf_one] at hρord
      have : 1 < r ^ e := Nat.one_lt_pow (by omega) hr.one_lt
      omega
    refine ⟨Subgroup.zpowers ρ, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]; exact RR_le_normalizer_PP1 hq hcT hρRR
    · apply IsPGroup.of_card (n := e)
      rw [Nat.card_zpowers, hρord]
    · rw [Nat.card_zpowers, hρord, hfac, hq1, Nat.factorization_mul (by norm_num) (by omega),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h => by
          have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
          rw [this] at hrodd; exact absurd hrodd (by decide)), zero_add]
    · intro n hn hnR x hx
      have hnρ := hnR ρ (Subgroup.mem_zpowers _)
      have hnJ := IV_RR hq hK hρRR hρ1 hnρ
      exact commute_zpowers (commute_of_normalizes hq hK hcT hn hnJ hρRR hnρ) hx

omit [CharP K 3] [DecidableEq K] [Fintype K] in
theorem exists_mem_normalizer_not_mem {P H : Subgroup G} (hP : IsPGroup 3 P) (hHP : H ≤ P)
    (hlt : H ≠ P) : ∃ y ∈ P, y ∉ H ∧ ∀ x ∈ H, y * x * y⁻¹ ∈ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil := hP.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := P)
  have hH' : H.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hlt
    apply le_antisymm hHP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ H.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨y, hy, hyH⟩ := IsConcreteLE.exists_of_lt (hNC _ hH')
  refine ⟨y, y.2, hyH, fun x hx => ?_⟩
  have hxP : x ∈ P := hHP hx
  have h1 : (⟨x, hxP⟩ : P) ∈ H.subgroupOf P := hx
  have h2 := (Subgroup.mem_normalizer_iff.mp hy _).mp h1
  exact h2

include hq hK hcT hG hA hC1 in
theorem exists_sylow_NN1 : ∃ P : Subgroup G, P ≤ NN1 S ∧ PP1 S ≤ P ∧ IsPGroup 3 P ∧
    Nat.card P = q ^ 3 ∧ (∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) ∧
    Nat.card (NN1 S) = q ^ 3 * (q - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := card_NN1 hq hK hcT hG hA hC1
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have h3q : ¬ 3 ∣ q - 1 := by
    have : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
    omega
  obtain ⟨P, hPN, hPmem, hPc, hPn⟩ := exists_normal_sylow_of_burnside (NN1 S) (p := 3) (a := b)
    (m := q - 1) (by rw [hb, mul_comm]) h3q (burnside_NN1 hq hK hcT hb)
  have hPp : IsPGroup 3 P := IsPGroup.of_card hPc
  have hRP : RR S ≤ Subgroup.normalizer (P : Set G) := fun d hd =>
    mem_normalizer_of_conj_mem (fun x hx => hPn d (RR_le_normalizer_PP1 hq hcT hd) x hx)
  obtain ⟨t, ht⟩ := card_RR_invariant hq hK hPp hRP
  have hP1P : PP1 S ≤ P := by
    intro x hx
    refine (hPmem x (Subgroup.le_normalizer hx)).mpr ?_
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp isPGroup_PP1) ⟨x, hx⟩
    exact ⟨N, by rw [← hN, Subgroup.orderOf_mk]⟩
  have hP1c := card_PP1 hq hK hcT hG
  have hne : PP1 S ≠ P := by
    intro heq
    obtain ⟨Q, hQ⟩ := (isPGroup_PP1 (S := S)).exists_le_sylow
    have hQc := card_sylow3 hq hG Q
    have hne' : PP1 S ≠ Q := by
      intro h; rw [← h, hP1c] at hQc
      have : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    obtain ⟨y, hyQ, hyP1, hy⟩ := exists_mem_normalizer_not_mem Q.2 hQ hne'
    have hyN : y ∈ NN1 S := mem_normalizer_of_conj_mem hy
    apply hyP1
    rw [heq]
    refine (hPmem y hyN).mpr ?_
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp Q.2) ⟨y, hyQ⟩
    exact ⟨N, by rw [← hN, Subgroup.orderOf_mk]⟩
  have hgt : q ^ 2 < Nat.card P := by
    have hle := Subgroup.card_le_of_le hP1P
    rw [hP1c] at hle
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hP1P (by rw [hP1c, h])) hne
  have hle3 : Nat.card P ≤ q ^ 3 := by
    obtain ⟨Q, hQ⟩ := hPp.exists_le_sylow
    rw [← card_sylow3 hq hG Q]
    exact Subgroup.card_le_of_le hQ
  have ht3 : t = 3 := by
    rw [ht] at hgt hle3
    have h1 : 2 < t := (Nat.pow_lt_pow_iff_right (by omega)).mp hgt
    have h2 : t ≤ 3 := (Nat.pow_le_pow_iff_right (by omega)).mp hle3
    omega
  refine ⟨P, hPN, hP1P, hPp, by rw [ht, ht3], hPn, ?_⟩
  rw [hb, mul_comm, ← hPc, ht, ht3]

end CFSG.Walter.WardLocal
