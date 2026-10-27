module

public import CFSG.Quasithin.Background.Harris.R1.QbetaDAbelFin
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.SzR1Fam
public import CFSG.Quasithin.Recognition.SzR1Perm

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.LieType.BorelTits

theorem abelian_of_card_le_four {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hD : IsPGroup 2 D) (h4 : Nat.card D ≤ 4) : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsMulCommutative D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hD
    have hn2 : n ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hgt
      omega
    interval_cases n
    · have : Nat.card D = 1 := by simpa using hn
      have : Subsingleton D := (Nat.card_eq_one_iff_unique.mp this).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have hn' : Nat.card D = 2 := by simpa using hn
      have : IsCyclic D := isCyclic_of_prime_card (p := 2) hn'
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hn
  intro a ha b hb
  have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem conj_eq_of_two_pow {G : Type*} [Group G] (D : Subgroup G) (q t : G)
    (hq : Nat.Coprime 3 (orderOf q)) (hqN : q ∈ Subgroup.normalizer (D : Set G))
    (ht : t ^ 3 = 1) (hact : ∀ d ∈ D, t * d * t⁻¹ = q * d * q⁻¹) :
    ∀ d ∈ D, t * d * t⁻¹ = d := by
  have hpow : ∀ n : ℕ, ∀ d ∈ D, t ^ n * d * (t ^ n)⁻¹ = q ^ n * d * (q ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro d _; simp
    | succ n ih =>
      intro d hd
      have hqn : q ^ n ∈ Subgroup.normalizer (D : Set G) := Subgroup.pow_mem _ hqN n
      have hd' : q ^ n * d * (q ^ n)⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hqn d).mp hd
      calc t ^ (n + 1) * d * (t ^ (n + 1))⁻¹
          = t * (t ^ n * d * (t ^ n)⁻¹) * t⁻¹ := by rw [pow_succ']; group
        _ = t * (q ^ n * d * (q ^ n)⁻¹) * t⁻¹ := by rw [ih d hd]
        _ = q * (q ^ n * d * (q ^ n)⁻¹) * q⁻¹ := hact _ hd'
        _ = q ^ (n + 1) * d * (q ^ (n + 1))⁻¹ := by rw [pow_succ']; group
  intro d hd
  have h3 : (q ^ 3) * d = d * (q ^ 3) := by
    have := hpow 3 d hd
    rw [ht, one_mul, inv_one, mul_one] at this
    calc q ^ 3 * d = (q ^ 3 * d * (q ^ 3)⁻¹) * q ^ 3 := by group
      _ = d * q ^ 3 := by rw [← this]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hq
  have hc : Commute q d := by
    rw [← hm]
    exact Commute.pow_left h3 m
  rw [hact d hd, hc.eq]
  group

theorem c3_pow_two_pow (n : ℕ) : c3 ^ (2 ^ n) = c3 ∨ c3 ^ (2 ^ n) = c3 ^ 2 := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · rw [h]; right; rfl
    · rw [h]; left
      calc (c3 ^ 2) ^ 2 = c3 ^ 3 * c3 := by group
        _ = c3 := by rw [c3_pow_three, one_mul]

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_t3 (C : FamCtx K1 L2 S Zs (Fin 5))
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (h3 : ∃ k : ↥K1, C.D.act k = c3) : ∃ t : ↥K1, t ^ 3 = 1 ∧ C.D.act t = c3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h3
  have hk3 : C.D.act (k ^ 3) = 1 := by rw [map_pow, hk, c3_pow_three]
  have hmem : ((k ^ 3 : ↥K1) : G) ∈ pCoreOf 2 K1 := hker _ hk3
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup (r := 2) K1) ⟨((k ^ 3 : ↥K1) : G), hmem⟩
  have ha' : (k ^ 3) ^ (2 ^ a) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val ha
    simpa using this
  set t0 : ↥K1 := k ^ (2 ^ a) with ht0
  have ht03 : t0 ^ 3 = 1 := by
    rw [ht0, ← pow_mul, mul_comm, pow_mul]
    exact ha'
  have hact : C.D.act t0 = c3 ^ (2 ^ a) := by rw [ht0, map_pow, hk]
  rcases c3_pow_two_pow a with h | h
  · exact ⟨t0, ht03, by rw [hact, h]⟩
  · refine ⟨t0⁻¹, ?_, ?_⟩
    · rw [inv_pow, ht03, inv_one]
    · rw [map_inv, hact, h]
      refine inv_eq_of_mul_eq_one_right ?_
      calc c3 ^ 2 * c3 = c3 ^ 3 := by group
        _ = 1 := c3_pow_three

end CFSG.Quasithin.Background.Harris.R1
