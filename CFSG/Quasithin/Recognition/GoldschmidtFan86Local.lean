module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TwoFix
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem valence_isPrime (v : V) : (CFSG.Quasithin.Fan86.valence Γ v).Prime := by
  have h := F.valence v
  have e : CFSG.Quasithin.Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  rw [e]
  rcases h with h | h
  · rw [h]
    exact Nat.prime_three
  · rw [h]
    exact Nat.prime_five

theorem orbit_stabilizer_eq_neighborSet {v a : V} (ha : Γ.Adj v a) :
    MulAction.orbit (MulAction.stabilizer G v) a = Γ.neighborSet v := by
  ext b
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact F.adj_smul_of_mem_stabilizer hg ha
  · intro hb
    obtain ⟨g, hg, hga⟩ := F.loc_trans v a b ha hb
    exact ⟨⟨g, hg⟩, hga⟩

theorem valence_dvd_card_stabilizer (v : V) :
    CFSG.Quasithin.Fan86.valence Γ v ∣ Nat.card (MulAction.stabilizer G v) := by
  obtain ⟨a, ha⟩ := F.exists_adj v
  have hcard : Nat.card (MulAction.orbit (MulAction.stabilizer G v) a) =
      CFSG.Quasithin.Fan86.valence Γ v := by
    rw [F.orbit_stabilizer_eq_neighborSet ha]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer (MulAction.stabilizer G v) a)
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (MulAction.stabilizer G v) a),
    hcard] at h1
  exact ⟨_, h1⟩

theorem exists_orderOf_eq_valence (v : V) :
    ∃ x ∈ MulAction.stabilizer G v, orderOf x = CFSG.Quasithin.Fan86.valence Γ v := by
  have : Fact (CFSG.Quasithin.Fan86.valence Γ v).Prime := ⟨F.valence_isPrime v⟩
  have : Finite (MulAction.stabilizer G v) := F.loc_finite v
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer G v)
    (CFSG.Quasithin.Fan86.valence Γ v) (F.valence_dvd_card_stabilizer v)
  refine ⟨x, x.2, ?_⟩
  rw [← hx]
  exact Subgroup.orderOf_coe x

theorem not_pclosed (v : V) : ¬ PClosed Γ G v := by
  intro hP
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence v
  set H := MulAction.stabilizer G v with hH
  have : Finite H := F.loc_finite v
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : (CFSG.Quasithin.Fan86.valence Γ v).Prime := F.valence_isPrime v
  have hodd : CFSG.Quasithin.Fan86.valence Γ v ≠ 2 := by
    have e : CFSG.Quasithin.Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
    rw [e]
    rcases F.valence v with h | h <;> omega
  have hO2 : IsPGroup 2 (pCoreOf 2 H) :=
    (pCore_isPGroup (G := ↥H) 2).map H.subtype
  have hxp : x ^ CFSG.Quasithin.Fan86.valence Γ v = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have key : ∀ c ∈ Subgroup.zpowers x, c ∈ pCoreOf 2 H → c = 1 := by
    intro c hc hcO
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨n, hn⟩ := hO2 ⟨x ^ k, hcO⟩
    have h2 : (x ^ k) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 : (x ^ k) ^ CFSG.Quasithin.Fan86.valence Γ v = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    have hcop : Nat.Coprime (2 ^ n) (CFSG.Quasithin.Fan86.valence Γ v) :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))
    have := pow_gcd_eq_one.2 ⟨h2, h3⟩
    rwa [hcop, pow_one] at this
  have hcent : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hoH : o ∈ H := pCoreOf_le 2 H ho
    have h1 : o⁻¹ * x * o⁻¹⁻¹ ∈ Subgroup.zpowers x := hP x hx hxo o⁻¹ (H.inv_mem hoH)
    have h2 : x⁻¹ * o⁻¹ * x * o ∈ Subgroup.zpowers x := by
      have := (Subgroup.zpowers x).mul_mem (inv_mem (Subgroup.mem_zpowers x)) h1
      simpa [mul_assoc] using this
    have h3 : x⁻¹ * o⁻¹ * x * o ∈ pCoreOf 2 H := by
      have hn := le_normalizer_pCoreOf 2 H (H.inv_mem hx)
      have := (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.1 hn o⁻¹).1
        ((pCoreOf 2 H).inv_mem ho)) ho
      simpa [mul_assoc] using this
    have hc := key _ h2 h3
    have e1 : o⁻¹ * x * o = x := by
      have := congrArg (fun y => x * y) hc
      simpa [mul_assoc] using this
    calc o * x = o * (o⁻¹ * x * o) * 1 := by rw [e1, mul_one]
      _ = x * o := by group
  have hxO : x ∈ pCoreOf 2 H := F.charTwo v ⟨hx, hcent⟩
  have := key x (Subgroup.mem_zpowers x) hxO
  rw [this, orderOf_one] at hxo
  have := hp.two_le
  omega

theorem exists_fixed_nbr_of_two_group (v : V) (M : Subgroup G) (hM : M ≤ MulAction.stabilizer G v)
    (h2 : ∀ g ∈ M, ∃ k : ℕ, g ^ (2 ^ k) ∈ nbrStab Γ G v) :
    ∃ w, Γ.Adj v w ∧ ∀ g ∈ M, g • w = w := by
  let _ : MulAction M (Γ.neighborSet v) :=
    { smul := fun g w => ⟨(g : G) • (w : V), F.adj_smul_of_mem_stabilizer (hM g.2) w.2⟩
      one_smul := fun w => Subtype.ext (one_smul _ _)
      mul_smul := fun g h w => Subtype.ext (mul_smul _ _ _) }
  have hfinΩ : Finite (Γ.neighborSet v) :=
    Set.finite_coe_iff.2 (Set.finite_of_ncard_pos (by
      have h := F.valence v
      rw [← Nat.card_coe_set_eq]
      omega))
  let φ : M →* Equiv.Perm (Γ.neighborSet v) := MulAction.toPermHom M (Γ.neighborSet v)
  have hφ : ∀ (g : M) (w : Γ.neighborSet v), (φ g w : V) = (g : G) • (w : V) := fun g w => rfl
  have hp : IsPGroup 2 φ.range := by
    rintro ⟨q, m, hm⟩
    obtain ⟨k, hk⟩ := h2 m m.2
    refine ⟨k, Subtype.ext ?_⟩
    show q ^ 2 ^ k = 1
    rw [← hm, ← map_pow]
    refine Equiv.ext fun w => Subtype.ext ?_
    rw [hφ]
    simpa [Subgroup.coe_pow] using hk _ w.2
  have hmod := hp.card_modEq_card_fixedPoints (α := Γ.neighborSet v)
  have hodd : ¬ 2 ∣ Nat.card (Γ.neighborSet v) := by
    have h := F.valence v
    rcases h with h | h <;> rw [h] <;> decide
  have hfix : Nat.card (MulAction.fixedPoints φ.range (Γ.neighborSet v)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hodd ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨w, hw⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix)).1
  refine ⟨w, w.2, fun g hg => ?_⟩
  have := hw ⟨φ ⟨g, hg⟩, ⟨_, rfl⟩⟩
  exact congrArg Subtype.val this

end FanTree

end CFSG.Quasithin.Fan86
