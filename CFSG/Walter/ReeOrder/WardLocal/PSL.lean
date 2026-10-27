module

public import CFSG.Walter.ReeOrder.JT.AuxPSL2Borel
public import CFSG.Walter.ReeOrder.JT.PSL2Unipotent

public section

open scoped MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.JT

variable {K : Type*} [Field K]

theorem pslU_zero : pslU (0 : K) = 1 := by
  rw [pslU, slU_zero, QuotientGroup.mk_one]

theorem pslU_inv (b : K) : (pslU b)⁻¹ = pslU (-b) := by
  rw [inv_eq_iff_mul_eq_one, pslU_mul, add_neg_cancel, pslU_zero]

theorem pslU_pow (b : K) (n : ℕ) : pslU b ^ n = pslU ((n : K) * b) := by
  rw [pslU, ← QuotientGroup.mk_pow, slU_pow]
  rfl

theorem pslU_pow_three [CharP K 3] (b : K) : pslU b ^ 3 = 1 := by
  rw [pslU_pow, show ((3 : ℕ) : K) = 0 from CharP.cast_eq_zero K 3, zero_mul, pslU_zero]

theorem pslU_ne_one {b : K} (hb : b ≠ 0) : pslU b ≠ 1 := by
  rw [← pslU_zero]
  exact fun h => hb (pslU_injective h)

theorem mem_pslE_iff {x : PSL(2, K)} : x ∈ pslE K ↔ ∃ b, pslU b = x := Iff.rfl

theorem card_pslE [Finite K] : Nat.card (pslE K) = Nat.card K := by
  rw [show Nat.card (pslE K) = Nat.card (Set.range (pslU (K := K))) from rfl,
    Nat.card_range_of_injective pslU_injective]

theorem centralizer_pslU {p f : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hf : f ≠ 0)
    {b : GaloisField p f} (hb : b ≠ 0) :
    Subgroup.centralizer ({pslU b} : Set PSL(2, GaloisField p f)) = pslE (GaloisField p f) := by
  have hfacts := psl2UnipotentFacts (⊤ : Subgroup PSL(2, GaloisField p f)) Subgroup.topEquiv hp hf
  have hcard : Nat.card (pslE (GaloisField p f)) = p ^ f := by
    rw [card_pslE, GaloisField.card p f hf]
  have h := hfacts.centralizer (pslE (GaloisField p f)) le_top hcard (pslU b) ⟨b, rfl⟩
    (pslU_ne_one hb)
  rwa [top_inf_eq] at h

section Torus

variable [Fintype K] [DecidableEq K]

@[expose] noncomputable def gen (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Kˣ :=
  (IsCyclic.exists_generator (α := Kˣ)).choose

theorem gen_spec : ∀ x : Kˣ, x ∈ Subgroup.zpowers (gen K) :=
  (IsCyclic.exists_generator (α := Kˣ)).choose_spec

theorem orderOf_gen : orderOf (gen K) = Fintype.card K - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers gen_spec, Nat.card_eq_fintype_card,
    Fintype.card_units]

@[expose] noncomputable def dgen (K : Type*) [Field K] [Fintype K] [DecidableEq K] : PSL(2, K) :=
  pslD (gen K)

theorem dgen_eq : dgen K = pslD (gen K) := rfl

theorem dgen_pow_conj (j : ℕ) (b : K) :
    dgen K ^ j * pslU b * (dgen K ^ j)⁻¹ = pslU (((gen K : Kˣ) : K) ^ (2 * j) * b) :=
  pslD_pow_conj _ j b

theorem dgen_pow (j : ℕ) : dgen K ^ j = pslD (gen K ^ j) := pslD_pow _ j

theorem dgen_pow_eq_one_iff {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (j : ℕ) :
    dgen K ^ j = 1 ↔ k ∣ j := by
  rw [dgen_pow, pslD, QuotientGroup.eq_one_iff, slD_mem_center_iff, ← pow_two, ← pow_mul,
    ← orderOf_dvd_iff_pow_eq_one, orderOf_gen, hq, Nat.add_sub_cancel]
  constructor
  · intro h
    exact Nat.dvd_of_mul_dvd_mul_left two_pos (by rw [mul_comm j 2] at h; exact h)
  · intro h
    rw [mul_comm j 2]
    exact Nat.mul_dvd_mul_left 2 h

theorem orderOf_dgen {k : ℕ} (hq : Fintype.card K = 2 * k + 1) : orderOf (dgen K) = k := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((dgen_pow_eq_one_iff hq k).mpr dvd_rfl)
  · exact (dgen_pow_eq_one_iff hq _).mp (pow_orderOf_eq_one _)

theorem fpf {k : ℕ} (hq : Fintype.card K = 2 * k + 1) {j : ℕ} {b : K} (hb : b ≠ 0)
    (h : dgen K ^ j * pslU b * (dgen K ^ j)⁻¹ = pslU b) : dgen K ^ j = 1 := by
  rw [dgen_pow_conj] at h
  have h1 := pslU_injective h
  have h2 : ((gen K : Kˣ) : K) ^ (2 * j) = 1 :=
    mul_right_cancel₀ hb (h1.trans (one_mul b).symm)
  have h3 : gen K ^ (2 * j) = 1 := Units.ext (by simpa using h2)
  rw [dgen_pow_eq_one_iff hq]
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_gen, hq, Nat.add_sub_cancel] at h4
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h4

theorem conj_pslU {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : Odd k) {b : K} (hb : b ≠ 0) :
    ∃ j : ℕ, dgen K ^ j * pslU 1 * (dgen K ^ j)⁻¹ = pslU b ∨
      dgen K ^ j * pslU (-1) * (dgen K ^ j)⁻¹ = pslU b := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, gen K ^ i = Units.mk0 b hb := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (gen_spec (Units.mk0 b hb))
    refine ⟨(z % orderOf (gen K)).toNat, ?_⟩
    have hpos : 0 < orderOf (gen K) := orderOf_pos (gen K)
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne')),
      zpow_mod_orderOf, hz]
  have hord := orderOf_gen (K := K)
  rw [hq, Nat.add_sub_cancel] at hord
  have hneg : ((gen K : Kˣ) : K) ^ k = -1 := by
    have h1 : (((gen K : Kˣ) : K) ^ k) * (((gen K : Kˣ) : K) ^ k) = 1 := by
      have h0 : gen K ^ (k + k) = 1 := by
        rw [← two_mul, ← hord, pow_orderOf_eq_one]
      rw [← pow_add, ← Units.val_pow_eq_pow_val, h0, Units.val_one]
    have h2 : ((gen K : Kˣ) : K) ^ k ≠ 1 := by
      intro h
      have h' : gen K ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have := orderOf_dvd_of_pow_eq_one h'
      rw [hord] at this
      have hk0 := hk.pos
      have := Nat.le_of_dvd hk0 this
      omega
    exact (mul_self_eq_one_iff.mp h1).resolve_left h2
  have hb' : ((gen K : Kˣ) : K) ^ i = b := by
    have := congrArg Units.val hi
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at this
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | hio
  · refine ⟨j, Or.inl ?_⟩
    rw [dgen_pow_conj, mul_one, ← hb', hj, two_mul]
  · obtain ⟨j, hj⟩ : Even (i + k) := hio.add_odd hk
    refine ⟨j, Or.inr ?_⟩
    rw [dgen_pow_conj, ← hb']
    congr 1
    rw [two_mul, ← hj, pow_add, hneg]
    ring

end Torus

end CFSG.Walter.WardLocal
