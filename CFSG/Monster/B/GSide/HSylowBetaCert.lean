module

public import CFSG.Monster.B.GSide.HSylowBetaCertData
public import CFSG.Monster.B.CTIB.SylowCenter
public import Certificates.Certificate3011
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3121
public import Certificates.Certificate3137
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr autApply liftImgs6)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem qmul_self_cases (k : ℕ) : qmul gArr k k = 0 ∨ qmul gArr k k = 2 ^ 22 := by
  simp only [qmul, Nat.xor_self, Nat.zero_mod, Bool.xor_self, Bool.false_xor, Nat.zero_or]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem qS_inv_eq
    (k : ℕ) : (qS k)⁻¹ = qS (hc5Inv k) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hc5Inv]
  split_ifs with h
  · rw [qS_mul, h, qS_zero]
  · have h2 : qmul gArr k k = 2 ^ 22 := (qmul_self_cases k).resolve_left h
    rw [← qS_mul, ← mul_assoc, qS_mul, h2, qS_two_pow_22, xs_mul_self]

theorem rs6_eq_mul :
    rs 6 = hs 6 * qS 10541 := rfl

theorem conj_rs6_qS
    (k : ℕ) : (rs 6)⁻¹ * qS k * rs 6 = qS (hc5ConjR k) := by
  have e : (rs 6)⁻¹ * qS k * rs 6 = (qS 10541)⁻¹ * ((hs 6)⁻¹ * qS k * hs 6) * qS 10541 := by
    rw [rs6_eq_mul]
    group
  rw [e, conj_hs6_qS, qS_inv_eq, qS_mul, qS_mul]
  rfl

theorem hc5Z_spec
    (m : ℕ) : (rs 6)⁻¹ * (qS m)⁻¹ * rs 6 * qS m = qS (hc5Z m) := by
  have e : (rs 6)⁻¹ * (qS m)⁻¹ * rs 6 * qS m = ((rs 6)⁻¹ * qS m * rs 6)⁻¹ * qS m := by group
  rw [e, conj_rs6_qS, qS_inv_eq, qS_mul]
  rfl

theorem hc5Comm_iff
    (m : ℕ) : qS m * e2158 = e2158 * qS m ↔ hc5Comm m = true := by
  rw [e2158_eq, qS_mul, qS_mul, hc5Comm, beq_iff_eq]
  exact qS_injOn.eq_iff (qmul_lt _ _) (qmul_lt _ _)

theorem hc5_commutator_mem
    {n : Sbp} (hn : n ∈ Qs) (hne : n * e2158 = e2158 * n) :
    ∃ z ∈ hc5Orbit, (rs 6)⁻¹ * n⁻¹ * rs 6 * n = qS z := by
  obtain ⟨m, hm, rfl⟩ := exists_qS hn
  have h := hc5_brute
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at h
  have hm' : (!hc5Comm m || hc5Orbit.contains (hc5Z m)) = true := h ⟨m, hm⟩ (List.mem_finRange _)
  rw [(hc5Comm_iff m).1 hne, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hm'
  exact ⟨_, hm', hc5Z_spec m⟩

theorem hc5_exists_commutator
    {z : ℕ} (hz : z ∈ hc5Orbit) :
    ∃ n ∈ Qs, n * e2158 = e2158 * n ∧ (rs 6)⁻¹ * n⁻¹ * rs 6 * n = qS z := by
  obtain ⟨hl, hl', hall⟩ := hc5_wit
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  rw [List.all_eq_true] at hall
  have h := hall i (List.mem_range.2 (hl' ▸ hi))
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨-, hc⟩, hZ⟩ := h
  refine ⟨qS (hc5Wit.getD i 0), qS_mem _, (hc5Comm_iff _).2 hc, ?_⟩
  rw [hc5Z_spec, hZ, List.getD_eq_getElem _ _ hi]

theorem hc5_ranks
    {z : ℕ} (hz : z ∈ hc5Orbit) (h0 : z ≠ 0) :
    qS z ≠ 1 ∧ qS z * qS z = 1 ∧ ((βr (qS z)) - 1).rank = 2048 ∧
      ((βr (xs * qS z)) - 1).rank = 2048 ∧ ((βr (e2158 * qS z)) - 1).rank = 2168 ∧
      ((βr (e2158 * (xs * qS z))) - 1).rank = 2168 := by
  have h := hc5_rank_codes
  rw [List.all_eq_true] at h
  have hz' := h z hz
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, h0,
    false_or] at hz'
  obtain ⟨hlt, ⟨⟨⟨⟨hsq, h1⟩, h2⟩, h3⟩, h4⟩⟩ := hz'
  have key : ∀ n, n < 2 ^ 23 → innerTyRank (innerTy innerTab n) = 2048 ∨
      innerTyRank (innerTy innerTab n) = 2168 →
      ((βr (qS n)) - 1).rank = innerTyRank (innerTy innerTab n) := fun n hn hr =>
    ((innerRank_spec hn).2.2 (by rcases hr with hr | hr <;> rw [hr] <;> decide)).2
  refine ⟨fun h => h0 ((qS_eq_one_iff hlt).1 h), by rw [qS_mul, hsq, qS_zero], ?_, ?_, ?_, ?_⟩
  · rw [key z hlt (Or.inl h1), h1]
  · rw [← qS_two_pow_22, qS_mul, key _ (qmul_lt _ _) (Or.inl h2), h2]
  · rw [e2158_eq, qS_mul, key _ (qmul_lt _ _) (Or.inr h3), h3]
  · rw [e2158_eq, ← qS_two_pow_22, qS_mul, qS_mul, key _ (qmul_lt _ _) (Or.inr h4), h4]

theorem zero_mem_hc5Orbit : 0 ∈ hc5Orbit := List.mem_cons_self ..

theorem hc5_set_eq :
    {s : Sbp | ∃ n ∈ Qs, n * e2158 = e2158 * n ∧ (rs 6)⁻¹ * n⁻¹ * rs 6 * n = s} =
      qS '' {z | z ∈ hc5Orbit} := by
  ext s
  constructor
  · rintro ⟨n, hn, hne, rfl⟩
    obtain ⟨z, hz, h⟩ := hc5_commutator_mem hn hne
    exact ⟨z, hz, h.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact hc5_exists_commutator hz

theorem hc5Orbit_lt {z : ℕ} (hz : z ∈ hc5Orbit) : z < 2 ^ 23 := by
  have h := hc5_rank_codes
  rw [List.all_eq_true] at h
  have hz' := h z hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz'
  exact hz'.1

theorem ncard_hc5_set :
    (qS '' {z | z ∈ hc5Orbit} \ {1}).ncard = 63 := by
  have hinj : Set.InjOn qS {z | z ∈ hc5Orbit} := fun a ha b hb h =>
    qS_injOn (hc5Orbit_lt ha) (hc5Orbit_lt hb) h
  have h1 : qS '' {z | z ∈ hc5Orbit} \ {1} = qS '' ({z | z ∈ hc5Orbit} \ {0}) := by
    rw [Set.image_sdiff_of_injOn hinj (Set.singleton_subset_iff.2 zero_mem_hc5Orbit),
      Set.image_singleton, qS_zero]
  rw [h1, (hinj.mono Set.sdiff_subset).ncard_image, Set.ncard_sdiff_singleton_of_mem
    (show (0 : ℕ) ∈ {z | z ∈ hc5Orbit} from zero_mem_hc5Orbit),
    show {z | z ∈ hc5Orbit} = (hc5Orbit.toFinset : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hc5_nodup, hc5_wit.2.1]

end CFSG.Monster.B.GSide
