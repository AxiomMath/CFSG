module

public import CFSG.Quasithin.H13.GoldschmidtC137S168Act

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ.S168

open MulAction

theorem conj_pow_nat {G : Type} [Group G] {g x : G} {m : ℕ} (h : g * x * g⁻¹ = x ^ m) (n : ℕ) :
    g ^ n * x * (g ^ n)⁻¹ = x ^ (m ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by group
      _ = g * x ^ (m ^ n) * g⁻¹ := by rw [ih]
      _ = (g * x * g⁻¹) ^ (m ^ n) := conj_pow.symm
      _ = x ^ (m ^ (n + 1)) := by rw [h, ← pow_mul, pow_succ, mul_comm]

namespace Frame

variable {S : Type} [Group S] (F : Frame S)

theorem x_pow_seven : F.x ^ 7 = 1 := F.hxo ▸ pow_orderOf_eq_one F.x

@[expose] def pt (i : ZMod 7) : Sylow 7 S := F.x ^ i.val • F.Q₀

theorem pow_smul_eq (n : ℕ) : F.x ^ n • F.Q₀ = F.pt (n : ZMod 7) := by
  unfold pt
  rw [ZMod.val_natCast, pow_eq_pow_mod n F.x_pow_seven]

theorem pt_zero : F.pt 0 = F.Q₀ := by
  simp [pt]

theorem x_smul_pt (i : ZMod 7) : F.x • F.pt i = F.pt (i + 1) := by
  unfold pt
  rw [← mul_smul, ← pow_succ', F.pow_smul_eq]
  simp [pt]

theorem y_smul_pt (i : ZMod 7) : F.y • F.pt i = F.pt (2 * i) := by
  unfold pt
  have h1 : F.y * F.x ^ i.val = (F.x ^ (2 * i.val)) * F.y := by
    have h2 : F.y * F.x ^ i.val * F.y⁻¹ = F.x ^ (2 * i.val) := by
      rw [← conj_pow, F.hrel, ← pow_mul, mul_comm]
    rw [← h2]
    group
  rw [← mul_smul, h1, mul_smul, F.hyQ]
  have := F.pow_smul_eq (2 * i.val)
  rw [this]
  simp [pt]

theorem inf_stabilizer_eq_bot [Finite S] (hcard : Nat.card S = 168) :
    (F.P : Subgroup S) ⊓ stabilizer S F.Q₀ = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPc : Nat.card F.P = 7 := card_sylow hcard F.P
  have hd : Nat.card ↥((F.P : Subgroup S) ⊓ stabilizer S F.Q₀) ∣ 7 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : (F.P : Subgroup S) ⊓ stabilizer S F.Q₀ ≤ F.P)
    rwa [hPc] at this
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hd with h1 | h7
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have heq : (F.P : Subgroup S) ⊓ stabilizer S F.Q₀ = F.P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, hPc])
    have hPle : (F.P : Subgroup S) ≤ stabilizer S F.Q₀ := heq ▸ inf_le_right
    have hPn : (F.P : Subgroup S) ≤ Subgroup.normalizer (F.Q₀ : Set S) := by
      rw [← Sylow.stabilizer_eq_normalizer]
      exact hPle
    have hinf := F.P.2.inf_normalizer_sylow F.Q₀
    have hPQ : (F.P : Subgroup S) ≤ F.Q₀ := by
      rw [inf_eq_left.2 hPn] at hinf
      exact inf_eq_left.1 hinf.symm
    exact F.hQP (Sylow.ext (F.P.is_maximal' F.Q₀.2 hPQ))

theorem pt_ne_P (i : ZMod 7) : F.pt i ≠ F.P := by
  intro h
  have hxP : F.x ^ i.val ∈ Subgroup.normalizer (F.P : Set S) :=
    Subgroup.pow_mem _ (Subgroup.le_normalizer F.hx) _
  have h1 : (F.x ^ i.val)⁻¹ • F.P = F.P := Sylow.smul_eq_iff_mem_normalizer.2 (inv_mem hxP)
  have h2 : (F.x ^ i.val)⁻¹ • F.pt i = F.Q₀ := by
    unfold pt
    exact inv_smul_smul _ _
  apply F.hQP
  rw [← h2, h]
  exact h1

theorem pt_injective [Finite S] (hcard : Nat.card S = 168) : Function.Injective F.pt := by
  intro i j h
  have hij : (F.x ^ j.val)⁻¹ * F.x ^ i.val ∈ stabilizer S F.Q₀ := by
    rw [mem_stabilizer_iff, mul_smul]
    have : F.x ^ i.val • F.Q₀ = F.x ^ j.val • F.Q₀ := h
    rw [this, inv_smul_smul]
  have hP : (F.x ^ j.val)⁻¹ * F.x ^ i.val ∈ (F.P : Subgroup S) :=
    mul_mem (inv_mem (Subgroup.pow_mem _ F.hx _)) (Subgroup.pow_mem _ F.hx _)
  have h1 : (F.x ^ j.val)⁻¹ * F.x ^ i.val ∈ (F.P : Subgroup S) ⊓ stabilizer S F.Q₀ := ⟨hP, hij⟩
  rw [F.inf_stabilizer_eq_bot hcard, Subgroup.mem_bot] at h1
  have h3 : F.x ^ i.val = F.x ^ j.val := (inv_mul_eq_one.1 h1).symm
  have h4 := (pow_eq_pow_iff_modEq).1 h3
  rw [F.hxo] at h4
  have h5 : i.val = j.val := by
    have := ZMod.val_lt i
    have := ZMod.val_lt j
    unfold Nat.ModEq at h4
    omega
  exact ZMod.val_injective 7 h5

@[expose] def e : Option (ZMod 7) → Sylow 7 S
  | none => F.P
  | some i => F.pt i

theorem e_injective [Finite S] (hcard : Nat.card S = 168) : Function.Injective F.e := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => exact absurd h.symm (F.pt_ne_P j)
  | some i =>
    cases b with
    | none => exact absurd h (F.pt_ne_P i)
    | some j => exact congrArg some (F.pt_injective hcard h)

theorem e_bijective [Finite S] [IsSimpleGroup S] (hcard : Nat.card S = 168) :
    Function.Bijective F.e := by
  refine (F.e_injective hcard).bijective_of_nat_card_le ?_
  rw [card_sylow_eight hcard F.P, Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

end Frame

end CFSG.Quasithin.H13.U3.GC137.SQ.S168
