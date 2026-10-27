module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_three_of_isL2Quot {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hL : IsL2Quot n (oTwoQuot ↥L)) : ∃ x ∈ L, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  have h3 : 3 ∣ 4 ^ n - 1 := by
    have h : 4 ^ n ≡ 1 ^ n [MOD 3] := Nat.ModEq.pow n rfl
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm
  have h3dvd : 3 ∣ Nat.card ↥L := by
    rw [hcard, CFSG.Quasithin.IsL2Quot.card hn hL]
    exact (h3.trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem str86_oTwoUpper_le_of_normal {L1 L2 S C : Subgroup G}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hC : C ≤ L2 ⊔ Q2 L1 L2 S) (hCn : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (C : Set G))
    (hCQ : ¬ C ≤ Q2 L1 L2 S) : oTwoUpper (L2 ⊔ Q2 L1 L2 S) ≤ C := by
  have hHQ2 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.normalizer (C : Set G) := le_sup_right.trans hCn
  have hsup : C ⊔ Q2 L1 L2 S = L2 ⊔ Q2 L1 L2 S := by
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 (sup_le hC le_sup_right)
      (F1.le_normalizer_sup hCn hHQ2) le_sup_right with h | h
    · exact absurd (h ▸ le_sup_left) hCQ
    · exact h
  have hsub : IsSubnormal C (L2 ⊔ Q2 L1 L2 S) :=
    A4.subnormal_of_normal hC ((Subgroup.normal_subgroupOf_iff_le_normalizer hC).mpr hCn)
  refine oTwoUpper_le_of_subnormal_mul hsub (pCoreOf_isPGroup 2 (P2 L1 L2 S)) fun x hx => ?_
  rw [← hsup] at hx
  obtain ⟨c, hc, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2C).mp hx
  exact ⟨c, hc, q, hq, rfl⟩

private theorem str86_not_s_le_q2 {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) : ¬ S ≤ Q2 L1 L2 S := by
  intro hle
  have h := str86_relIndex_q2_s hF.toW hSB hn hL2
  rw [Subgroup.relIndex_eq_one.mpr hle] at h
  have : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem str86_b2_commutator_oTwoUpper_core_le
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hn : 2 ≤ n)
    (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {W : Subgroup G} (hWQ1 : W ≤ Q1 L1 L2 S)
    (hWS : W ⊔ Q2 L1 L2 S = S) (hWc : ⁅Q1 L1 L2 S, W⁆ ≤ Z2 L1 L2 S) :
    ⁅oTwoUpper (L2 ⊔ Q2 L1 L2 S), str86Core L1 L2 S⁆ ≤ Z2 L1 L2 S := by
  set C : Subgroup G := centralizerMod (Z2 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) (str86Core L1 L2 S)
    with hCdef
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hn hL2
  have hHZ : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hCn : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod hHZ Subgroup.le_normalizer
      ((u3H_le_p2 L1 L2 S).trans (le_normalizer_str86Core L1 L2 S))
  have hWC : W ≤ C := by
    intro w hw
    have hwH : w ∈ L2 ⊔ Q2 L1 L2 S := hSH (hQ1S (hWQ1 hw))
    refine mem_centralizerMod.mpr ⟨hwH, hHZ hwH, fun u hu => ?_⟩
    have h := hWc (Subgroup.commutator_mem_commutator (str86Core_le_q1 L1 L2 S hu) hw)
    have e : w * u * w⁻¹ * u⁻¹ = ⁅u, w⁆⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
    rw [e]
    exact (Z2 L1 L2 S).inv_mem h
  have hCQ : ¬ C ≤ Q2 L1 L2 S := by
    intro hle
    exact str86_not_s_le_q2 hF hSB hn hL2 (hWS.symm.le.trans (sup_le (hWC.trans hle) le_rfl))
  have hle := str86_oTwoUpper_le_of_normal hF hn hL2 (centralizerMod_le_left _ _ _) hCn hCQ
  refine Subgroup.commutator_le.mpr fun x hx u hu => ?_
  have h := (mem_centralizerMod.mp (hle hx)).2.2 u hu
  rwa [commutatorElement_def]

theorem str86_b2_false_of_inf_le_core {L1 L2 S : Subgroup G}
    {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {W : Subgroup G} (hWQ1 : W ≤ Q1 L1 L2 S) (hWS : W ⊔ Q2 L1 L2 S = S)
    (hWc : ⁅Q1 L1 L2 S, W⁆ ≤ Z2 L1 L2 S)
    (hfree : ∀ ω ∈ L2, orderOf ω = 3 → ∀ z ∈ Z2 L1 L2 S, ⁅z, ω⁆ = 1 → z = 1)
    (hd : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ str86Core L1 L2 S) : False := by
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hn hL2
  have hSP2 : S ≤ P2 L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hHZ : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  set C : Subgroup G := centralizerMod (str86Core L1 L2 S) (L2 ⊔ Q2 L1 L2 S) (Q2 L1 L2 S)
    with hCdef
  have hCn : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod ((u3H_le_p2 L1 L2 S).trans (le_normalizer_str86Core L1 L2 S))
      Subgroup.le_normalizer ((u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 _))
  have hQ1C : Q1 L1 L2 S ≤ C := by
    intro x hx
    have hxS : x ∈ S := hQ1S hx
    refine mem_centralizerMod.mpr ⟨hSH hxS, le_normalizer_str86Core L1 L2 S (hSP2 hxS),
      fun u hu => hd (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)⟩
    · have huS : u ∈ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW) hu
      have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_q1_of_sylow (L1 := L1)
        (L2 := L2) (S := S) huS) x⁻¹).mp ((Q1 L1 L2 S).inv_mem hx)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]
      exact (Q1 L1 L2 S).mul_mem hx h
    · have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_q2_of_sylow (L1 := L1)
        (L2 := L2) (S := S) hxS) u).mp hu
      exact (Q2 L1 L2 S).mul_mem h ((Q2 L1 L2 S).inv_mem hu)
  have hCQ : ¬ C ≤ Q2 L1 L2 S := by
    intro hle
    exact str86_not_s_le_q2 hF hSB hn hL2
      (hWS.symm.le.trans (sup_le ((hWQ1.trans hQ1C).trans hle) le_rfl))
  have hle := str86_oTwoUpper_le_of_normal hF hn hL2 (centralizerMod_le_left _ _ _) hCn hCQ
  have h5 : ⁅oTwoUpper (L2 ⊔ Q2 L1 L2 S), Q2 L1 L2 S⁆ ≤ str86Core L1 L2 S := by
    refine Subgroup.commutator_le.mpr fun x hx u hu => ?_
    have h := (mem_centralizerMod.mp (hle hx)).2.2 u hu
    rwa [commutatorElement_def]
  have h6 := str86_b2_commutator_oTwoUpper_core_le hF hSB hn hL2 hWQ1 hWS hWc
  have hCA := A4.commutator_le_of_oTwoUpper (A := oTwoUpper (L2 ⊔ Q2 L1 L2 S))
    (N := Z2 L1 L2 S) (B := str86Core L1 L2 S) (D := Q2 L1 L2 S)
    ((oTwoUpper_le _).trans hHZ) ((le_sup_right : Q2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S).trans hHZ)
    (str86Core_le_q2 hF hSB hn hL2)
    (fun d hd => by
      obtain ⟨j, hj⟩ := hQ2p ⟨d, hd⟩
      refine ⟨j, ?_⟩
      have h : d ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      rw [h]
      exact (Z2 L1 L2 S).one_mem)
    h5 h6
  obtain ⟨ω, hωL, hω3⟩ := exists_orderOf_three_of_isL2Quot (by omega) hL2
  have hodd : Odd (orderOf ω) := by rw [hω3]; decide
  have hωA : ω ∈ oTwoUpper (oTwoUpper (L2 ⊔ Q2 L1 L2 S)) :=
    mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd
      ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S) hωL) hodd) hodd
  have hcomm : ∀ x ∈ Q2 L1 L2 S, ⁅x, ω⁆ ∈ Z2 L1 L2 S := by
    intro x hx
    have h := hCA (Subgroup.commutator_mem_commutator hωA hx)
    rw [← commutatorElement_inv]
    exact (Z2 L1 L2 S).inv_mem h
  have hZc : Z2 L1 L2 S ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S))
  have hinv : ∀ z ∈ Q2 L1 L2 S, z ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) →
      z ^ 2 = 1 → z ∈ Z2 L1 L2 S := fun z hz hzc hz2 =>
    mem_omegaOneCenterOf hz (fun y hy => Subgroup.mem_centralizer_iff.mp hzc y hy) hz2
  have hQZ : Q2 L1 L2 S = Z2 L1 L2 S :=
    eq_of_commutator_le_of_fixedPointFree hQ2p (omegaOneCenterOf_le _) hZc hinv hcomm
      (hfree ω hωL hω3)
  have hSQ1 : S ≤ Q1 L1 L2 S := hWS.symm.le.trans (sup_le hWQ1 (hQZ.le.trans hZ))
  have h := str86_relIndex_q1_s hF hSB hk hFc hU3
  rw [Subgroup.relIndex_eq_one.mpr hSQ1] at h
  have : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h64 : 64 ≤ (2 ^ k) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left this 3
  omega

end CFSG.Quasithin.Stroth

end
