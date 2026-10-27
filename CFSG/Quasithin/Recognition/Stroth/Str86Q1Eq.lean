module

public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp2
public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqCommMap
public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqChief
public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqOrder
public import CFSG.Quasithin.Recognition.Stroth.Str86X1K1Chief
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat3
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBridge

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_exists_mem_u3X1_not_mem_q2 {L1 L2 S : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    ∃ x ∈ u3X1 L1 L2 S, x ∉ Q2 L1 L2 S := by
  by_contra h
  push Not at h
  have hle : S ≤ Q2 L1 L2 S :=
    calc S = u3X1 L1 L2 S ⊔ Q2 L1 L2 S := hX1Q2.symm
      _ ≤ Q2 L1 L2 S := sup_le h le_rfl
  have h1 : (Q2 L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hle
  rw [h1, pow_two] at hSQ2
  have hr : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h4 : 2 * 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ hr
  omega

theorem str86_z2_isChiefStep_u3H
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4) :
    IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (u3H L1 L2 S) ⊥ (Z2 L1 L2 S) := by
  obtain ⟨W, hWZ, hstepW, hncW⟩ := str86_exists_chiefStep_u3H hF hSB hk hFc hU3 hB2 h2 hZI
  have hn : 2 ≤ 2 * k := by omega
  have hge : (2 ^ (2 * k)) ^ 2 ≤ (⊥ : Subgroup G).relIndex W :=
    str86_card_chiefStep_ge hF.toW hn hL2 hstepW hncW
  have hcard : Nat.card (Z2 L1 L2 S) ≤ Nat.card W := by
    have e : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [hZ2, ← Subgroup.relIndex_bot_left]
    calc (2 ^ k) ^ 4 = (2 ^ (2 * k)) ^ 2 := by rw [e]; ring
      _ ≤ (⊥ : Subgroup G).relIndex W := hge
  have hW : W = Z2 L1 L2 S := Subgroup.eq_of_le_of_card_ge hWZ hcard
  rw [hW] at hstepW hncW
  exact ⟨hstepW, hncW⟩

theorem str86_q2_noncentral_count_le_one
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    ∀ c, F112W.IsChiefSeriesBetween (u3H L1 L2 S) (Q2 L1 L2 S) (Z2 L1 L2 S) (Q2 L1 L2 S) c →
      c ≤ 1 := by
  intro c hser
  have hn : 2 ≤ 2 * k := by omega
  have e2 : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  obtain ⟨x, hxX, hxQ⟩ := str86_exists_mem_u3X1_not_mem_q2 (by omega) hX1Q2 hSQ2
  have hxS : x ∈ S := hX1Q2 ▸ (le_sup_left : u3X1 L1 L2 S ≤ u3X1 L1 L2 S ⊔ Q2 L1 L2 S) hxX
  have hcore : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  refine chiefSeriesBetween_count_le_one_of_displacement hn (str86_isL2Quot_u3H hF.toW hL2)
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)) (q2_le_u3H L1 L2 S) (str86_s_le_u3H hF.toW hSB hn hL2 hxS)
    ?_ ?_ ?_ hser
  · rw [hcore]
    exact str86_sq_mem_q2 hF.toW hSB hn hL2 hxS
  · rw [hcore]
    exact hxQ
  · rw [e2]
    exact str86_q2_displacement_le hF hY hI4 hX1Q2 hSQ2 x hxX

theorem str86_q2_chiefFactor_natural_card
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    {Lo Hi : Subgroup G} (hZLo : Z2 L1 L2 S ≤ Lo)
    (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) Lo Hi)
    (hnc : ¬ IsCentralStep (u3H L1 L2 S) Lo Hi) :
    Lo.relIndex Hi = (2 ^ k) ^ 4 ∧ Lo.relIndex (centralizerMod Lo Hi S) = (2 ^ k) ^ 2 := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hn : 2 ≤ 2 * k := by omega
  have e2 : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  obtain ⟨x, hxX, hxQ⟩ := str86_exists_mem_u3X1_not_mem_q2 (by omega) hX1Q2 hSQ2
  have hxS : x ∈ S := hX1Q2 ▸ (le_sup_left : u3X1 L1 L2 S ≤ u3X1 L1 L2 S ⊔ Q2 L1 L2 S) hxX
  have hcore : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
  have hHQ : u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hXX : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ ≤ Lo := by
    rw [hX1']
    exact hZ1Z2.trans hZLo
  have hHiLo : Hi ≤ Subgroup.normalizer (Lo : Set G) :=
    (hstep.1.1.trans (q2_le_u3H L1 L2 S)).trans (D14.le_normalizer_of_isNormalIn hstep.2.1)
  have hdisp : (centralizerMod Lo Hi (Subgroup.zpowers x)).relIndex Hi ≤ 2 ^ (2 * k) := by
    rw [e2]
    exact (relIndex_centralizerMod_le_of_section hZLo hstep.1.1 hHiLo).trans
      (str86_q2_displacement_le hF hY hI4 hX1Q2 hSQ2 x hxX)
  have hxsq : x * x ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [hcore]
    exact str86_sq_mem_q2 hF.toW hSB hn hL2 hxS
  have hxO : x ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rw [hcore]
    exact hxQ
  obtain ⟨hcard, hfix⟩ := l2_chiefFactor_card_of_quadratic hn (str86_isL2Quot_u3H hF.toW hL2)
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)) (q2_le_u3H L1 L2 S) hHQ hstep hnc
    (str86_s_le_u3H hF.toW hSB hn hL2) (le_normalizer_u3X1_sylow hF) hX1Q2 hXX hxX hxsq hxO hdisp
  refine ⟨?_, ?_⟩
  · rw [hcard, e2]
    ring
  · rw [hfix, e2]

theorem str86_q2_fixed_mem_z2
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    ∀ x ∈ Q2 L1 L2 S, (∀ g ∈ L2 ⊔ Q2 L1 L2 S, g * x * g⁻¹ * x⁻¹ ∈ Z2 L1 L2 S) →
      x ∈ Z2 L1 L2 S := by
  intro c hcQ hc
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hn : 2 ≤ 2 * k := by omega
  obtain ⟨hstepZ, hncZ⟩ := str86_z2_isChiefStep_u3H hF hSB hk hFc hU3 hB2 h2 hZI hL2 hZ2
  have hZc : ∀ z ∈ Z2 L1 L2 S, ∀ y ∈ Q2 L1 L2 S, z * y = y * z := fun z hz y hy =>
    Subgroup.mem_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hy) z hz
  have hHQ : u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  by_cases hcent : ∀ y ∈ Q2 L1 L2 S, c * y = y * c
  · exact mem_omegaOneCenterOf_of_central_fixed (pCoreOf_isPGroup 2 (P2 L1 L2 S))
      (str86_centralizer_u3H_z2 hF hSB h1 hB2 h2 hZI) hcQ hcent hc
  · push Not at hcent
    have hsurj := exists_commutator_eq_of_minimal hZc hHQ hQH hstepZ hcQ hc hcent
    obtain ⟨hstepK, hncK⟩ :=
      isChiefStep_centralizer_of_commutatorMap hZc hHQ hQH hstepZ hncZ hcQ hc hsurj
    have hfixK := relIndex_centralizerMod_centralizer_eq_card hZc hHQ hQH
      (str86_s_le_u3H hF.toW hSB hn hL2) hcQ hc hsurj
    have hZK : Z2 L1 L2 S ≤ Q2 L1 L2 S ⊓ Subgroup.centralizer ({c} : Set G) := by
      intro z hz
      refine ⟨omegaOneCenterOf_le _ hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hZc z hz c hcQ).symm
    obtain ⟨-, hK⟩ := str86_q2_chiefFactor_natural_card hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2
      hX1' hY hI4 hX1Q2 hSQ2 hZK hstepK hncK
    have hZS : Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S :=
      (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.2.2.2
    rw [hK, hZS, hZ1] at hfixK
    have hr : 2 ≤ 2 ^ k :=
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 * 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ hr
    rw [pow_two] at hfixK
    omega

theorem str86_q2_quot_elemAbelian
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    (∀ x ∈ Q2 L1 L2 S, ∀ y ∈ Q2 L1 L2 S, x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) ∧
      (∀ x ∈ Q2 L1 L2 S, x * x ∈ Z2 L1 L2 S) ∧
      (Z2 L1 L2 S).relIndex (centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S) ≤ (2 ^ k) ^ 2 := by
  have hn : 2 ≤ 2 * k := by omega
  have hcore : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hHQ : u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hHZ : u3H L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hZn : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (Z2 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer (omegaOneCenterOf_le _) hHZ
  have hfix := str86_q2_fixed_mem_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4
    hX1Q2 hSQ2
  have hcount := str86_q2_noncentral_count_le_one hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hY hI4
    hX1Q2 hSQ2
  have hnat : ∀ Lo Hi : Subgroup G, Z2 L1 L2 S ≤ Lo →
      IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) Lo Hi → ¬ IsCentralStep (u3H L1 L2 S) Lo Hi →
      Lo.relIndex (centralizerMod Lo Hi S) ≤ (2 ^ k) ^ 2 := fun Lo Hi hZLo hstep hnc =>
    (str86_q2_chiefFactor_natural_card hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hX1' hY hI4
      hX1Q2 hSQ2 hZLo hstep hnc).2.le
  obtain ⟨N, hZN, hNQ, hHN, hO2, hNQZ, hNsq, hCN⟩ :=
    exists_chiefStep_above_of_count_le_one hcore.ge hHQ hZn hcount hnat
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) hfix
  have hSyl : IsSylowTwoOf S (u3H L1 L2 S) :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) (str86_s_le_u3H hF.toW hSB hn hL2)
      (u3H_le_p2 L1 L2 S)
  have hQS : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  obtain ⟨hab, hsq⟩ :=
    commutator_mem_and_sq_mem_of_minimal hSyl hQS hZN hNQ hHZ hHN hHQ hO2 hNQZ hNsq hfix
  have hCle : centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S ≤ N :=
    centralizerMod_sylow_le_of_elemAbelian hSyl hZN hNQ hHZ hHN hHQ
      (str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hn hL2) hO2 hab hsq hfix
  have heq : centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) S = centralizerMod (Z2 L1 L2 S) N S :=
    le_antisymm (fun y hy => ⟨hCle hy, hy.2⟩) (centralizerMod_mono_left S hNQ)
  refine ⟨hab, hsq, ?_⟩
  rw [heq]
  exact hCN

theorem str86_q1_eq_of_parts
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI3 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7) :
    Q1 L1 L2 S = u3X1 L1 L2 S := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hn : 2 ≤ 2 * k := by omega
  obtain ⟨c, hser⟩ := exists_isChiefSeriesFrom_u3X1 hF
  have hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_u3X1_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hser
  have hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2 := by
    rw [str86_relIndex_q2_s hF.toW hSB hn hL2, ← pow_mul, mul_comm]
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
  obtain ⟨hab, -, hC⟩ := str86_q2_quot_elemAbelian hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2
    hZ1 hY hX1' hI4 hX1Q2 hSQ2
  exact str86_q1_eq_of_card hF hX1Q2 hSQ2 hY hI4
    (str86_q1_inf_q2_le_centralizerMod hX1Q2 hI3 hZ1Z2 hab) hC

theorem str86Q1Eq_holds :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
      VU3Big L1 → VBig L2 → VL2 L2 →
      L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S →
        Q1 L1 L2 S = u3X1 L1 L2 S := by
  intro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI hZQ
  obtain ⟨k, hk, F, hFld, hFin, hFc, hU3⟩ := h1
  letI : Field F := hFld
  letI : Finite F := hFin
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨hL2, hZ2, hZ1, hY, hX1', hX1Q1⟩ :=
    str86_l2_eq_and_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ
  obtain ⟨hM, -⟩ :=
    str86_X1Natural_holds hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1
  have hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7 :=
    card_u3X1_of_card_u3M (u3Z1_le_u3X1 hF hSB h1 hB2 h2 hZI) hZ1 hM
  exact str86_q1_eq_of_parts hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1 hI4

theorem str86X1K1_holds
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    Str86X1K1 L1 L2 S := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨hL2, hZ2, hZ1, hY, hX1', hX1Q1⟩ :=
    str86_l2_eq_and_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ
  have hQ1 : Q1 L1 L2 S = u3X1 L1 L2 S := str86Q1Eq_holds G L1 L2 S hF hSB h1 hB2 h2 hZI hZQ
  have hchief := str86_X1_isChiefStep_z1 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
    hX1Q1
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ1
    have hr : 2 ≤ 2 ^ k :=
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact str86X1K1_of_q1_eq hF hSB h1 hB2 h2 hZI hQ1 hchief hX1' hZ1ne

theorem str86X1Module_holds
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S) :
    Str86X1Module hF k hX1' := by
  obtain ⟨hL2, hZ2, hZ1, hY, -, hX1Q1⟩ := str86_l2_eq_and_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ
  exact And.intro
    (str86_X1Natural_holds hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1)
    (str86X1K1_holds hF hSB hk hFc hU3 hB2 h2 hZI hZQ)

end CFSG.Quasithin.Stroth
