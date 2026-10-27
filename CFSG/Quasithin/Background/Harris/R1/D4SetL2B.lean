module

public import CFSG.Quasithin.Recognition.F112J2Torus
public import CFSG.Quasithin.Recognition.SzR1MNU
import CFSG.RankThree.PartOne.SRC.LiftP

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.F112W

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem bigB_eq_of_le (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    bigB K1 L2 S = K1 ⊓ Subgroup.normalizer (S : Set G) := by
  have h1 := F1.bigB_eq_inf_normalizer hR
  rw [inf_eq_left.mpr hSK] at h1
  have h2 : K1 ⊔ S ⊔ borelOf L2 S = K1 :=
    le_antisymm (sup_le (sup_le le_rfl hSK) ((F112J2.borelOf_L2_le_S h hR).trans hSK))
      (le_sup_left.trans le_sup_left)
  rw [h1, h2]

theorem bigB_le_K1 (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    bigB K1 L2 S ≤ K1 :=
  (bigB_eq_of_le h hR hSK).le.trans inf_le_left

omit [Finite G] in
theorem sup_bigB_eq (K1 L2 S : Subgroup G) :
    L2 ⊔ bigB K1 L2 S = L2 ⊔ S ⊔ borelOf K1 S := by
  have hSB : S ≤ bigB K1 L2 S := le_sup_right
  have hBK : borelOf K1 S ≤ bigB K1 L2 S := le_sup_left.trans le_sup_left
  have hBL : borelOf L2 S ≤ L2 := F1.borelOf_le L2 S
  refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) (sup_le (sup_le le_sup_right
    (hBL.trans (le_sup_left.trans le_sup_left))) (le_sup_right.trans le_sup_left)))
    (sup_le (sup_le le_sup_left (hSB.trans le_sup_right)) (hBK.trans le_sup_right))

theorem bigB_le_normalizer_L2S (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    bigB K1 L2 S ≤ Subgroup.normalizer ((L2 ⊔ S : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (F1.bigB_le_normalizer_left hR).2
    ((bigB_eq_of_le h hR hSK).le.trans inf_le_right)

theorem pCoreOf_L2B (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    pCoreOf 2 (L2 ⊔ bigB K1 L2 S) = pCoreOf 2 (L2 ⊔ S) := by
  have hP : L2 ⊔ S ≤ L2 ⊔ bigB K1 L2 S := sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hN : L2 ⊔ bigB K1 L2 S ≤ Subgroup.normalizer ((L2 ⊔ S : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_normalizer.trans' le_sup_left) (bigB_le_normalizer_L2S h hR hSK)
  exact le_antisymm
    (pCoreOf_le_pCoreOf_of_isSylowTwoOf (isSylowTwoOf_parabolic' hR) le_sup_right hP)
    (pCoreOf_mono_of_le_normalizer hP hN)

theorem centralizer_pCore_L2B_le (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S)
    (hSK : S ≤ K1) :
    (L2 ⊔ bigB K1 L2 S) ⊓ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S) : Set G) ≤
      pCoreOf 2 (L2 ⊔ S) := by
  have hc : CharTwo (L2 ⊔ bigB K1 L2 S) := by
    rw [sup_bigB_eq]
    exact hR.hyp.h2.charTwo
  unfold CharTwo at hc
  rwa [pCoreOf_L2B h hR hSK] at hc

theorem card_L2S_eq (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    Nat.card (L2 ⊔ S : Subgroup G) = 3 * Nat.card S := by
  have h1 := Subgroup.relIndex_mul_card (H := S) (K := L2 ⊔ S)
  rw [F112J2.relIndex_L2S hR h.s3, inf_eq_left.mpr le_sup_right] at h1
  exact h1.symm

theorem inf_bigB_L2S (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    (L2 ⊔ S) ⊓ bigB K1 L2 S = S := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  calc (L2 ⊔ S) ⊓ bigB K1 L2 S ≤ (L2 ⊔ S) ⊓ (K1 ⊔ S) :=
        inf_le_inf_left _ ((bigB_le_K1 h hR hSK).trans le_sup_left)
    _ = S := F112J2.inf_L2S_K1S hR h.s3

theorem card_L2B_eq (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) :
    Nat.card (L2 ⊔ bigB K1 L2 S : Subgroup G) = 3 * Nat.card (bigB K1 L2 S) := by
  have hSB : S ≤ bigB K1 L2 S := le_sup_right
  have hX : L2 ⊔ bigB K1 L2 S = (L2 ⊔ S) ⊔ bigB K1 L2 S := by
    rw [sup_assoc, sup_eq_right.mpr hSB]
  have h1 := Subgroup.relIndex_mul_card (H := bigB K1 L2 S) (K := (L2 ⊔ S) ⊔ bigB K1 L2 S)
  rw [relIndex_sup_eq_relIndex_inf (bigB_le_normalizer_L2S h hR hSK), inf_bigB_L2S h hR hSK,
    F112J2.relIndex_L2S hR h.s3, inf_eq_left.mpr le_sup_right, ← hX] at h1
  exact h1.symm

theorem exists_three_comm (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1)
    (t : G) (ht : t ∈ bigB K1 L2 S) (ht7 : orderOf t = 7) :
    ∃ s ∈ L2 ⊔ S, orderOf s = 3 ∧ s * t = t * s ∧
      s ∉ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
  set P : Subgroup G := L2 ⊔ S with hP
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h.hyp.h1.pgroup
  have hcardP : Nat.card P = 3 * 2 ^ k := by rw [hP, card_L2S_eq h hR, hk]
  have h7P : ¬ 7 ∣ Nat.card P := by
    rw [hcardP]
    intro hd
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime 7)).mp hd with hd | hd
    · omega
    · have := (Fact.out : Nat.Prime 7).dvd_of_dvd_pow hd
      omega
  have hE : IsPGroup 7 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht7, pow_one])
  have hEN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr (bigB_le_normalizer_L2S h hR hSK ht))
  obtain ⟨T, hT⟩ := CFSG.RankThree.PartOne.SRC.exists_sylow_fixed (p := 7) 3 hE hEN h7P
  set T' : Subgroup G := (T : Subgroup P).map P.subtype with hT'
  have hT'P : T' ≤ P := Subgroup.map_subtype_le _
  have hcardT : Nat.card T' = 3 := by
    rw [hT', Subgroup.card_map_of_injective P.subtype_injective, T.card_eq_multiplicity, hcardP,
      Nat.factorization_mul (by norm_num) (by positivity)]
    simp [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T') 3 (by rw [hcardT])
  set s : G := (x : G) with hs
  have hsT : s ∈ T' := x.2
  have hs3 : orderOf s = 3 := by rw [hs, Subgroup.orderOf_coe]; exact hx
  have hzp : Subgroup.zpowers s = T' := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hsT) ?_
    rw [Nat.card_zpowers, hs3, hcardT]
  have hconj : t * s * t⁻¹ ∈ T' := by
    have := hT t (Subgroup.mem_zpowers t) s hsT
    exact this
  have hcomm : s * t = t * s := by
    rw [← hzp] at hconj
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hconj
    have hs3' : s ^ 3 = 1 := by rw [← hs3]; exact pow_orderOf_eq_one s
    have key := zpow_mod_orderOf s m
    rw [hs3] at key
    have hmod : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by
      push_cast
      omega
    rcases hmod with h0 | h1 | h2
    · rw [h0, zpow_zero, hm] at key
      have : s = 1 := by simpa using (mul_inv_eq_one.mp key.symm)
      rw [this, orderOf_one] at hs3
      omega
    · rw [h1, zpow_one, hm] at key
      exact (mul_inv_eq_iff_eq_mul.mp key.symm).symm
    · have hA : t * s * t⁻¹ = s⁻¹ := by
        rw [h2, hm] at key
        rw [← key]
        have : s ^ (2 : ℤ) * s = 1 := by
          rw [← zpow_add_one]
          simpa using hs3'
        exact eq_inv_of_mul_eq_one_left this
      have e1 : t * s = s⁻¹ * t := mul_inv_eq_iff_eq_mul.mp hA
      have e2 : s * t = t * s⁻¹ := by
        calc s * t = s * t * s * s⁻¹ := by group
          _ = s * (t * s) * s⁻¹ := by group
          _ = s * (s⁻¹ * t) * s⁻¹ := by rw [e1]
          _ = t * s⁻¹ := by group
      have hc2 : Commute s (t ^ 2) := by
        show s * t ^ 2 = t ^ 2 * s
        rw [pow_two]
        calc s * (t * t) = (s * t) * t := (mul_assoc _ _ _).symm
          _ = (t * s⁻¹) * t := by rw [e2]
          _ = t * (s⁻¹ * t) := mul_assoc _ _ _
          _ = t * (t * s) := by rw [e1]
          _ = (t * t) * s := (mul_assoc _ _ _).symm
      have hc8 := hc2.pow_right 4
      have ht8 : (t ^ 2) ^ 4 = t := by
        have h7 : t ^ 7 = 1 := by rw [← ht7]; exact pow_orderOf_eq_one t
        calc (t ^ 2) ^ 4 = t ^ 7 * t := by rw [← pow_mul, ← pow_succ]
          _ = t := by rw [h7, one_mul]
      rw [ht8] at hc8
      exact hc8
  refine ⟨s, hT'P hsT, hs3, hcomm, fun hsC => ?_⟩
  have hsQ : s ∈ pCoreOf 2 P :=
    SzR1.MNU.centralizer_V_le_pCore h hR ⟨hT'P hsT, hsC⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 P)) ⟨s, hsQ⟩
  have h3 : orderOf s = orderOf (⟨s, hsQ⟩ : pCoreOf 2 P) :=
    Subgroup.orderOf_coe (⟨s, hsQ⟩ : pCoreOf 2 P)
  rw [hs3, hj] at h3
  have hj := h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (dvd_of_eq hj)
  omega

end CFSG.Quasithin.Background.Harris.R1
