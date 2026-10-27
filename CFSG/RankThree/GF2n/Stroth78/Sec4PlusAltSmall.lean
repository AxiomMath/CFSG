module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.GroupTheory.Alt8InvolutionCentralizer
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod (commSpaceOf commSpace_le_commSpaceOf apply_mem_commSpaceOf)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem six_lt_finrank_commSpaceOf_Xsub_of_mulEquiv_alt8
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8))
    (ρ : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
    (hρ : ∀ x : ↥(Xsub S a), ρ x = (rhoBar S (x : Hbar z) :
      Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) :
    6 < finrank (ZMod 2) ↥(commSpaceOf ρ ⊤) := by
  classical
  by_contra hle
  push Not at hle
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hR : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  obtain ⟨⟨α, hαR⟩, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα1' : α ≠ 1 := fun h1 => hα1 (Subtype.ext h1)
  have hαX : α ∈ Xsub S a := h.Rbar_le_Xsub hαR
  let αX : ↥(Xsub S a) := ⟨α, hαX⟩
  have hα2 : α * α = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hαR)
  have hαX2 : αX * αX = 1 := Subtype.ext hα2
  have hαX1 : αX ≠ 1 := fun h1 => hα1' (congrArg Subtype.val h1)
  have hC := CFSG.GroupTheory.card_centralizer_dvd_one_ninety_two_of_mulEquiv e hαX2 hαX1
  set ã := aVec S h.mem_Q with hã
  have hã0 : ã ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hãW : ã ∈ commSpaceOf ρ ⊤ := by
    have hmem := aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hαR hα1'
    refine commSpace_le_commSpaceOf ρ (Subgroup.mem_top αX) ?_
    rw [hρ αX]
    exact hmem
  letI : MulAction ↥(Xsub S a) (Additive (QbarOf S)) := MulAction.compHom _ ρ
  have hsmul : ∀ (x : ↥(Xsub S a)) (v : Additive (QbarOf S)), x • v = ρ x v :=
    fun x v => rfl
  set K : Subgroup ↥(Xsub S a) := MulAction.stabilizer ↥(Xsub S a) ã with hK
  have hKmem : ∀ x : ↥(Xsub S a), x ∈ K ↔ ρ x ã = ã := fun x => by
    rw [hK, MulAction.mem_stabilizer_iff, hsmul]
  have hX20160 : Nat.card ↥(Xsub S a) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcard : Nat.card ↥K * K.index = 20160 := (Subgroup.card_mul_index K).trans hX20160
  have hidx : K.index = (MulAction.orbit ↥(Xsub S a) ã).ncard :=
    MulAction.index_stabilizer ↥(Xsub S a) ã
  have hW64 : Nat.card ↥(commSpaceOf ρ ⊤) ≤ 64 := by
    rw [CFSG.LargeExtraspecial.AS35QCo.natCard_submodule]
    calc 2 ^ finrank (ZMod 2) ↥(commSpaceOf ρ ⊤) ≤ 2 ^ 6 :=
          Nat.pow_le_pow_right (by norm_num) hle
      _ = 64 := by norm_num
  have horb : (MulAction.orbit ↥(Xsub S a) ã).ncard ≤ 63 := by
    have hsub : MulAction.orbit ↥(Xsub S a) ã ⊆
        ((commSpaceOf ρ ⊤ : Submodule (ZMod 2) (Additive (QbarOf S))) :
          Set (Additive (QbarOf S))) \ {0} := by
      rintro _ ⟨x, rfl⟩
      refine ⟨apply_mem_commSpaceOf ρ (Subgroup.mem_top x) hãW, ?_⟩
      intro h0
      have h0' : ρ x ã = 0 := h0
      exact hã0 ((map_eq_zero_iff _ (LinearEquiv.injective _)).mp h0')
    have hncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_diff_singleton_of_mem (Submodule.zero_mem _)] at hncard
    have hnc : ((commSpaceOf ρ ⊤ : Submodule (ZMod 2) (Additive (QbarOf S))) :
        Set (Additive (QbarOf S))).ncard ≤ 64 := by
      rw [← Nat.card_coe_set_eq]
      exact hW64
    omega
  have hKodd : ∀ x ∈ K, Odd (orderOf x) → x * αX = αX * x := by
    intro x hx hodd
    let Y : Subgroup (Hbar z) := K.map (Xsub S a).subtype
    have hfix : ∀ y ∈ Y, rhoLin S y ã = ã := by
      rintro _ ⟨x', hx', rfl⟩
      have h1 := (hKmem x').mp hx'
      rw [hρ x'] at h1
      exact h1
    have hZ' : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u := by
      rintro _ ⟨x', _, rfl⟩ u
      exact rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ x' x'.2 u
    have hy : (x : Hbar z) ∈ Y := ⟨x, hx, rfl⟩
    have hodd' : Odd (orderOf (x : Hbar z)) := by
      have : orderOf ((x : ↥(Xsub S a)) : Hbar z) = orderOf x := Subgroup.orderOf_coe x
      rwa [this]
    have hCH := mem_CHbar_of_odd_orderOf S h.mem_Q hfix hZ' hy hodd'
    have hcomm := commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR hαR hα1' hCH
    exact Subtype.ext hcomm
  set Cα : Subgroup ↥(Xsub S a) := Subgroup.centralizer ({αX} : Set ↥(Xsub S a)) with hCα
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → Odd p → p ∣ 192 := by
    intro p hp hpd hpo
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpd
    have hxo : orderOf (x : ↥(Xsub S a)) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hcomm := hKodd x x.2 (by rw [hxo]; exact hpo)
    have hmem : (x : ↥(Xsub S a)) ∈ Cα := by
      rw [hCα, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hd : orderOf (⟨(x : ↥(Xsub S a)), hmem⟩ : ↥Cα) ∣ Nat.card ↥Cα := orderOf_dvd_natCard _
    have hxo' : orderOf (⟨(x : ↥(Xsub S a)), hmem⟩ : ↥Cα) = p := by
      rw [← hxo, ← Subgroup.orderOf_coe]
    rw [hxo'] at hd
    exact hd.trans hC
  have h5 : ¬ 5 ∣ Nat.card ↥K := fun hd => by
    have := hprime 5 (by norm_num) hd (by decide)
    omega
  have h7 : ¬ 7 ∣ Nat.card ↥K := fun hd => by
    have := hprime 7 (by norm_num) hd (by decide)
    omega
  have h9 : ¬ 9 ∣ Nat.card ↥K := by
    intro hd
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 3 (n := 2) (by simpa using hd)
    let P' : Subgroup ↥(Xsub S a) := P.map K.subtype
    have hP'card : Nat.card ↥P' = 9 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hP]
      norm_num
    have hPC : P' ≤ Cα := by
      rintro _ ⟨k, hk, rfl⟩
      have hord : orderOf (⟨k, hk⟩ : ↥P) ∣ 9 := by
        have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥P)
        rwa [hP] at this
      have hodd : Odd (orderOf ((k : ↥K) : ↥(Xsub S a))) := by
        have h1 : orderOf ((k : ↥K) : ↥(Xsub S a)) = orderOf (⟨k, hk⟩ : ↥P) := by
          rw [Subgroup.orderOf_coe k]
          exact Subgroup.orderOf_coe (⟨k, hk⟩ : ↥P)
        rw [h1]
        exact Odd.of_dvd_nat (by decide) hord
      have hcomm := hKodd (k : ↥(Xsub S a)) k.2 hodd
      show (k : ↥(Xsub S a)) ∈ Cα
      rw [hCα, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have h99 : 9 ∣ Nat.card ↥Cα := by
      rw [← hP'card]
      exact Subgroup.card_dvd_of_le hPC
    have := h99.trans hC
    omega
  have hidx_pos : 0 < K.index := by
    rcases Nat.eq_zero_or_pos K.index with h0 | h0
    · rw [h0, mul_zero] at hcard
      omega
    · exact h0
  have h5' : 5 ∣ K.index := by
    have : 5 ∣ Nat.card ↥K * K.index := by rw [hcard]; norm_num
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp this with h | h
    · exact absurd h h5
    · exact h
  have h7' : 7 ∣ K.index := by
    have : 7 ∣ Nat.card ↥K * K.index := by rw [hcard]; norm_num
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp this with h | h
    · exact absurd h h7
    · exact h
  have h3' : 3 ∣ K.index := by
    by_contra hn
    have hcop : Nat.Coprime 9 K.index := by
      have h3c : Nat.Coprime 3 K.index := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn
      simpa using Nat.Coprime.pow_left 2 h3c
    have : 9 ∣ Nat.card ↥K * K.index := by rw [hcard]; norm_num
    exact h9 (hcop.dvd_of_dvd_mul_right this)
  have h105 : 105 ∣ K.index := by
    have h35 : 35 ∣ K.index := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5' h7'
    have : 3 * 35 ∣ K.index := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3' h35
    simpa using this
  have hle105 : 105 ≤ K.index := Nat.le_of_dvd hidx_pos h105
  omega

theorem six_lt_finrank_commSpaceOf_rhoX_of_mulEquiv_alt8
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) :
    6 < finrank (ZMod 2) ↥(commSpaceOf (rhoX S a) ⊤) :=
  six_lt_finrank_commSpaceOf_Xsub_of_mulEquiv_alt8 S h h217 h34 hZ e (rhoX S a) (rhoX_apply S a)

end CFSG.RankThree.GF2n.Stroth78
