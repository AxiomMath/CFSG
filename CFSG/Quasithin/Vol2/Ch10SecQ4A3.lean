module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A2
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Vol2.Ch10SecQ4H1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] [Finite G] {K J X : Subgroup G}

omit [Finite G] in
theorem perfect_of_isAltType_five (hK : IsShort2 K) (h5 : IsAltType K 5) : ⁅K, K⁆ = K := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hQ : commutator ↥(alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  apply C1GN.isShort2_eq_top_of_sup_pCore hK (commutator ↥K)
  have hmap : (commutator ↥K).map α = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hα]
    exact hQ
  have h := Subgroup.comap_map_eq α (commutator ↥K)
  rw [hmap, Subgroup.comap_top, hαk] at h
  exact h.symm

omit [Finite G] in
theorem ne_bot_of_isAltType_five (h5 : IsAltType K 5) : K ≠ ⊥ := by
  rintro rfl
  obtain ⟨α, hα, -⟩ := h5
  have hc : Nat.card ↥(alternatingGroup (Fin 5)) ≤ Nat.card ↥(⊥ : Subgroup G) :=
    Nat.card_le_card_of_surjective α hα
  rw [Subgroup.card_bot, nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

variable (hK : IsShort2 K) (hKJ : K ≤ J) (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
include hK hKJ hQK

theorem commutator_mem_conjClosure (h5 : IsAltType K 5) (hJ : J ∈ cComp X) {j : G} (hj : j ∈ J)
    {q : G} (hq : q ∈ pCoreOf 2 J) : j * q * j⁻¹ * q⁻¹ ∈ conjClosure (blockU K) J := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hKA : K ≤ actTriv J (pCoreOf 2 J) (conjClosure (blockU K) J) hPnorm
      (le_normalizer_conjClosure _ J) := fun k hk =>
    ⟨hKJ hk, fun x hx => le_conjClosure _ J (commutator_mem_blockU_of_pCoreOf' hK hKJ hQK hx hk)⟩
  have hJA : conjClosure K J ≤ actTriv J (pCoreOf 2 J) (conjClosure (blockU K) J) hPnorm
      (le_normalizer_conjClosure _ J) :=
    conjClosure_le fun h hh k hk => conj_mem_actTriv hh (hKA hk)
  rw [conjClosure_eq_of_mem_cComp hJ hKJ (perfect_of_isAltType_five hK h5)
    (ne_bot_of_isAltType_five h5)] at hJA
  exact (hJA hj).2 q hq

theorem commute_of_mem_center (hUQ : blockU K ≤ pCoreOf 2 J) (hZ : blockZ K = ⊥) {z : G}
    (hzK : z ∈ K) (hzC : z ∈ Subgroup.centralizer (K : Set G)) {w : G}
    (hw : w ∈ conjClosure (blockU K) J) : z * w = w * z := by
  have hWQ := conjClosure_le_pCoreOf (K := K) (J := J) hUQ
  have hQK' : blockQ K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hUK : blockU K ≤ K := Subgroup.commutator_le.mpr fun q hq k hk =>
    K.mul_mem (K.mul_mem (K.mul_mem (hQK' hq) hk) (K.inv_mem (hQK' hq))) (K.inv_mem hk)
  have hUW : blockU K ≤ conjClosure (blockU K) J := le_conjClosure _ J
  have hJW := le_normalizer_conjClosure (blockU K) J
  have hcomm := fun {a b : G} (ha : a ∈ conjClosure (blockU K) J)
    (hb : b ∈ conjClosure (blockU K) J) => commute_of_mem_conjClosure hK hKJ hQK hUQ ha hb
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk => (Subgroup.mem_centralizer_iff.mp hzC k hk)
  set c := z * w * z⁻¹ * w⁻¹ with hc
  have hcU : c ∈ blockU K := commutator_mem_blockU_of_pCoreOf' hK hKJ hQK (hWQ hw) hzK
  have hcK : ∀ k ∈ K, k * c = c * k := by
    intro k hk
    set w' := k * w * k⁻¹ with hw'
    have hw'W : w' ∈ conjClosure (blockU K) J :=
      (Subgroup.mem_normalizer_iff.mp (hJW (hKJ hk)) w).mp hw
    set u' := w' * w⁻¹ with hu'
    have hu'U : u' ∈ blockU K := by
      rw [hu', hw']
      exact commutator_mem_blockU_of_pCoreOf' hK hKJ hQK (hWQ hw) hk
    have hzu' : z * u' = u' * z := (hzc u' (hUK hu'U)).symm
    have hzk : k * z = z * k := hzc k hk
    have h1 : k * c * k⁻¹ = z * w' * z⁻¹ * w'⁻¹ := by
      have hzk' : k * z * k⁻¹ = z := by rw [hzk, mul_inv_cancel_right]
      calc k * c * k⁻¹ = (k * z * k⁻¹) * w' * (k * z * k⁻¹)⁻¹ * w'⁻¹ := by
            rw [hc, hw']; group
        _ = z * w' * z⁻¹ * w'⁻¹ := by rw [hzk']
    have hzw : z * w * z⁻¹ ∈ conjClosure (blockU K) J :=
      (Subgroup.mem_normalizer_iff.mp (hJW (hKJ hzK)) w).mp hw
    have h2 : z * w' * z⁻¹ * w'⁻¹ = c := by
      have hw'eq : w' = u' * w := by rw [hu', inv_mul_cancel_right]
      have hcw : u' * c = c * u' := hcomm (hUW hu'U) (hUW hcU)
      calc z * w' * z⁻¹ * w'⁻¹ = (z * u' * z⁻¹) * (z * w * z⁻¹ * w⁻¹) * u'⁻¹ := by
            rw [hw'eq]; group
        _ = u' * c * u'⁻¹ := by rw [hzu', mul_inv_cancel_right]
        _ = c := by rw [hcw, mul_inv_cancel_right]
    have := congrArg (· * k) (h1.trans h2)
    simpa [mul_assoc] using this
  have hcZ : c ∈ blockZ K := ⟨hcU, Subgroup.mem_centralizer_iff.mpr fun k hk => hcK k hk⟩
  rw [hZ, Subgroup.mem_bot, hc] at hcZ
  have := congrArg (· * (w * z)) hcZ
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
