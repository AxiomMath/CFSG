module

public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Cop
public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

variable [Finite G]

omit [Finite G] in
theorem card_conjClosure_eq {H V D : Subgroup G}
    (hDY : D ≤ conjClosure V H) (hD : E2.IsExtraspecialPlus 2 D)
    (φ : ↥(conjClosure V H) →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf (conjClosure V H)) : Nat.card (conjClosure V H) = 192 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
    gold_card_perm_fin_three, hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv,
    hD.2.1] at h1
  rw [h1]
  norm_num

theorem relIndex_eq_three {T Mc M H V D : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hH : IsHStar T M H) (hNV : Subgroup.normalizer (V : Set G) = M) (hVT : V ≤ T)
    (hV : ¬ V ≤ pCoreOf 2 H) (hDY : D ≤ conjClosure V H) (hD : E2.IsExtraspecialPlus 2 D)
    (φ : ↥(conjClosure V H) →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf (conjClosure V H)) :
    T.relIndex H = 3 ∧ ¬ H ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hq.sylow
  have hT2 : IsPGroup 2 (S : Subgroup G) := hq.sylow.1
  have hTH : (S : Subgroup G) ≤ H := hH.1.1
  have hY192 : Nat.card (conjClosure V H) = 192 := card_conjClosure_eq hDY hD φ hφs hφk
  set T : Subgroup G := (S : Subgroup G) with hTdef
  set Y := conjClosure V H with hYdef
  have hVH : V ≤ H := hVT.trans hTH
  have hYH : Y ≤ H :=
    conjClosure_le fun h hh v hv => H.mul_mem (H.mul_mem hh (hVH hv)) (H.inv_mem hh)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_conjClosure V H
  have hnT : ¬ H ≤ Subgroup.normalizer (T : Set G) := by
    intro hHT
    have hYT : Y ≤ T := conjClosure_le fun h hh v hv =>
      (Subgroup.mem_normalizer_iff.mp (hHT hh) v).mp (hVT hv)
    obtain ⟨n, hn⟩ := (hT2.to_le hYT).exists_card_eq
    rw [hY192] at hn
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hnotM : ¬ T ⊔ Y ≤ M := by
    intro hle
    have hYM : Y ≤ M := le_sup_right.trans hle
    have hVY : V ≤ Y := le_conjClosure V H
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hNV ▸ hYM
    have hV2 : IsPGroup 2 V := hT2.to_le hVT
    have h1 : V ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer 2 hVY hYV hV2
    have h2 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
        (hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
    exact hV (h1.trans h2)
  have hinH : InH T (T ⊔ Y) := inH_of_le S le_sup_left (sup_le hTH hYH) hH.1
  have hHeq : T ⊔ Y = H := hH.2.2 (T ⊔ Y) hinH (sup_le hTH hYH) hnotM
  have hTN : T ≤ Subgroup.normalizer (Y : Set G) := hTH.trans hHY
  have e1 : Y.relIndex (T ⊔ Y) = Y.relIndex T := relIndex_sup_eq hTN
  rw [hHeq] at e1
  have e2 := Subgroup.relIndex_mul_card Y H
  have e3 := Subgroup.relIndex_mul_card Y T
  have e4 := Subgroup.relIndex_mul_card T H
  rw [inf_eq_left.mpr hYH, hY192] at e2
  rw [inf_eq_left.mpr hTH] at e4
  have hr0 : Y.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e2
    have := Nat.card_pos (α := H)
    omega
  have hkey : T.relIndex H * Nat.card ↥(Y ⊓ T) = 192 := by
    have h5 : Y.relIndex H * (T.relIndex H * Nat.card ↥(Y ⊓ T)) = Y.relIndex H * 192 := by
      calc Y.relIndex H * (T.relIndex H * Nat.card ↥(Y ⊓ T))
          = T.relIndex H * (Y.relIndex T * Nat.card ↥(Y ⊓ T)) := by rw [e1]; ring
        _ = T.relIndex H * Nat.card T := by rw [e3]
        _ = Nat.card H := e4
        _ = Y.relIndex H * 192 := e2.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) h5
  have hodd : ¬ 2 ∣ T.relIndex H := by
    intro h2
    apply hq.sylow.2
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le hTH)
  have hdvd : T.relIndex H ∣ 3 := by
    have h192 : T.relIndex H ∣ 2 ^ 6 * 3 := ⟨Nat.card ↥(Y ⊓ T), by rw [hkey]; norm_num⟩
    have hcop : Nat.Coprime (T.relIndex H) (2 ^ 6) :=
      Nat.Coprime.pow_right 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact hcop.dvd_of_dvd_mul_left h192
  have h1 : T.relIndex H ≠ 1 := by
    intro h1
    apply hnT
    have : H ≤ T := Subgroup.relIndex_eq_one.mp h1
    exact (le_antisymm this hTH) ▸ Subgroup.le_normalizer
  have h3 : T.relIndex H = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h h1
    · exact h
  exact ⟨h3, hnT⟩

end Y15111

end CFSG.Quasithin
