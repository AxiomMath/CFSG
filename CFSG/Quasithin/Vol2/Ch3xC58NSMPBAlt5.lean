module

public import CFSG.Quasithin.Background.C2Basic
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.CoreFree

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.QuasithinUnique

theorem exists_sylow_eq_of_card_three {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y ∣ 60)
    {H : Subgroup Y} (hH : Nat.card H = 3) : ∃ Q : Sylow 3 Y, (Q : Subgroup Y) = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 H := IsPGroup.of_card (n := 1) (by rw [hH, pow_one])
  obtain ⟨Q, hHQ⟩ := hp.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hHQ ?_).symm⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvd : 3 ^ k ∣ 60 := hk ▸ (Subgroup.card_subgroup_dvd_card (Q : Subgroup Y)).trans hY
  have hk1 : k ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  rw [hk, hH]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := pow_one 3

theorem card_alt_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem alt5_three_excluded {L K T : Subgroup Γ} (eL : ↥L ≃* alternatingGroup (Fin 5))
    (hKL : K ≤ L) (eK : ↥K ≃* alternatingGroup (Fin 3)) (hT : IsSylowTwoOf T L)
    (hsub : IsSubnormal K (K ⊔ T)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = 3 := (Nat.card_congr eK.toEquiv).trans card_alt_three
  have hL60 : Nat.card L = 60 := (Nat.card_congr eL.toEquiv).trans card_alt_five
  have hKY : K ≤ K ⊔ T := le_sup_left
  have hY60 : Nat.card ↥(K ⊔ T) ∣ 60 := hL60 ▸ Subgroup.card_dvd_of_le (sup_le hKL hT.1)
  have hKYc : Nat.card ↥(K.subgroupOf (K ⊔ T)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv).trans hK3
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card_three hY60 hKYc
  have hQsub : (Q : Subgroup ↥(K ⊔ T)).IsSubnormal := by
    rw [hQ]
    exact (isSubnormal_iff_subgroupOf hKY).mp hsub
  have hQn := CFSG.LyonsUnitaryFour.sylow_normal_of_isSubnormal Q hQsub
  rw [hQ] at hQn
  have hTN : T ≤ Subgroup.normalizer (K : Set Γ) :=
    le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mp hQn)
  have hKLc : Nat.card ↥(K.subgroupOf L) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv).trans hK3
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_card_three (by rw [hL60]) hKLc
  set N := Subgroup.normalizer ((P : Subgroup ↥L) : Set ↥L) with hN
  have hPN : (P : Subgroup ↥L) ≤ N := Subgroup.le_normalizer
  have hTLN : T.subgroupOf L ≤ N := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    rw [hN, hP, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hTN ht)) (x : Γ)
  have hidxP : (P : Subgroup ↥L).index = 20 := by
    have h := Subgroup.card_mul_index (K.subgroupOf L)
    rw [hKLc, hL60] at h
    rw [hP]
    omega
  have hdvd20 : N.index ∣ 20 := hidxP ▸ Subgroup.index_dvd_of_le hPN
  have hodd : ¬ 2 ∣ N.index := fun h2 => hT.2.2 (h2.trans (Subgroup.index_dvd_of_le hTLN))
  have hmod : N.index ≡ 1 [MOD 3] := by
    have h := card_sylow_modEq_one (p := 3) (G := ↥L)
    rwa [Sylow.card_eq_index_normalizer P] at h
  have h1 : N.index = 1 := by
    have hpos : 0 < N.index := Nat.pos_of_dvd_of_pos hdvd20 (by norm_num)
    have hle : N.index ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd20
    rw [Nat.ModEq] at hmod
    generalize N.index = d at hdvd20 hodd hmod hpos hle ⊢
    interval_cases d <;> omega
  have hPn : (P : Subgroup ↥L).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h1)
  have : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eL).2 inferInstance
  have hc : Nat.card ↥(P : Subgroup ↥L) = 3 := by rw [hP]; exact hKLc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup ↥L) with h | h
  · rw [h, Subgroup.card_bot] at hc
    omega
  · rw [h, Subgroup.card_top, hL60] at hc
    omega

end CFSG.Quasithin.C58NS.MPB
