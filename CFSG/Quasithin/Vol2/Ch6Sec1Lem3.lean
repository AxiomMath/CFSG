module

public import CFSG.Quasithin.Background.E6TwentySix
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem le_of_isUniqueM_of_le_twoLocal {X M Y : Subgroup G} (hU : IsUniqueM X M) (hXY : X ≤ Y)
    (hY : IsTwoLocal Y) : Y ≤ M := by
  obtain ⟨M', hM', hYM'⟩ := exists_maxTwoLocal_ge hY
  rw [← hU.2 M' ⟨hM', hXY.trans hYM'⟩]
  exact hYM'

theorem one_le_rParam {V : Subgroup G} (hV : IsPGroup 2 V) : 1 ≤ rParam V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hdvd : U.relIndex V ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    have hVU : V ≤ U := Subgroup.relIndex_eq_one.mp (by rw [hj]; rfl)
    rw [le_antisymm hUV hVU] at hC
    exact hC (Subgroup.centralizer_le_normalizer _)
  have hm : mQuot V U = j := by
    unfold mQuot
    rw [hj, padicValNat.prime_pow]
  rw [hm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0

variable {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_3 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
      (IsTISetIn V M → E6.HypE61 T M V) ∧ (rParam V = 1 ∨ ¬ thompsonJk 1 T ≤ ch6Q T V) := by
  intro G _ _ T M L V n h
  refine ⟨fun hTI => stmt6_1_3_one h432 h hTI, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hr, hJ⟩ := hcon
  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  rw [← hMeq] at hH
  have hU := h.isUniqueM h432
  have hV := h.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hNV : Subgroup.normalizer (V : Set G) ≤ M :=
    le_of_isUniqueM_of_le_twoLocal hU h.sup_le_normalizer ⟨V, h.ne_bot, hV2, rfl⟩
  have hQ := h.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hNQ : IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M :=
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩
  have hr1 : (1 : ℕ∞) < rParam V := lt_of_le_of_ne (one_le_rParam hV2) (Ne.symm hr)
  have hSH : IsSylowIn 2 T H :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      hH.1.1 le_top
  have := ch6InE626_proved G T V M H T 1 h.sylow h.ne_bot hV h.le_T h.T_le_normalizer hNV hNQ
    one_pos
    (by rw [h.nParam_eq_one H hH, Nat.cast_one]) hSH inf_le_left le_rfl (by exact_mod_cast hr1) hJ
  exact hH.2.1 this.1

end CFSG.Quasithin.H13
