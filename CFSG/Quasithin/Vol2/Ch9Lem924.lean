module

public import CFSG.Quasithin.Vol2.Ch9Lem923
public import CFSG.Quasithin.Background.E6TwentySix

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem isUniqueM_normalizer_Q : IsUniqueM (Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G)) (fsuM T L) := by
  have hQ1 : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≠ ⊥ := fun h0 =>
    S.fsuV_ne_bot (le_bot_iff.mp (h0 ▸ S.fsuV_le_Q))
  have hLT : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
    S.L0_sup_T ▸ S.L0T_le_normalizer_Q
  refine ⟨⟨S.uniq.1.1, S.normalizer_le_of_le S.isPGroup_Q hQ1 hLT⟩, fun M' hM' => ?_⟩
  exact S.uniq.2 M' ⟨hM'.1, hLT.trans hM'.2⟩

theorem isSylowIn_of_le {H : Subgroup G} (hTH : T ≤ H) : IsSylowIn 2 T H :=
  ⟨hTH, S.hyp.fsu.sylow.1,
    fun h => S.hyp.fsu.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem nParam_ne_zero {H : Subgroup G} (hTH : T ≤ H) : E1.nParam H ≠ 0 := by
  intro h0
  unfold E1.nParam at h0
  split_ifs at h0 with hodd
  · have hV2 : 2 ∣ Nat.card ↥(fsuV T I) := by
      have := S.comm
      have hc := Vol2.Ch10.SecA.card_fsuV_of_omegaPlus (h := S.row)
      rw [hc]
      exact dvd_pow_self 2 (by have := S.two_le; omega)
    have hdvd : Nat.card ↥(fsuV T I) ∣ Nat.card ↥H :=
      Subgroup.card_dvd_of_le (S.fsuV_le_T.trans hTH)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hV2.trans hdvd))
  · have h1 : (1 : ℕ∞) ≤ ⨅ i ∈ {i : ℕ | 0 < i ∧ E1.InE i H}, (i : ℕ∞) :=
      le_iInf₂ fun i hi => by exact_mod_cast hi.1
    rw [h0] at h1
    exact absurd h1 (by norm_num)

theorem le_nParam_add_one (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : (n : ℕ∞) ≤ E1.nParam H + 1 := by
  by_contra hlt
  push Not at hlt
  have hne := S.nParam_ne_zero hH.1.1
  have hfin : E1.nParam H ≠ ⊤ := fun h => by rw [h] at hlt; simp at hlt
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hk' : E1.nParam H = (k : ℕ∞) := hk.symm
  rw [hk'] at hlt hne
  have hkn : k + 1 < n := by exact_mod_cast hlt
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (by rw [h0]; rfl) hne
    · exact h0
  have hr := S.le_rParam h37 h38 h39 h3228 hE610 h63 hH11 h1
  obtain ⟨hHM, -⟩ := E6.e6_26 (j := n - 2) S.hyp.fsu.sylow.1 S.fsuV_ne_bot S.hV S.fsuV_le_T
    S.hNM S.isUniqueM_normalizer_Q (by omega) (by rw [hk']; exact_mod_cast (by omega))
    (S.isSylowIn_of_le hH.1.1) inf_le_left le_rfl
    (lt_of_lt_of_le (by exact_mod_cast (by omega : n - 2 < n)) hr)
    (S.thompsonJk_sub_two_le hH11)
  exact hH.2.1 hHM

end Setup

end CFSG.Quasithin.H13.Ch9
