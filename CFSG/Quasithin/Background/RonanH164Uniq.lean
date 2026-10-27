module

public import CFSG.Quasithin.Background.RonanH163Chain
public import CFSG.Quasithin.Background.RonanH163Transv
public import CFSG.Quasithin.Background.RonanH164Base

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem card_eq_pow_rk (H : Subgroup W10) : Nat.card ↥H = 2 ^ rk ↥H := by
  have hdvd : Nat.card ↥H ∣ 2 ^ 10 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_eq_fintype_card (α := W10), card_Wn] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hk', rk, hk', padicValNat.prime_pow]

theorem card_of_rk (H : Subgroup W10) (n : ℕ) (h : rk ↥H = n) : Nat.card ↥H = 2 ^ n := by
  rw [card_eq_pow_rk H, h]

theorem card_W10 : Nat.card W10 = 2 ^ 10 := by
  rw [Nat.card_eq_fintype_card, card_Wn]

theorem V5_le_U9 : V5 ≤ U9 := by
  rintro _ ⟨m, hm, rfl⟩
  have h : ∀ m ∈ combos c5, m ∈ combos b9 := by decide +kernel
  exact ⟨m, h m hm, rfl⟩

theorem V5_not_le_U4 : ¬ V5 ≤ U4 := by
  intro h
  have key : ∃ m ∈ combos c5, m ∉ combos b4 := by decide +kernel
  obtain ⟨m, hm, hm4⟩ := key
  have hlt : ∀ a ∈ c5, a < 2 ^ 10 := by decide +kernel
  have hm10 : m < 2 ^ 10 := combos_lt hlt m hm
  have := h ⟨m, hm, rfl⟩
  exact hm4 ((toW_mem_U4_iff hm10).1 this)

theorem unique_chain163
    (V₈ V₉ : Subgroup W10) (h : Chain163 R Qstd V₈ V₉) : V₈ = U8 ∧ V₉ = U9 := by
  have hT := fullTransp_std
  unfold Chain163 at h
  rw [KY_Q_L2, fixV_NQ2] at h hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have cU4 : Nat.card ↥U4 = 2 ^ 4 := card_of_rk U4 4 rk_U4
  have cU8 : Nat.card ↥U8 = 2 ^ 8 := card_of_rk U8 8 rk_U8
  have cU9 : Nat.card ↥U9 = 2 ^ 9 := card_of_rk U9 9 rk_U9
  have cV8 : Nat.card ↥V₈ = 2 ^ 8 := card_of_rk V₈ 8 h4
  have cV9 : Nat.card ↥V₉ = 2 ^ 9 := card_of_rk V₉ 9 h6
  have hV8 : V₈ = U8 := by
    have hI : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) (V₈ ⊓ U8) := by
      intro f hf u hu
      obtain ⟨y, hy, rfl⟩ := hf
      exact ⟨h3.2.2.1 _ ⟨y, hy, rfl⟩ u hu.1, inv_U8 y hy u hu.2⟩
    rcases U8_minimal _ (le_inf h3.1.le U4_le_U8) inf_le_right hI with he | he
    · exfalso
      have hidx := Subgroup.index_inf_le (H := V₈) (K := U8)
      rw [he] at hidx
      have c4 := Subgroup.card_mul_index U4
      have c8 := Subgroup.card_mul_index U8
      have c88 := Subgroup.card_mul_index V₈
      rw [card_W10, cU4] at c4
      rw [card_W10, cU8] at c8
      rw [card_W10, cV8] at c88
      have i4 : U4.index = 64 := by omega
      have i8 : U8.index = 4 := by omega
      have iV : V₈.index = 4 := by omega
      rw [i4, i8, iV] at hidx
      omega
    · have hle : U8 ≤ V₈ := inf_eq_right.1 he
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [cV8, cU8])).symm
  subst hV8
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hnle : ¬ V₉ ≤ U9 := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [cV9, cU9]))
  obtain ⟨v, hvV, hvU⟩ := Set.not_subset.1 hnle
  have hU8V : U8 ≤ V₉ := h5.1.le
  have hJ : V₉ ⊓ U9 = U8 := by
    have hlt : V₉ ⊓ U9 < V₉ := by
      refine lt_of_le_of_ne inf_le_left (fun he => hvU ?_)
      have : v ∈ V₉ ⊓ U9 := by rw [he]; exact hvV
      exact this.2
    have hdvd : Nat.card ↥(V₉ ⊓ U9) ∣ 2 ^ 9 := by
      rw [← cV9]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hltc : Nat.card ↥(V₉ ⊓ U9) < 2 ^ 9 := by
      rw [← cV9]
      exact Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk8 : k ≤ 8 := by
      by_contra hc
      have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : Nat.card ↥(V₉ ⊓ U9) ≤ 2 ^ 8 := by
      rw [hk']
      exact Nat.pow_le_pow_right (by norm_num) hk8
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hU8V U8_le_U9) (by rw [cU8]; exact this)).symm
  obtain ⟨c, hcU9, hcU8⟩ : ∃ c ∈ U9, c ∉ U8 := by
    by_contra hcon
    have hcon' : ∀ x ∈ U9, x ∈ U8 := fun x hx => by_contra fun hx8 => hcon ⟨x, hx, hx8⟩
    have hle : U9 ≤ U8 := fun x hx => hcon' x hx
    have := Subgroup.card_le_of_le hle
    rw [cU8, cU9] at this
    omega
  obtain ⟨g, hgX, hgT⟩ := hT.2.1 c hcU9
  have hgG : g ∈ rImg R (MY mog22plus Qstd) := by
    obtain ⟨k, hk, rfl⟩ := hgX
    exact ⟨k, Subgroup.mem_subgroupOf.2 (NQ2_le_MY_Q (Subgroup.mem_subgroupOf.1 hk)), rfl⟩
  have hgv : g v ∈ V₉ := h5.2.2.1 (fun x => g x) ⟨g, hgG, rfl⟩ v hvV
  have h1' : g v * v⁻¹ * c⁻¹ ∈ U4 := hgT.2 v hvU
  have hc9 : c⁻¹ ∈ V₉ := by
    have hU4V : U4 ≤ V₉ := h3.1.le.trans hU8V
    have e : c⁻¹ = (g v * v⁻¹)⁻¹ * (g v * v⁻¹ * c⁻¹) := (inv_mul_cancel_left _ _).symm
    rw [e]
    exact V₉.mul_mem (V₉.inv_mem (V₉.mul_mem hgv (V₉.inv_mem hvV))) (hU4V h1')
  have : c ∈ V₉ ⊓ U9 := ⟨(Subgroup.inv_mem_iff V₉).1 hc9, hcU9⟩
  rw [hJ] at this
  exact hcU8 this

theorem part4_std :
    (∃ V₈ V₉ : Subgroup W10, Chain163 R Qstd V₈ V₉ ∧
        V5 ≤ V₉ ∧ ¬ V5 ≤ fixV (rImg R (KY mog22plus Qstd))) ∧
      (∀ V₈ V₉ : Subgroup W10, Chain163 R Qstd V₈ V₉ →
        V5 ≤ V₉ ∧ ¬ V5 ≤ fixV (rImg R (KY mog22plus Qstd))) := by
  rw [KY_Q_L2, fixV_NQ2]
  refine ⟨⟨U8, U9, ?_, V5_le_U9, V5_not_le_U4⟩, ?_⟩
  · have := chain_std
    unfold Chain163 at this ⊢
    rwa [KY_Q_L2, fixV_NQ2] at this ⊢
  · intro V₈ V₉ h
    obtain ⟨-, rfl⟩ := unique_chain163 V₈ V₉ (by
      unfold Chain163 at h ⊢
      rwa [KY_Q_L2, fixV_NQ2] at h ⊢)
    exact ⟨V5_le_U9, V5_not_le_U4⟩

end CFSG.Quasithin.RonanH163
