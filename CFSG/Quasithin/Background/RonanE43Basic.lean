module

public import CFSG.Quasithin.Background.RonanE42Main

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G]

theorem le_normalizer_sup_pair {H A B : Subgroup G} (hA : H ≤ Subgroup.normalizer (A : Set G))
    (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ k ∈ H, ∀ w ∈ A ⊔ B, k * w * k⁻¹ ∈ A ⊔ B := by
    intro k hk w hw
    have hmap : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hA hk) a).mp ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hB hk) b).mp hb
    exact hmap ⟨w, hw, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key h hh w
  · intro hw
    have := key h⁻¹ (H.inv_mem hh) _ hw
    simpa [mul_assoc] using this

theorem le_normalizer_of_conj_mem {H Y : Subgroup G}
    (hYn : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) : H ≤ Subgroup.normalizer (Y : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hYn h hh y
  · intro hy
    have := hYn h⁻¹ (H.inv_mem hh) _ hy
    simpa [mul_assoc] using this

variable [Finite G]

theorem good_of_card_le {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (h2 : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H)) {Y : Subgroup G} (hYH : Y ≤ H)
    (hYn : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 H)) :
    H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  set R := pCoreOf 2 H with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTH
  have hRH : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hRn : H ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hYnorm : H ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_conj_mem hYn
  obtain ⟨y, hyYT, hyR⟩ : ∃ y ∈ Y ⊓ T, y ∉ R := by
    by_contra hcon
    push Not at hcon
    exact hYT fun y hy => hcon y hy
  have hyY : y ∈ Y := hyYT.1
  have hyT : y ∈ T := hyYT.2
  have hidx : (R.subgroupOf T).index = 2 := by
    have h1 := Subgroup.card_mul_index (R.subgroupOf T)
    have h2' : Nat.card (R.subgroupOf T) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
    rw [h2'] at h1
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hle : (R.subgroupOf T).index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : Nat.card R * 3 ≤ Nat.card R * (R.subgroupOf T).index :=
        Nat.mul_le_mul_left _ hlt
      omega
    have hne : (R.subgroupOf T).index ≠ 1 := by
      intro h1'
      rw [Subgroup.index_eq_one] at h1'
      have : (⟨y, hyT⟩ : T) ∈ R.subgroupOf T := by rw [h1']; exact Subgroup.mem_top _
      exact hyR (Subgroup.mem_subgroupOf.mp this)
    have hpos : (R.subgroupOf T).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hTYR : T ≤ Y ⊔ R := by
    intro t ht
    by_cases htR : t ∈ R
    · exact Subgroup.mem_sup_right htR
    · have hty : (⟨t, ht⟩ : T) * ⟨y, hyT⟩ ∈ R.subgroupOf T := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        have h1 : (⟨t, ht⟩ : T) ∉ R.subgroupOf T := fun h => htR (Subgroup.mem_subgroupOf.mp h)
        have h2 : (⟨y, hyT⟩ : T) ∉ R.subgroupOf T := fun h => hyR (Subgroup.mem_subgroupOf.mp h)
        simp [h1, h2]
      have hty' : t * y ∈ R := Subgroup.mem_subgroupOf.mp hty
      have e : t = (t * y) * y⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hty') (Subgroup.mem_sup_left (Y.inv_mem hyY))
  have hXH : Y ⊔ R ≤ H := sup_le hYH hRH
  have hXT : (Y ⊔ R) ⊔ T = Y ⊔ R := sup_eq_left.mpr hTYR
  have hnorm : H ≤ Subgroup.normalizer (((Y ⊔ R) ⊔ T : Subgroup G) : Set G) := by
    rw [hXT]
    exact le_normalizer_sup_pair hYnorm hRn
  have hFr := le_normalizer_sup_of_normal hT hTH hXH hnorm
  refine hFr.trans (sup_le_sup_left ?_ _)
  exact sup_le (le_sup_of_le_right le_rfl) (hRT.trans le_sup_left)


theorem pRank_le_one_of_card_le {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (h2 : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H)) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 1 := by
  set R := pCoreOf 2 H with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTH
  have hHQ : Nat.card H = Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) * Nat.card R := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
    have h2' : Nat.card (CFSG.pCore 2 ↥H) = Nat.card R :=
      (Subgroup.card_map_of_injective H.subtype_injective).symm
    rw [h2'] at h1
    exact h1
  have hTm : Nat.card T * T.relIndex H = Nat.card H := by
    have h1 := Subgroup.relIndex_mul_card (H := T) (K := H)
    rw [inf_eq_left.mpr hTH] at h1
    rw [← h1]; ring
  have hodd : ¬ 2 ∣ T.relIndex H := by
    intro hd
    apply hT.not_dvd_relIndex
    rw [← Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top]
    exact Dvd.dvd.mul_right hd _
  obtain ⟨c, hc⟩ : ∃ c, Nat.card T = Nat.card R * c := Subgroup.card_dvd_of_le hRT
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hc2 : c ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : Nat.card R * 3 ≤ Nat.card R * c := Nat.mul_le_mul_left _ hlt
    omega
  have hq : Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) = c * T.relIndex H := by
    have : Nat.card R * Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) = Nat.card R * (c * T.relIndex H) := by
      calc Nat.card R * Nat.card (↥H ⧸ CFSG.pCore 2 ↥H)
          = Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) * Nat.card R := by ring
        _ = Nat.card H := hHQ.symm
        _ = Nat.card T * T.relIndex H := hTm.symm
        _ = Nat.card R * (c * T.relIndex H) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hRpos this
  have h4 : ¬ 4 ∣ Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) := by
    rw [hq]
    intro hd
    have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases hc' with rfl | rfl | rfl
    · simp at hd
      exact absurd hd (by
        have := (Nat.card_pos : 0 < Nat.card (↥H ⧸ CFSG.pCore 2 ↥H))
        omega)
    · have : 4 ∣ T.relIndex H := by simpa using hd
      exact hodd (Dvd.dvd.trans (by norm_num) this)
    · have : 2 ∣ T.relIndex H := by omega
      exact hodd this
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  by_contra hk
  push Not at hk
  have h4E : 4 ∣ Nat.card E := by
    rw [hE]
    exact (pow_dvd_pow 2 (by omega : 2 ≤ k))
  exact h4 (h4E.trans (Subgroup.card_subgroup_dvd_card E))


theorem exists_moved_of_lt {V : Type} [CommGroup V] (ρ : G →* MulAut V) {T L : Subgroup G}
    (hLT : L ⊔ T = ⊤) (hlt : fixV ρ.range < fixV (T.map ρ)) :
    ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v := by
  by_contra hcon
  push Not at hcon
  refine absurd hlt (not_lt_of_ge fun v hv => ?_)
  rw [mem_fixV]
  rintro _ ⟨g, rfl⟩
  have hTv : ∀ t ∈ T, ρ t v = v := fun t ht => hv (ρ t) (Subgroup.mem_map_of_mem ρ ht)
  let K : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        show ρ (a * b) v = v
        rw [map_mul, MulAut.mul_apply]
        have hb' : ρ b v = v := hb
        have ha' : ρ a v = v := ha
        rw [hb', ha']
      one_mem' := by
        show ρ 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        show ρ a⁻¹ v = v
        have ha' : ρ a v = v := ha
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hLK : L ≤ K := fun l hl => hcon v hv l hl
  have hTK : T ≤ K := fun t ht => hTv t ht
  have hK : (⊤ : Subgroup G) ≤ K := by
    rw [← hLT]
    exact sup_le hLK hTK
  exact hK (Subgroup.mem_top g)

theorem aParam_le_card_of_family (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (Δ : Finset (Subgroup G)) (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G)
    (hLq : CFSG.IsQuasisimple ↥L) (hLT : L ⊔ T = ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hΔ : (⨆ H ∈ Δ, H) = ⊤) (hΔT : ∀ H ∈ Δ, T ≤ H)
    (h2 : ∀ H ∈ Δ, Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H)) :
    aParam ρ.range ≤ Δ.card := by
  classical
  have hfix := exists_moved_of_lt ρ hLT hlt
  have hmain := e4_2_of_good G V ρ hρ hO2 T L (↑Δ : Set (Subgroup G)) hT hLF hLq
    (by simpa using hΔ) (fun H hH => hΔT H hH)
    (fun H hH Y hYH hYn hYT => good_of_card_le hT (hΔT H hH) (h2 H hH) hYH hYn hYT) hfix
  refine hmain.trans ?_
  rw [finsum_mem_coe_finset]
  calc ∑ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))
      ≤ ∑ _H ∈ Δ, 1 := Finset.sum_le_sum fun H hH =>
        pRank_le_one_of_card_le hT (hΔT H hH) (h2 H hH)
    _ = Δ.card := by simp

end CFSG.Quasithin.RonanE43
