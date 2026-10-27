module

public import CFSG.Quasithin.Background.D2Dihedral

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

structure CycCtx (X : Subgroup (MulAut V)) : Prop where
  hyp : D217Hyp X 2
  cyc : ∀ B ∈ QhatStar X, Nat.card B = 2
  no5 : ∀ B ∈ QhatStar X, ⁅pCoreOf 5 X, B⁆ = ⊥

theorem conj_mem_TInv {X : Subgroup (MulAut V)} {t g : MulAut V} (ht : t ∈ TInv X) (hg : g ∈ X) :
    g * t * g⁻¹ ∈ TInv X := by
  obtain ⟨htX, ht1, ht2, htr⟩ := ht
  refine ⟨X.mul_mem (X.mul_mem hg htX) (X.inv_mem hg), ?_, ?_, ?_⟩
  · intro h
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h]; group
  · rw [conj_pow, ht2]; group
  · have : Subgroup.zpowers (g * t * g⁻¹) = conjBy g (Subgroup.zpowers t) := by
      rw [conjBy, MonoidHom.map_zpowers]
      rfl
    rw [this, rk_commV_conjBy]
    exact htr

theorem rAV_zpowers {t : MulAut V} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    rAV (Subgroup.zpowers t) = (rk (commV (Subgroup.zpowers t)) : ℚ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hrk : rk (Subgroup.zpowers t) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hord]
    simp
  unfold rAV
  rw [hrk, rkIdx_fixV_zpowers]
  simp

namespace CycCtx

variable {X : Subgroup (MulAut V)}

theorem rk_eq_two (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V} (ht : t ∈ TInv X) :
    rk (commV (Subgroup.zpowers t)) = 2 := by
  have hq := c.hyp.qhat
  have hA : IsA2 X (Subgroup.zpowers t) := (D2_11_4 hV ht).1.1
  have hcub : commSeries (Subgroup.zpowers t) 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num) ((D2_11_4 hV ht).2)
  have h2 : (2 : ℚ) ≤ rAV (Subgroup.zpowers t) := by
    have := le_kq_iff.mp hq.ge (Subgroup.zpowers t) hA hcub
    exact_mod_cast this
  rw [rAV_zpowers ht.2.1 ht.2.2.1] at h2
  have h3 : 2 ≤ rk (commV (Subgroup.zpowers t)) := by exact_mod_cast h2
  exact le_antisymm ht.2.2.2 h3

theorem zpowers_mem_qhatStar (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V}
    (ht : t ∈ TInv X) : Subgroup.zpowers t ∈ QhatStar X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsA2 X (Subgroup.zpowers t) := (D2_11_4 hV ht).1.1
  have hcub : commSeries (Subgroup.zpowers t) 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num) ((D2_11_4 hV ht).2)
  have hr : rAV (Subgroup.zpowers t) ≤ 2 := by
    rw [rAV_zpowers ht.2.1 ht.2.2.1, c.rk_eq_two hV ht]
    norm_num
  refine ⟨2, c.hyp.qhat, by norm_num, ⟨⟨hA, hr⟩, hcub⟩, fun B hB hBt => ?_⟩
  have hBne : B ≠ ⊥ := hB.1.1.ne_bot
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  have hbt : b ∈ Subgroup.zpowers t := hBt hbB
  have hord : orderOf t = 2 := orderOf_eq_prime ht.2.2.1 ht.2.1
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  have hz : Subgroup.zpowers b = Subgroup.zpowers t :=
    zpowers_eq_of_prime_card hcard hbt hb1
  apply le_antisymm hBt
  rw [← hz]
  exact Subgroup.zpowers_le.mpr hbB

theorem exists_tinv (c : CycCtx X) {B : Subgroup (MulAut V)}
    (hB : B ∈ QhatStar X) : ∃ t ∈ TInv X, Subgroup.zpowers t = B := by
  obtain ⟨t, ht, htz, -⟩ := exists_tinv_of_card_two c.hyp.qhat hB (c.cyc B hB)
  exact ⟨t, ht, htz⟩

theorem closure_eq (c : CycCtx X) : Subgroup.closure (TInv X) = X := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro t ht
    exact ht.1
  · calc X = Jhat X := c.hyp.jhat
      _ ≤ Subgroup.closure (TInv X) := by
        refine iSup₂_le fun B hB => ?_
        obtain ⟨t, ht, rfl⟩ := c.exists_tinv hB
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ht)

theorem induction (c : CycCtx X) {P : MulAut V → Prop} (h1 : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hinv : ∀ a, P a → P a⁻¹)
    (hT : ∀ t ∈ TInv X, P t) : ∀ g ∈ X, P g := by
  intro g hg
  rw [← c.closure_eq] at hg
  exact Subgroup.closure_induction (p := fun g _ => P g) (fun t ht => hT t ht)
    h1 (fun a b _ _ ha hb => hmul a b ha hb) (fun a _ ha => hinv a ha) hg

theorem fixV_T (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {W : Subgroup V}
    (hW : ∀ t ∈ TInv X, ∀ w ∈ W, t w = w) : W = ⊥ := by
  refine (D2_20 hV c.hyp).2 W fun B hB w hw => ?_
  obtain ⟨t, ht, rfl⟩ := c.exists_tinv hB
  exact mem_fixV_zpowers_iff.mpr (hW t ht w hw)

theorem comm_pCoreOf_ge_five (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V}
    (ht : t ∈ TInv X) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∀ y ∈ pCoreOf p X, t * y = y * t := by
  have hB := c.zpowers_mem_qhatStar hV ht
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hne⟩ := hcon
  have hne' : ⁅pCoreOf p X, Subgroup.zpowers t⁆ ≠ ⊥ :=
    commutator_ne_bot_iff.mpr ⟨y, hy, t, Subgroup.mem_zpowers t, hne⟩
  have h35 := (D2_13 hV c.hyp.qhat hB hp2 rfl hne').1
  rcases h35 with h | h
  · exact hp3 h
  · subst h
    exact hne' (c.no5 _ hB)

theorem exists_element_of_card_prime {p : ℕ} [Fact p.Prime] {P : Subgroup (MulAut V)}
    (hP : IsPGroup p P) (hne : P ≠ ⊥) : ∃ z ∈ P, orderOf z = p := by
  have hdvd : p ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq P h) hne
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩

theorem pCoreOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : pCoreOf p X = ⊥ := by
  by_contra hne
  obtain ⟨z, hzP, hzord⟩ := exists_element_of_card_prime (pCoreOf_isPGroup p X) hne
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hzord
    exact (Fact.out : p.Prime).one_lt.ne hzord
  have hcomm := fun t ht => c.comm_pCoreOf_ge_five hV (t := t) ht hp2 hp3 z hzP
  have hp5 : 5 ≤ p := by
    have h1 := (Fact.out : p.Prime).two_le
    have h4 : p ≠ 4 := by
      intro h; have := (Fact.out : p.Prime); rw [h] at this; exact absurd this (by norm_num)
    omega
  set Z := Subgroup.zpowers z with hZ
  have hZcard : Nat.card Z = p := by rw [Nat.card_zpowers, hzord]
  have hZodd : Odd (Nat.card Z) := by
    rw [hZcard]; exact (Fact.out : p.Prime).odd_of_ne_two hp2
  set W := commV Z with hW
  have hWinv : ∀ g ∈ Z, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact commV_smul_mem (fun q hq => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      have : z ^ k * z ^ j * (z ^ k)⁻¹ = z ^ j := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j) hw
  obtain ⟨-, hinf⟩ := coprime_decomp hZodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at hinf
  have hWne : W ≠ ⊥ := by
    intro h
    have h1 := one_le_rk_commV_zpowers hV hz1
    rw [← hZ, ← hW, h, rk_bot] at h1
    omega
  apply hWne
  refine c.fixV_T hV fun t ht w hw => ?_
  set F := commSub W (Subgroup.zpowers t) with hF
  have htW : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have htz : ∀ q ∈ Z, (t ^ k) * q * (t ^ k)⁻¹ ∈ Z := by
      intro q hq
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      have : (t ^ k) * z ^ j * (t ^ k)⁻¹ = z ^ j := by
        have hc : Commute (t ^ k) (z ^ j) := (show Commute t z from hcomm t ht).zpow_zpow k j
        rw [hc.eq]; group
      rw [this]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j
    exact commV_smul_mem htz hw
  have hFle : F ≤ W := commSub_le_of_invariant htW
  have hFinv : ∀ g ∈ Z, ∀ f ∈ F, g f ∈ F := by
    intro g hg f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hzt : z ^ k * t = t * z ^ k := ((show Commute z t from (hcomm t ht).symm).zpow_left k).eq
    refine Subgroup.closure_induction (p := fun f _ => (z ^ k) f ∈ F) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨x, hx, w', hw', rfl⟩
      rw [map_mul, map_inv]
      have hxc : (z ^ k) * x = x * (z ^ k) := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have : Commute (z ^ k) (t ^ j) :=
          ((show Commute z t from (hcomm t ht).symm).zpow_zpow k j)
        exact this.eq
      have : (z ^ k) (x w') = x ((z ^ k) w') := by
        calc (z ^ k) (x w') = ((z ^ k) * x) w' := rfl
          _ = (x * (z ^ k)) w' := by rw [hxc]
          _ = x ((z ^ k) w') := rfl
      rw [this]
      exact Subgroup.subset_closure ⟨x, hx, (z ^ k) w', hWinv _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k) w' hw', rfl⟩
    · rw [map_one]; exact F.one_mem
    · intro a b _ _ ha hb; rw [map_mul]; exact F.mul_mem ha hb
    · intro a _ ha; rw [map_inv]; exact F.inv_mem ha
  have hFfix : F ⊓ fixV Z = ⊥ := by
    refine le_bot_iff.mp ?_
    calc F ⊓ fixV Z ≤ W ⊓ fixV Z := inf_le_inf_right _ hFle
      _ = ⊥ := hinf
      _ ≤ ⊥ := le_rfl
  have hFbot : F = ⊥ := by
    by_contra hFne
    have hdvd := prime_dvd_card_sub_one hZcard hFinv hFfix
    have hrkF : rk F ≤ 2 := by
      have := rk_mono (commSub_mono (le_top : W ≤ ⊤) (le_refl (Subgroup.zpowers t)))
      rw [← commV_eq_commSub, c.rk_eq_two hV ht] at this
      exact this
    have hrk0 : rk F ≠ 0 := fun h => hFne ((rk_eq_zero_iff hV).mp h)
    rw [card_eq_two_pow hV F] at hdvd
    have key : ∀ e ≤ 2, e ≠ 0 → ¬ p ∣ 2 ^ e - 1 := by
      intro e he he0 hpd
      have h1 := Nat.le_of_dvd (by
        have : 2 ^ e ≥ 2 := by
          calc 2 ^ e ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        omega) hpd
      have : 2 ^ e ≤ 4 := by
        calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) he
          _ = 4 := by norm_num
      omega
    exact key _ hrkF hrk0 hdvd
  have hmem : t w * w⁻¹ ∈ F :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, hw, rfl⟩
  rw [hFbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem fittingOf_eq (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) :
    fittingOf X = pCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply le_antisymm
  · unfold fittingOf
    rw [CFSG.fitting_eq_sup_pCore ↥X, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    have hmap : (CFSG.Open.pCore p.1.1 ↥X).map X.subtype = pCoreOf p.1.1 X := rfl
    rw [hmap]
    have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
    have : Fact p.1.1.Prime := ⟨hp⟩
    by_cases h3 : p.1.1 = 3
    · rw [h3]
    · by_cases h2 : p.1.1 = 2
      · rw [h2, c.hyp.o2]; exact bot_le
      · rw [c.pCoreOf_eq_bot hV h2 h3]; exact bot_le
  · exact le_fittingOf_of_normal (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X)
      (fun x hx g hg => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hx) g).mp hg)

theorem faithful_three (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V} (ht : t ∈ TInv X) :
    ∃ y ∈ pCoreOf 3 X, t * y ≠ y * t := by
  have hB := c.zpowers_mem_qhatStar hV ht
  obtain ⟨⟨p, hp, hp2, hne⟩, -⟩ := D2_18 hV c.hyp hB (c.cyc _ hB)
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨y, hy, a, ha, hne'⟩ := commutator_ne_bot_iff.mp hne
    refine ⟨y, hy, fun h => hne' ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute t y from h).zpow_left k).eq
  · exfalso
    obtain ⟨y, hy, a, ha, hne'⟩ := commutator_ne_bot_iff.mp hne
    apply hne'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute t y from c.comm_pCoreOf_ge_five hV ht hp2 hp3 y hy).zpow_left k).eq

end CycCtx

end CFSG.Quasithin
