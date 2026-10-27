module

public import CFSG.Quasithin.MS93.M15Quot
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.F918D4
public import CFSG.Quasithin.EmptyFaithful.F918C10
public import CFSG.Quasithin.Background.FFC8A

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

section Comm

omit [Finite V] in
theorem commSub_zpowers_mono {y z : MulAut V} (hz : z ∈ Subgroup.zpowers y) :
    commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ (Subgroup.zpowers y) :=
  commSub_mono le_rfl ((Subgroup.zpowers_le).2 hz)

omit [Finite V] in
theorem fixV_zpowers_anti {y z : MulAut V} (hz : z ∈ Subgroup.zpowers y) :
    fixV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers z) :=
  fun _ hv g hg => hv g ((Subgroup.zpowers_le).2 hz hg)

omit [Finite V] in
theorem fixV_le_zpowers {K : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ K) :
    fixV K ≤ fixV (Subgroup.zpowers y) :=
  fun _ hv g hg => hv g ((Subgroup.zpowers_le).2 hy hg)

omit [Finite V] in
theorem mem_fixV_zpowers {y : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers y) ↔ y v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

@[expose] def commHom (y : MulAut V) : V →* V where
  toFun v := y v * v⁻¹
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_inv]; ac_rfl

omit [Finite V] in
theorem commHom_apply (y : MulAut V) (v : V) : commHom y v = y v * v⁻¹ := rfl

omit [Finite V] in
theorem ker_commHom (y : MulAut V) : (commHom y).ker = fixV (Subgroup.zpowers y) := by
  ext v
  rw [MonoidHom.mem_ker, commHom_apply, mul_inv_eq_one, mem_fixV_zpowers]

omit [Finite V] in
theorem range_commHom_eq (y : MulAut V) :
    (commHom y).range = commSub ⊤ (Subgroup.zpowers y) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, Subgroup.mem_top v, rfl⟩
  · set S : Subgroup (MulAut V) :=
      { carrier := {g | ∀ w : V, g w * w⁻¹ ∈ (commHom y).range}
        one_mem' := fun w => by rw [MulAut.one_apply, mul_inv_cancel]; exact Subgroup.one_mem _
        mul_mem' := fun {a b} ha hb w => by
          have e : (a * b) w * w⁻¹ = (a (b w) * (b w)⁻¹) * (b w * w⁻¹) := by
            rw [MulAut.mul_apply, mul_assoc, inv_mul_cancel_left]
          rw [e]
          exact Subgroup.mul_mem _ (ha _) (hb w)
        inv_mem' := fun {a} ha w => by
          have e : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
            rw [MulAut.apply_inv_self, mul_inv, inv_inv]
            exact mul_comm _ _
          rw [e]
          exact Subgroup.inv_mem _ (ha _) } with hS
    have hyS : y ∈ S := fun w => ⟨w, rfl⟩
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, -, rfl⟩
    exact (Subgroup.zpowers_le.2 hyS) hg w

omit [Finite V] in
theorem exists_orderOf_two_pow {S : Subgroup (MulAut V)} (hS : IsPGroup 2 S) {t : MulAut V}
    (ht : t ∈ S) : ∃ k, orderOf t = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨t, ht⟩
  exact ⟨k, (Subgroup.orderOf_coe ⟨t, ht⟩).trans hk⟩

omit [Finite V] in
theorem exists_pow_invol {S : Subgroup (MulAut V)} (hS : IsPGroup 2 S) {t : MulAut V}
    (ht : t ∈ S) (ht1 : t ≠ 1) :
    ∃ m, t ^ m ≠ 1 ∧ (t ^ m) ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_two_pow hS ht
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have hd : 2 ^ (k - 1) ∣ orderOf t := hk ▸ Nat.pow_dvd_pow 2 (Nat.sub_le k 1)
  have ho : orderOf (t ^ 2 ^ (k - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hd, hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
    simp [pow_succ]
  refine ⟨2 ^ (k - 1), fun h1 => ?_, ?_⟩
  · rw [h1, orderOf_one] at ho
    omega
  · have := pow_orderOf_eq_one (t ^ 2 ^ (k - 1))
    rwa [ho] at this

omit [Finite V] in
theorem exists_pow_order_four {S : Subgroup (MulAut V)} (hS : IsPGroup 2 S) {t : MulAut V}
    (ht : t ∈ S) (ht2 : t ^ 2 ≠ 1) : ∃ m, orderOf (t ^ m) = 4 := by
  obtain ⟨k, hk⟩ := exists_orderOf_two_pow hS ht
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply ht2
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    interval_cases k <;> norm_num
  have hd : 2 ^ (k - 2) ∣ orderOf t := hk ▸ Nat.pow_dvd_pow 2 (Nat.sub_le k 2)
  refine ⟨2 ^ (k - 2), ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) hd, hk]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  rw [show 2 + j - 2 = j by omega, pow_add]
  simp

end Comm

section L3

variable {X K : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K)
  (hnat : BinaryNaturalSL K ⊤ (fixV K) 3 1)
include hV h hnat

omit [Finite V] hV h in
theorem hnat' : BinaryNaturalSL K ⊤ (⊤ ⊓ fixV K) 3 1 := by
  rw [top_inf_eq]
  exact hnat

theorem card_fixV_eq_two : Nat.card (fixV K) = 2 := by
  have hle := card_fixV_le_two_of_natural3 hV K ⊤ (fun _ _ _ _ => Subgroup.mem_top _)
    ((xmodCommOf_top_eq K).trans h.comm) (hnat' hnat)
  rw [top_inf_eq] at hle
  have h1 : 1 < Nat.card (fixV K) := (Subgroup.one_lt_card_iff_ne_bot _).2 h.fix_ne
  omega

theorem card_eq_sixteen : Nat.card V = 16 := by
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := hnat
  have h1 := card_eq_of_realizesVia hπ
  rw [Subgroup.card_top, card_fixV_eq_two hV h ⟨F, iF, fF, hF, π, hπ⟩,
    card_natQuot_three (hF.trans (pow_one 2))] at h1
  omega

theorem invol_facts {t : MulAut V} (htK : t ∈ K) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) :
    Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) = 4 ∧
      commSub ⊤ (Subgroup.zpowers t) = fixV (Subgroup.zpowers t) := by
  have hZ : Nat.card ↥(⊤ ⊓ fixV K) = 2 := by
    rw [top_inf_eq]
    exact card_fixV_eq_two hV h hnat
  obtain ⟨h4, heq⟩ := cover_commSub_involution hV K ⊤ (fun _ _ _ _ => Subgroup.mem_top _)
    ((xmodCommOf_top_eq K).trans h.comm) (hnat' hnat) hZ t htK ht1 ht2
  rw [top_inf_eq] at heq
  exact ⟨h4, heq⟩

theorem fixV_order_four {y : MulAut V} (hyK : y ∈ K)
    (hy4 : orderOf y = 4) : fixV (Subgroup.zpowers y) = fixV K := by
  refine le_antisymm ?_ (fixV_le_zpowers hyK)
  by_contra hne
  set t := y ^ 2 with htdef
  have htK : t ∈ K := K.pow_mem hyK 2
  have ht2 : t ^ 2 = 1 := by
    rw [htdef, ← pow_mul, show 2 * 2 = 4 by norm_num, ← hy4, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one (by norm_num) h1
    omega
  obtain ⟨h4, heq⟩ := invol_facts hV h hnat htK ht1 ht2
  have hinv : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])
  have hff : (commHom y).comp (commHom y) = commHom t := by
    ext v
    simp only [MonoidHom.comp_apply, commHom_apply, hinv, map_mul]
    rw [htdef, pow_two, MulAut.mul_apply, mul_assoc, ← mul_assoc (y v) (y v) v, ← pow_two, hV,
      one_mul]
  have hker : (commHom y).ker = fixV (Subgroup.zpowers y) := ker_commHom y
  have hrt : (commHom t).range = fixV (Subgroup.zpowers t) := by
    rw [range_commHom_eq t, heq]
  have hC2 := card_fixV_eq_two hV h hnat
  have hC : fixV K ≤ (commHom y).ker := hker ▸ fixV_le_zpowers hyK
  have hkt : (commHom y).ker ≤ fixV (Subgroup.zpowers t) :=
    hker ▸ fixV_zpowers_anti (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2)
  have hc4 : Nat.card ↥(fixV (Subgroup.zpowers t)) = 4 := by rw [← heq]; exact h4
  have hdvd : Nat.card (commHom y).ker ∣ 4 := hc4 ▸ Subgroup.card_dvd_of_le hkt
  have hgt : 2 < Nat.card (commHom y).ker := by
    by_contra hle
    apply hne
    rw [← hker]
    have := Subgroup.eq_of_le_of_card_ge hC (by omega)
    rw [this]
  have hk4 : Nat.card (commHom y).ker = 4 := by
    have : Nat.card (commHom y).ker ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hk : Nat.card (commHom y).ker <;> simp_all
  have hkeq : (commHom y).ker = fixV (Subgroup.zpowers t) :=
    Subgroup.eq_of_le_of_card_ge hkt (by rw [hk4, hc4])
  have hr4 : Nat.card (commHom y).range = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range (commHom y)
    rw [hk4, card_eq_sixteen hV h hnat] at h1
    omega
  have hmap : (commHom y).range.map (commHom y) = (commHom t).range := by rw [MonoidHom.map_range, hff]
  have hkr : (commHom y).ker ≤ (commHom y).range := by
    rw [hkeq, ← hrt, ← hmap]
    exact Subgroup.map_le_range _ _
  have h2 := B1More.card_map_mul_card_inf_ker (commHom y).range (commHom y)
  rw [inf_eq_right.2 hkr, hk4, hr4, hmap, hrt, hc4] at h2
  omega

theorem fixV_two_invol {t₁ t₂ : MulAut V} (h1K : t₁ ∈ K)
    (h2K : t₂ ∈ K) (h11 : t₁ ≠ 1) (h21 : t₂ ≠ 1) (h12 : t₁ ^ 2 = 1) (h22 : t₂ ^ 2 = 1)
    (hne : commSub ⊤ (Subgroup.zpowers t₁) ≠ commSub ⊤ (Subgroup.zpowers t₂)) :
    fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) ≤ fixV K := by
  obtain ⟨c1, e1⟩ := invol_facts hV h hnat h1K h11 h12
  obtain ⟨c2, e2⟩ := invol_facts hV h hnat h2K h21 h22
  rw [e1] at c1 hne
  rw [e2] at c2 hne
  have hC2 := card_fixV_eq_two hV h hnat
  have hCle : fixV K ≤ fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) :=
    le_inf (fixV_le_zpowers h1K) (fixV_le_zpowers h2K)
  have hdvd : Nat.card ↥(fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)) ∣ 4 :=
    c1 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne4 : Nat.card ↥(fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)) ≠ 4 := by
    intro h4
    apply hne
    have ha := Subgroup.eq_of_le_of_card_ge (inf_le_left :
      fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) ≤ _) (by rw [c1, h4])
    have hb := Subgroup.eq_of_le_of_card_ge (inf_le_right :
      fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) ≤ _) (by rw [c2, h4])
    rw [← ha, hb]
  have hle2 : Nat.card ↥(fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)) ≤ 2 := by
    have : Nat.card ↥(fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hk : Nat.card ↥(fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)) <;>
      simp_all
  exact (Subgroup.eq_of_le_of_card_ge hCle (by omega)).symm.le

theorem caseL3 : MS15CaseL3 X K := by
  have hC2 := card_fixV_eq_two hV h hnat
  have hZ : Nat.card ↥(⊤ ⊓ fixV K) = 2 := by rw [top_inf_eq]; exact hC2
  have hXK : X = K := by
    refine le_antisymm (fun x hx => ?_) h.le
    obtain ⟨l, hl, hxl⟩ := cover_normalizer_stab hV K ⊤ (fun _ _ _ _ => Subgroup.mem_top _)
      ((xmodCommOf_top_eq K).trans h.comm) (hnat' hnat) hZ x
      (fun y => Subgroup.mem_normalizer_iff.1 (h.le_normalizer hx) y) (fun _ => Iff.rfl)
    have : x = l := MulEquiv.ext fun v => hxl v (Subgroup.mem_top v)
    rw [this]
    exact hl
  have hiso : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (↥K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := hnat
    exact ⟨F, iF, fF, hF.trans (pow_one 2),
      ⟨(FFC.equivOfRealizes (FFModel.nat_faithful _) hπ).symm⟩⟩
  refine ⟨hXK, hnat, hiso, by rw [hXK]; exact hC2, fun S hS => ⟨fun t ht ht1 => ?_, ?_⟩⟩
  ·
    have htK : ∀ {g}, g ∈ S → g ∈ K := fun hg => hXK ▸ hS.1 hg
    obtain ⟨m, hm1, hm2⟩ := exists_pow_invol hS.2.1 ht ht1
    obtain ⟨-, heq⟩ := invol_facts hV h hnat (htK (S.pow_mem ht m)) hm1 hm2
    rw [hXK, commV_eq_commSub]
    calc fixV K ≤ fixV (Subgroup.zpowers (t ^ m)) := fixV_le_zpowers (htK (S.pow_mem ht m))
      _ = commSub ⊤ (Subgroup.zpowers (t ^ m)) := heq.symm
      _ ≤ commSub ⊤ (Subgroup.zpowers t) :=
        commSub_zpowers_mono (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) m)
  ·
    intro Y hYS hcard
    have hYK : ∀ {g}, g ∈ Y → g ∈ K := fun hg => hXK ▸ hS.1 (hYS hg)
    have hY2 : IsPGroup 2 Y := hS.2.1.to_le hYS
    rw [hXK]
    refine le_antisymm ?_ (fun v hv g hg => hv g (hYK hg))
    by_cases h4 : ∃ y ∈ Y, y ^ 2 ≠ 1
    · obtain ⟨y, hy, hy2⟩ := h4
      obtain ⟨m, hm⟩ := exists_pow_order_four hY2 hy hy2
      have hym : y ^ m ∈ Y := Y.pow_mem hy m
      rw [← fixV_order_four hV h hnat (hYK hym) hm]
      exact fun v hv g hg => hv g ((Subgroup.zpowers_le).2 hym hg)
    · push Not at h4
      by_cases h2 : ∃ t₁ ∈ Y, ∃ t₂ ∈ Y, t₁ ≠ 1 ∧ t₂ ≠ 1 ∧
          commSub ⊤ (Subgroup.zpowers t₁) ≠ commSub ⊤ (Subgroup.zpowers t₂)
      · obtain ⟨t₁, ht₁, t₂, ht₂, h11, h21, hne⟩ := h2
        refine le_trans ?_ (fixV_two_invol hV h hnat (hYK ht₁) (hYK ht₂) h11 h21 (h4 t₁ ht₁)
          (h4 t₂ ht₂) hne)
        exact le_inf (fun v hv g hg => hv g ((Subgroup.zpowers_le).2 ht₁ hg))
          (fun v hv g hg => hv g ((Subgroup.zpowers_le).2 ht₂ hg))
      · exfalso
        push Not at h2
        by_cases hY1 : ∃ t₀ ∈ Y, t₀ ≠ 1
        · obtain ⟨t₀, ht₀, ht₀1⟩ := hY1
          obtain ⟨c4, heq⟩ := invol_facts hV h hnat (hYK ht₀) ht₀1 (h4 t₀ ht₀)
          have hle : commV Y ⊔ fixV K ≤ commSub ⊤ (Subgroup.zpowers t₀) := by
            refine sup_le ?_ (heq ▸ fixV_le_zpowers (hYK ht₀))
            rw [commV, Subgroup.closure_le]
            rintro _ ⟨y, hy, v, rfl⟩
            by_cases hy1 : y = 1
            · rw [hy1, MulAut.one_apply, mul_inv_cancel]
              exact Subgroup.one_mem _
            · rw [← h2 y hy t₀ ht₀ hy1 ht₀1]
              exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, Subgroup.mem_top v,
                rfl⟩
          have := Subgroup.card_le_of_le hle
          omega
        · push Not at hY1
          have hbot : commV Y = ⊥ := by
            rw [commV, Subgroup.closure_eq_bot_iff]
            rintro _ ⟨y, hy, v, rfl⟩
            rw [hY1 y hy, MulAut.one_apply, mul_inv_cancel]
            rfl
          rw [hbot, bot_sup_eq] at hcard
          omega

end L3

end CFSG.Quasithin.MS93
