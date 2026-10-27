module

public import CFSG.RankThree.PartTwo.Sec10.Item10Std
public import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Lemmas

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

omit [Finite G] in
theorem exists_zpow_mul_of_mem_sup_zpowers {H : Subgroup G} {x : G}
    (hxH : ∀ h ∈ H, h * x = x * h) {y : G} (hy : y ∈ Subgroup.zpowers x ⊔ H) :
    ∃ k : ℤ, ∃ z ∈ H, y = x ^ k * z := by
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hxH)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨k, z, hz, rfl⟩

theorem Sec10Std.c_mem_thetaQuotCentralizer (h : Sec10Std G A c L a R) :
    c ∈ Sec4.thetaQuotCentralizer L := by
  have hcomm : ∀ l ∈ L, c * l * c⁻¹ = l := fun l hl => by
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hl)),
      mul_inv_cancel_right]
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hl))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
  rw [hcomm l hl, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem Sec10Std.commute_of_mem_thetaQuotCentralizer (h : Sec10Std G A c L a R) {r x : G}
    (hrR : r ∈ R) (hr : r ∈ Sec4.thetaQuotCentralizer L) (hx : x ∈ R ⊓ L) : x * r = r * x := by
  obtain ⟨-, hrl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hr
  have h1 := h.eq_one_of_mem_R_of_mem_theta
    (R.mul_mem (R.inv_mem hx.1) (R.mul_mem (R.mul_mem hrR hx.1) (R.inv_mem hrR))) (hrl x hx.2)
  have h2 : r * x * r⁻¹ = x := (inv_mul_eq_one.mp h1).symm
  calc x * r = r * x * r⁻¹ * r := by rw [h2]
    _ = r * x := by group

theorem Sec10Std.mem_zpowers_of_mem_thetaQuotCentralizer (h : Sec10Std G A c L a R) {r : G}
    (hrR : r ∈ R) (hr : r ∈ Sec4.thetaQuotCentralizer L) (hr3 : r ^ 3 = 1) :
    r ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc3 : c ^ 3 = 1 := h.pow_three h.mem_A
  have hcC := h.c_mem_thetaQuotCentralizer
  by_cases hrD : r ∈ sec10D c R L
  ·
    obtain ⟨k, x, hx, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
      (fun y hy => h.commute_c_of_mem_inf hy) hrD
    have hxC : x ∈ Sec4.thetaQuotCentralizer L := by
      have := (Sec4.thetaQuotCentralizer L).mul_mem
        ((Sec4.thetaQuotCentralizer L).zpow_mem ((Sec4.thetaQuotCentralizer L).inv_mem hcC) k) hr
      rwa [← mul_assoc, inv_zpow', ← zpow_add, neg_add_cancel, zpow_zero, one_mul] at this
    rw [h.eq_one_of_mem_inf_thetaQuotCentralizer hx.1 hx.2 hxC, mul_one]
    exact Subgroup.zpow_mem_zpowers c k
  · exfalso
    have hrc : r * c = c * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hrR)
    have hrRL : ∀ x ∈ R ⊓ L, x * r = r * x := fun x hx =>
      h.commute_of_mem_thetaQuotCentralizer hrR hr hx
    have hDr : sec10D c R L ≤ Subgroup.centralizer ({r} : Set G) := by
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hrc.symm
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hrRL x hx
    have hrD' : ∀ e ∈ sec10D c R L, e * r = r * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hDr he)
    set F := sec10D c R L ⊔ Subgroup.zpowers r with hF
    have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
      Sec15.isElemAbelian_sup_zpowers h.isElemAbelian_D hr3 hrD'
    have hFcard : Nat.card F = 243 := by
      have hN : Subgroup.zpowers r ≤ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hrD')
      have hr1 : r ≠ 1 := fun h1 => hrD (h1 ▸ Subgroup.one_mem _)
      rw [hF, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
        (disjoint_zpowers_of_pow_three hr3 hrD), h.card_D, Nat.card_zpowers,
        orderOf_eq_prime hr3 hr1]
    obtain ⟨⟨x, hxRL⟩, hx1⟩ : ∃ x : (R ⊓ L : Subgroup G), x ≠ 1 := by
      by_contra hall
      push Not at hall
      have : Nat.card (R ⊓ L : Subgroup G) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun u v => (hall u).trans (hall v).symm⟩, ⟨1⟩⟩
      rw [h.card_inf] at this
      norm_num at this
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hx3 : x ^ 3 = 1 := h.isElemAbelian_inf.2 x hxRL
    set E₀ := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hE₀
    set E := E₀ ⊔ Subgroup.zpowers r with hE
    have hxc : x * c = c * x := h.commute_c_of_mem_inf hxRL
    have hE₀e : CFSG.Assembly.IsElemAbelian 3 E₀ :=
      Sec15.isElemAbelian_sup_zpowers (isElemAbelian_zpowers_of_pow_three hx3) hc3 fun e he => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
        exact (Commute.zpow_left hxc k).eq
    have hE₀D : E₀ ≤ sec10D c R L :=
      sup_le (Subgroup.zpowers_le.mpr (h.inf_le_D hxRL)) (Subgroup.zpowers_le.mpr h.c_mem_D)
    have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
      Sec15.isElemAbelian_sup_zpowers hE₀e hr3 fun e he => hrD' e (hE₀D he)
    have hE₀card : Nat.card E₀ = 9 := by
      have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) :
          Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact (Commute.zpow_left hxc k).eq)
      have hcx : c ∉ Subgroup.zpowers x := fun hc =>
        h.c_not_mem_L (Subgroup.zpowers_le.mpr hxRL.2 hc)
      rw [hE₀, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
        (disjoint_zpowers_of_pow_three hc3 hcx), Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime hx3 hx1', h.orderOf_c]
    have hEcard : Nat.card E = 27 := by
      have hN : Subgroup.zpowers r ≤ Subgroup.normalizer ((E₀ : Subgroup G) : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun e he => hrD' e (hE₀D he))
      have hr1 : r ≠ 1 := fun h1 => hrD (h1 ▸ Subgroup.one_mem _)
      rw [hE, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
        (disjoint_zpowers_of_pow_three hr3 fun hrE => hrD (hE₀D hrE)), hE₀card,
        Nat.card_zpowers, orderOf_eq_prime hr3 hr1]
    obtain ⟨eL⟩ := h.exists_mulEquiv_psl2
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    set xb : L ⧸ aschbacherSolvableCore 3 L := π ⟨x, hxRL.2⟩ with hxb
    have hxb3 : xb ^ 3 = 1 := by
      rw [hxb, ← map_pow]
      have : (⟨x, hxRL.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hxb1 : xb ≠ 1 := by
      intro h1
      exact hx1' (h.eq_one_of_mem_R_of_mem_theta hxRL.1 (mem_theta_of_mk_eq_one h1))
    obtain ⟨Vb, hVb1, hVb2, hVbN⟩ := KFacts.exists_two_subgroup_of_card_eq_three eL
      (P := Subgroup.zpowers xb) (by rw [Nat.card_zpowers, orderOf_eq_prime hxb3 hxb1])
    set Y := thetaPreimage L Vb with hY
    have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Subgroup.zpowers_le]
        exact mem_normalizer_thetaPreimage_of_mem hxRL.2 (hVbN (Subgroup.mem_zpowers xb))
      · rw [Subgroup.zpowers_le]
        exact mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer hcC
      · rw [Subgroup.zpowers_le]
        exact mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer hr
    have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hEe.2 e e.2)⟩
    obtain ⟨T, -, hT1, hT2, hET⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2) hE3
      (not_three_dvd_card_thetaPreimage hVb2) (two_dvd_card_thetaPreimage hVb2 hVb1) hEY
    have hEmem : E ∈ partTwoE G := ⟨hEe, hEcard, T, hT1, hT2, hET⟩
    rw [h.partTwoE_eq h.card_eq] at hEmem
    have hEF : E ≤ F := sup_le (hE₀D.trans le_sup_left) le_sup_right
    have := hEmem.2.1 F hFe hEF
    rw [this, hEcard] at hFcard
    norm_num at hFcard

end Lemmas

theorem rank3II_10_1 :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
      (R : Subgroup G), Sec10Std G A c L a R →
        IsCyclic (R ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
  intro G _ _ A c L a R h
  apply Late.isCyclic_of_forall_elemAbelian_card_le_three h.isPGroup_R.to_inf_left
  intro F hF hFe
  have hle : F ≤ Subgroup.zpowers c := fun x hx =>
    h.mem_zpowers_of_mem_thetaQuotCentralizer (hF hx).1 (hF hx).2 (hFe.2 x hx)
  calc Nat.card F ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hle
    _ = 3 := by rw [Nat.card_zpowers, h.orderOf_c]

end CFSG.RankThree.PartTwo.Sec10
