module

public import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
public import CFSG.RankThree.GF2n.Tim77.Sec41
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.Open
open scoped commutatorElement

structure Sec42Data (Y₀ : Type) [Group Y₀] (N₀ : Subgroup Y₀) (D₀ : Set Y₀) : Prop where
  sq : ∀ n ∈ N₀, n ^ 2 = 1
  disj : ∀ t ∈ D₀, t ∉ N₀
  invol : ∀ t ∈ D₀, t ^ 2 = 1
  ord : ∀ t ∈ D₀, ∀ t' ∈ D₀, orderOf (t * t') ∣ 2 ∨ Odd (orderOf (t * t'))
  conjD : ∀ g : Y₀, ∀ t ∈ D₀, g * t * g⁻¹ ∈ D₀
  gen : ∀ y : Y₀, y ∈ Subgroup.closure (D₀ ∪ (N₀ : Set Y₀))
  cent : ∀ t ∈ D₀, ∀ x ∈ D₀, ∀ y ∈ D₀, Commute x t → Commute y t → Commute x y
  single : ∃ d₀ ∈ D₀, ∀ d ∈ D₀, ∃ g : Y₀, d = g * d₀ * g⁻¹
  O2 : ∀ z ∈ CFSG.pCore 2 Y₀, ∀ g : Y₀, ⁅z, g⁆ ∈ N₀

theorem qp_commute_of_invol {H : Type} [Group H] {x y : H} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact hxy)
  rw [mul_inv_rev, hx', hy'] at h1
  exact h1

theorem qp_mem_of_sq_mem_of_odd {H : Type} [Group H] {K : Subgroup H} {x : H}
    (hx : x ^ 2 ∈ K) (hodd : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : x ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one x
  have e : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hpow, one_mul]
  rw [e]
  exact K.pow_mem hx _

section QS

variable {W : Type} [Group W] {N₀ : Subgroup W} [N₀.Normal] {D₀ : Set W}

theorem qp_isOddTransp (h : Sec42Data W N₀ D₀) :
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (QuotientGroup.mk' N₀ '' D₀) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨t, ht, rfl⟩
    have h1 : QuotientGroup.mk' N₀ t ≠ 1 := fun h1 =>
      h.disj t ht ((QuotientGroup.eq_one_iff t).mp h1)
    have h2 : QuotientGroup.mk' N₀ t ^ 2 = 1 := by
      rw [← map_pow, h.invol t ht, map_one]
    exact orderOf_eq_prime h2 h1
  · rintro x ⟨t, ht, rfl⟩ y ⟨t', ht', rfl⟩
    rw [← map_mul]
    have hd := orderOf_map_dvd (QuotientGroup.mk' N₀) (t * t')
    rcases h.ord t ht t' ht' with h2 | hodd
    · exact Or.inl (hd.trans h2)
    · exact Or.inr (Odd.of_dvd_nat hodd hd)

theorem qp_closure (h : Sec42Data W N₀ D₀) :
    Subgroup.closure (QuotientGroup.mk' N₀ '' D₀) = ⊤ := by
  rw [eq_top_iff]
  have key : ∀ z ∈ Subgroup.closure (D₀ ∪ (N₀ : Set W)),
      QuotientGroup.mk' N₀ z ∈ Subgroup.closure (QuotientGroup.mk' N₀ '' D₀) := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact Subgroup.subset_closure ⟨w, hw, rfl⟩
      · have e : QuotientGroup.mk' N₀ w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
        rw [e]
        exact one_mem _
    | one => exact one_mem _
    | mul a b _ _ iha ihb =>
      rw [map_mul]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [map_inv]
      exact inv_mem iha
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact key y (h.gen y)

theorem qp_sq_mem (h : Sec42Data W N₀ D₀) {t t' : W} (ht : t ∈ D₀) (ht' : t' ∈ D₀)
    (hc : Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ t')) :
    (t * t') ^ 2 ∈ N₀ := by
  have hsq : (QuotientGroup.mk' N₀ t * QuotientGroup.mk' N₀ t') ^ 2 = 1 := by
    rw [hc.mul_pow 2, ← map_pow, ← map_pow, h.invol t ht, h.invol t' ht', map_one, mul_one]
  have : QuotientGroup.mk' N₀ ((t * t') ^ 2) = 1 := by
    rw [map_pow, map_mul]
    exact hsq
  exact (QuotientGroup.eq_one_iff _).mp this

theorem qp_commute_lift (h : Sec42Data W N₀ D₀) {t t' : W} (ht : t ∈ D₀) (ht' : t' ∈ D₀)
    (hne : QuotientGroup.mk' N₀ t ≠ QuotientGroup.mk' N₀ t')
    (hc : Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ t')) : Commute t t' := by
  have ht2 : t * t = 1 := by rw [← pow_two]; exact h.invol t ht
  have ht2' : t' * t' = 1 := by rw [← pow_two]; exact h.invol t' ht'
  rcases h.ord t ht t' ht' with h2 | hodd
  · exact qp_commute_of_invol ht2 ht2' (orderOf_dvd_iff_pow_eq_one.mp h2)
  · exfalso
    have hmem : t * t' ∈ N₀ := qp_mem_of_sq_mem_of_odd (qp_sq_mem h ht ht' hc) hodd
    have h1 : QuotientGroup.mk' N₀ t * QuotientGroup.mk' N₀ t' = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hsqt' : QuotientGroup.mk' N₀ t' * QuotientGroup.mk' N₀ t' = 1 := by
      rw [← map_mul, ht2', map_one]
    apply hne
    exact mul_right_cancel (h1.trans hsqt'.symm)

theorem qp_trans (h : Sec42Data W N₀ D₀) :
    ∀ x ∈ QuotientGroup.mk' N₀ '' D₀, ∀ y ∈ QuotientGroup.mk' N₀ '' D₀,
      ∀ z ∈ QuotientGroup.mk' N₀ '' D₀, Commute x y → Commute y z → Commute x z := by
  rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩ _ ⟨t₃, ht₃, rfl⟩ h12 h23
  by_cases e12 : QuotientGroup.mk' N₀ t₁ = QuotientGroup.mk' N₀ t₂
  · rw [e12]
    exact h23
  by_cases e23 : QuotientGroup.mk' N₀ t₂ = QuotientGroup.mk' N₀ t₃
  · rw [← e23]
    exact h12
  have c12 := qp_commute_lift h ht₁ ht₂ e12 h12
  have c23 := qp_commute_lift h ht₂ ht₃ e23 h23
  have c13 : Commute t₁ t₃ := h.cent t₂ ht₂ t₁ ht₁ t₃ ht₃ c12 c23.symm
  exact c13.map _

theorem qp_O2 (h : Sec42Data W N₀ D₀) :
    ∀ z ∈ CFSG.pCore 2 (W ⧸ N₀), ∀ g : W ⧸ N₀, g * z = z * g := by
  have hP : (CFSG.pCore 2 (W ⧸ N₀)).comap (QuotientGroup.mk' N₀) ≤ CFSG.pCore 2 W := by
    show _ ≤ sSup {K : Subgroup W | K.Normal ∧ IsPGroup 2 K}
    refine le_sSup ⟨inferInstance, ?_⟩
    intro x
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup
      (⟨QuotientGroup.mk' N₀ x.1, x.2⟩ : CFSG.pCore 2 (W ⧸ N₀))
    have h1 : QuotientGroup.mk' N₀ (x.1 ^ 2 ^ n) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hn
      simpa using this
    have hmem : x.1 ^ 2 ^ n ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h1
    have hsq2 : (x.1 ^ 2 ^ n) ^ 2 = 1 := h.sq _ hmem
    refine ⟨n + 1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ, pow_mul]
    exact hsq2
  intro z hz g
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective g
  have ht : t ∈ CFSG.pCore 2 W := hP hz
  have hcomm := h.O2 t ht s'
  have h1 : QuotientGroup.mk' N₀ ⁅t, s'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
  simp only [commutatorElement_def, map_mul, map_inv, QuotientGroup.mk'_apply] at h1
  have e : (t : W ⧸ N₀) * (s' : W ⧸ N₀) = (s' : W ⧸ N₀) * (t : W ⧸ N₀) := by
    calc (t : W ⧸ N₀) * (s' : W ⧸ N₀)
        = (t : W ⧸ N₀) * (s' : W ⧸ N₀) * (t : W ⧸ N₀)⁻¹ * (s' : W ⧸ N₀)⁻¹ *
            ((s' : W ⧸ N₀) * (t : W ⧸ N₀)) := by group
      _ = (s' : W ⧸ N₀) * (t : W ⧸ N₀) := by rw [h1, one_mul]
  exact e.symm

theorem qp_mul_self (h : Sec42Data W N₀ D₀) {d : W ⧸ N₀} (hd : d ∈ QuotientGroup.mk' N₀ '' D₀) :
    d * d = 1 := by
  obtain ⟨t, ht, rfl⟩ := hd
  rw [← pow_two, ← map_pow, h.invol t ht, map_one]

theorem qp_setup (h : Sec42Data W N₀ D₀) :
    CFSG.Timmesfeld.Bridge.Asc72.Setup (W ⧸ N₀) (QuotientGroup.mk' N₀ '' D₀) := by
  obtain ⟨d₀, hd₀, hcls⟩ := h.single
  refine ⟨⟨QuotientGroup.mk' N₀ d₀, ?_⟩, qp_isOddTransp h, qp_closure h⟩
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨g, hg⟩ := hcls d hd
    show IsConj (QuotientGroup.mk' N₀ d₀) (QuotientGroup.mk' N₀ d)
    refine isConj_iff.mpr ⟨QuotientGroup.mk' N₀ g, ?_⟩
    rw [hg]
    simp
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨g * d₀ * g⁻¹, h.conjD g d₀ hd₀, ?_⟩
    rw [← hc]
    simp

theorem qp_hE (h : Sec42Data W N₀ D₀) :
    ∀ d ∈ QuotientGroup.mk' N₀ '' D₀,
      IsElemAbelian 2 (Subgroup.closure {e | e ∈ QuotientGroup.mk' N₀ '' D₀ ∧ Commute e d}) := by
  intro d hd
  refine sec41_isElemAbelian_closure ?_ ?_
  · intro e he f hf
    have he' : e ∈ QuotientGroup.mk' N₀ '' D₀ ∧ Commute e d := he
    have hf' : f ∈ QuotientGroup.mk' N₀ '' D₀ ∧ Commute f d := hf
    exact (qp_trans h e he'.1 d hd f hf'.1 he'.2 hf'.2.symm).eq
  · intro e he
    have he' : e ∈ QuotientGroup.mk' N₀ '' D₀ ∧ Commute e d := he
    exact qp_mul_self h he'.1

theorem qp_hO2 (h : Sec42Data W N₀ D₀) : CFSG.pCore 2 (W ⧸ N₀) ≤ Subgroup.center (W ⧸ N₀) := by
  intro z hz
  exact Subgroup.mem_center_iff.mpr (qp_O2 h z hz)

theorem qp_main [Finite W]
    (h : Sec42Data W N₀ D₀) (hns : ¬ Group.IsSolvable (W ⧸ N₀)) :
    CFSG.solvableRadical (W ⧸ N₀) = Subgroup.center (W ⧸ N₀) ∧
      CFSG.BenderSuzuki.IsBenderGroup ((W ⧸ N₀) ⧸ Subgroup.center (W ⧸ N₀)) :=
  CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_center_quot_of_elemComponents
    (qp_setup h) (qp_hE h) (qp_hO2 h) hns

theorem qp_inj (h : Sec42Data W N₀ D₀) {d : W ⧸ N₀} (hd : d ∈ QuotientGroup.mk' N₀ '' D₀)
    {z : W ⧸ N₀} (hz : z ∈ Subgroup.center (W ⧸ N₀)) (hz1 : z ≠ 1) :
    d * z ∉ QuotientGroup.mk' N₀ '' D₀ :=
  fun hdz => (qp_setup h).false_of_mul_mem_center hd hdz hz hz1

theorem qp_aut_eq_of_fix (h : Sec42Data W N₀ D₀) (φ : MulAut (W ⧸ N₀))
    (hφ : ∀ d ∈ QuotientGroup.mk' N₀ '' D₀, φ d = d) : φ = 1 := by
  have key : ∀ x : W ⧸ N₀, φ x = x := by
    intro x
    have hx : x ∈ Subgroup.closure (QuotientGroup.mk' N₀ '' D₀) := by
      rw [qp_closure h]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hφ y hy
    | one => exact map_one φ
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb]
    | inv a _ iha => rw [map_inv, iha]
  ext x
  rw [MulAut.one_apply]
  exact key x

theorem qp_commute_lift_Z (h : Sec42Data W N₀ D₀) {d e : W ⧸ N₀}
    (hd : d ∈ QuotientGroup.mk' N₀ '' D₀) (he : e ∈ QuotientGroup.mk' N₀ '' D₀)
    (hc : Commute (QuotientGroup.mk' (Subgroup.center (W ⧸ N₀)) d)
      (QuotientGroup.mk' (Subgroup.center (W ⧸ N₀)) e)) : Commute d e := by
  have hdd : d * d = 1 := qp_mul_self h hd
  have hee : e * e = 1 := qp_mul_self h he
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have h1 : QuotientGroup.mk' (Subgroup.center (W ⧸ N₀)) (d * e) =
      QuotientGroup.mk' (Subgroup.center (W ⧸ N₀)) (e * d) := by
    rw [map_mul, map_mul]
    exact hc.eq
  have h2 : (d * e)⁻¹ * (e * d) ∈ Subgroup.center (W ⧸ N₀) := QuotientGroup.eq.mp h1
  have h3 : (d * e)⁻¹ = e * d := by rw [mul_inv_rev, hd_inv, he_inv]
  rw [h3] at h2
  rcases (qp_isOddTransp h).2 e he d hd with h4 | hodd
  · exact (qp_commute_of_invol hee hdd (orderOf_dvd_iff_pow_eq_one.mp h4)).symm
  · have hv2 : (e * d) ^ 2 ∈ Subgroup.center (W ⧸ N₀) := by
      rw [pow_two]
      exact h2
    have hv : e * d ∈ Subgroup.center (W ⧸ N₀) := qp_mem_of_sq_mem_of_odd hv2 hodd
    by_cases hv1 : e * d = 1
    · have hed : e = d := by
        calc e = (e * d) * d := by rw [mul_assoc, hdd, mul_one]
          _ = d := by rw [hv1, one_mul]
      subst hed
      exact Commute.refl _
    · exfalso
      have he_eq : e = d * (e * d) := by
        calc e = (e * d) * d := by rw [mul_assoc, hdd, mul_one]
          _ = d * (e * d) := (Subgroup.mem_center_iff.mp hv d).symm
      have he_mem : d * (e * d) ∈ QuotientGroup.mk' N₀ '' D₀ := by
        rw [← he_eq]
        exact he
      exact qp_inj h hd hv hv1 he_mem

end QS

end CFSG.RankThree.GF2n.Tim77
