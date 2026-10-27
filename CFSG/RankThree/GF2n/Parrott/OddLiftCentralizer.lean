module

public import CFSG.RankThree.GF2n.Parrott.LiftSquareOdd
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_orderOf_three_lift {rb : QA45.originalSubgroup} (h3 : rb ^ 3 = 1) (h1 : rb ≠ 1) :
    ∃ r : ↥(H z), qH D r = rb ∧ orderOf r = 3 := by
  have hord : orderOf rb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3 h1
  exact ⟨lift3 D rb hord, qH_lift3 D rb hord, orderOf_lift3 D rb hord⟩

theorem exists_lift_centralizer_of_le {K : Subgroup ↥(H z)} {r : ↥(H z)} (hr : orderOf r = 3)
    (hrK : ∀ x ∈ K, r * x * r⁻¹ ∈ K) (hKJ : ¬ 3 ∣ Nat.card ↥(K ⊓ (J z).subgroupOf (H z)))
    {s₀ : ↥(H z)} (hs₀ : s₀ ∈ K) (hg : qH D s₀ * qH D r = qH D r * qH D s₀) :
    ∃ s ∈ K, qH D s = qH D s₀ ∧ s * r = r * s := by
  classical
  let X : Type _ := {x : ↥(H z) // x ∈ K ∧ qH D x = qH D s₀}
  let eX : X ≃ ↥(K ⊓ (J z).subgroupOf (H z)) :=
    { toFun := fun x => ⟨s₀⁻¹ * x.1, Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem hs₀) x.2.1,
        (J_mem_iff D _).2 (by rw [map_mul, map_inv, x.2.2, inv_mul_cancel])⟩⟩
      invFun := fun j => ⟨s₀ * j.1, K.mul_mem hs₀ (Subgroup.mem_inf.mp j.2).1, by
        rw [map_mul, (J_mem_iff D _).1 (Subgroup.mem_inf.mp j.2).2, mul_one]⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun j => by
        apply Subtype.ext
        simp }
  have hr3 : r ^ 3 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  have hrrr : r * r * r = 1 := by rw [← pow_three']; exact hr3
  have hconj : ∀ x : X, r * x.1 * r⁻¹ ∈ K ∧ qH D (r * x.1 * r⁻¹) = qH D s₀ := fun x =>
    ⟨hrK _ x.2.1, by rw [map_mul, map_mul, map_inv, x.2.2, ← hg, mul_inv_cancel_right]⟩
  have hconj' : ∀ x : X, r⁻¹ * x.1 * r ∈ K ∧ qH D (r⁻¹ * x.1 * r) = qH D s₀ := fun x => by
    have key : r⁻¹ * x.1 * r = r * (r * x.1 * r⁻¹) * r⁻¹ := by
      have hr2 : r * r = r⁻¹ := eq_inv_of_mul_eq_one_left hrrr
      calc r⁻¹ * x.1 * r = (r * r) * x.1 * (r * r)⁻¹ := by rw [hr2, inv_inv]
        _ = r * (r * x.1 * r⁻¹) * r⁻¹ := by group
    refine ⟨by rw [key]; exact hrK _ (hrK _ x.2.1), ?_⟩
    rw [map_mul, map_mul, map_inv, x.2.2]
    have : (qH D r)⁻¹ * qH D s₀ = qH D s₀ * (qH D r)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hg, mul_assoc, mul_inv_cancel, mul_one]
    rw [this, mul_assoc, inv_mul_cancel, mul_one]
  let σ : Equiv.Perm X :=
    { toFun := fun x => ⟨r * x.1 * r⁻¹, hconj x⟩
      invFun := fun x => ⟨r⁻¹ * x.1 * r, hconj' x⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun x => by
        apply Subtype.ext
        simp [mul_assoc] }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show r * (r * (r * x.1 * r⁻¹) * r⁻¹) * r⁻¹ = x.1
    have key : r * (r * (r * x.1 * r⁻¹) * r⁻¹) * r⁻¹ = (r * r * r) * x.1 * (r * r * r)⁻¹ := by
      group
    rw [key, hrrr]
    group
  have hfin : Finite X := Finite.of_equiv _ eX.symm
  let _ : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X = Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr eX
  have hnd : ¬ 3 ∣ Fintype.card X := by
    rw [hcard]
    exact hKJ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hnd hσ
  refine ⟨x.1, x.2.1, x.2.2, ?_⟩
  have hx' : r * x.1 * r⁻¹ = x.1 := congrArg Subtype.val hx
  calc x.1 * r = (r * x.1 * r⁻¹) * r := by rw [hx']
    _ = r * x.1 := by group

theorem exists_lift_centralizer {r : ↥(H z)} (hr : orderOf r = 3) {g : QA45.originalSubgroup}
    (hg : g * qH D r = qH D r * g) : ∃ s : ↥(H z), qH D s = g ∧ s * r = r * s := by
  obtain ⟨s₀, hs₀⟩ := qH_surjective D g
  obtain ⟨s, -, hs, hsr⟩ := exists_lift_centralizer_of_le D (K := ⊤) hr (fun x _ => trivial)
    (by
      rw [top_inf_eq]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1
        (coprime_three_card_J_subgroupOf (z := z)))
    (s₀ := s₀) trivial (by rw [hs₀]; exact hg)
  exact ⟨s, hs.trans hs₀, hsr⟩

section Odd

variable (h : Tim79a.ParrottHyp z)

omit hN in
theorem zpowers_odd_data {r s : ↥(H z)} (hr : orderOf r = 3) (hrs : s * r = r * s)
    (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1) :
    ∃ hRH : Subgroup.zpowers (r : G) ≤ H z, Odd (Nat.card (Subgroup.zpowers (r : G))) ∧
      (∀ r' ∈ Subgroup.zpowers (r : G), r' * (s : G) = (s : G) * r') ∧
      ∀ v : QuotientV.V z, (∀ (r' : G) (hr' : r' ∈ Subgroup.zpowers (r : G)),
        conjV h ⟨r', hRH hr'⟩ v = v) → v = 1 := by
  have hRH : Subgroup.zpowers (r : G) ≤ H z := Subgroup.zpowers_le.mpr r.2
  refine ⟨hRH, ?_, ?_, fun v hv => hrv v (hv (r : G) (Subgroup.mem_zpowers _))⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hr]
    exact ⟨1, rfl⟩
  · intro r' hr'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr'
    have hc : Commute (r : G) (s : G) := by
      have := congrArg Subtype.val hrs
      exact this.symm
    exact (hc.zpow_left k).eq

omit hN in
theorem sq_mem_centerIn_of_fixed_point_free {r s : ↥(H z)} (hr : orderOf r = 3)
    (hrs : s * r = r * s) (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1)
    (hss : (s : G) * s ∈ J z) : (s : G) * s ∈ centerIn (J z) := by
  obtain ⟨-, -, -, hRV⟩ := zpowers_odd_data h hr hrs hrv
  have hrr : conjV h r (QuotientV.pi z ⟨(s : G) * s, hss⟩) = QuotientV.pi z ⟨(s : G) * s, hss⟩ := by
    rw [conjV_pi_conj h r hss]
    congr 1
    apply Subtype.ext
    show (r : G) * ((s : G) * s) * (r : G)⁻¹ = (s : G) * s
    have hc : (r : G) * (s : G) = (s : G) * (r : G) := by
      have := congrArg Subtype.val hrs
      exact this.symm
    have h1 : (r : G) * ((s : G) * s) = ((s : G) * s) * r := by
      rw [← mul_assoc, hc, mul_assoc, hc, mul_assoc]
    rw [h1]
    group
  exact (pi_eq_one_iff_mem_centerIn hss).mp (hrv _ hrr)

omit hN in
theorem conj_eq_of_fixed (hZ : centerIn (J z) = centerIn (H z)) {r s : ↥(H z)}
    (hr : orderOf r = 3) (hrs : s * r = r * s)
    (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1) (hss : (s : G) * s ∈ J z) {c : G}
    (hcJ : c ∈ J z) (hfix : conjV h s (QuotientV.pi z ⟨c, hcJ⟩) = QuotientV.pi z ⟨c, hcJ⟩) :
    (s : G) * c * (s : G)⁻¹ = c := by
  obtain ⟨hRH, hRodd, hRs, hRV⟩ := zpowers_odd_data h hr hrs hrv
  have hssZ := sq_mem_centerIn_of_fixed_point_free h hr hrs hrv hss
  have hexp : (c * (s : G)) * (c * (s : G)) = (c * ((s : G) * c * (s : G)⁻¹)) * ((s : G) * s) := by
    group
  have hscJ : (s : G) * c * (s : G)⁻¹ ∈ J z := H_conj_mem_J s hcJ
  have hsq : (c * (s : G)) * (c * (s : G)) ∈ centerIn (J z) := by
    rw [hexp]
    refine Subgroup.mul_mem _ ?_ hssZ
    have h1 : QuotientV.pi z ⟨c, hcJ⟩ * QuotientV.pi z ⟨(s : G) * c * (s : G)⁻¹, hscJ⟩ = 1 := by
      rw [← conjV_pi_conj h s hcJ, hfix]
      have := QuotientV.pow_two_eq_one_V h (QuotientV.pi z ⟨c, hcJ⟩)
      rwa [pow_two] at this
    have h2 : QuotientV.pi z ⟨c * ((s : G) * c * (s : G)⁻¹), (J z).mul_mem hcJ hscJ⟩ = 1 := by
      rw [← h1, ← map_mul]
      rfl
    exact (pi_eq_one_iff_mem_centerIn _).mp h2
  have h3 := mul_self_eq_of_sq_mem_centerIn_of_odd h hZ (s := (s : G)) s.2 hss
    (R := Subgroup.zpowers (r : G)) hRH hRodd hRs hRV c hcJ hsq
  rw [hexp] at h3
  have h4 : c * ((s : G) * c * (s : G)⁻¹) = c * c := mul_right_cancel h3
  exact mul_left_cancel h4

omit hN in
theorem fixed_of_sq_mem_centerIn {r s : ↥(H z)} (hr : orderOf r = 3) (hrs : s * r = r * s)
    (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1) (hss : (s : G) * s ∈ J z) {j : G}
    (hjJ : j ∈ J z) (hjs : (j * (s : G)) * (j * (s : G)) ∈ centerIn (J z)) :
    conjV h s (QuotientV.pi z ⟨j, hjJ⟩) = QuotientV.pi z ⟨j, hjJ⟩ := by
  have hssZ := sq_mem_centerIn_of_fixed_point_free h hr hrs hrv hss
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  have hinvV : ∀ v : QuotientV.V z, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hexp : (j * (s : G)) * (j * (s : G)) = (j * ((s : G) * j * (s : G)⁻¹)) * ((s : G) * s) := by
    group
  have hjsj : j * ((s : G) * j * (s : G)⁻¹) ∈ centerIn (J z) := by
    have h1 : j * ((s : G) * j * (s : G)⁻¹) =
        ((j * (s : G)) * (j * (s : G))) * ((s : G) * s)⁻¹ := by
      rw [hexp]
      group
    rw [h1]
    exact Subgroup.mul_mem _ hjs (Subgroup.inv_mem _ hssZ)
  have hsjJ : (s : G) * j * (s : G)⁻¹ ∈ J z := H_conj_mem_J s hjJ
  have h1 := (pi_eq_one_iff_mem_centerIn ((J z).mul_mem hjJ hsjJ)).mpr hjsj
  have h2 : QuotientV.pi z ⟨j, hjJ⟩ * QuotientV.pi z ⟨(s : G) * j * (s : G)⁻¹, hsjJ⟩ = 1 := by
    rw [← map_mul]
    exact h1
  rw [← conjV_pi_conj h s hjJ] at h2
  rw [eq_inv_of_mul_eq_one_right h2, hinvV]

omit hN in
theorem mem_centerIn_of_centralizes {r : ↥(H z)}
    (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1) {c : G} (hcJ : c ∈ J z)
    (hc : (r : G) * c * (r : G)⁻¹ = c) : c ∈ centerIn (J z) := by
  apply (pi_eq_one_iff_mem_centerIn hcJ).mp
  apply hrv
  rw [conjV_pi_conj h r hcJ]
  congr 1
  apply Subtype.ext
  exact hc

end Odd

end CFSG.RankThree.GF2n.Parrott
