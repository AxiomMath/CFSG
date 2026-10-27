module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveRankOne
public import CFSG.LocalAnalysis.WeakClosure81.TwelveEightA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem map_odd_part_eq {G Y : Type} [Group G] [Group Y] (π : G →* Y) {c w y : G}
    (hc : c = w * y) (hw : w ∈ Subgroup.zpowers c) (hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hodd : Odd (orderOf (π c))) : π y = π c := by
  obtain ⟨k, hk⟩ := hw2
  have hw_dvd : orderOf (π w) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have hw_zp : π w ∈ Subgroup.zpowers (π c) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨m, by rw [← hm, map_zpow]⟩
  have hw_ord_dvd : orderOf (π w) ∣ orderOf (π c) := orderOf_dvd_of_mem_zpowers hw_zp
  have hcop : Nat.Coprime (2 ^ k) (orderOf (π c)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf (π w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hw_dvd hw_ord_dvd
  have hw1 : π w = 1 := orderOf_eq_one_iff.mp h1
  rw [hc, map_mul, hw1, one_mul]

private theorem b12_TwelveLift_eq_one_of_mul_self_of_odd {Y : Type} [Group Y] {v : Y}
    (hv : v * v = 1) (hodd : Odd (orderOf v)) : v = 1 := by
  have hdvd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) dvd_rfl hdvd)

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.exists_lift (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) {u v : G ⧸ CFSG.Quasithin.kerIn M ⊤} (hu : u * u = 1)
    (hv : v * v = 1) (huv : Odd (orderOf (u * v))) (huv1 : u * v ≠ 1) :
    ∃ a g x : G, a ∈ A ∧ a ∉ CFSG.Quasithin.kerIn M ⊤ ∧ g ∉ M ∧
      QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) (x⁻¹ * (a * (g * a * g⁻¹)) * x) = u * v := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  obtain ⟨a, ha, haK⟩ : ∃ a ∈ A, a ∉ CFSG.Quasithin.kerIn M ⊤ := by
    by_contra hc
    rw [not_exists] at hc
    exact h.not_le_ker fun a ha => by
      by_contra haK
      exact hc a ⟨ha, haK⟩
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have hpa2 : π a * π a = 1 := by rw [← map_mul, ha2, map_one]
  have hpa1 : π a ≠ 1 := fun hcon => haK ((QuotientGroup.eq_one_iff a).mp hcon)
  have hu1 : u ≠ 1 := by
    intro hu_eq
    have hoddv : Odd (orderOf v) := by rwa [hu_eq, one_mul] at huv
    have hv1 : v = 1 := b12_TwelveLift_eq_one_of_mul_self_of_odd hv hoddv
    exact huv1 (by rw [hu_eq, hv1, one_mul])
  have hv1 : v ≠ 1 := by
    intro hv_eq
    have hoddu : Odd (orderOf u) := by rwa [hv_eq, mul_one] at huv
    have hu1' : u = 1 := b12_TwelveLift_eq_one_of_mul_self_of_odd hu hoddu
    exact huv1 (by rw [hu1', hv_eq, one_mul])
  obtain ⟨xb, hxb⟩ := isConj_iff.mp (rankOne_isConj_of_involutions h.type hu hu1 hpa2 hpa1)
  set v' : G ⧸ CFSG.Quasithin.kerIn M ⊤ := xb * v * xb⁻¹ with hv'def
  have hv'2 : v' * v' = 1 := by
    rw [hv'def]
    calc (xb * v * xb⁻¹) * (xb * v * xb⁻¹) = xb * (v * v) * xb⁻¹ := by group
      _ = 1 := by rw [hv, mul_one, mul_inv_cancel]
  have hv'1 : v' ≠ 1 := by
    intro hv1'
    apply hv1
    calc v = xb⁻¹ * v' * xb := by rw [hv'def]; group
      _ = 1 := by rw [hv1']; group
  obtain ⟨gb, hgb⟩ := isConj_iff.mp
    (rankOne_isConj_of_involutions h.type hpa2 hpa1 hv'2 hv'1)
  obtain ⟨g, hg⟩ : ∃ g : G, π g = gb := QuotientGroup.mk'_surjective _ gb
  obtain ⟨x, hx⟩ : ∃ x : G, π x = xb := QuotientGroup.mk'_surjective _ xb
  let c : G := a * (g * a * g⁻¹)
  have hexp : π (x⁻¹ * c * x)
      = (π x)⁻¹ * (π a * (π g * π a * (π g)⁻¹)) * π x := by
    dsimp only [c]
    simp only [map_mul, map_inv]
  have hmain : π (x⁻¹ * c * x) = u * v := by
    rw [hexp, hx, hg]
    rw [hgb]
    rw [hv'def]
    rw [← hxb]
    group
  have hgM_not : g ∉ M := by
    intro hgM
    have hpaM : π a ∈ M.map π := Subgroup.mem_map_of_mem π (h.A_le_M ha)
    have hgagM : g * a * g⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hgM (h.A_le_M ha)) (M.inv_mem hgM)
    have hpgag : π (g * a * g⁻¹) = v' := by
      simp only [map_mul, map_inv, hg, hgb]
    have hv'M : v' ∈ M.map π := by
      rw [← hpgag]
      exact Subgroup.mem_map_of_mem π hgagM
    have hcomm : π a * v' = v' * π a :=
      h.map_involutions_commute hpaM hv'M hpa2 hv'2
    have hcc : π c * π c = 1 := by
      have hpc : π c = π a * v' := by
        dsimp only [c]
        rw [map_mul, hpgag]
      rw [hpc]
      calc (π a * v') * (π a * v') = π a * (v' * π a) * v' := by group
        _ = π a * (π a * v') * v' := by rw [← hcomm]
        _ = (π a * π a) * (v' * v') := by group
        _ = 1 := by rw [hpa2, hv'2, one_mul]
    have hsq : (u * v) * (u * v) = 1 := by
      have h2 : (u * v) * (u * v) = π ((x⁻¹ * c * x) * (x⁻¹ * c * x)) := by
        rw [← hmain, ← map_mul]
      rw [h2]
      rw [show (x⁻¹ * c * x) * (x⁻¹ * c * x) = x⁻¹ * (c * c) * x by group]
      simp only [map_mul, map_inv]
      rw [hcc]
      group
    exact huv1 (b12_TwelveLift_eq_one_of_mul_self_of_odd hsq huv)
  exact ⟨a, g, x, ha, haK, hgM_not, hmain⟩

theorem Setting12Two.exists_odd_part_lift (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) {u v : G ⧸ CFSG.Quasithin.kerIn M ⊤} (hu : u * u = 1)
    (hv : v * v = 1) (huv : Odd (orderOf (u * v))) (huv1 : u * v ≠ 1) :
    ∃ a g x w y : G, a ∈ A ∧ a ∉ CFSG.Quasithin.kerIn M ⊤ ∧ g ∉ M ∧
      a * (g * a * g⁻¹) = w * y ∧ w ∈ Subgroup.zpowers (a * (g * a * g⁻¹)) ∧
      y ∈ Subgroup.zpowers (a * (g * a * g⁻¹)) ∧ (∃ k : ℕ, w ^ 2 ^ k = 1) ∧
      Odd (orderOf y) ∧ y ∉ M ∧ a * y * a⁻¹ = y⁻¹ ∧
      QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) (x⁻¹ * y * x) = u * v := by
  obtain ⟨a, g, x, ha, haK, hg, hx⟩ := h.exists_lift hA hu hv huv huv1
  obtain ⟨w, y, hc, hw, hy, hw2, hyodd, hyM, hinv⟩ := h.exists_inverted_odd hA ha haK hg
  refine ⟨a, g, x, w, y, ha, haK, hg, hc, hw, hy, hw2, hyodd, hyM, hinv, ?_⟩
  have hsem : SemiconjBy (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) x) (u * v)
      (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) (a * (g * a * g⁻¹))) := by
    unfold SemiconjBy
    rw [← hx]
    simp only [map_mul, map_inv]
    group
  have hord : orderOf (u * v)
      = orderOf (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) (a * (g * a * g⁻¹))) :=
    SemiconjBy.orderOf_eq (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) x) hsem
  have hodd' : Odd (orderOf (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
      (a * (g * a * g⁻¹)))) := by
    rw [← hord]
    exact huv
  have hy' : QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) y
      = QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) (a * (g * a * g⁻¹)) :=
    map_odd_part_eq (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) hc hw hw2 hodd'
  rw [← hx]
  simp only [map_mul, map_inv, hy']

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
