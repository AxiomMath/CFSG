module

public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

private lemma w183b5_conj_zpow_eq_inv_zpow {Y : Type*} [Group Y] {c u : Y}
    (h : c * u * c⁻¹ = u⁻¹) (k : ℤ) : c * u ^ k * c⁻¹ = u ^ (-k) := by
  rw [← conj_zpow, h, inv_zpow']

private lemma w183b5_mul_zpow_eq {Y : Type*} [Group Y] {c u : Y}
    (h : c * u * c⁻¹ = u⁻¹) (k : ℤ) : c * u ^ k = u ^ (-k) * c := by
  rw [← w183b5_conj_zpow_eq_inv_zpow h k]
  group

private lemma w183b5_zpow_conj_eq {Y : Type*} [Group Y] {c u : Y}
    (h : c * u * c⁻¹ = u⁻¹) (k : ℤ) : u ^ k * c * (u ^ k)⁻¹ = u ^ (2 * k) * c := by
  rw [← zpow_neg u k, mul_assoc (u ^ k) c (u ^ (-k))]
  rw [w183b5_mul_zpow_eq h (-k), neg_neg]
  rw [← mul_assoc (u ^ k) (u ^ k) c, ← zpow_add]
  rw [show k + k = 2 * k by ring]

private lemma w183b5_zpow_mul_c_conj_eq {Y : Type*} [Group Y] {c u : Y} (hc2 : c * c = 1)
    (h : c * u * c⁻¹ = u⁻¹) (k : ℤ) :
    (u ^ k * c) * c * (u ^ k * c)⁻¹ = u ^ (2 * k) * c := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc2
  rw [mul_inv_rev, ← zpow_neg u k]
  rw [mul_assoc (u ^ k) c c, hc2, mul_one]
  rw [hcinv, w183b5_mul_zpow_eq h (-k), neg_neg]
  rw [← mul_assoc (u ^ k) (u ^ k) c, ← zpow_add]
  rw [show k + k = 2 * k by ring]

theorem isOddTransp_class_of_comm_or_conj {Y : Type} [Group Y] [Finite Y] {a : Y}
    (ha : orderOf a = 2)
    (h132 : ∀ c d : Y, IsConj a c → IsConj a d →
      c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹) :
    IsOddTransp {x : Y | IsConj a x} := by
  have hord : ∀ x : Y, IsConj a x → orderOf x = 2 := by
    intro x hx
    obtain ⟨e, he⟩ := isConj_iff.1 hx
    rw [← he]
    have hconj : orderOf (e * a * e⁻¹) = orderOf a := by
      simpa using (MulAut.conj e).orderOf_eq a
    rw [hconj, ha]
  constructor
  · exact hord
  · intro c hc d hd
    have hc2 : c * c = 1 := by
      rw [← pow_two, ← hord c hc]
      exact pow_orderOf_eq_one c
    have hd2 : d * d = 1 := by
      rw [← pow_two, ← hord d hd]
      exact pow_orderOf_eq_one d
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc2
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_left hd2
    rcases h132 c d hc hd with hcomm | ⟨z, hz, hdz⟩
    · left
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      calc (c * d) * (c * d) = c * (d * c) * d := by simp only [mul_assoc]
        _ = c * (c * d) * d := by rw [← hcomm]
        _ = (c * c) * (d * d) := by simp only [mul_assoc]
        _ = 1 := by rw [hc2, hd2, mul_one]
    · right
      let u : Y := c * d
      have hcu : c * u * c⁻¹ = u⁻¹ := by
        simp only [u]
        rw [← mul_assoc c c d, hc2, one_mul, mul_inv_rev, hcinv, hdinv]
      let P' : Y → Prop := fun y => ∃ k : ℤ, y = u ^ k ∨ y = u ^ k * c
      have hPc : P' c := ⟨0, Or.inr (by simp)⟩
      have hPd : P' d := by
        refine ⟨-1, Or.inr ?_⟩
        calc d = c * u := by
              simp only [u]
              rw [← mul_assoc c c d, hc2, one_mul]
          _ = u⁻¹ * c := by rw [← hcu]; group
          _ = u ^ (-1 : ℤ) * c := by simp
      have hPone : P' 1 := ⟨0, Or.inl (by simp)⟩
      have hPmul : ∀ x y : Y, P' x → P' y → P' (x * y) := by
        intro x y hx hy
        obtain ⟨kx, hx | hx⟩ := hx
        · obtain ⟨ky, hy | hy⟩ := hy
          · exact ⟨kx + ky, Or.inl (by rw [hx, hy, ← zpow_add])⟩
          · exact ⟨kx + ky, Or.inr (by rw [hx, hy, ← mul_assoc, ← zpow_add])⟩
        · obtain ⟨ky, hy | hy⟩ := hy
          · refine ⟨kx - ky, Or.inr ?_⟩
            rw [hx, hy, mul_assoc (u ^ kx) c (u ^ ky), w183b5_mul_zpow_eq hcu ky,
              ← mul_assoc (u ^ kx) (u ^ (-ky)) c, ← zpow_add,
              show kx + -ky = kx - ky by ring]
          · refine ⟨kx - ky, Or.inl ?_⟩
            rw [hx, hy, mul_assoc (u ^ kx) c (u ^ ky * c), ← mul_assoc c (u ^ ky) c,
              w183b5_mul_zpow_eq hcu ky, mul_assoc (u ^ (-ky)) c c, hc2, mul_one,
              ← zpow_add, show kx + -ky = kx - ky by ring]
      have hPinv : ∀ x : Y, P' x → P' x⁻¹ := by
        intro x hx
        obtain ⟨kx, hx | hx⟩ := hx
        · exact ⟨-kx, Or.inl (by rw [hx, ← zpow_neg u kx])⟩
        · refine ⟨kx, Or.inr ?_⟩
          rw [hx, mul_inv_rev, hcinv, ← zpow_neg u kx, w183b5_mul_zpow_eq hcu (-kx), neg_neg]
      have hPz : P' z := by
        refine Subgroup.closure_induction (p := fun y _ => P' y) ?_ hPone ?_ ?_ hz
        · intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hPc
          · exact hPd
        · intro x y _ _ hx hy
          exact hPmul x y hx hy
        · intro x _ hx
          exact hPinv x hx
      have hd_eq' : d = u⁻¹ * c := by
        have : u⁻¹ * c = d := by
          rw [show u⁻¹ = c * u * c⁻¹ from hcu.symm]
          rw [show (c * u * c⁻¹) * c = c * u by group]
          simp only [u]
          rw [← mul_assoc c c d, hc2, one_mul]
        exact this.symm
      have hodd : Odd (orderOf u) := by
        obtain ⟨k, hk | hk⟩ := hPz
        · have hd_eq : d = u ^ (2 * k) * c := by
            rw [hdz, hk, w183b5_zpow_conj_eq hcu k]
          have hpow : u ^ (2 * k) = u⁻¹ :=
            mul_right_cancel (hd_eq.symm.trans hd_eq')
          have hpow1 : u ^ (2 * k + 1) = 1 := by
            rw [zpow_add, hpow, zpow_one, inv_mul_cancel]
          have hdvd : (orderOf u : ℤ) ∣ (2 * k + 1) := by
            rw [orderOf_dvd_iff_zpow_eq_one]
            exact hpow1
          have hodd_int : Odd (2 * k + 1) :=
            Int.not_even_iff_odd.mp (Int.not_even_two_mul_add_one k)
          have hodd_nat : Odd ((2 * k + 1).natAbs) := Int.natAbs_odd.mpr hodd_int
          have hdvd_nat : orderOf u ∣ (2 * k + 1).natAbs := by
            simpa using Int.natAbs_dvd_natAbs.mpr hdvd
          exact hodd_nat.of_dvd_nat hdvd_nat
        · have hd_eq : d = u ^ (2 * k) * c := by
            rw [hdz, hk, w183b5_zpow_mul_c_conj_eq hc2 hcu k]
          have hpow : u ^ (2 * k) = u⁻¹ :=
            mul_right_cancel (hd_eq.symm.trans hd_eq')
          have hpow1 : u ^ (2 * k + 1) = 1 := by
            rw [zpow_add, hpow, zpow_one, inv_mul_cancel]
          have hdvd : (orderOf u : ℤ) ∣ (2 * k + 1) := by
            rw [orderOf_dvd_iff_zpow_eq_one]
            exact hpow1
          have hodd_int : Odd (2 * k + 1) :=
            Int.not_even_iff_odd.mp (Int.not_even_two_mul_add_one k)
          have hodd_nat : Odd ((2 * k + 1).natAbs) := Int.natAbs_odd.mpr hodd_int
          have hdvd_nat : orderOf u ∣ (2 * k + 1).natAbs := by
            simpa using Int.natAbs_dvd_natAbs.mpr hdvd
          exact hodd_nat.of_dvd_nat hdvd_nat
      exact hodd

theorem le_of_simple_section {Y : Type} [Group Y] [Finite Y] {Kk P Lc : Subgroup Y}
    (hKP : Kk ≤ P) (hPn : P.Normal) (h2q : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P) {S : Type}
    [Group S] [IsSimpleGroup S] (hSnc : ∃ u v : S, u * v ≠ v * u) (φ : ↥Lc →* S)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥Lc, φ k = 1 ↔ (k : Y) ∈ Kk) : Lc ≤ P := by
  let N : Subgroup ↥Lc := P.subgroupOf Lc
  have hNn : N.Normal := hPn.subgroupOf Lc
  haveI hmapn : (N.map φ).Normal := hNn.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  · exfalso
    haveI : Finite S := Finite.of_surjective φ hφs
    have hS2 : IsPGroup 2 S := by
      intro s
      obtain ⟨l, rfl⟩ := hφs s
      obtain ⟨k, hk⟩ := h2q (l : Y)
      refine ⟨k, ?_⟩
      have hmN : (l ^ 2 ^ k : ↥Lc) ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hk
      have hφm : φ (l ^ 2 ^ k) = 1 := by
        have : φ (l ^ 2 ^ k) ∈ N.map φ := ⟨l ^ 2 ^ k, hmN, rfl⟩
        rw [hbot] at this
        simpa using this
      rwa [map_pow] at hφm
    have hcenter : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hcb | hct
    · exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center S)).mp hcenter hcb
    · obtain ⟨u, v, huv⟩ := hSnc
      have : u * v = v * u := by
        have hu : u ∈ Subgroup.center S := by rw [hct]; trivial
        exact (Subgroup.mem_center_iff.mp hu v).symm
      exact huv this
  · intro l hl
    let l' : ↥Lc := ⟨l, hl⟩
    have hl'mem : φ l' ∈ N.map φ := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hnN, hnφ⟩ := Subgroup.mem_map.mp hl'mem
    have hnP : (n : Y) ∈ P := Subgroup.mem_subgroupOf.mp hnN
    have hm1 : φ (n⁻¹ * l') = 1 := by
      rw [map_mul, map_inv, hnφ, inv_mul_cancel]
    have hmK : ((n⁻¹ * l' : ↥Lc) : Y) ∈ Kk := (hφk (n⁻¹ * l')).mp hm1
    have hmP : ((n⁻¹ * l' : ↥Lc) : Y) ∈ P := hKP hmK
    have hl_eq : l = (n : Y) * ((n⁻¹ * l' : ↥Lc) : Y) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, l', Subtype.coe_mk]
      group
    rw [hl_eq]
    exact P.mul_mem hnP hmP

end CFSG.LocalAnalysis.WeakClosure81

end
