module

public import CFSG.Quasithin.Vol2.GoldschmidtE217DihOdd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_comm_mem {Q U : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (Q : Set G))
    (h : ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ Q) (k : ℕ) :
    ∀ u ∈ U, a ^ k * u * (a ^ k)⁻¹ * u⁻¹ ∈ Q := by
  induction k with
  | zero => intro u _; simp
  | succ k ih =>
    intro u hu
    have h3 : a * (a ^ k * u * (a ^ k)⁻¹ * u⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp ha _).mp (ih u hu)
    have e : a ^ (k + 1) * u * (a ^ (k + 1))⁻¹ * u⁻¹ =
        (a * (a ^ k * u * (a ^ k)⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹ * u⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact Q.mul_mem h3 (h u hu)

theorem cube_mem_kerIn_of_odd {H T M V U : Subgroup G} (hyp : Hyp28 H T M V) (hchar : CharTwo H)
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H))
    (hUV : U ≤ V) (hVQU : V ⊓ pCoreOf 2 H ≤ U) {x : G} (hxV : x ∈ V) (hxU : x ∉ U)
    (hU2 : ∀ v ∈ V, v ∈ U ∨ x * v ∈ U) {g : G} (hg : g ∈ H)
    (hUy : ∀ u ∈ U, (x * (g * x * g⁻¹)) * u * (x * (g * x * g⁻¹))⁻¹ * u⁻¹ ∈ pCoreOf 2 H)
    {n : ℕ} (hn : Odd n) (hyn : (x * (g * x * g⁻¹)) ^ n ∈ kerIn M H) :
    (x * (g * x * g⁻¹)) ^ 3 ∈ kerIn M H := by
  set y := x * (g * x * g⁻¹) with hy
  have hx2 : x * x = 1 := by simpa [pow_two] using hyp.elem.2 x hxV
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hw2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hwi : (g * x * g⁻¹)⁻¹ = g * x * g⁻¹ := inv_eq_of_mul_eq_one_right hw2
  have hxy : x * y * x⁻¹ = y⁻¹ := by
    have e1 : x * y * x⁻¹ = g * x * g⁻¹ * x := by
      rw [hy, hxi]
      calc x * (x * (g * x * g⁻¹)) * x = (x * x) * (g * x * g⁻¹) * x := by group
        _ = g * x * g⁻¹ * x := by rw [hx2, one_mul]
    have e2 : y⁻¹ = g * x * g⁻¹ * x := by
      rw [hy, mul_inv_rev, hwi, hxi]
    rw [e1, e2]
  have hyH : y ∈ H := H.mul_mem (hyp.le_H hxV)
    (H.mul_mem (H.mul_mem hg (hyp.le_H hxV)) (H.inv_mem hg))
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hzord : orderOf (y ^ 2 ^ s) = t := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨t, hst⟩, hst,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hcube : (y ^ 3) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    by_cases ht1 : t = 1
    · have : y ^ 2 ^ s = 1 := by
        rw [← orderOf_eq_one_iff, hzord, ht1]
      rw [this, one_pow]
    · have hz1 : y ^ 2 ^ s ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hzord
        exact ht1 hzord.symm
      have hzH : y ^ 2 ^ s ∈ H := H.pow_mem hyH _
      have hxz : x * y ^ 2 ^ s * x⁻¹ = (y ^ 2 ^ s)⁻¹ :=
        conj_eq_inv_of_mem_zpowers hxy (Subgroup.npow_mem_zpowers y _)
      have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
        le_normalizer_pCoreOf 2 H hyH
      have hmin := hyp.minParabolic
      have d : DihedralPair H T V U x (y ^ 2 ^ s) :=
        ⟨hmin.isSylow.2.1, hmin.isSylow.1, B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow, hchar,
          hyp.le_T, hyp.normal_T, hyp.elem, hUV, hVQU, hxV, hxU, hU2, hzH,
          by rw [hzord]; exact ht, hz1, hxz, pow_comm_mem hyN hUy _⟩
      have h3 := d.orderOf_eq_three_of_odd hV16 hq
      rw [← pow_orderOf_eq_one (y ^ 2 ^ s), h3]
  have hord : orderOf (y ^ 3) ∣ 2 ^ s := orderOf_dvd_of_pow_eq_one hcube
  have hcop : Nat.Coprime (orderOf (y ^ 3)) n :=
    Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hn))
  refine B6.mem_of_pow_mem_of_coprime ?_ hcop
  rw [← pow_mul, mul_comm, pow_mul]
  exact (kerIn M H).pow_mem hyn 3

omit [Finite G] in
theorem forall_mem_or_mul_mem_of_relIndex_eq_two {V Q : Subgroup G} (hV : IsElemAbelian 2 V)
    (h2 : (V ⊓ Q).relIndex V = 2) {x : G} (hxV : x ∈ V) (hxQ : x ∉ Q) :
    ∀ v ∈ V, v ∈ V ⊓ Q ∨ x * v ∈ V ⊓ Q := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
  intro v hv
  by_cases hvQ : v ∈ V ⊓ Q
  · exact Or.inl hvQ
  right
  have hxa : (⟨x, hxV⟩ : ↥V) * a ∈ (V ⊓ Q).subgroupOf V := by
    rcases ha ⟨x, hxV⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (Subgroup.mem_subgroupOf.1 h).2 hxQ
  have hva : (⟨v, hv⟩ : ↥V) * a ∈ (V ⊓ Q).subgroupOf V := by
    rcases ha ⟨v, hv⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (Subgroup.mem_subgroupOf.1 h : v ∈ V ⊓ Q) hvQ
  have h1 := ((V ⊓ Q).subgroupOf V).mul_mem hxa (((V ⊓ Q).subgroupOf V).inv_mem hva)
  rw [Subgroup.mem_subgroupOf] at h1
  have e : (((⟨x, hxV⟩ : ↥V) * a * ((⟨v, hv⟩ : ↥V) * a)⁻¹ : ↥V) : G) = x * v⁻¹ := by
    simp [mul_assoc]
  rw [e] at h1
  have hv2 : v * v = 1 := by simpa [pow_two] using hV.2 v hv
  rwa [inv_eq_of_mul_eq_one_right hv2] at h1

theorem cube_mem_kerIn_of_relIndex_eq_two {H T M V : Subgroup G} (hyp : Hyp28 H T M V)
    (hchar : CharTwo H) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H))
    (h2 : (V ⊓ pCoreOf 2 H).relIndex V = 2) {x : G} (hxV : x ∈ V) (hxQ : x ∉ pCoreOf 2 H)
    {g : G} (hg : g ∈ H) {n : ℕ} (hn : Odd n) (hyn : (x * (g * x * g⁻¹)) ^ n ∈ kerIn M H) :
    (x * (g * x * g⁻¹)) ^ 3 ∈ kerIn M H := by
  have hyH : x * (g * x * g⁻¹) ∈ H := H.mul_mem (hyp.le_H hxV)
    (H.mul_mem (H.mul_mem hg (hyp.le_H hxV)) (H.inv_mem hg))
  refine cube_mem_kerIn_of_odd (U := V ⊓ pCoreOf 2 H) hyp hchar hV16 hq inf_le_left le_rfl hxV
    (fun h => hxQ h.2) (forall_mem_or_mul_mem_of_relIndex_eq_two hyp.elem h2 hxV hxQ) hg
    (fun u hu => ?_) hn hyn
  have hyN := le_normalizer_pCoreOf 2 H hyH
  exact (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN u).mp hu.2)
    ((pCoreOf 2 H).inv_mem hu.2)

end E2

end CFSG.Quasithin
