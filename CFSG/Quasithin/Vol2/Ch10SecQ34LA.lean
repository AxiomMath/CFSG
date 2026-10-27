module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

variable {G : Type*} [Group G]

@[expose] noncomputable def conjAutOf {U : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (U : Set G)) : MulAut ↥U where
  toFun u := ⟨a * u * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha u).mp u.2⟩
  invFun u := ⟨a⁻¹ * u * a, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) u).mp u.2
    simpa using this⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjAutOf_apply {U : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (U : Set G))
    (u : ↥U) : ((conjAutOf ha u : ↥U) : G) = a * u * a⁻¹ := rfl

theorem conjAutOf_pow_apply {U : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (U : Set G)) (n : ℕ) (u : ↥U) :
    (((conjAutOf ha ^ n) u : ↥U) : G) = a ^ n * u * (a ^ n)⁻¹ := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    show a * (((conjAutOf ha ^ n) u : ↥U) : G) * a⁻¹ = _
    rw [ih, pow_succ']
    group

theorem mem_centralizer_of_cyclic {U : Subgroup G} [Finite U] (hc : IsCyclic U)
    (h2 : IsPGroup 2 U) {a : G} (ha : a ∈ Subgroup.normalizer (U : Set G))
    (hodd : Odd (orderOf a)) : a ∈ Subgroup.centralizer (U : Set G) := by
  set φ := conjAutOf ha with hφ
  have hφk : φ ^ orderOf a = 1 := by
    ext u
    rw [conjAutOf_pow_apply, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hodd' : Odd (orderOf φ) := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hφk)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hcard : Nat.card (MulAut ↥U) ∣ 2 ^ r := by
    rw [IsCyclic.card_mulAut, hr]
    rcases r with _ | r
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos r), Nat.succ_sub_one,
        show (2 : ℕ) - 1 = 1 from rfl, mul_one]
      exact Nat.pow_dvd_pow 2 (Nat.le_succ r)
  have hdvd : orderOf φ ∣ 2 ^ r := (orderOf_dvd_natCard φ).trans hcard
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra h
    rw [hj] at hodd'
    exact Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, h⟩) hodd'
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have := congrArg (fun f : MulAut ↥U => ((f ⟨u, hu⟩ : ↥U) : G)) hj
  simp only [hφ, MulAut.one_apply] at this
  have h' : a * u * a⁻¹ = u := this
  calc u * a = a * u * a⁻¹ * a := by rw [h']
    _ = a * u := by group

theorem mem_centralizer_of_index_two {S U : Subgroup G} (h2 : IsPGroup 2 S)
    (hidx : U.relIndex S = 2) {a : G} (haS : a ∈ Subgroup.normalizer (S : Set G))
    (haU : a ∈ Subgroup.centralizer (U : Set G)) (hodd : Odd (orderOf a)) :
    a ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hidx' : (U.subgroupOf S).index = 2 := hidx
  have haU' : ∀ w ∈ U, a * w * a⁻¹ = w := fun w hw => by
    have := Subgroup.mem_centralizer_iff.mp haU w hw
    rw [← this]; group
  have havS : a * v * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp haS v).mp hv
  have hw : (a * v * a⁻¹) * v⁻¹ ∈ U := by
    by_cases hvU : v ∈ U
    · rw [haU' v hvU, mul_inv_cancel]; exact U.one_mem
    · have hav : a * v * a⁻¹ ∉ U := by
        intro h
        apply hvU
        have e : v = a⁻¹ * (a * v * a⁻¹) * a := by group
        have hx := Subgroup.mem_centralizer_iff.mp haU _ h
        have e2 : a⁻¹ * (a * v * a⁻¹) * a = a * v * a⁻¹ := by
          calc a⁻¹ * (a * v * a⁻¹) * a = a⁻¹ * ((a * v * a⁻¹) * a) := by group
            _ = a⁻¹ * (a * (a * v * a⁻¹)) := by rw [hx]
            _ = a * v * a⁻¹ := by group
        rw [e, e2]
        exact h
      have key := (Subgroup.mul_mem_iff_of_index_two hidx'
        (a := ⟨a * v * a⁻¹, havS⟩) (b := (⟨v, hv⟩ : ↥S)⁻¹)).mpr
      have h1 : (⟨a * v * a⁻¹, havS⟩ : ↥S) ∉ U.subgroupOf S := hav
      have h2' : (⟨v, hv⟩ : ↥S)⁻¹ ∉ U.subgroupOf S := by
        rw [Subgroup.inv_mem_iff]; exact hvU
      exact key (iff_of_false h1 h2')
  set w := (a * v * a⁻¹) * v⁻¹ with hwdef
  have hav : a * v * a⁻¹ = w * v := by rw [hwdef]; group
  have hpow : ∀ n : ℕ, a ^ n * v * (a ^ n)⁻¹ = w ^ n * v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * v * (a ^ (n + 1))⁻¹ = a * (a ^ n * v * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * (w ^ n * v) * a⁻¹ := by rw [ih]
        _ = (a * w ^ n * a⁻¹) * (a * v * a⁻¹) := by group
        _ = w ^ n * (w * v) := by rw [haU' _ (U.pow_mem hw n), hav]
        _ = w ^ (n + 1) * v := by group
  have h1 := hpow (orderOf a)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hwk : w ^ orderOf a = 1 := by
    have := congrArg (fun x => x * v⁻¹) h1
    simpa using this.symm
  have hwS : w ∈ S := S.mul_mem havS (S.inv_mem hv)
  obtain ⟨j, hj⟩ := h2 ⟨w, hwS⟩
  have hj' : w ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hw1 : w = 1 := by
    have hd1 := orderOf_dvd_of_pow_eq_one hwk
    have hd2 := orderOf_dvd_of_pow_eq_one hj'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hi0 : i = 0 := by
      by_contra h
      have hodd' : Odd (orderOf w) := hodd.of_dvd_nat hd1
      rw [hi] at hodd'
      exact Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, h⟩) hodd'
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  rw [hw1, one_mul] at hav
  calc v * a = a * v * a⁻¹ * a := by rw [hav]
    _ = a * v := by group

theorem mem_centralizer_of_dihedral {S : Subgroup G} [Finite S] {n : ℕ} (hn : 4 ≤ n)
    (e : ↥S ≃* DihedralGroup n) (h2 : IsPGroup 2 S) {a : G}
    (ha : a ∈ Subgroup.normalizer (S : Set G)) (hodd : Odd (orderOf a)) :
    a ∈ Subgroup.centralizer (S : Set G) := by
  have : NeZero n := ⟨by omega⟩
  set u : ↥S := e.symm (DihedralGroup.r 1) with hu
  set U : Subgroup G := Subgroup.zpowers (u : G) with hU
  have hUS : U ≤ S := (Subgroup.zpowers_le).mpr u.2
  have hou : orderOf (u : G) = n := by
    rw [Subgroup.orderOf_coe, hu, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have key : ∀ x : ↥S, 2 < orderOf x → (x : G) ∈ U := by
    intro x hx
    rcases hex : e x with i | i
    · have : x = u ^ i.val := by
        apply e.injective
        rw [hex, map_pow, hu, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow,
          ZMod.natCast_zmod_val]
      rw [this, Subgroup.coe_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · exfalso
      have h1 : orderOf x = 2 := by
        rw [← MulEquiv.orderOf_eq e, hex, DihedralGroup.orderOf_sr]
      omega
  have hconj : ∀ b : G, b ∈ Subgroup.normalizer (S : Set G) → b * u * b⁻¹ ∈ U := by
    intro b hb
    have hbS : b * u * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hb u).mp u.2
    have hord : orderOf (⟨b * u * b⁻¹, hbS⟩ : ↥S) = n := by
      rw [Subgroup.orderOf_mk, ← hou, show b * (u : G) * b⁻¹ = MulAut.conj b (u : G) from rfl,
        MulEquiv.orderOf_eq]
    exact key ⟨_, hbS⟩ (by omega)
  have hU_le : ∀ b : G, b ∈ Subgroup.normalizer (S : Set G) → ∀ g ∈ U, b * g * b⁻¹ ∈ U := by
    intro b hb g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : b * (u : G) ^ k * b⁻¹ = (b * u * b⁻¹) ^ k := by
      rw [conj_zpow]
    rw [this]
    exact U.zpow_mem (hconj b hb) k
  have haU : a ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hU_le a ha g, fun h => ?_⟩
    have := hU_le a⁻¹ (Subgroup.inv_mem _ ha) _ h
    simpa [mul_assoc] using this
  have hUfin : Finite ↥U := Finite.of_injective _ (Subgroup.inclusion_injective hUS)
  have hUc := mem_centralizer_of_cyclic (U := U) inferInstance (h2.to_le hUS) haU hodd
  have hidx : U.relIndex S = 2 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, Nat.card_zpowers, hou,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h1
    have hn0 : 0 < n := by omega
    exact Nat.eq_of_mul_eq_mul_left hn0 (by
      show n * (U.subgroupOf S).index = n * 2
      rw [h1, mul_comm])
  exact mem_centralizer_of_index_two h2 hidx ha hUc hodd

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
