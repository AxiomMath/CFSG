module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.Quasithin.H13.U43

section Sylow

variable {K : Type} [Group K] [Finite K]

theorem u43_exists_sylow_eq {p : ℕ} [Fact p.Prime] {Y : Subgroup K} (hY : IsPGroup p Y)
    (h : ∀ x ∈ Subgroup.normalizer (Y : Set K), IsPGroup p (Subgroup.zpowers x) → x ∈ Y) :
    ∃ P : Sylow p K, (P : Subgroup K) = Y := by
  obtain ⟨P, hP⟩ := hY.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  by_contra hnot
  have hIlt : Y.subgroupOf (P : Subgroup K) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hnot ?_)
    intro y hy
    have : (⟨y, hy⟩ : ↥(P : Subgroup K)) ∈ Y.subgroupOf (P : Subgroup K) := by
      rw [htop]
      trivial
    exact this
  have : Group.IsNilpotent ↥(P : Subgroup K) := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(P : Subgroup K) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup K))
  obtain ⟨x, hxN, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hIlt)
  have hxNorm : (x : K) ∈ Subgroup.normalizer (Y : Set K) := by
    have : x ∈ (Subgroup.normalizer (Y : Set K)).subgroupOf (P : Subgroup K) := by
      rw [Subgroup.subgroupOf_normalizer_eq hP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp this
  have hxY : (x : K) ∉ Y := fun hx => hxn (Subgroup.mem_subgroupOf.mpr hx)
  have hpg : IsPGroup p (Subgroup.zpowers (x : K)) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.mpr x.2)
  exact hxY (h _ hxNorm hpg)

theorem u43_frattini_quaternion (P : Sylow 2 K)
    (hP : Nonempty ((P : Subgroup K) ≃* QuaternionGroup 2)) {z : K}
    (hzP : z ∈ (P : Subgroup K)) (hz : orderOf z = 2) (g : K) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set K), ∃ k ∈ CFSG.oddCore K, g = c * k := by
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz])
  have hP' : Nonempty ((P : Subgroup K) ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    simpa using hP
  have hcen := CFSG.BrauerSuzuki.brauer_suzuki 3 le_rfl P hP' z hzP hz
  exact CFSG.Adapters.eq_centralizer_mul_oddCore hzz hcen g

end Sylow

section Fpf

variable {C : Type} [Group C]

theorem u43_inverts_of_fpf [Finite C] {Y : Subgroup C} {u : C} (hu : u ^ 2 = 1)
    (hY : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) (hf : ∀ y ∈ Y, u * y = y * u → y = 1) :
    ∀ y ∈ Y, u * y * u⁻¹ = y⁻¹ := by
  classical
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  let φ : Y → Y := fun y => ⟨(y : C)⁻¹ * (u * y * u⁻¹), Y.mul_mem (Y.inv_mem y.2) (hY y y.2)⟩
  have hinj : Function.Injective φ := by
    intro y y' h
    have h' : (y : C)⁻¹ * (u * y * u⁻¹) = (y' : C)⁻¹ * (u * y' * u⁻¹) := congrArg Subtype.val h
    have h1 : (y' : C) * (y : C)⁻¹ = u * ((y' : C) * (y : C)⁻¹) * u⁻¹ := by
      have h2 : (y' : C) * ((y : C)⁻¹ * (u * y * u⁻¹)) = u * y' * u⁻¹ := by rw [h']; group
      calc (y' : C) * (y : C)⁻¹
          = ((y' : C) * ((y : C)⁻¹ * (u * y * u⁻¹))) * (u * y * u⁻¹)⁻¹ := by group
        _ = (u * y' * u⁻¹) * (u * y * u⁻¹)⁻¹ := by rw [h2]
        _ = u * ((y' : C) * (y : C)⁻¹) * u⁻¹ := by group
    have hwY : (y' : C) * (y : C)⁻¹ ∈ Y := Y.mul_mem y'.2 (Y.inv_mem y.2)
    have hw := hf _ hwY (by
      calc u * ((y' : C) * (y : C)⁻¹) = (u * ((y' : C) * (y : C)⁻¹) * u⁻¹) * u := by group
        _ = ((y' : C) * (y : C)⁻¹) * u := by rw [← h1])
    have : (y' : C) = y := by
      calc (y' : C) = ((y' : C) * (y : C)⁻¹) * y := by group
        _ = y := by rw [hw]; group
    exact Subtype.ext this.symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨y, hy⟩ := hsurj ⟨w, hw⟩
  have hwy : w = (y : C)⁻¹ * (u * y * u⁻¹) := (congrArg Subtype.val hy).symm
  have hu2 : u⁻¹ * u⁻¹ = 1 := by rw [hui]; rwa [← pow_two]
  rw [hwy]
  calc u * ((y : C)⁻¹ * (u * y * u⁻¹)) * u⁻¹
      = u * (y : C)⁻¹ * u * y * (u⁻¹ * u⁻¹) := by group
    _ = u * (y : C)⁻¹ * u * y := by rw [hu2]; group
    _ = u * (y : C)⁻¹ * u⁻¹ * y := by rw [hui]
    _ = ((y : C)⁻¹ * (u * y * u⁻¹))⁻¹ := by group

theorem u43_commutator_mem [Finite C] (N V : Subgroup C) [N.Normal] {z : C} (hz : z * z = 1)
    (hV : ∀ y ∈ V, z * y * z⁻¹ ∈ V)
    (hf : ∀ y ∈ V, z * y * z⁻¹ * y⁻¹ ∈ N → y ∈ N) :
    (∀ y ∈ V, z * y * z⁻¹ * y ∈ N) ∧ ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y⁻¹ * x * y ∈ N := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set V' : Subgroup (C ⧸ N) := V.map π with hV'
  have hu2 : (π z) ^ 2 = 1 := by rw [pow_two, ← map_mul, hz, map_one]
  have hY : ∀ y ∈ V', (π z) * y * (π z)⁻¹ ∈ V' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨z * y * z⁻¹, hV y hy, by simp⟩
  have hF : ∀ y ∈ V', (π z) * y = y * (π z) → y = 1 := by
    rintro _ ⟨y, hy, rfl⟩ hc
    have e1 : π (z * y * z⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hyN : y ∈ N := hf y hy ((QuotientGroup.eq_one_iff _).mp e1)
    exact (QuotientGroup.eq_one_iff y).mpr hyN
  have key := u43_inverts_of_fpf hu2 hY hF
  refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
  · have h1 := key (π y) ⟨y, hy, rfl⟩
    have e1 : π (z * y * z⁻¹ * y) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, h1]
      group
    exact (QuotientGroup.eq_one_iff _).mp e1
  · have ha := key (π x) ⟨x, hx, rfl⟩
    have hb := key (π y) ⟨y, hy, rfl⟩
    have hab := key (π (x * y)) ⟨x * y, mul_mem hx hy, rfl⟩
    rw [map_mul] at hab
    have e0 : (π z) * (π x * π y) * (π z)⁻¹ =
        ((π z) * π x * (π z)⁻¹) * ((π z) * π y * (π z)⁻¹) := by group
    rw [e0, ha, hb, mul_inv_rev] at hab
    have e1 : π (x⁻¹ * y⁻¹ * x * y) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (π x)⁻¹ * (π y)⁻¹ * π x * π y = ((π x)⁻¹ * (π y)⁻¹) * π x * π y := by group
        _ = ((π y)⁻¹ * (π x)⁻¹) * π x * π y := by rw [hab]
        _ = 1 := by group
    exact (QuotientGroup.eq_one_iff _).mp e1

end Fpf

section Four

theorem u43_eq_of_card_four {Q : Type} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) {a b : Q}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1) (q : Q) :
    q = 1 ∨ q = a ∨ q = b ∨ q = a * b := by
  classical
  have := Fintype.ofFinite Q
  have hcard : Fintype.card Q = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hQ
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have hb : b = a⁻¹ := by
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ := by rw [h, mul_one]
    rw [hb, hai]
  have hab2 : a ≠ a * b := by
    intro h
    apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ * a := by rw [← h]
      _ = 1 := by group
  have hab3 : b ≠ a * b := by
    intro h
    apply ha1
    calc a = (a * b) * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [← h]
      _ = 1 := by group
  have hS : ({1, a, b, a * b} : Finset Q) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]
    have h1 : (1 : Q) ∉ ({a, b, a * b} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have h2 : a ∉ ({b, a * b} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hab2⟩
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_pair hab3]
  have hq : q ∈ ({1, a, b, a * b} : Finset Q) := by
    rw [hS]
    exact Finset.mem_univ q
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hq

end Four

section Four4

theorem u43_pow_four {K : Type} [Group K] (g : K) : g ^ 4 = (g * g) * (g * g) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]

theorem u43_mem_zpowers_of_pow_four {K : Type} [Group K] {g : K} (h : g ^ 4 = 1) {x : K}
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g ∨ x = g * g ∨ x = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : g ^ (4 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact h
  have e : g ^ k = g ^ (k % 4) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 4, zpow_add, zpow_mul, h4, one_zpow, mul_one]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h1 | h2 | h3
  · left
    rw [e, h0]
    simp
  · right
    left
    rw [e, h1]
    simp
  · right
    right
    left
    rw [e, h2, zpow_two]
  · right
    right
    right
    rw [e, h3]
    have : g ^ (3 : ℤ) * g = 1 := by
      rw [← zpow_add_one]
      exact h4
    exact eq_inv_of_mul_eq_one_left this

end Four4

end CFSG.Quasithin.H13.U43
