module

public import CFSG.Walter.Bender1970.S2.Basic

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem le_centralizer_of_mk_eq_one {E : Subgroup X} {a k : X} (hk : k ∈ E)
    (hak : ∀ x ∈ E, a * x * a⁻¹ = k * x * k⁻¹)
    (h1 : ((⟨k, hk⟩ : E) : E ⧸ Subgroup.center E) = 1) :
    E ≤ Subgroup.centralizer ({a} : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hkZ : (⟨k, hk⟩ : E) ∈ Subgroup.center E := (QuotientGroup.eq_one_iff _).mp h1
  have hc : k * x = x * k :=
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hkZ ⟨x, hx⟩).symm)
  have h2 : a * x * a⁻¹ = x := by rw [hak x hx, hc, mul_inv_cancel_right]
  calc x * a = (a * x * a⁻¹) * a := by rw [h2]
    _ = a * x := by group

theorem mk_sq_eq_one_of_inner {E : Subgroup X} {a k : X} (ha : a * a = 1) (hk : k ∈ E)
    (hak : ∀ x ∈ E, a * x * a⁻¹ = k * x * k⁻¹) :
    ((⟨k, hk⟩ : E) : E ⧸ Subgroup.center E) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hm : a * (y : X) * a⁻¹ ∈ E := by
    rw [hak y y.2]
    exact E.mul_mem (E.mul_mem hk y.2) (E.inv_mem hk)
  have h1 : k * (k * (y : X) * k⁻¹) * k⁻¹ = y := by
    rw [← hak y y.2, ← hak _ hm]
    calc a * (a * (y : X) * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ := by group
      _ = y := by rw [ha]; group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, SubgroupClass.coe_pow, pow_two]
  calc (y : X) * (k * k) = (k * (k * (y : X) * k⁻¹) * k⁻¹) * (k * k) := by rw [h1]
    _ = k * k * y := by group

theorem orderOf_mk_eq_two_of_inner {E : Subgroup X} {a k : X} (ha : a * a = 1) (hk : k ∈ E)
    (hak : ∀ x ∈ E, a * x * a⁻¹ = k * x * k⁻¹) (hE : ¬ E ≤ Subgroup.centralizer ({a} : Set X)) :
    orderOf ((⟨k, hk⟩ : E) : E ⧸ Subgroup.center E) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (mk_sq_eq_one_of_inner ha hk hak)
    (fun h1 => hE (le_centralizer_of_mk_eq_one hk hak h1))

section Lift

theorem mem_centralizer_iff_of_inner {E : Subgroup X} (hZ : Odd (Nat.card (Subgroup.center E)))
    {a k : X} (ha : a * a = 1) (hk : k ∈ E) (hak : ∀ x ∈ E, a * x * a⁻¹ = k * x * k⁻¹) (x : E) :
    (x : X) ∈ Subgroup.centralizer ({a} : Set X) ↔
      ((x : E) : E ⧸ Subgroup.center E) ∈ Subgroup.centralizer
        ({((⟨k, hk⟩ : E) : E ⧸ Subgroup.center E)} : Set (E ⧸ Subgroup.center E)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hax := hak x x.2
  constructor
  · intro h
    have h1 : k * x * k⁻¹ = x := by
      rw [← hax]
      calc a * (x : X) * a⁻¹ = x * a * a⁻¹ := by rw [h]
        _ = x := by group
    have h2 : (x : X) * k = k * x := by
      calc (x : X) * k = (k * x * k⁻¹) * k := by rw [h1]
        _ = k * x := by group
    have h3 : (x * ⟨k, hk⟩ : E) = ⟨k, hk⟩ * x := Subtype.ext h2
    rw [h3, inv_mul_cancel]
    exact one_mem _
  · intro h
    set w : E := (x * ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ * x) with hw
    have hwc : ∀ y : E, y * w = w * y := Subgroup.mem_center_iff.mp h
    have hkx : k * (x : X) * k⁻¹ = x * w := by
      have h1 : (⟨k, hk⟩ : E) * x = x * ⟨k, hk⟩ * w := by rw [hw]; group
      have h2 : (⟨k, hk⟩ : E) * w = w * ⟨k, hk⟩ := hwc _
      have h3 : (⟨k, hk⟩ : E) * x * (⟨k, hk⟩ : E)⁻¹ = x * w := by
        calc (⟨k, hk⟩ : E) * x * (⟨k, hk⟩ : E)⁻¹ = x * (⟨k, hk⟩ * w) * (⟨k, hk⟩ : E)⁻¹ := by
              rw [h1]; group
          _ = x * (w * ⟨k, hk⟩) * (⟨k, hk⟩ : E)⁻¹ := by rw [h2]
          _ = x * w := by group
      exact congrArg Subtype.val h3
    have haw : a * (w : X) * a⁻¹ = w := by
      rw [hak w w.2]
      have h2 : k * (w : X) = w * k := congrArg Subtype.val (hwc ⟨k, hk⟩)
      rw [h2, mul_inv_cancel_right]
    have hax' : a * (x : X) * a⁻¹ = x * w := hax.trans hkx
    have hww : w * w = 1 := by
      have h1 : (x : X) * 1 = x * (w * w) := by
        calc (x : X) * 1 = (a * a) * x * (a * a)⁻¹ := by rw [ha]; group
          _ = a * (a * x * a⁻¹) * a⁻¹ := by group
          _ = a * (x * w) * a⁻¹ := by rw [hax']
          _ = (a * x * a⁻¹) * (a * w * a⁻¹) := by group
          _ = x * (w * w) := by rw [hax', haw]; group
      have h2 : (1 : X) = w * w := mul_left_cancel h1
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← h2, Subgroup.coe_one])
    have hw1 : w = 1 := by
      have hdvd : orderOf (⟨w, h⟩ : Subgroup.center E) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [pow_two]; exact hww))
      have hodd : orderOf (⟨w, h⟩ : Subgroup.center E) ∣ Nat.card (Subgroup.center E) :=
        orderOf_dvd_natCard _
      have h1 : orderOf (⟨w, h⟩ : Subgroup.center E) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd
          (Nat.coprime_two_left.mpr hZ)) hodd
      have := orderOf_eq_one_iff.mp h1
      exact congrArg Subtype.val this
    have hkx' : k * (x : X) * k⁻¹ = x := by
      rw [hkx, hw1, Subgroup.coe_one, mul_one]
    calc (x : X) * a = (a * x * a⁻¹) * a := by rw [hax, hkx']
      _ = a * x := by group

theorem eq_top_of_sup_center_eq_top {G : Type*} [Group G] (hG : commutator G = ⊤)
    {M : Subgroup G} (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  rw [commutatorElement_mul_left_of_commute' (Subgroup.mem_center_iff.mp hz _).symm,
    commutatorElement_mul_right_of_commute' (Subgroup.mem_center_iff.mp hz' _).symm,
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

end Lift

end CFSG.Walter
