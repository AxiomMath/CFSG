module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Core

public section

namespace CFSG.Quasithin.Fan86.Sigma3

abbrev oQ (H : Type*) [Group H] : Subgroup H := CFSG.Open.pCore 2 H

variable {H : Type*} [Group H] {S : Subgroup H}

def oneCenter (Q : Subgroup H) : Subgroup H where
  carrier := {e | e ∈ Q ∧ e * e = 1 ∧ ∀ q ∈ Q, e * q = q * e}
  one_mem' := ⟨Q.one_mem, by simp, fun q _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haQ, ha2, hac⟩ ⟨hbQ, hb2, hbc⟩
    refine ⟨Q.mul_mem haQ hbQ, ?_, fun q hq => ?_⟩
    · have hba : b * a = a * b := (hac b hbQ).symm
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · rw [mul_assoc, hbc q hq, ← mul_assoc, hac q hq, mul_assoc]
  inv_mem' := by
    rintro a ⟨haQ, ha2, hac⟩
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [this]
    exact ⟨haQ, ha2, hac⟩

theorem mem_oneCenter {Q : Subgroup H} {e : H} :
    e ∈ oneCenter Q ↔ e ∈ Q ∧ e * e = 1 ∧ ∀ q ∈ Q, e * q = q * e := Iff.rfl

theorem oneCenter_le {Q : Subgroup H} : oneCenter Q ≤ Q := fun _ he => he.1

theorem oneCenter_conj {Q : Subgroup H} (hQ : Q.Normal) {e : H} (he : e ∈ oneCenter Q) (g : H) :
    g * e * g⁻¹ ∈ oneCenter Q := by
  obtain ⟨heQ, he2, hec⟩ := he
  refine ⟨hQ.conj_mem e heQ g, ?_, fun q hq => ?_⟩
  · calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [he2]; group
  · have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q := hQ.conj_mem q hq g⁻¹
    have := hec _ hq'
    calc g * e * g⁻¹ * q = g * (e * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * e) * g⁻¹ := by rw [show g⁻¹ * q * g = g⁻¹ * q * g⁻¹⁻¹ by group, this]
      _ = q * (g * e * g⁻¹) := by group

def invCenterIn (S : Subgroup H) : Subgroup H where
  carrier := {z | z ∈ S ∧ z * z = 1 ∧ ∀ s ∈ S, z * s = s * z}
  one_mem' := ⟨S.one_mem, by simp, fun s _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haS, ha2, hac⟩ ⟨hbS, hb2, hbc⟩
    refine ⟨S.mul_mem haS hbS, ?_, fun s hs => ?_⟩
    · have hba : b * a = a * b := (hac b hbS).symm
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · rw [mul_assoc, hbc s hs, ← mul_assoc, hac s hs, mul_assoc]
  inv_mem' := by
    rintro a ⟨haS, ha2, hac⟩
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [this]
    exact ⟨haS, ha2, hac⟩

theorem mem_invCenterIn {z : H} :
    z ∈ invCenterIn S ↔ z ∈ S ∧ z * z = 1 ∧ ∀ s ∈ S, z * s = s * z := Iff.rfl

theorem invCenterIn_le : invCenterIn S ≤ S := fun _ hz => hz.1

theorem invCenterIn_char : ((invCenterIn S).subgroupOf S).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨-, hz2, hzc⟩ := Subgroup.mem_subgroupOf.1 hz
  have hz2' : z * z = 1 := Subtype.ext hz2
  have hcomm : ∀ w : ↥S, z * w = w * z := fun w => Subtype.ext (hzc w w.2)
  refine Subgroup.mem_subgroupOf.2 ⟨(φ z).2, ?_, fun s hs => ?_⟩
  · have : φ z * φ z = 1 := by rw [← map_mul, hz2', map_one]
    exact congrArg Subtype.val this
  · have h1 : φ z * φ (φ.symm ⟨s, hs⟩) = φ (φ.symm ⟨s, hs⟩) * φ z := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [φ.apply_symm_apply] at h1
    exact congrArg Subtype.val h1

theorem mul_mul_eq_one_of_orderOf {x : H} (hx : orderOf x = 3) : x * x * x = 1 := by
  have h := (hx ▸ pow_orderOf_eq_one x : x ^ 3 = 1)
  rwa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] at h

theorem x_central_of_inner [Finite H] {x q : H} (hx : orderOf x = 3) (hq : q ∈ oQ H)
    (h5 : ∀ y ∈ oQ H, x * y * x⁻¹ = q⁻¹ * y * q) : ∀ y ∈ oQ H, x * y = y * x := by
  have hQn : (oQ H).Normal := inferInstance
  have hx3 := mul_mul_eq_one_of_orderOf hx
  have hqQ : q⁻¹ ∈ oQ H := (oQ H).inv_mem hq
  have hq3 : ∀ y ∈ oQ H, q ^ 3 * y = y * q ^ 3 := by
    intro y hy
    have c1 := h5 y hy
    have c2 : x * (x * y * x⁻¹) * x⁻¹ = q⁻¹ * (q⁻¹ * y * q) * q := by
      rw [h5 _ (hQn.conj_mem y hy x), c1]
    have c3 : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = q⁻¹ * (q⁻¹ * (q⁻¹ * y * q) * q) * q := by
      rw [h5 _ (hQn.conj_mem _ (hQn.conj_mem y hy x) x), c2]
    have c4 : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = y := by
      calc x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * y * (x * x * x)⁻¹ := by group
        _ = y := by rw [hx3]; group
    rw [c4] at c3
    have c5 := congrArg (fun w => q * q * q * w) c3
    calc q ^ 3 * y = q * q * q * y := by rw [pow_succ, pow_two]
      _ = q * q * q * (q⁻¹ * (q⁻¹ * (q⁻¹ * y * q) * q) * q) := c5
      _ = y * (q * q * q) := by group
      _ = y * q ^ 3 := by rw [pow_succ, pow_two]
  have hqord : orderOf q ∣ 2 ^ (Classical.choose ((oQ_two (H := H)) ⟨q, hq⟩)) := by
    have hk := Classical.choose_spec ((oQ_two (H := H)) ⟨q, hq⟩)
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hcop : Nat.Coprime 3 (orderOf q) :=
    Nat.Coprime.coprime_dvd_right hqord (Nat.Coprime.pow_right _ (by decide))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hqc : ∀ y ∈ oQ H, q * y = y * q := by
    intro y hy
    have : Commute (q ^ 3) y := hq3 y hy
    have h2 := (this.pow_left m)
    rwa [hm] at h2
  intro y hy
  have h6 := h5 y hy
  have h7 : q⁻¹ * y * q = y := by
    have := hqc y hy
    calc q⁻¹ * y * q = q⁻¹ * (y * q) := by group
      _ = q⁻¹ * (q * y) := by rw [this]
      _ = y := by group
  rw [h7] at h6
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h6]

theorem Sig3.central_mem_Q [Finite H] (h : Sig3 H S) {x : H} (hx : orderOf x = 3)
    (hnc : ¬ ∀ q ∈ oQ H, x * q = q * x) {z : H} (hz : z ∈ S)
    (hzc : ∀ s ∈ S, z * s = s * z) : z ∈ oQ H := by
  by_contra hzQ
  obtain ⟨q, hq, hqeq⟩ := h.inv_mod hx hz hzQ
  have hQn : (oQ H).Normal := inferInstance
  have hQS := h.Q_le_S
  have hx3 := mul_mul_eq_one_of_orderOf hx
  have hxx : x * x = x⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact hx3
  have hxi : x⁻¹ * x⁻¹ = x := by
    rw [← hxx]
    calc x * x * (x * x) = x * (x * x * x) := by group
      _ = x := by rw [hx3]; group
  have hz1 : ∀ y ∈ oQ H, z * y = y * z := fun y hy => hzc y (hQS hy)
  have h3 : ∀ y ∈ oQ H, x * y * x⁻¹ = q * x⁻¹ * y * x * q⁻¹ := by
    intro y hy
    have hy' : x * y * x⁻¹ ∈ oQ H := hQn.conj_mem y hy x
    have hzy : z⁻¹ * y * z = y := by
      have := hz1 y hy
      calc z⁻¹ * y * z = z⁻¹ * (y * z) := by group
        _ = z⁻¹ * (z * y) := by rw [this]
        _ = y := by group
    have e1 : (z * x * z⁻¹) * y * (z * x * z⁻¹)⁻¹ = x * y * x⁻¹ := by
      calc (z * x * z⁻¹) * y * (z * x * z⁻¹)⁻¹ = z * (x * (z⁻¹ * y * z) * x⁻¹) * z⁻¹ := by group
        _ = z * (x * y * x⁻¹) * z⁻¹ := by rw [hzy]
        _ = x * y * x⁻¹ := by
          have := hz1 _ hy'
          calc z * (x * y * x⁻¹) * z⁻¹ = (x * y * x⁻¹ * z) * z⁻¹ := by rw [this]
            _ = x * y * x⁻¹ := by group
    rw [hqeq] at e1
    rw [← e1]; group
  have h4 : ∀ y ∈ oQ H, x⁻¹ * y * x = q * y * q⁻¹ := by
    intro y hy
    have hy' : x * y * x⁻¹ ∈ oQ H := hQn.conj_mem y hy x
    have := h3 _ hy'
    have e : x * (x * y * x⁻¹) * x⁻¹ = x⁻¹ * y * x := by
      calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x⁻¹ * x⁻¹) := by group
        _ = x⁻¹ * y * x := by rw [hxx, hxi]
    rw [e] at this
    rw [this]; group
  have h5 : ∀ y ∈ oQ H, x * y * x⁻¹ = q⁻¹ * y * q := by
    intro y hy
    have hy' : x * y * x⁻¹ ∈ oQ H := hQn.conj_mem y hy x
    have := h4 _ hy'
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at this
    calc x * y * x⁻¹ = q⁻¹ * (q * (x * y * x⁻¹) * q⁻¹) * q := by group
      _ = q⁻¹ * y * q := by rw [← this]
  exact hnc (x_central_of_inner hx hq h5)

end CFSG.Quasithin.Fan86.Sigma3
