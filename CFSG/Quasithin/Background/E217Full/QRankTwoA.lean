module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

private theorem mem_fixV_zpowers_iff' {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h x hx
    have : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut V) v := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hx

private theorem comm_apply' {z x : MulAut V} (hxz : x * z = z * x) (u : V) :
    x (z u) = z (x u) := by
  have h := DFunLike.congr_fun hxz u
  rwa [MulAut.mul_apply, MulAut.mul_apply] at h

private theorem zz_apply' {z : MulAut V} (hz : z * z = 1) (u : V) : z (z u) = u := by
  have h := DFunLike.congr_fun hz u
  rwa [MulAut.mul_apply, MulAut.one_apply] at h

private theorem inv_self' (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v := by
  have := hV v
  rw [pow_two, mul_eq_one_iff_eq_inv] at this
  exact this.symm

private theorem cancel_aux {p q r s : V} (h : p * q⁻¹ = r * s⁻¹) : p * r⁻¹ = q * s⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul] at h ⊢
  rw [h]
  ac_rfl

theorem fixV_zpowers_invariant {z x : MulAut V} (hxz : x * z = z * x) {w : V}
    (hw : w ∈ fixV (Subgroup.zpowers z)) : x w ∈ fixV (Subgroup.zpowers z) := by
  rw [mem_fixV_zpowers_iff'] at hw ⊢
  rw [← comm_apply' hxz w, hw]

theorem commutator_mem_of_fix (hV : ∀ v : V, v ^ 2 = 1) {z x : MulAut V} (hz : z * z = 1)
    (hxz : x * z = z * x) (hx : x ∈ centSub (fixV (Subgroup.zpowers z))) (v : V) :
    x v * v⁻¹ ∈ fixV (Subgroup.zpowers z) := by
  have hb : z v * v⁻¹ ∈ fixV (Subgroup.zpowers z) := by
    rw [mem_fixV_zpowers_iff', map_mul, map_inv, zz_apply' hz, inv_self' hV (z v),
      inv_self' hV v, mul_comm]
  have hxb : x (z v * v⁻¹) = z v * v⁻¹ := mem_centSub.1 hx _ hb
  have h1 : x (z v) * (x v)⁻¹ = z v * v⁻¹ := by
    rw [← hxb, map_mul, map_inv]
  rw [mem_fixV_zpowers_iff', map_mul, map_inv, ← comm_apply' hxz v]
  exact cancel_aux h1

theorem isElemAbelian2_inf_centSub (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {z : MulAut V} (hz : z * z = 1) (hzc : ∀ x ∈ X, x * z = z * x) :
    IsElemAbelian2 (X ⊓ centSub (fixV (Subgroup.zpowers z))) := by
  unfold IsElemAbelian2
  have hmem : ∀ a ∈ X ⊓ centSub (fixV (Subgroup.zpowers z)),
      a * z = z * a ∧ a ∈ centSub (fixV (Subgroup.zpowers z)) := by
    intro a ha
    exact ⟨hzc a (Subgroup.mem_inf.1 ha).1, (Subgroup.mem_inf.1 ha).2⟩
  have hcomm : ∀ x ∈ X ⊓ centSub (fixV (Subgroup.zpowers z)),
      ∀ y ∈ X ⊓ centSub (fixV (Subgroup.zpowers z)), ∀ v : V, x (y v) = y (x v) := by
    intro x hxA y hyA v
    obtain ⟨hxz, hxC⟩ := hmem x hxA
    obtain ⟨hyz, hyC⟩ := hmem y hyA
    have ha := commutator_mem_of_fix hV hz hxz hxC v
    have hb := commutator_mem_of_fix hV hz hyz hyC v
    have hxb : x (y v * v⁻¹) = y v * v⁻¹ := mem_centSub.1 hxC _ hb
    have hya : y (x v * v⁻¹) = x v * v⁻¹ := mem_centSub.1 hyC _ ha
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul] at hxb hya
    rw [hxb, hya]
    ac_rfl
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · ext v
    exact hcomm a ha b hb v
  · obtain ⟨haz, haC⟩ := hmem a ha
    rw [pow_two]
    ext v
    show a (a v) = v
    have hc := commutator_mem_of_fix hV hz haz haC v
    have h2 : a (a v * v⁻¹) = a v * v⁻¹ := mem_centSub.1 haC _ hc
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h2
    have hsq : a v * a v = 1 := by
      rw [← pow_two]
      exact hV _
    rw [h2, inv_self' hV v]
    calc a v * v * a v = (a v * a v) * v := by ac_rfl
      _ = v := by rw [hsq, one_mul]

theorem commSeries_inf_centSub_three (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {z : MulAut V} (hz : z * z = 1) (hzc : ∀ x ∈ X, x * z = z * x) :
    commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 3 = ⊥ := by
  have hWfix : fixV (Subgroup.zpowers z) ≤ fixV (X ⊓ centSub (fixV (Subgroup.zpowers z))) :=
    fun w hw a ha => mem_centSub.1 (Subgroup.mem_inf.1 ha).2 w hw
  have h1 : commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 1 ≤
      fixV (Subgroup.zpowers z) := by
    rw [commSeries_one]
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact commutator_mem_of_fix hV hz (hzc x (Subgroup.mem_inf.1 hx).1)
      (Subgroup.mem_inf.1 hx).2 v
  have h2 : commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 2 = ⊥ := by
    have e : commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 2 =
        commSub (commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 1)
          (X ⊓ centSub (fixV (Subgroup.zpowers z))) := rfl
    rw [e, eq_bot_iff]
    refine (commSub_mono h1 le_rfl).trans ?_
    rw [commSub_eq_bot_iff.2 hWfix]
  have e3 : commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 3 =
      commSub (commSeries (X ⊓ centSub (fixV (Subgroup.zpowers z))) 2)
        (X ⊓ centSub (fixV (Subgroup.zpowers z))) := rfl
  rw [e3, h2, commSub_eq_bot_iff]
  exact bot_le

end CFSG.Quasithin.E217Full.LemmaQ
