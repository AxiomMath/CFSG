module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G] {H V : Subgroup G} {t v : G}

theorem isElemAbelian_two_of_le {A B : Subgroup G} (hA : IsElemAbelian 2 A) (hBA : B ≤ A) :
    IsElemAbelian 2 B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem conjClosure_zpowers_le (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) :
    conjClosure (Subgroup.zpowers v) H ≤ V :=
  conjClosure_le fun _ hh _ hz =>
    (Subgroup.mem_normalizer_iff.mp (hHV hh) _).mp ((Subgroup.zpowers_le.mpr hv) hz)

theorem conj_mem_centralizer_of_mem {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

@[expose] def actTriv (H V U : Subgroup G) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) : Subgroup G where
  carrier := {k | k ∈ H ∧ ∀ x ∈ V, k * x * k⁻¹ * x⁻¹ ∈ U}
  one_mem' := ⟨H.one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨H.mul_mem ha hb, fun x hx => ?_⟩
    have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHU ha) _).mp (hB x hx)
    have := U.mul_mem h1 (hA x hx)
    convert this using 1
    group
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨H.inv_mem ha, fun x hx => ?_⟩
    have hy : a⁻¹ * x * a⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hHV (H.inv_mem ha)) x).mp hx
    have := U.inv_mem (hA _ hy)
    convert this using 1
    group

theorem conj_mem_actTriv {U : Subgroup G} {hHV : H ≤ Subgroup.normalizer (V : Set G)}
    {hHU : H ≤ Subgroup.normalizer (U : Set G)} {h k : G} (hh : h ∈ H)
    (hk : k ∈ actTriv H V U hHV hHU) : h * k * h⁻¹ ∈ actTriv H V U hHV hHU := by
  obtain ⟨hkH, hk⟩ := hk
  refine ⟨H.mul_mem (H.mul_mem hh hkH) (H.inv_mem hh), fun x hx => ?_⟩
  have hy : h⁻¹ * x * h⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hHV (H.inv_mem hh)) x).mp hx
  have := (Subgroup.mem_normalizer_iff.mp (hHU hh) _).mp (hk _ hy)
  convert this using 1
  group

theorem conjClosure_le_actTriv (hV : IsElemAbelian 2 V) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (htH : t ∈ H) (hv : v ∈ V) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v) :
    conjClosure (Subgroup.zpowers t) H ≤
      actTriv H V (conjClosure (Subgroup.zpowers v) H) hHV (le_normalizer_conjClosure _ H) := by
  have ht : t ∈ actTriv H V (conjClosure (Subgroup.zpowers v) H) hHV
      (le_normalizer_conjClosure _ H) := by
    refine ⟨htH, fun x hx => ?_⟩
    rcases htr x hx with h | h
    · rw [h, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h]
      have : IsMulCommutative ↥V := hV.1
      have hxv : x * v = v * x := setLike_mul_comm hx hv
      rw [hxv, mul_inv_cancel_right]
      exact le_conjClosure _ H (Subgroup.mem_zpowers v)
  refine conjClosure_le fun h hh z hz => conj_mem_actTriv hh ?_
  exact (Subgroup.zpowers_le.mpr ht) hz

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
