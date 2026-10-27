module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.L828Lift

private lemma lift_relIndex_sup_eq {N : Type*} [Group N] [Finite N] (T C : Subgroup N)
    [C.Normal] : T.relIndex (T ⊔ C) = T.relIndex C := by
  have hb : C.relIndex (T ⊔ C) = C.relIndex T := Subgroup.relIndex_sup_right (H := T) (K := C)
  have hA : C.relIndex T * Nat.card (C ⊓ T : Subgroup N) = Nat.card T :=
    Subgroup.relIndex_mul_card (H := C) (K := T)
  have hC : C.relIndex (T ⊔ C) * Nat.card C = Nat.card (T ⊔ C : Subgroup N) := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := T ⊔ C)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hD : T.relIndex (T ⊔ C) * Nat.card T = Nat.card (T ⊔ C : Subgroup N) := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := T ⊔ C)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hE : T.relIndex C * Nat.card (T ⊓ C : Subgroup N) = Nat.card C :=
    Subgroup.relIndex_mul_card (H := T) (K := C)
  have hpos : 0 < Nat.card (C ⊓ T : Subgroup N) := Nat.card_pos
  have hx : 0 < C.relIndex T := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hA
    exact absurd hA.symm (Nat.card_pos (α := T)).ne'
  have key : C.relIndex T * (T.relIndex (T ⊔ C) * Nat.card (C ⊓ T : Subgroup N))
      = C.relIndex T * Nat.card C := by
    calc C.relIndex T * (T.relIndex (T ⊔ C) * Nat.card (C ⊓ T : Subgroup N))
        = T.relIndex (T ⊔ C) * (C.relIndex T * Nat.card (C ⊓ T : Subgroup N)) := by ring
      _ = T.relIndex (T ⊔ C) * Nat.card T := by rw [hA]
      _ = Nat.card (T ⊔ C : Subgroup N) := hD
      _ = C.relIndex (T ⊔ C) * Nat.card C := hC.symm
      _ = C.relIndex T * Nat.card C := by rw [hb]
  have key2 := Nat.eq_of_mul_eq_mul_left hx key
  have hmn : Nat.card (C ⊓ T : Subgroup N) = Nat.card (T ⊓ C : Subgroup N) := by
    rw [inf_comm]
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [key2, hmn, hE]

private lemma lift_relIndex_dvd {N : Type*} [Group N] [Finite N] (T C : Subgroup N)
    [C.Normal] : T.relIndex C ∣ T.index := by
  rw [← lift_relIndex_sup_eq T C]
  exact Dvd.intro _ (Subgroup.relIndex_mul_index (le_sup_left : T ≤ T ⊔ C))

private lemma lift_relIndex_inf_eq {N : Type*} [Group N] [Finite N] (T C Y : Subgroup N)
    [C.Normal] (hCY : C ≤ Y) (hY : Y = C ⊔ (T ⊓ Y)) :
    (T ⊓ Y).relIndex Y = T.relIndex C := by
  have hf : C.relIndex Y = C.relIndex (T ⊓ Y) := by
    conv_lhs => rw [hY]
    rw [Subgroup.relIndex_sup_left]
  have hg : C.relIndex Y * Nat.card C = Nat.card Y := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := Y)
    rwa [inf_eq_left.mpr hCY] at h
  have hh : (T ⊓ Y).relIndex Y * Nat.card (T ⊓ Y : Subgroup N) = Nat.card Y := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ Y) (K := Y)
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hi : C.relIndex (T ⊓ Y) * Nat.card (C ⊓ (T ⊓ Y) : Subgroup N)
      = Nat.card (T ⊓ Y : Subgroup N) :=
    Subgroup.relIndex_mul_card (H := C) (K := T ⊓ Y)
  have hj : C ⊓ (T ⊓ Y) = C ⊓ T := by
    rw [← inf_assoc]
    exact inf_eq_left.mpr (inf_le_left.trans hCY)
  rw [hj] at hi
  have hmn : Nat.card (C ⊓ T : Subgroup N) = Nat.card (T ⊓ C : Subgroup N) := by
    rw [inf_comm]
  have hE : T.relIndex C * Nat.card (T ⊓ C : Subgroup N) = Nat.card C :=
    Subgroup.relIndex_mul_card (H := T) (K := C)
  have hpos : 0 < Nat.card (C ⊓ T : Subgroup N) := Nat.card_pos
  have hxpos : 0 < C.relIndex (T ⊓ Y) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hi
    exact absurd hi.symm (Nat.card_pos (α := (T ⊓ Y : Subgroup N))).ne'
  have key : C.relIndex (T ⊓ Y) * ((T ⊓ Y).relIndex Y * Nat.card (C ⊓ T : Subgroup N))
      = C.relIndex (T ⊓ Y) * Nat.card C := by
    calc C.relIndex (T ⊓ Y) * ((T ⊓ Y).relIndex Y * Nat.card (C ⊓ T : Subgroup N))
        = (T ⊓ Y).relIndex Y * (C.relIndex (T ⊓ Y) * Nat.card (C ⊓ T : Subgroup N)) := by ring
      _ = (T ⊓ Y).relIndex Y * Nat.card (T ⊓ Y : Subgroup N) := by rw [hi]
      _ = Nat.card Y := hh
      _ = C.relIndex Y * Nat.card C := hg.symm
      _ = C.relIndex (T ⊓ Y) * Nat.card C := by rw [hf]
  have key2 := Nat.eq_of_mul_eq_mul_left hxpos key
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [key2, hmn, hE]

private lemma lift_conj_mem_sup_zpowers {N : Type*} [Group N] (C : Subgroup N) [C.Normal]
    {a y : N} (hy : y ∈ C ⊔ Subgroup.zpowers a) : y⁻¹ * a * y * a⁻¹ ∈ C := by
  rw [Subgroup.mem_sup_of_normal_left] at hy
  obtain ⟨c, hc, z, hz, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hu : c⁻¹ * (a * c * a⁻¹) ∈ C :=
    C.mul_mem (C.inv_mem hc) (Subgroup.Normal.conj_mem inferInstance c hc a)
  have hcomm : Commute a⁻¹ (a ^ k) := ((Commute.refl a).zpow_right k).inv_left
  have e : (c * a ^ k)⁻¹ * a * (c * a ^ k) * a⁻¹
      = (a ^ k)⁻¹ * (c⁻¹ * (a * c * a⁻¹)) * (a ^ k)⁻¹⁻¹ := by
    calc (c * a ^ k)⁻¹ * a * (c * a ^ k) * a⁻¹
        = (a ^ k)⁻¹ * c⁻¹ * a * c * (a ^ k * a⁻¹) := by group
      _ = (a ^ k)⁻¹ * c⁻¹ * a * c * (a⁻¹ * a ^ k) := by rw [← hcomm.eq]
      _ = (a ^ k)⁻¹ * (c⁻¹ * (a * c * a⁻¹)) * (a ^ k)⁻¹⁻¹ := by group
  rw [e]
  exact Subgroup.Normal.conj_mem inferInstance _ hu _

private lemma lift_exists_conj_mem {N : Type*} [Group N] [Finite N] (Y K : Subgroup N)
    (hK : IsPGroup 2 ↥K) (hKi : ¬ 2 ∣ K.relIndex Y) {a : N} (haY : a ∈ Y) (ha : a ^ 2 = 1) :
    ∃ g ∈ Y, g⁻¹ * a * g ∈ K := by
  have hK' : IsPGroup 2 ↥(K.subgroupOf Y) := hK.comap_subtype
  let SK : Sylow 2 ↥Y := hK'.toSylow hKi
  let aY : ↥Y := ⟨a, haY⟩
  have haY2 : aY ^ 2 = 1 := Subtype.ext (by simp [aY, ha])
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers aY) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one haY2)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hZ
  haveI : Finite (Sylow 2 ↥Y) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y SK Q
  have haQ : aY ∈ Q := hQ (Subgroup.mem_zpowers aY)
  have h1 : aY ∈ ((g • SK : Sylow 2 ↥Y) : Subgroup ↥Y) := by
    rw [hg]
    exact haQ
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h3 : (MulAut.conj g)⁻¹ • aY ∈ K.subgroupOf Y := h1
  rw [Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_inv_apply] at h3
  refine ⟨(g : N), g.2, ?_⟩
  simpa [aY] using h3

theorem exists_involution_lift {N : Type*} [Group N] [Finite N] (T C : Subgroup N) [C.Normal]
    (hTp : IsPGroup 2 ↥T) (hTi : ¬ 2 ∣ T.index) {a : N} (ha : a ^ 2 = 1)
    (hTa : ∃ t ∈ T, t * a⁻¹ ∈ C) : ∃ t ∈ T, t ^ 2 = 1 ∧ t * a⁻¹ ∈ C := by
  obtain ⟨t₀, ht₀T, ht₀C⟩ := hTa
  have haY : a ∈ C ⊔ Subgroup.zpowers a :=
    (le_sup_right : Subgroup.zpowers a ≤ C ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a)
  have hCY : C ≤ C ⊔ Subgroup.zpowers a := le_sup_left
  have ht₀Y : t₀ ∈ C ⊔ Subgroup.zpowers a := by
    have h := (C ⊔ Subgroup.zpowers a).mul_mem (hCY ht₀C) haY
    rwa [inv_mul_cancel_right] at h
  have hY : C ⊔ Subgroup.zpowers a = C ⊔ (T ⊓ (C ⊔ Subgroup.zpowers a)) := by
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [Subgroup.zpowers_le]
      have hc : a * t₀⁻¹ ∈ C := by simpa [mul_inv_rev] using C.inv_mem ht₀C
      have h := (C ⊔ (T ⊓ (C ⊔ Subgroup.zpowers a))).mul_mem
        (le_sup_left (a := C) (b := T ⊓ (C ⊔ Subgroup.zpowers a)) hc)
        (le_sup_right (a := C) (b := T ⊓ (C ⊔ Subgroup.zpowers a))
          (show t₀ ∈ T ⊓ (C ⊔ Subgroup.zpowers a) from ⟨ht₀T, ht₀Y⟩))
      rwa [inv_mul_cancel_right] at h
    · exact sup_le le_sup_left inf_le_right
  have hKi : ¬ 2 ∣ (T ⊓ (C ⊔ Subgroup.zpowers a)).relIndex (C ⊔ Subgroup.zpowers a) := by
    rw [lift_relIndex_inf_eq T C (C ⊔ Subgroup.zpowers a) hCY hY]
    exact fun h => hTi (dvd_trans h (lift_relIndex_dvd T C))
  have hKT : IsPGroup 2 ↥(T ⊓ (C ⊔ Subgroup.zpowers a)) := IsPGroup.to_le hTp inf_le_left
  obtain ⟨g, hgY, hgK⟩ := lift_exists_conj_mem (C ⊔ Subgroup.zpowers a)
    (T ⊓ (C ⊔ Subgroup.zpowers a)) hKT hKi haY ha
  refine ⟨g⁻¹ * a * g, (inf_le_left : T ⊓ (C ⊔ Subgroup.zpowers a) ≤ T) hgK, ?_, ?_⟩
  · have hsq : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by simp [pow_two, mul_assoc]
    rw [hsq, ha]
    simp
  · exact lift_conj_mem_sup_zpowers C hgY

end CFSG.Quasithin.H13.L828Lift
