module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.LocalAnalysis.StandardType.ElementaryAbelianNineLines
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16t_idem_inv_eq_self {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    (t : T) : t⁻¹ = t := by
  have h := hT t
  rw [pow_two, mul_eq_one_iff_eq_inv] at h
  exact h.symm

private def s16t_idem_norm {T : Type*} [CommGroup T] (a : MulAut T) : T →* T where
  toFun t := t * a t * a (a t)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul]
    ac_rfl

private theorem s16t_idem_norm_apply {T : Type*} [CommGroup T] (a : MulAut T) (t : T) :
    s16t_idem_norm a t = t * a t * a (a t) := rfl

private theorem s16t_idem_norm_mem_fixV {T : Type*} [CommGroup T] {a : MulAut T}
    (ha : a ^ 3 = 1) (t : T) : s16t_idem_norm a t ∈ fixV (Subgroup.zpowers a) := by
  rw [mem_fixV_zpowers_iff_apply, s16t_idem_norm_apply]
  have h3 : a (a (a t)) = t := by
    have h : (a ^ 3) t = t := by rw [ha]; rfl
    simpa [pow_three', MulAut.mul_apply] using h
  simp only [map_mul, h3]
  ac_rfl

private theorem s16t_idem_norm_smul {T : Type*} [CommGroup T] {a : MulAut T} (ha : a ^ 3 = 1)
    {x : MulAut T} (hx : x ∈ Subgroup.zpowers a) (t : T) :
    s16t_idem_norm a (x t) = s16t_idem_norm a t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [s16t_idem_norm_apply, s16t_idem_norm_apply]
  have hcomm : a * a ^ k = a ^ k * a := ((Commute.refl a).zpow_right k).eq
  have h1 : a ((a ^ k) t) = (a ^ k) (a t) := by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  have h2 : a (a ((a ^ k) t)) = (a ^ k) (a (a t)) := by
    rw [h1, ← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  rw [h2, h1, ← map_mul, ← map_mul]
  exact (s16t_idem_norm_mem_fixV ha t) (a ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)

private theorem s16t_idem_norm_eq_one_of_mem_commV {T : Type*} [CommGroup T] {a : MulAut T}
    (ha : a ^ 3 = 1) {w : T} (hw : w ∈ commV (Subgroup.zpowers a)) :
    s16t_idem_norm a w = 1 := by
  refine Subgroup.closure_induction (p := fun c _ => s16t_idem_norm a c = 1) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x, hx, v, rfl⟩
    rw [map_mul, map_inv, s16t_idem_norm_smul ha hx v, mul_inv_cancel]
  · exact map_one _
  · intro p q _ _ hp hq
    rw [map_mul, hp, hq, mul_one]
  · intro p _ hp
    rw [map_inv, hp, inv_one]

private theorem s16t_idem_commV_inf_fixV_eq_bot {T : Type*} [CommGroup T]
    (hT : ∀ t : T, t ^ 2 = 1) {a : MulAut T} (ha : a ^ 3 = 1) :
    commV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers a) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro w ⟨hw1, hw2⟩
  have h1 : s16t_idem_norm a w = 1 := s16t_idem_norm_eq_one_of_mem_commV ha hw1
  have h2 : s16t_idem_norm a w = w := by
    rw [s16t_idem_norm_apply]
    have haw : a w = w := mem_fixV_zpowers_iff_apply.mp hw2
    have haw2 : a (a w) = w := by rw [haw, haw]
    rw [haw2, haw]
    calc w * w * w = w ^ 2 * w := by rw [pow_two]
      _ = 1 * w := by rw [hT w]
      _ = w := one_mul w
  rw [h2] at h1
  exact h1

private theorem s16t_idem_trace {T : Type*} [CommGroup T] {a : MulAut T} (ha : a ^ 3 = 1)
    {U : Subgroup T} (hUa : ∀ w ∈ U, a w ∈ U) (hfpf : ∀ w ∈ U, a w = w → w = 1)
    {w : T} (hw : w ∈ U) : w * a w * a (a w) = 1 := by
  have h3 : a (a (a w)) = w := by
    have h : (a ^ 3) w = w := by rw [ha]; rfl
    simpa [pow_three', MulAut.mul_apply] using h
  have hmem : w * a w * a (a w) ∈ U :=
    U.mul_mem (U.mul_mem hw (hUa w hw)) (hUa _ (hUa w hw))
  refine hfpf _ hmem ?_
  simp only [map_mul, h3]
  ac_rfl

private theorem s16t_idem_mem_commV_of_fpf {T : Type*} [CommGroup T]
    (hT : ∀ t : T, t ^ 2 = 1) {c z : MulAut T} (hc : c ^ 3 = 1)
    (hzc : z * c * z⁻¹ = c⁻¹) {U : Subgroup T}
    (hUc : ∀ w ∈ U, c w ∈ U) (hUz : ∀ w ∈ U, z w ∈ U)
    (hfpf : ∀ w ∈ U, c w = w → w = 1) :
    U ⊓ fixV (Subgroup.zpowers z) ≤ commV (Subgroup.zpowers z) := by
  rintro v ⟨hvU, hvz⟩
  have hv : z v = v := mem_fixV_zpowers_iff_apply.mp hvz
  have hcc : c * c = c⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← pow_three, hc])
  have hzc' : z * c = c⁻¹ * z := by rw [← hzc]; group
  have h1 : z (c v) = c (c v) := by
    calc z (c v) = (z * c) v := rfl
      _ = (c⁻¹ * z) v := by rw [hzc']
      _ = c⁻¹ (z v) := rfl
      _ = c⁻¹ v := by rw [hv]
      _ = c (c v) := by rw [← hcc]; rfl
  have h2 : v * c v * c (c v) = 1 := s16t_idem_trace hc hUc hfpf hvU
  have h3 : c v * c (c v) = v := by
    have h2' : v * (c v * c (c v)) = 1 := by rw [← mul_assoc]; exact h2
    have := eq_inv_of_mul_eq_one_right h2'
    rwa [s16t_idem_inv_eq_self hT v] at this
  have h4 : z (c v) * (c v)⁻¹ = v := by
    rw [h1, s16t_idem_inv_eq_self hT (c v), mul_comm, h3]
  rw [← h4]
  exact Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, c v, rfl⟩

private theorem s16t_idem_apply_mem_commV {T : Type*} [CommGroup T] {g x : MulAut T}
    (hx : ∀ y ∈ Subgroup.zpowers g, ∃ y' ∈ Subgroup.zpowers g, x * y = y' * x)
    {t : T} (ht : t ∈ commV (Subgroup.zpowers g)) :
    x t ∈ commV (Subgroup.zpowers g) := by
  refine Subgroup.closure_induction (p := fun c _ => x c ∈ commV (Subgroup.zpowers g))
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨y, hy, v, rfl⟩
    obtain ⟨y', hy', hxy⟩ := hx y hy
    rw [map_mul, map_inv, ← MulAut.mul_apply, hxy, MulAut.mul_apply]
    exact Subgroup.subset_closure ⟨y', hy', x v, rfl⟩
  · rw [map_one]; exact (commV (Subgroup.zpowers g)).one_mem
  · intro p q _ _ hp hq
    rw [map_mul]
    exact (commV (Subgroup.zpowers g)).mul_mem hp hq
  · intro p _ hp
    rw [map_inv]
    exact (commV (Subgroup.zpowers g)).inv_mem hp

theorem s16t_exists_gens_E9 {H : Type} [Group H] {A : Subgroup H}
    (hA : IsElemAbelianOfRank 3 2 ↥A) :
    ∃ a ∈ A, ∃ b ∈ A, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
      ∀ x ∈ A, ∃ i j : ℕ, x = a ^ i * b ^ j := by
  obtain ⟨e⟩ := hA
  have hcomm : ∀ x y : ↥A, x * y = y * x := by
    intro x y
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hexp : ∀ x : ↥A, x ^ 3 = 1 := by
    intro x
    apply e.injective
    rw [map_pow, map_one]
    have h3 : ∀ y : Multiplicative (Fin 2 → ZMod 3), y ^ 3 = 1 := by
      intro y
      induction y using Multiplicative.rec with
      | ofAdd w =>
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 w, ZMod.natCast_self 3,
          zero_smul, ofAdd_zero]
    exact h3 (e x)
  have hcard : Nat.card ↥A = 9 := by
    have h1 : Nat.card ↥A = Nat.card (Multiplicative (Fin 2 → ZMod 3)) :=
      Nat.card_congr e.toEquiv
    rw [h1, show Nat.card (Multiplicative (Fin 2 → ZMod 3)) =
      Nat.card (Fin 2 → ZMod 3) from rfl, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
  obtain ⟨a, b, -, -, hgen⟩ :=
    CFSG.StandardType.ElementaryAbelianNine.exists_generators hcomm hexp hcard
  refine ⟨(a : H), a.2, (b : H), b.2, ?_, ?_, ?_, ?_⟩
  · have h := map_pow (Subgroup.subtype A) a 3
    rw [hexp a, map_one] at h
    simpa using h.symm
  · have h := map_pow (Subgroup.subtype A) b 3
    rw [hexp b, map_one] at h
    simpa using h.symm
  · simpa using congrArg Subtype.val (hcomm a b)
  · intro x hx
    obtain ⟨i, j, hij⟩ := hgen ⟨x, hx⟩
    exact ⟨i, j, by simpa using congrArg Subtype.val hij⟩

theorem s16t_fixV_le_commV_of_inv {T : Type} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    {a b z : MulAut T} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hza : z * a * z⁻¹ = a⁻¹) (hzb : z * b * z⁻¹ = b⁻¹)
    (hfix : ∀ v : T, a v = v → b v = v → v = 1) :
    fixV (Subgroup.zpowers z) ≤ commV (Subgroup.zpowers z) := by
  intro c hc
  rw [mem_fixV_zpowers_iff_apply] at hc
  set v : T := s16t_idem_norm a c with hv_def
  set w : T := c * v with hw_def
  have hv_fix : v ∈ fixV (Subgroup.zpowers a) := by
    rw [hv_def]; exact s16t_idem_norm_mem_fixV ha c
  have hza' : z * a = a⁻¹ * z := by rw [← hza]; group
  have hz2 : z * (a * a) = (a⁻¹ * a⁻¹) * z := by
    calc z * (a * a) = (z * a) * a := (mul_assoc z a a).symm
      _ = (a⁻¹ * z) * a := by rw [hza']
      _ = a⁻¹ * (z * a) := mul_assoc a⁻¹ z a
      _ = a⁻¹ * (a⁻¹ * z) := by rw [hza']
      _ = (a⁻¹ * a⁻¹) * z := (mul_assoc a⁻¹ a⁻¹ z).symm
  have hmul3 : a * (a * a) = 1 := by
    calc a * (a * a) = a ^ 3 := (pow_three a).symm
      _ = 1 := ha
  have hainv : a⁻¹ = a * a := (eq_inv_of_mul_eq_one_right hmul3).symm
  have hainv2 : a⁻¹ * a⁻¹ = a := by
    rw [← mul_inv_rev, ← hainv, inv_inv]
  have hvz : z v = v := by
    rw [hv_def, s16t_idem_norm_apply]
    have h1 : z (a c) = a (a c) := by
      calc z (a c) = (z * a) c := rfl
        _ = (a⁻¹ * z) c := by rw [hza']
        _ = a⁻¹ (z c) := rfl
        _ = a⁻¹ c := by rw [hc]
        _ = (a * a) c := by rw [hainv]
        _ = a (a c) := rfl
    have h2 : z (a (a c)) = a c := by
      calc z (a (a c)) = z ((a * a) c) := by rw [show (a * a) c = a (a c) from rfl]
        _ = (z * (a * a)) c := rfl
        _ = ((a⁻¹ * a⁻¹) * z) c := by rw [hz2]
        _ = (a⁻¹ * a⁻¹) (z c) := rfl
        _ = (a⁻¹ * a⁻¹) c := by rw [hc]
        _ = a c := by rw [hainv2]
    rw [map_mul, map_mul, hc, h1, h2]
    ac_rfl
  have ha_norm : ∀ y ∈ Subgroup.zpowers a, ∃ y' ∈ Subgroup.zpowers a, a * y = y' * a := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨a ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩,
      ((Commute.refl a).zpow_right k).eq⟩
  have hz_norm : ∀ y ∈ Subgroup.zpowers a, ∃ y' ∈ Subgroup.zpowers a, z * y = y' * z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨(a ^ k)⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩), ?_⟩
    have h : z * a ^ k * z⁻¹ = (a ^ k)⁻¹ := by
      rw [← conj_zpow, hza, inv_zpow]
    rw [← h]
    group
  have ha_commV : ∀ t ∈ commV (Subgroup.zpowers a), a t ∈ commV (Subgroup.zpowers a) :=
    fun t ht => s16t_idem_apply_mem_commV ha_norm ht
  have hz_commV : ∀ t ∈ commV (Subgroup.zpowers a), z t ∈ commV (Subgroup.zpowers a) :=
    fun t ht => s16t_idem_apply_mem_commV hz_norm ht
  have ha_fpf : ∀ t ∈ commV (Subgroup.zpowers a), a t = t → t = 1 := by
    intro t ht hat
    have hmem : t ∈ commV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers a) :=
      ⟨ht, mem_fixV_zpowers_iff_apply.mpr hat⟩
    rw [s16t_idem_commV_inf_fixV_eq_bot hT ha, Subgroup.mem_bot] at hmem
    exact hmem
  have hb_fixV_a : ∀ t ∈ fixV (Subgroup.zpowers a), b t ∈ fixV (Subgroup.zpowers a) := by
    intro t ht
    rw [mem_fixV_zpowers_iff_apply] at ht ⊢
    rw [← MulAut.mul_apply, hab, MulAut.mul_apply, ht]
  have hz_fixV_a : ∀ t ∈ fixV (Subgroup.zpowers a), z t ∈ fixV (Subgroup.zpowers a) := by
    intro t ht
    rw [mem_fixV_zpowers_iff_apply] at ht ⊢
    have haz : a * z = z * a⁻¹ := by
      have h : a * z * a = z := by
        calc a * z * a = a * (z * a * z⁻¹) * z := by group
          _ = a * a⁻¹ * z := by rw [hza]
          _ = z := by group
      calc a * z = a * z * a * a⁻¹ := by group
        _ = z * a⁻¹ := by rw [h]
    have hat : a t = t := ht
    have hainv_t : a⁻¹ t = t := by
      have h : (a⁻¹ * a) t = t := by rw [inv_mul_cancel]; rfl
      rwa [MulAut.mul_apply, hat] at h
    rw [← MulAut.mul_apply, haz, MulAut.mul_apply, hainv_t]
  have hb_fpf : ∀ t ∈ fixV (Subgroup.zpowers a), b t = t → t = 1 := by
    intro t ht hbt
    exact hfix t (mem_fixV_zpowers_iff_apply.mp ht) hbt
  have hwz : z w = w := by
    rw [hw_def, map_mul, hc, hvz]
  have hw_comm : w ∈ commV (Subgroup.zpowers a) := by
    have hmem1 : a c * c⁻¹ ∈ commV (Subgroup.zpowers a) :=
      Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, c, rfl⟩
    have hmem2 : a (a c) * c⁻¹ ∈ commV (Subgroup.zpowers a) := by
      have haa : a * a ∈ Subgroup.zpowers a := by
        rw [← pow_two]
        exact (Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) 2
      have h : (a * a) c * c⁻¹ ∈ commV (Subgroup.zpowers a) :=
        Subgroup.subset_closure ⟨a * a, haa, c, rfl⟩
      rwa [MulAut.mul_apply] at h
    have hrepr : w = (a c * c⁻¹) * (a (a c) * c⁻¹) := by
      rw [hw_def, hv_def, s16t_idem_norm_apply, s16t_idem_inv_eq_self hT c]
      ac_rfl
    rw [hrepr]
    exact mul_mem hmem1 hmem2
  have hw_mem : w ∈ commV (Subgroup.zpowers z) :=
    s16t_idem_mem_commV_of_fpf hT ha hza ha_commV hz_commV ha_fpf
      ⟨hw_comm, mem_fixV_zpowers_iff_apply.mpr hwz⟩
  have hv_mem : v ∈ commV (Subgroup.zpowers z) :=
    s16t_idem_mem_commV_of_fpf hT hb hzb hb_fixV_a hz_fixV_a hb_fpf
      ⟨hv_fix, mem_fixV_zpowers_iff_apply.mpr hvz⟩
  have hcwv : w * v = c := by
    rw [hw_def, mul_assoc, ← pow_two, hT v, mul_one]
  rw [← hcwv]
  exact mul_mem hw_mem hv_mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
