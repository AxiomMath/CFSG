module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Defs

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

variable {Y : Type*} [Group Y]

theorem mem_zpowers_cases {c y : Y} (hc : orderOf c = 3) (hy : y ∈ Subgroup.zpowers c) :
    y = 1 ∨ y = c ∨ y = c⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hmod := zpow_mod_orderOf c k
  rw [hc] at hmod
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk
  · left
    rw [← hmod]
    simp [hk]
  · right; left
    rw [← hmod]
    simp [hk]
  · right; right
    rw [← hmod]
    simp only [Nat.cast_ofNat, hk]
    have : c ^ (2 : ℤ) * c = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_succ]; exact hc3
    exact eq_inv_of_mul_eq_one_left this

theorem commute_of_mem_zpowers {c a b : Y} (ha : a ∈ Subgroup.zpowers c)
    (hb : b ∈ Subgroup.zpowers c) : Commute a b := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact Commute.zpow_zpow_self c i j

theorem mem_centralizer_zpowers_iff {c z : Y} :
    z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y) ↔ c * z = z * c := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hz
    exact hz c (Subgroup.mem_zpowers c)
  · intro hcz y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute c z from hcz) k).eq

theorem le_normalizer_zpowers {c : Y} {H : Subgroup Y}
    (hH : ∀ g ∈ H, g * c * g⁻¹ ∈ Subgroup.zpowers c) :
    H ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hH g hg) k
  · intro hy
    have hc : g⁻¹ * c * g ∈ Subgroup.zpowers c := by simpa using hH g⁻¹ (H.inv_mem hg)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy' : y = (g⁻¹ * c * g) ^ k := by
      rw [show (g⁻¹ * c * g) = g⁻¹ * c * g⁻¹⁻¹ by simp, conj_zpow, hk]
      group
    rw [hy']
    exact Subgroup.zpow_mem _ hc k

theorem exists_orderOf_eq_two_pow {u x : Y}
    (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))
    (hu : orderOf u = 2) (hx : Commute x u) : ∃ k : ℕ, orderOf x = 2 ^ k := by
  have hmem : x ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hY2 u hu) ⟨x, hmem⟩
  exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

theorem not_commute_of_orderOf_three {c u : Y}
    (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))
    (hc : orderOf c = 3) (hu : orderOf u = 2) : ¬ Commute c u := by
  intro h
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hY2 hu h
  rw [hc] at hk
  have : 3 ∣ 2 ^ k := hk ▸ dvd_refl 3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

theorem odd_orderOf_of_commute [Finite Y] {c z : Y}
    (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))
    (hc : orderOf c = 3) (hcz : Commute c z) : Odd (orderOf z) := by
  by_contra hodd
  have heven : 2 ∣ orderOf z := by
    rcases Nat.even_or_odd (orderOf z) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have hu : orderOf (z ^ (orderOf z / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne' heven
  exact not_commute_of_orderOf_three hY2 hc hu (hcz.pow_right _)

theorem eq_one_of_commute_of_odd {z u : Y}
    (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))
    (hu : orderOf u = 2) (hz : Odd (orderOf z)) (hzu : Commute z u) : z = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hY2 hu hzu
  rw [hk] at hz
  have hk0 : k = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hz) (by
      rw [Nat.even_pow]; exact ⟨even_two, h⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem inv_of_fixedPointFree [Finite Y] {Z : Subgroup Y} {t : Y} (htt : t * t = 1)
    (hZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z) (hfix : ∀ z ∈ Z, t * z = z * t → z = 1) :
    ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let φ : Z → Z := fun z => ⟨z⁻¹ * (t * z * t⁻¹), Z.mul_mem (Z.inv_mem z.2) (hZ z z.2)⟩
  have hinj : Function.Injective φ := by
    intro z w hzw
    have hzw' : (z : Y)⁻¹ * (t * z * t⁻¹) = (w : Y)⁻¹ * (t * w * t⁻¹) := congrArg Subtype.val hzw
    set a := (z : Y)⁻¹ * (t * z * t⁻¹) with ha
    have e1 : t * z * t⁻¹ = z * a := by rw [ha]; group
    have e2 : t * w * t⁻¹ = w * a := by rw [hzw']; group
    have hu : t * ((w : Y) * (z : Y)⁻¹) = ((w : Y) * (z : Y)⁻¹) * t := by
      have : t * ((w : Y) * (z : Y)⁻¹) * t⁻¹ = (w : Y) * (z : Y)⁻¹ :=
        calc t * ((w : Y) * (z : Y)⁻¹) * t⁻¹
            = (t * w * t⁻¹) * (t * z * t⁻¹)⁻¹ := by group
          _ = (w * a) * (z * a)⁻¹ := by rw [e1, e2]
          _ = (w : Y) * (z : Y)⁻¹ := by group
      calc t * ((w : Y) * (z : Y)⁻¹) = (t * ((w : Y) * (z : Y)⁻¹) * t⁻¹) * t := by group
        _ = ((w : Y) * (z : Y)⁻¹) * t := by rw [this]
    have h1 := hfix _ (Z.mul_mem w.2 (Z.inv_mem z.2)) hu
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro z hz
  obtain ⟨w, hw⟩ := hsurj ⟨z, hz⟩
  have hw' : (w : Y)⁻¹ * (t * w * t⁻¹) = z := congrArg Subtype.val hw
  rw [← hw']
  simp only [htinv]
  calc t * ((w : Y)⁻¹ * (t * w * t)) * t = t * (w : Y)⁻¹ * t * w * (t * t) := by group
    _ = t * (w : Y)⁻¹ * t * w := by rw [htt, mul_one]
    _ = ((w : Y)⁻¹ * (t * w * t))⁻¹ := by simp only [mul_inv_rev, inv_inv, htinv]; group

theorem commutative_of_inv {Z : Subgroup Y} {t : Y} (hinv : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) :
    IsMulCommutative Z := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab := hinv (a * b) (Z.mul_mem a.2 b.2)
  have h1 : t * (a * b : Y) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [h1, hinv a a.2, hinv b b.2, mul_inv_rev] at hab
  apply Subtype.ext
  change (a : Y) * b = b * a
  have := congrArg (fun x => x⁻¹) hab
  simpa using this.symm

theorem commute_of_mem_fixedFitting [Finite Y] {f : MulAut Y} {x y : Y}
    (hx : x ∈ fixedFitting f) (hy : y ∈ fixedFitting f)
    (hxy : (orderOf x).Coprime (orderOf y)) : Commute x y := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)) := inferInstance
  have hx2 : orderOf (⟨x', hx'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f))) =
      orderOf (x' : Y) := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hy2 : orderOf (⟨y', hy'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f))) =
      orderOf (y' : Y) := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hc : Commute (⟨x', hx'⟩ : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)))
      ⟨y', hy'⟩ := Group.IsNilpotent.commute_of_orderOf_coprime (by rw [hx2, hy2]; exact hxy)
  have h := congrArg (fun z : ↥(CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f)) =>
    ((z : ↥(signalizerFixedSubgroup f)) : Y)) hc.eq
  exact h

structure S3Data (f : MulAut Y) (c t : Y) : Prop where
  c_mem : c ∈ signalizerFixedSubgroup f
  t_mem : t ∈ signalizerFixedSubgroup f
  order_c : orderOf c = 3
  order_t : orderOf t = 2
  inv : t * c * t⁻¹ = c⁻¹
  card : Nat.card (signalizerFixedSubgroup f) = 6

namespace S3Data

variable {f : MulAut Y} {c t : Y} (h : S3Data f c t)

include h

theorem zpowers_le : Subgroup.zpowers c ≤ signalizerFixedSubgroup f :=
  Subgroup.zpowers_le.mpr h.c_mem

theorem card_zpowers : Nat.card (Subgroup.zpowers c) = 3 := by
  rw [Nat.card_zpowers, h.order_c]

theorem t_not_mem : t ∉ Subgroup.zpowers c := by
  intro ht
  have := Subgroup.orderOf_dvd_natCard _ ht
  rw [h.order_t, h.card_zpowers] at this
  omega

theorem mul_self_t : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [h.order_t, pow_two] at this

theorem inv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.mul_self_t

theorem c_cube : c * c * c = 1 := by
  have := pow_orderOf_eq_one c
  rw [h.order_c] at this
  simpa [pow_succ] using this

theorem mul_self_c : c * c = c⁻¹ := eq_inv_of_mul_eq_one_left h.c_cube

theorem index_eq_two :
    ((Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f)).index = 2 := by
  have h1 := Subgroup.index_mul_card ((Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f))
  have h2 : Nat.card ((Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.zpowers_le).toEquiv, h.card_zpowers]
  rw [h2, h.card] at h1
  omega

theorem mul_mem_iff {x y : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hy : y ∈ signalizerFixedSubgroup f) :
    x * y ∈ Subgroup.zpowers c ↔ (x ∈ Subgroup.zpowers c ↔ y ∈ Subgroup.zpowers c) := by
  have := Subgroup.mul_mem_iff_of_index_two h.index_eq_two (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem conj_inv_of_mem {w : Y} (hw : w ∈ Subgroup.zpowers c) : t * w * t⁻¹ = w⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← conj_zpow, h.inv, inv_zpow]

theorem exists_mul_t {x : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hxP : x ∉ Subgroup.zpowers c) : ∃ w ∈ Subgroup.zpowers c, x = w * t := by
  refine ⟨x * t⁻¹, ?_, by group⟩
  rw [h.mul_mem_iff hx (Subgroup.inv_mem _ h.t_mem), inv_mem_iff]
  exact iff_of_false hxP h.t_not_mem

theorem mul_self_of_not_mem {x : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hxP : x ∉ Subgroup.zpowers c) : x * x = 1 := by
  obtain ⟨w, hw, rfl⟩ := h.exists_mul_t hx hxP
  have htw : t * w = w⁻¹ * t := by
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w⁻¹ * t := by rw [h.conj_inv_of_mem hw]
  calc w * t * (w * t) = w * (t * w) * t := by group
    _ = w * (w⁻¹ * t) * t := by rw [htw]
    _ = t * t := by group
    _ = 1 := h.mul_self_t

theorem orderOf_eq_two_of_not_mem {x : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hxP : x ∉ Subgroup.zpowers c) : orderOf x = 2 := by
  refine orderOf_eq_prime (by rw [pow_two]; exact h.mul_self_of_not_mem hx hxP) ?_
  rintro rfl
  exact hxP (Subgroup.one_mem _)

theorem conj_inv_of_not_mem {x w : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hxP : x ∉ Subgroup.zpowers c) (hw : w ∈ Subgroup.zpowers c) : x * w * x⁻¹ = w⁻¹ := by
  obtain ⟨v, hv, rfl⟩ := h.exists_mul_t hx hxP
  have hvw : v * w⁻¹ = w⁻¹ * v :=
    (commute_of_mem_zpowers hv (Subgroup.inv_mem _ hw)).eq
  calc v * t * w * (v * t)⁻¹ = v * (t * w * t⁻¹) * v⁻¹ := by group
    _ = v * w⁻¹ * v⁻¹ := by rw [h.conj_inv_of_mem hw]
    _ = w⁻¹ := by rw [hvw]; group

theorem conj_mem_zpowers {g : Y} (hg : g ∈ signalizerFixedSubgroup f) :
    g * c * g⁻¹ ∈ Subgroup.zpowers c := by
  by_cases hgP : g ∈ Subgroup.zpowers c
  · rw [(commute_of_mem_zpowers hgP (Subgroup.mem_zpowers c)).eq, mul_assoc, mul_inv_cancel,
      mul_one]
    exact Subgroup.mem_zpowers c
  · rw [h.conj_inv_of_not_mem hg hgP (Subgroup.mem_zpowers c)]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)

theorem commutator_mem {x y : Y} (hx : x ∈ signalizerFixedSubgroup f)
    (hy : y ∈ signalizerFixedSubgroup f) : ⁅x, y⁆ ∈ Subgroup.zpowers c := by
  have h1 : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by
    simp only [commutatorElement_def]; group
  have hxy := h.mul_mem_iff hx hy
  have hyx := h.mul_mem_iff hy hx
  have hz := h.mul_mem_iff (Subgroup.mul_mem _ hx hy)
    (Subgroup.inv_mem _ (Subgroup.mul_mem _ hy hx))
  rw [h1, hz, inv_mem_iff, hxy, hyx]
  exact iff_comm.mp (Iff.rfl.trans (by tauto))

theorem zpowers_le_fixedFitting : Subgroup.zpowers c ≤ fixedFitting f := by
  have hPC := h.zpowers_le
  have hnorm : ((Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f)).Normal :=
    Subgroup.normal_of_index_eq_two h.index_eq_two
  have hnil : Group.IsNilpotent ↥((Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f)) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hPC)).mpr inferInstance
  have hle : (Subgroup.zpowers c).subgroupOf (signalizerFixedSubgroup f) ≤
      CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f) := le_sSup ⟨hnorm, hnil⟩
  intro x hx
  exact ⟨⟨x, hPC hx⟩, hle (by rwa [Subgroup.mem_subgroupOf]), rfl⟩

section Fitting

variable [Finite Y]

theorem fixedFitting_eq : fixedFitting f = Subgroup.zpowers c := by
  refine le_antisymm ?_ h.zpowers_le_fixedFitting
  rintro x hx
  by_contra hxP
  have hxC : x ∈ signalizerFixedSubgroup f := fixedFitting_le f hx
  have hcF : c ∈ fixedFitting f := h.zpowers_le_fixedFitting (Subgroup.mem_zpowers c)
  have hcomm : Commute x c := commute_of_mem_fixedFitting hx hcF (by
    rw [h.orderOf_eq_two_of_not_mem hxC hxP, h.order_c]; norm_num)
  have h1 : x * c * x⁻¹ = c⁻¹ := h.conj_inv_of_not_mem hxC hxP (Subgroup.mem_zpowers c)
  have h2 : x * c * x⁻¹ = c := by rw [hcomm.eq]; group
  have h3 : c * c = 1 := by
    have : c = c⁻¹ := h2.symm.trans h1
    calc c * c = c * c⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel c
  have : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rw [h.order_c] at this
  omega

end Fitting

section Centralizer

variable [Finite Y]
  (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))

include hY2 in
theorem odd_orderOf_of_mem_centralizer {z : Y}
    (hz : z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y)) : Odd (orderOf z) :=
  odd_orderOf_of_commute hY2 h.order_c (mem_centralizer_zpowers_iff.mp hz)

omit [Finite Y] in
theorem conj_mem_centralizer {z : Y}
    (hz : z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y)) :
    t * z * t⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y) := by
  rw [mem_centralizer_zpowers_iff] at hz ⊢
  have h1 : t⁻¹ * c * t = c⁻¹ := by
    have h' := h.inv
    rw [h.inv_t] at h' ⊢
    exact h'
  have h2 : t * c⁻¹ * t⁻¹ = c := by
    calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
      _ = c := by rw [h.inv, inv_inv]
  have h3 : c⁻¹ * z = z * c⁻¹ := (Commute.inv_left (show Commute c z from hz)).eq
  calc c * (t * z * t⁻¹) = t * (t⁻¹ * c * t) * z * t⁻¹ := by group
    _ = t * c⁻¹ * z * t⁻¹ := by rw [h1]
    _ = t * (z * c⁻¹) * t⁻¹ := by rw [mul_assoc t c⁻¹ z, h3, ← mul_assoc]
    _ = t * z * t⁻¹ * (t * c⁻¹ * t⁻¹) := by group
    _ = t * z * t⁻¹ * c := by rw [h2]

include hY2 in
theorem conj_eq_inv_of_mem_centralizer {z : Y}
    (hz : z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y)) : t * z * t⁻¹ = z⁻¹ :=
  inv_of_fixedPointFree h.mul_self_t (fun _ hz' => h.conj_mem_centralizer hz')
    (fun _ hz' htz => eq_one_of_commute_of_odd hY2 h.order_t
      (h.odd_orderOf_of_mem_centralizer hY2 hz') htz.symm) z hz

include hY2 in
theorem isMulCommutative_centralizer :
    IsMulCommutative (Subgroup.centralizer (Subgroup.zpowers c : Set Y)) :=
  commutative_of_inv fun _ hz => h.conj_eq_inv_of_mem_centralizer hY2 hz

include hY2 in
theorem eq_one_of_commute {v z : Y} (hv : v ∈ signalizerFixedSubgroup f)
    (hvP : v ∉ Subgroup.zpowers c)
    (hz : z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y)) (hvz : v * z = z * v) :
    z = 1 :=
  eq_one_of_commute_of_odd hY2 (h.orderOf_eq_two_of_not_mem hv hvP)
    (h.odd_orderOf_of_mem_centralizer hY2 hz) hvz.symm

end Centralizer

theorem exists_normalizer_decomp {x : Y}
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set Y)) :
    ∃ z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set Y),
      ∃ d ∈ signalizerFixedSubgroup f, x = z * d := by
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c)
  rcases mem_zpowers_cases h.order_c hxc with h1 | h1 | h1
  · exfalso
    have hc1 : c = 1 := by
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this
    have := h.order_c
    rw [hc1, orderOf_one] at this
    omega
  · refine ⟨x, mem_centralizer_zpowers_iff.mpr ?_, 1, Subgroup.one_mem _, (mul_one x).symm⟩
    calc c * x = (x * c * x⁻¹) * x := by rw [h1]
      _ = x * c := by group
  · refine ⟨x * t, mem_centralizer_zpowers_iff.mpr ?_, t⁻¹, Subgroup.inv_mem _ h.t_mem, by group⟩
    have e : x * c⁻¹ * x⁻¹ = c := by
      calc x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := by group
        _ = c := by rw [h1, inv_inv]
    have e2 : x * t * c * (x * t)⁻¹ = c :=
      calc x * t * c * (x * t)⁻¹ = x * (t * c * t⁻¹) * x⁻¹ := by group
        _ = x * c⁻¹ * x⁻¹ := by rw [h.inv]
        _ = c := e
    calc c * (x * t) = (x * t * c * (x * t)⁻¹) * (x * t) := by rw [e2]
      _ = x * t * c := by group

theorem zpowers_le_of_normal {N : Subgroup Y} (hNC : N ≤ signalizerFixedSubgroup f)
    (hN : (N.subgroupOf (signalizerFixedSubgroup f)).Normal) (hbot : N ≠ ⊥) :
    Subgroup.zpowers c ≤ N := by
  have hconj : ∀ x ∈ signalizerFixedSubgroup f, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mp hN hx) n).mp hn
  obtain ⟨n, hn, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  have hcN : c ∈ N := by
    by_cases hnP : n ∈ Subgroup.zpowers c
    · rcases mem_zpowers_cases h.order_c hnP with h1 | h1 | h1
      · exact absurd h1 hn1
      · rwa [← h1]
      · have := N.inv_mem hn
        rwa [h1, inv_inv] at this
    · have hnC := hNC hn
      have h1 := hconj c h.c_mem n hn
      have h2 : n * c * n⁻¹ = c⁻¹ := h.conj_inv_of_not_mem hnC hnP (Subgroup.mem_zpowers c)
      have h3 : c * n * c⁻¹ * n⁻¹ = c * c := by
        have : n * c⁻¹ * n⁻¹ = c := by
          calc n * c⁻¹ * n⁻¹ = (n * c * n⁻¹)⁻¹ := by group
            _ = c := by rw [h2, inv_inv]
        calc c * n * c⁻¹ * n⁻¹ = c * (n * c⁻¹ * n⁻¹) := by group
          _ = c * c := by rw [this]
      have h4 : c * c ∈ N := h3 ▸ N.mul_mem h1 (N.inv_mem hn)
      rw [h.mul_self_c] at h4
      have := N.inv_mem h4
      rwa [inv_inv] at this
  exact Subgroup.zpowers_le.mpr hcN

section Finite

variable [Finite Y]

theorem fixedCore1_ne : fixedCore1 f ≠ fixedFitting f := by
  intro heq
  have ht : t ∈ fixedCore1 f :=
    ⟨h.t_mem, fun x hx => by rw [h.fixedFitting_eq]; exact h.commutator_mem h.t_mem hx⟩
  rw [heq, h.fixedFitting_eq] at ht
  exact h.t_not_mem ht

theorem sylow_eq (h9 : ¬ 9 ∣ Nat.card Y) {Q : Subgroup Y} (hQ : IsPGroup 3 Q)
    (hle : fixedFitting f ≤ Q) : Q = fixedFitting f := by
  rw [h.fixedFitting_eq] at hle ⊢
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card Q
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    apply h9
    have : 9 ∣ 3 ^ k := by
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk2
      simpa using this
    exact this.trans (hk ▸ hdvd)
  have hcardP : Nat.card (Subgroup.zpowers c) ≤ Nat.card Q := Subgroup.card_le_of_le hle
  rw [h.card_zpowers] at hcardP
  have hk1' : k = 1 := by
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rfl
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_zpowers, hk, hk1']; norm_num)).symm

end Finite

end S3Data

theorem exists_S3Data [Finite Y] (f : MulAut Y)
    (hY2 : ∀ u : Y, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set Y)))
    (hC : Nat.card (signalizerFixedSubgroup f) = 6) : ∃ c t : Y, S3Data f c t := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' (G := signalizerFixedSubgroup f) 3
    (by rw [hC]; norm_num)
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := signalizerFixedSubgroup f) 2
    (by rw [hC]; norm_num)
  have hc : orderOf (c' : Y) = 3 := by rw [Subgroup.orderOf_coe, hc']
  have ht : orderOf (t' : Y) = 2 := by rw [Subgroup.orderOf_coe, ht']
  have hP'card : Nat.card (Subgroup.zpowers c') = 3 := by rw [Nat.card_zpowers, hc']
  have hidx : (Subgroup.zpowers c').index = 2 := by
    have := Subgroup.index_mul_card (Subgroup.zpowers c')
    rw [hP'card, hC] at this
    omega
  have hnormal : (Subgroup.zpowers c').Normal := Subgroup.normal_of_index_eq_two hidx
  have hconj : t' * c' * t'⁻¹ ∈ Subgroup.zpowers c' :=
    hnormal.conj_mem c' (Subgroup.mem_zpowers c') t'
  refine ⟨c', t', ?_⟩
  rcases mem_zpowers_cases hc' hconj with h1 | h1 | h1
  · exfalso
    have hc1 : c' = 1 := by
      have := congrArg (fun y => t'⁻¹ * y * t') h1
      simpa [mul_assoc] using this
    rw [hc1, orderOf_one] at hc'
    omega
  · exfalso
    have h4 : t' * c' = c' * t' := by
      calc t' * c' = (t' * c' * t'⁻¹) * t' := by group
        _ = c' * t' := by rw [h1]
    have h5 : (c' : Y) * t' = t' * c' := (congrArg Subtype.val h4).symm
    exact not_commute_of_orderOf_three hY2 hc ht h5
  · refine ⟨c'.2, t'.2, hc, ht, ?_, hC⟩
    exact congrArg Subtype.val h1

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
