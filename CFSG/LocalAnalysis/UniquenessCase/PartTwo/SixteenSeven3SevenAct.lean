module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {M L : Subgroup (MulAut W)} {Z : Subgroup W}

theorem SevenCfg.map_eq_of_mem (h : SevenCfg M L Z) {l : MulAut W} (hl : l ∈ L)
    {Y : Subgroup W} (hY : Y ∈ conjSubs M Z) : Y.map l.toMonoidHom = Y := by
  classical
  have hcard : Nat.card ↥(conjSubs M Z) = 4 := by
    rw [Nat.card_coe_set_eq]
    exact h.ncard
  haveI : Finite ↥(conjSubs M Z) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ↥(conjSubs M Z) := Fintype.ofFinite _
  have hcard' : Fintype.card ↥(conjSubs M Z) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let m : ↥M := ⟨l, h.le hl⟩
  have hm7 : m ^ 7 = 1 := Subtype.ext (h.pow_seven hl)
  have hσ7 : (sevenPerm M Z m) ^ 7 = 1 := by
    rw [← map_pow, hm7, map_one]
  have h7 : orderOf (sevenPerm M Z m) ∣ 7 := orderOf_dvd_of_pow_eq_one hσ7
  have h24 : orderOf (sevenPerm M Z m) ∣ 24 := by
    have := orderOf_dvd_card (G := Equiv.Perm ↥(conjSubs M Z)) (x := sevenPerm M Z m)
    rwa [Fintype.card_perm, hcard', show Nat.factorial 4 = 24 from rfl] at this
  have h1 : orderOf (sevenPerm M Z m) = 1 := by
    have := Nat.dvd_gcd h7 h24
    exact Nat.dvd_one.1 (by simpa using this)
  have hone : sevenPerm M Z m = 1 := orderOf_eq_one_iff.1 h1
  have h2 := congrArg
    (fun σ : Equiv.Perm ↥(conjSubs M Z) => ((σ ⟨Y, hY⟩ : ↥(conjSubs M Z)) : Subgroup W)) hone
  exact h2

theorem SevenCfg.eq_one_of_fixed (h : SevenCfg M L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs M Z)
    {l : MulAut W} (hl : l ∈ L) {y' : W} (hy' : y' ∈ Y) (hly' : l y' ≠ y') {y : W}
    (hy : y ∈ Y) (hly : l y = y) : y = 1 := by
  have hmap := h.map_eq_of_mem hl hY
  have hstab : l ∈ stabSub Y := by
    intro u
    constructor
    · intro hu
      have hu' : l u ∈ Y.map l.toMonoidHom := by rw [hmap]; exact hu
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
      have : w = u := l.injective hwu
      exact this ▸ hw
    · intro hu
      rw [← hmap]
      exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
  let r : MulAut ↥Y := resHom Y ⟨l, hstab⟩
  have hr7 : r ^ 7 = 1 := by
    have h7 : (⟨l, hstab⟩ : ↥(stabSub Y)) ^ 7 = 1 := Subtype.ext (h.pow_seven hl)
    show (resHom Y ⟨l, hstab⟩) ^ 7 = 1
    rw [← map_pow, h7, map_one]
  have hr1 : r ≠ 1 := by
    intro hr
    have := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y', hy'⟩ : ↥Y) : W)) hr
    exact hly' this
  have hcard : Nat.card ↥Y = 8 := h.card_of_mem hY
  have hfix : r ⟨y, hy⟩ = ⟨y, hy⟩ := Subtype.ext hly
  have := s16c167_seven_fix_eq_one hcard hr7 hr1 hfix
  exact congrArg Subtype.val this

theorem SevenCfg.le_commSub_of_ne (h : SevenCfg M L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs M Z)
    {l : MulAut W} (hl : l ∈ L) {y : W} (hy : y ∈ Y) (hly : l y ≠ y) : Y ≤ commSub ⊤ L := by
  have hmap := h.map_eq_of_mem hl hY
  have hlY : ∀ u ∈ Y, l u ∈ Y := fun u hu => by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
  let ψ : ↥Y → ↥Y := fun w => ⟨l (w : W) * (w : W)⁻¹, Y.mul_mem (hlY _ w.2) (Y.inv_mem w.2)⟩
  have hinj : Function.Injective ψ := by
    intro w w' hww
    have h1 : l (w : W) * (w : W)⁻¹ = l (w' : W) * (w' : W)⁻¹ := congrArg Subtype.val hww
    have h2 : l ((w : W) * (w' : W)⁻¹) = (w : W) * (w' : W)⁻¹ := by
      rw [map_mul, map_inv]
      calc l (w : W) * (l (w' : W))⁻¹
          = (l (w : W) * (w : W)⁻¹) * ((w : W) * (l (w' : W))⁻¹) := by group
        _ = (l (w' : W) * (w' : W)⁻¹) * ((w : W) * (l (w' : W))⁻¹) := by rw [h1]
        _ = (l (w' : W) * (l (w' : W))⁻¹) * ((w : W) * (w' : W)⁻¹) := by ac_rfl
        _ = (w : W) * (w' : W)⁻¹ := by rw [mul_inv_cancel, one_mul]
    have h3 := h.eq_one_of_fixed hY hl hy hly (Y.mul_mem w.2 (Y.inv_mem w'.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hsurj : Function.Surjective ψ := Finite.surjective_of_injective hinj
  intro u hu
  obtain ⟨w, hw⟩ := hsurj ⟨u, hu⟩
  have hu' : l (w : W) * (w : W)⁻¹ = u := congrArg Subtype.val hw
  rw [← hu']
  exact Subgroup.subset_closure ⟨l, hl, w, Subgroup.mem_top _, rfl⟩

theorem SevenCfg.eq_one_of_fix_all (h : SevenCfg M L Z) {k : MulAut W}
    (hk : ∀ Y ∈ conjSubs M Z, ∀ y ∈ Y, k y = y) : k = 1 := by
  have hle : sSup (conjSubs M Z) ≤ MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id W) :=
    sSup_le fun Y hY y hy => hk Y hY y hy
  rw [h.sup] at hle
  exact MulEquiv.ext fun w => hle (Subgroup.mem_top w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
