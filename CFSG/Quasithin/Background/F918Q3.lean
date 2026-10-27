module

public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.F918Q2

public section

namespace CFSG.Quasithin

open CFSG.Open

section Abstract

variable {Y : Type} [CommGroup Y]

private theorem pow_apply_eq_of_eqOnQ3 {D : Subgroup Y} {g h : MulAut Y}
    (hh : ∀ d ∈ D, h d ∈ D) (hgh : ∀ d ∈ D, g d = h d) :
    ∀ j : ℕ, ∀ d ∈ D, (g ^ j) d = (h ^ j) d := by
  intro j
  induction j with
  | zero => intro d _; simp
  | succ j ih =>
    intro d hd
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hgh d hd, ih _ (hh d hd)]

theorem eq_one_of_trivial_mod_of_pCoreOf_eq_bot (hY : ∀ y : Y, y ^ 2 = 1)
    {X : Subgroup (MulAut Y)} {D : Subgroup Y} (hD : ∀ g ∈ X, ∀ d ∈ D, g d ∈ D)
    (hO2 : pCoreOf 2 X = ⊥) (h2 : ∀ g ∈ X, ∃ k : ℕ, ∀ d ∈ D, (g ^ (2 ^ k)) d = d) :
    ∀ g ∈ X, (∀ y : Y, g y * y⁻¹ ∈ D) → g = 1 := by
  let K : Subgroup (MulAut Y) :=
    { carrier := {g | g ∈ X ∧ ∀ y : Y, g y * y⁻¹ ∈ D}
      one_mem' := ⟨X.one_mem, fun y => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, fun y => by
        have e : (a * b) y * y⁻¹ = (a (b y) * (b y)⁻¹) * (b y * y⁻¹) := by
          rw [MulAut.mul_apply, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact D.mul_mem (ha.2 _) (hb.2 _)⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, fun y => by
        have e : a⁻¹ y * y⁻¹ = (a (a⁻¹ y) * (a⁻¹ y)⁻¹)⁻¹ := by simp
        rw [e]
        exact D.inv_mem (ha.2 _)⟩ }
  have hconj : ∀ x ∈ X, ∀ g ∈ K, x * g * x⁻¹ ∈ K := by
    intro x hx g hg
    refine ⟨X.mul_mem (X.mul_mem hx hg.1) (X.inv_mem hx), fun y => ?_⟩
    have e : (x * g * x⁻¹) y * y⁻¹ = x (g (x⁻¹ y) * (x⁻¹ y)⁻¹) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact hD x hx _ (hg.2 _)
  have hnorm : X ≤ Subgroup.normalizer (K : Set (MulAut Y)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj x hx g, fun h => ?_⟩
    have h1 := hconj x⁻¹ (X.inv_mem hx) _ h
    have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [e] at h1
  have hK2 : IsPGroup 2 K := by
    intro g
    obtain ⟨k, hk⟩ := h2 g g.2.1
    refine ⟨k + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ, pow_mul, sq]
    ext y
    obtain ⟨d, hdD, hdy⟩ : ∃ d ∈ D, ((g : MulAut Y) ^ 2 ^ k) y = d * y :=
      ⟨_, (K.pow_mem g.2 (2 ^ k)).2 y, (inv_mul_cancel_right _ _).symm⟩
    rw [MulAut.mul_apply, MulAut.one_apply, hdy, map_mul, hk d hdD, hdy, ← mul_assoc, ← sq, hY,
      one_mul]
  have hKO : K ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun g hg => hg.1) hnorm hK2
  intro g hg hgD
  have h := hKO ⟨hg, hgD⟩
  rwa [hO2, Subgroup.mem_bot] at h

end Abstract

section D36

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem L_fix_UtQ3 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ L, g (t u) = t u := by
  intro u hu g hg
  obtain ⟨-, -, -, hperm⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have h1 : conjAutSub t⁻¹ L = conjAutSub t L := by
    rcases hperm t⁻¹ (T.inv_mem n.tT) with h | h
    · exfalso
      apply n.tn
      have : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
      simpa using inv_mem this
    · exact h
  have h3 : t⁻¹ * g * t ∈ conjAutSub t L := by
    rw [← h1, mem_conjAutSub_iff]
    simpa [mul_assoc] using hg
  calc g (t u) = t ((t⁻¹ * g * t) u) := by simp [MulAut.mul_apply]
    _ = t u := by rw [(d36_part1 hL38 n).2 u hu _ h3]

private theorem Mp_fix_DQ3 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ m ∈ Mp, ∀ d ∈ commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom,
      m d = d := by
  have hle : Mp ≤
      centSub (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) := by
    rw [n.Mp_eq]
    refine sup_le (fun g hg d hd => ?_) (fun g hg d hd => (d36_part1 hL38 n).2 d hd.1 g hg)
    obtain ⟨u, hu, rfl⟩ := hd.2
    exact L_fix_UtQ3 hL38 n u hu g hg
  intro m hm d hd
  exact hle hm d hd

theorem d36_faithful_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ g ∈ autSub (Mp ⊔ T) (orbSup T V),
      (∀ y : ↥(orbSup T V), g y * y⁻¹ ∈
        (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
          ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → g = 1 := by
  have hY : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using n.std.hyp.exp y.1)
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [n.std.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  have hD : ∀ g ∈ autSub (Mp ⊔ T) (orbSup T V), ∀ d ∈
      (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V),
      g d ∈ (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) := by
    intro g hg d hd
    rcases d36_perm_Y hL38 n g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(h1 d).mpr hd.1, (h2 d).mpr hd.2⟩
    · refine ⟨?_, ?_⟩
      · rw [← h2]
        exact ⟨d, hd.2, rfl⟩
      · rw [← h1]
        exact ⟨d, hd.1, rfl⟩
  have hres : ∀ s (hs : s ∈ T),
      resHom (orbSup T V) ⟨s, le_stabSub_orbSup T V hs⟩ ∈ autSub (Mp ⊔ T) (orbSup T V) :=
    fun _ hs => mem_autSub.mpr ⟨_, le_sup_right (a := Mp) hs, rfl⟩
  have hact : ∀ g ∈ autSub (Mp ⊔ T) (orbSup T V), ∃ s ∈ T, ∀ d ∈
      (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V),
      ((g d : ↥(orbSup T V)) : W) = s d := by
    intro g hg
    obtain ⟨y, hyX, rfl⟩ := mem_autSub.mp hg
    have hy : (y : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hyX
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hy
    obtain ⟨m, hm, s, hs, hms⟩ := hy
    refine ⟨s, hs, fun d hd => ?_⟩
    have hsd := hD _ (hres s hs) d hd
    rw [resHom_apply, ← hms, MulAut.mul_apply]
    exact Mp_fix_DQ3 hL38 n m hm _ ⟨hsd.1, hsd.2⟩
  have h2 : ∀ g ∈ autSub (Mp ⊔ T) (orbSup T V), ∃ k : ℕ, ∀ d ∈
      (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V),
      (g ^ (2 ^ k)) d = d := by
    intro g hg
    obtain ⟨s, hs, e⟩ := hact g hg
    obtain ⟨k, hk⟩ := n.std.hyp.sylow.2.1 ⟨s, hs⟩
    let ys : stabSub (orbSup T V) := ⟨s, le_stabSub_orbSup T V hs⟩
    have hys : ys ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine ⟨k, fun d hd => ?_⟩
    rw [pow_apply_eq_of_eqOnQ3 (hD _ (hres s hs)) (fun d hd => Subtype.ext (e d hd)) _ d hd,
      ← map_pow, hys, map_one]
    rfl
  exact eq_one_of_trivial_mod_of_pCoreOf_eq_bot hY hD (d36_pCoreOf_eq_bot hL38 n) h2

end D36

end CFSG.Quasithin
