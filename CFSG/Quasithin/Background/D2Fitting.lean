module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.Quasithin.Background.D2Involutions
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] noncomputable def fittingOf (X : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  (CFSG.fittingSubgroup X).map X.subtype

theorem fittingOf_le (X : Subgroup (MulAut V)) : fittingOf X ≤ X := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem fittingOf_nilpotent [Finite V] (X : Subgroup (MulAut V)) :
    Group.IsNilpotent (fittingOf X) :=
  Group.nilpotent_of_mulEquiv (G := CFSG.fittingSubgroup X)
    (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective)

theorem conj_mem_fittingOf {X : Subgroup (MulAut V)} {g f : MulAut V} (hg : g ∈ X)
    (hf : f ∈ fittingOf X) : g * f * g⁻¹ ∈ fittingOf X := by
  obtain ⟨f', hf', rfl⟩ := hf
  have := (CFSG.fittingSubgroup_normal (G := X)).conj_mem f' hf' ⟨g, hg⟩
  exact ⟨_, this, rfl⟩

section Prime

variable [Finite V]

theorem zpowers_eq_of_prime_card {p : ℕ} [Fact p.Prime] {Y : Subgroup (MulAut V)}
    (hY : Nat.card Y = p) {g : MulAut V} (hg : g ∈ Y) (hg1 : g ≠ 1) : Subgroup.zpowers g = Y := by
  have hle : Subgroup.zpowers g ≤ Y := (Subgroup.zpowers_le).mpr hg
  have hdvd : orderOf g ∣ p := by
    have : orderOf (⟨g, hg⟩ : Y) ∣ Nat.card Y := orderOf_dvd_natCard _
    rwa [hY, Subgroup.orderOf_mk] at this
  have hne : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = p := ((Nat.dvd_prime Fact.out).mp hdvd).resolve_left hne
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, hord, hY]

theorem exists_generator_of_prime_card {p : ℕ} [Fact p.Prime] {Y : Subgroup (MulAut V)}
    (hY : Nat.card Y = p) : ∃ y : MulAut V, y ∈ Y ∧ y ≠ 1 ∧ Subgroup.zpowers y = Y ∧
      orderOf y = p := by
  have hp1 : 1 < Nat.card Y := by rw [hY]; exact (Fact.out : p.Prime).one_lt
  obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Y)).mp (by
    intro h
    rw [h] at hp1
    simp at hp1)
  have hy1 : (y : MulAut V) ≠ 1 := fun h => hy (Subtype.ext h)
  have hz := zpowers_eq_of_prime_card hY y.2 hy1
  refine ⟨y, y.2, hy1, hz, ?_⟩
  rw [← Nat.card_zpowers, hz, hY]

theorem prime_dvd_card_sub_one {p : ℕ} [Fact p.Prime] {Y : Subgroup (MulAut V)}
    (hY : Nat.card Y = p) {F : Subgroup V} (hF : ∀ g ∈ Y, ∀ f ∈ F, g f ∈ F)
    (hfix : F ⊓ fixV Y = ⊥) : p ∣ Nat.card F - 1 := by
  let Ω : Set V := {c | c ∈ F ∧ c ≠ 1}
  have hΩ : ∀ g ∈ Y, ∀ c ∈ Ω, g c ∈ Ω := by
    rintro g hg c ⟨hcF, hc1⟩
    exact ⟨hF g hg c hcF, fun h => hc1 (g.injective (by rw [h, map_one]))⟩
  have hfree : ∀ g ∈ Y, ∀ c ∈ Ω, g c = c → g = 1 := by
    rintro g hg c ⟨hcF, hc1⟩ hgc
    by_contra hg1
    have hz := zpowers_eq_of_prime_card hY hg hg1
    have hcfix : c ∈ fixV Y := by
      rw [← hz]
      exact mem_fixV_zpowers_iff.mpr hgc
    have : c ∈ F ⊓ fixV Y := ⟨hcF, hcfix⟩
    rw [hfix, Subgroup.mem_bot] at this
    exact hc1 this
  have h1 := card_dvd_card_of_free hΩ hfree
  rw [hY] at h1
  have h2 := card_ne_one_add_one F
  have h3 : Nat.card ↥Ω = Nat.card {c : V // c ∈ F ∧ c ≠ 1} := rfl
  rw [h3] at h1
  rwa [show Nat.card {c : V // c ∈ F ∧ c ≠ 1} = Nat.card F - 1 by omega] at h1

end Prime

@[expose] def Xk (X : Subgroup (MulAut V)) (k : ℕ) : Set (Subgroup (MulAut V)) :=
  {Y | Y ≤ fittingOf X ∧ Nat.card Y = 2 * k + 1 ∧ rk (commV Y) = 2 * k}

@[expose] def Gk (X : Subgroup (MulAut V)) (k : ℕ) : Subgroup (MulAut V) := ⨆ Y ∈ Xk X k, Y

theorem fact_prime_two_mul_add_one {k : ℕ} (hk : k = 1 ∨ k = 2) : Fact (2 * k + 1).Prime := by
  rcases hk with rfl | rfl <;> exact ⟨by norm_num⟩

section Xk

variable [Finite V]

theorem Xk_decomp (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {k : ℕ}
    {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk X k) :
    commV Y ⊔ fixV Y = ⊤ ∧ commV Y ⊓ fixV Y = ⊥ := by
  have hodd : Odd (Nat.card Y) := by
    rw [hY.2.1]; exact ⟨k, rfl⟩
  obtain ⟨h1, h2⟩ := coprime_decomp hodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem Xk_irreducible (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {k : ℕ}
    (hk : k = 1 ∨ k = 2) {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk X k) {F : Subgroup V}
    (hF : ∀ g ∈ Y, ∀ f ∈ F, g f ∈ F) (hFle : F ≤ commV Y) (hF0 : F ≠ ⊥) : F = commV Y := by
  have := fact_prime_two_mul_add_one hk
  obtain ⟨-, hinf⟩ := Xk_decomp hV hY
  have hfix : F ⊓ fixV Y = ⊥ := by
    refine le_bot_iff.mp ?_
    calc F ⊓ fixV Y ≤ commV Y ⊓ fixV Y := inf_le_inf_right _ hFle
      _ = ⊥ := hinf
      _ ≤ ⊥ := le_rfl
  have hdvd := prime_dvd_card_sub_one hY.2.1 hF hfix
  rw [card_eq_two_pow hV F] at hdvd
  have hrkle : rk F ≤ 2 * k := hY.2.2 ▸ rk_mono hFle
  have hrk0 : rk F ≠ 0 := fun h => hF0 ((rk_eq_zero_iff hV).mp h)
  have hrk : rk F = 2 * k := by
    rcases hk with rfl | rfl
    · have key : ∀ e ≤ 2, e ≠ 0 → 3 ∣ 2 ^ e - 1 → e = 2 := by decide
      exact key _ hrkle hrk0 hdvd
    · have key : ∀ e ≤ 4, e ≠ 0 → 5 ∣ 2 ^ e - 1 → e = 4 := by decide
      exact key _ hrkle hrk0 hdvd
  exact eq_of_le_of_rk_le hV hFle (by rw [hY.2.2, hrk])

omit [Finite V] in
theorem conj_eq_of_commute {Y Z : Subgroup (MulAut V)}
    (hcomm : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y) {g p : MulAut V} (hg : g ∈ Z) (hp : p ∈ Y) :
    g * p * g⁻¹ = p := by
  rw [← hcomm p hp g hg, mul_inv_cancel_right]

omit [Finite V] in
theorem commute_stab {Y Z : Subgroup (MulAut V)} (hcomm : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y) :
    Z ≤ stabSub (commV Y) ∧ Z ≤ stabSub (fixV Y) := by
  have h1 : ∀ g ∈ Z, ∀ p ∈ Y, g * p * g⁻¹ ∈ Y := fun g hg p hp => by
    rw [conj_eq_of_commute hcomm hg hp]; exact hp
  have h2 : ∀ g ∈ Z, ∀ p ∈ Y, g⁻¹ * p * g ∈ Y := fun g hg p hp => by
    have := conj_eq_of_commute hcomm (Z.inv_mem hg) hp
    rw [inv_inv] at this
    rw [this]; exact hp
  exact ⟨fun g hg => mem_stabSub_commV (h1 g hg) (h2 g hg),
    fun g hg => mem_stabSub_fixV (h1 g hg) (h2 g hg)⟩

theorem Xk_centralizes (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {k : ℕ}
    (hk : k = 1 ∨ k = 2) {Y Z : Subgroup (MulAut V)} (hY : Y ∈ Xk X k) (hZ : Z ∈ Xk X k)
    (hYZ : Y ≠ Z) (hcomm : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y) :
    ∀ z ∈ Z, ∀ w ∈ commV Y, z w = w := by
  have := fact_prime_two_mul_add_one hk
  obtain ⟨hsupY, hinfY⟩ := Xk_decomp hV hY
  obtain ⟨y, hyY, hy1, hyy, hyord⟩ := exists_generator_of_prime_card hY.2.1
  obtain ⟨z, hzZ, hz1, hzz, hzord⟩ := exists_generator_of_prime_card hZ.2.1
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    rw [← hyy] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl y).zpow_zpow i j).eq
  obtain ⟨hZW, hZC⟩ := commute_stab hcomm
  obtain ⟨hYW, -⟩ := commute_stab hYab
  have hFinv : ∀ g ∈ Y, ∀ f ∈ commV Y ⊓ fixV Z, g f ∈ commV Y ⊓ fixV Z := by
    intro g hg f hf
    refine ⟨((hYW hg) f).mpr hf.1, fun z' hz' => ?_⟩
    have h1 : z' * g = g * z' := (hcomm g hg z' hz').symm
    calc z' (g f) = (z' * g) f := rfl
      _ = (g * z') f := by rw [h1]
      _ = g (z' f) := rfl
      _ = g f := by rw [hf.2 z' hz']
  by_cases hF0 : commV Y ⊓ fixV Z = ⊥
  · exfalso
    have hWz : ∀ x ∈ Subgroup.zpowers z, ∀ w ∈ commV Y, x w ∈ commV Y := by
      intro x hx w hw
      have : Subgroup.zpowers z ≤ stabSub (commV Y) := by rw [hzz]; exact hZW
      exact ((this hx) w).mpr hw
    have hCz : ∀ x ∈ Subgroup.zpowers z, ∀ w ∈ fixV Y, x w ∈ fixV Y := by
      intro x hx w hw
      have : Subgroup.zpowers z ≤ stabSub (fixV Y) := by rw [hzz]; exact hZC
      exact ((this hx) w).mpr hw
    have hrk1 := rk_commSub_add_rk_inf_fixV hWz
    have hF0' : commV Y ⊓ fixV (Subgroup.zpowers z) = ⊥ := by rw [hzz]; exact hF0
    rw [hF0', rk_bot, hY.2.2] at hrk1
    have hle : commSub (commV Y) (Subgroup.zpowers z) ≤ commV Z := by
      rw [← hzz, commV_eq_commSub (Subgroup.zpowers z)]
      exact commSub_mono le_top le_rfl
    have heq : commSub (commV Y) (Subgroup.zpowers z) = commV Z :=
      eq_of_le_of_rk_le hV hle (by rw [hZ.2.2]; omega)
    have hCfix : ∀ c ∈ fixV Y, z c = c := by
      intro c hc
      have h1 : z c * c⁻¹ ∈ commV Z := Subgroup.subset_closure ⟨z, hzZ, c, rfl⟩
      rw [← heq] at h1
      have h2 : z c * c⁻¹ ∈ commV Y := commSub_le_of_invariant hWz h1
      have h3 : z c * c⁻¹ ∈ fixV Y :=
        Subgroup.mul_mem _ (hCz z (Subgroup.mem_zpowers z) c hc) (Subgroup.inv_mem _ hc)
      have h4 : z c * c⁻¹ ∈ commV Y ⊓ fixV Y := ⟨h2, h3⟩
      rw [hinfY, Subgroup.mem_bot, mul_inv_eq_one] at h4
      exact h4
    have hCZ : ∀ z' ∈ Z, ∀ c ∈ fixV Y, z' c = c := by
      intro z' hz' c hc
      have : c ∈ fixV (Subgroup.zpowers z) := mem_fixV_zpowers_iff.mpr (hCfix c hc)
      rw [hzz] at this
      exact this z' hz'
    let f : ↥Y × ↥Z →* MulAut V :=
      MonoidHom.noncommCoprod Y.subtype Z.subtype (fun a b => hcomm a a.2 b b.2)
    let E := f.range
    have hmemE : ∀ g ∈ E, ∃ a ∈ Y, ∃ b ∈ Z, g = a * b := by
      rintro g ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    have hYE : Y ≤ E := fun g hg => ⟨(⟨g, hg⟩, 1), by
      show (g : MulAut V) * (1 : MulAut V) = g
      exact mul_one g⟩
    have hZE : Z ≤ E := fun g hg => ⟨(1, ⟨g, hg⟩), by
      show (1 : MulAut V) * (g : MulAut V) = g
      exact one_mul g⟩
    have hEdvd : Nat.card E ∣ Nat.card Y * Nat.card Z := by
      have := Subgroup.card_range_dvd f
      rwa [Nat.card_prod] at this
    let Ω : Set V := {c | c ∈ commV Y ∧ c ≠ 1}
    have hΩ : ∀ g ∈ E, ∀ c ∈ Ω, g c ∈ Ω := by
      rintro g hg c ⟨hcW, hc1⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hmemE g hg
      refine ⟨?_, fun h => hc1 ((a * b).injective (by rw [h, map_one]))⟩
      exact ((hYW ha) _).mpr (((hZW hb) c).mpr hcW)
    have hfree : ∀ g ∈ E, ∀ c ∈ Ω, g c = c → g = 1 := by
      rintro g hg c ⟨hcW, hc1⟩ hgc
      obtain ⟨a, ha, b, hb, rfl⟩ := hmemE g hg
      have hU : ∀ y' ∈ Y, ∀ u ∈ commV Y ⊓ fixV (Subgroup.zpowers (a * b)),
          y' u ∈ commV Y ⊓ fixV (Subgroup.zpowers (a * b)) := by
        intro y' hy' u hu
        refine ⟨((hYW hy') u).mpr hu.1, ?_⟩
        show y' u ∈ fixV (Subgroup.zpowers (a * b))
        rw [mem_fixV_zpowers_iff]
        have hc1' : y' * (a * b) = (a * b) * y' := by
          rw [← mul_assoc, hYab y' hy' a ha, mul_assoc, hcomm y' hy' b hb, ← mul_assoc]
        have := mem_fixV_zpowers_iff.mp hu.2
        calc (a * b) (y' u) = ((a * b) * y') u := rfl
          _ = (y' * (a * b)) u := by rw [hc1']
          _ = y' ((a * b) u) := rfl
          _ = y' u := by rw [this]
      have hU0 : commV Y ⊓ fixV (Subgroup.zpowers (a * b)) ≠ ⊥ := by
        intro h
        have : c ∈ commV Y ⊓ fixV (Subgroup.zpowers (a * b)) :=
          ⟨hcW, mem_fixV_zpowers_iff.mpr hgc⟩
        rw [h, Subgroup.mem_bot] at this
        exact hc1 this
      have hUeq := Xk_irreducible hV hk hY hU inf_le_left hU0
      ext v
      have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsupY]; exact Subgroup.mem_top v
      obtain ⟨w, hw, c', hc', rfl⟩ := Subgroup.mem_sup.mp hv
      have h1 : (a * b) w = w := by
        have : w ∈ commV Y ⊓ fixV (Subgroup.zpowers (a * b)) := by rw [hUeq]; exact hw
        exact mem_fixV_zpowers_iff.mp this.2
      have h2 : (a * b) c' = c' := by
        rw [MulAut.mul_apply, hCZ b hb c' hc', hc' a ha]
      rw [map_mul, h1, h2]
      rfl
    have hdvd := card_dvd_card_of_free hΩ hfree
    have hΩcard : Nat.card ↥Ω + 1 = 2 ^ (2 * k) := by
      have h := card_ne_one_add_one (commV Y)
      rw [card_eq_two_pow hV, hY.2.2] at h
      exact h
    have hpE : Nat.card Y ∣ Nat.card E := Subgroup.card_dvd_of_le hYE
    rw [hY.2.1] at hpE hEdvd
    rw [hZ.2.1] at hEdvd
    have hEp : Nat.card E = 2 * k + 1 := by
      rcases hk with rfl | rfl
      · have h2 : (2 : ℕ) ^ (2 * 1) = 4 := by norm_num
        rw [h2] at hΩcard
        have h1 : Nat.card ↥Ω = 3 := by omega
        rw [h1] at hdvd
        exact Nat.dvd_antisymm hdvd hpE
      · have h2 : (2 : ℕ) ^ (2 * 2) = 16 := by norm_num
        rw [h2] at hΩcard
        have h1 : Nat.card ↥Ω = 15 := by omega
        rw [h1] at hdvd
        have h2 := Nat.dvd_gcd hdvd hEdvd
        have h3 : Nat.gcd 15 ((2 * 2 + 1) * (2 * 2 + 1)) = 5 := by norm_num
        rw [h3] at h2
        exact Nat.dvd_antisymm h2 hpE
    have hYEeq : Y = E := Subgroup.eq_of_le_of_card_ge hYE (by rw [hEp, hY.2.1])
    have hZY : Z ≤ Y := hYEeq ▸ hZE
    exact hYZ (Subgroup.eq_of_le_of_card_ge hZY (by rw [hY.2.1, hZ.2.1])).symm
  · have hF := Xk_irreducible hV hk hY hFinv inf_le_left hF0
    intro z' hz' w hw
    have hwF : w ∈ commV Y ⊓ fixV Z := by rw [hF]; exact hw
    exact hwF.2 z' hz'

end Xk

@[expose] def conjBy (g : MulAut V) (Y : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  Y.map (MulAut.conj g).toMonoidHom

theorem mem_conjBy_iff {g x : MulAut V} {Y : Subgroup (MulAut V)} :
    x ∈ conjBy g Y ↔ g⁻¹ * x * g ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_conjBy_of_mem {g y : MulAut V} {Y : Subgroup (MulAut V)} (hy : y ∈ Y) :
    g * y * g⁻¹ ∈ conjBy g Y := ⟨y, hy, by simp [MulAut.conj_apply]⟩

theorem card_conjBy (g : MulAut V) (Y : Subgroup (MulAut V)) :
    Nat.card (conjBy g Y) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjBy_conjBy (g h : MulAut V) (Y : Subgroup (MulAut V)) :
    conjBy g (conjBy h Y) = conjBy (g * h) Y := by
  ext x
  simp only [mem_conjBy_iff]
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [this]

theorem conjBy_one (Y : Subgroup (MulAut V)) : conjBy 1 Y = Y := by
  ext x
  simp [mem_conjBy_iff]

theorem conjBy_mono {g : MulAut V} {Y Z : Subgroup (MulAut V)} (h : Y ≤ Z) :
    conjBy g Y ≤ conjBy g Z := Subgroup.map_mono h

theorem conjBy_injective (g : MulAut V) {Y Z : Subgroup (MulAut V)}
    (h : conjBy g Y = conjBy g Z) : Y = Z := by
  have := congrArg (conjBy g⁻¹) h
  rwa [conjBy_conjBy, conjBy_conjBy, inv_mul_cancel, conjBy_one, conjBy_one] at this

theorem commV_conjBy (g : MulAut V) (Y : Subgroup (MulAut V)) :
    commV (conjBy g Y) = (commV Y).map g.toMonoidHom := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, v, rfl⟩
    refine ⟨y (g⁻¹ v) * (g⁻¹ v)⁻¹, ⟨y, hy, g⁻¹ v, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  · rintro ⟨_, ⟨y, hy, v, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, mem_conjBy_of_mem hy, g v, ?_⟩
    simp [map_mul, map_inv, mul_assoc]

theorem rk_commV_conjBy [Finite V] (g : MulAut V) (Y : Subgroup (MulAut V)) :
    rk (commV (conjBy g Y)) = rk (commV Y) := by
  rw [commV_conjBy]
  unfold rk
  rw [Subgroup.card_map_of_injective g.injective]

theorem conjBy_le_fittingOf {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X)
    {Y : Subgroup (MulAut V)} (hY : Y ≤ fittingOf X) : conjBy g Y ≤ fittingOf X := by
  rintro _ ⟨y, hy, rfl⟩
  exact conj_mem_fittingOf hg (hY hy)

theorem conjBy_mem_Xk [Finite V] {X : Subgroup (MulAut V)} {k : ℕ} {g : MulAut V} (hg : g ∈ X)
    {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk X k) : conjBy g Y ∈ Xk X k :=
  ⟨conjBy_le_fittingOf hg hY.1, by rw [card_conjBy]; exact hY.2.1, by
    rw [rk_commV_conjBy]; exact hY.2.2⟩

theorem commute_of_normalizes_prime [Finite V] {p : ℕ} [Fact p.Prime] {A : Subgroup (MulAut V)}
    (hA : Nat.card A = p) {y : MulAut V} (hy : orderOf y = p)
    (hn : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hn' : ∀ a ∈ A, y⁻¹ * a * y ∈ A) :
    ∀ a ∈ A, y * a = a * y := by
  have hmem : y ∈ Subgroup.normalizer (A : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hn h, fun h' => ?_⟩
    have := hn' _ h'
    simpa [mul_assoc] using this
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  set ψ := A.normalizerMonoidHom ⟨y, hmem⟩ with hψ
  have h1 : orderOf ψ ∣ p := by
    have := orderOf_map_dvd A.normalizerMonoidHom (⟨y, hmem⟩ : Subgroup.normalizer (A : Set (MulAut V)))
    rwa [Subgroup.orderOf_mk, hy] at this
  have h2 : orderOf ψ ∣ p - 1 := by
    have := orderOf_dvd_natCard ψ
    rwa [IsCyclic.card_mulAut, hA, Nat.totient_prime Fact.out] at this
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h3 : orderOf ψ = 1 := by
    have := Nat.dvd_gcd h1 h2
    have hg : Nat.gcd p (p - 1) = 1 := by
      have : Nat.gcd p (p - 1) = Nat.gcd (p - 1 + 1) (p - 1) := by congr 1; omega
      rw [this]
      simp
    rwa [hg, Nat.dvd_one] at this
  have hψ1 : ψ = 1 := orderOf_eq_one_iff.mp h3
  intro a ha
  have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : MulAut V)) hψ1
  simp only [hψ, MulAut.one_apply] at this
  have h4 : y * a * y⁻¹ = a := this
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4


@[expose] def CommFamily (S : Set (Subgroup (MulAut V))) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

section CommFamily

variable [Finite V]

theorem disjoint_commV_biSup (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {k : ℕ}
    (hk : k = 1 ∨ k = 2) {S : Set (Subgroup (MulAut V))} (hS : S ⊆ Xk X k) (hc : CommFamily S)
    {Y : Subgroup (MulAut V)} (hY : Y ∈ S) :
    Disjoint (commV Y) (⨆ Z ∈ S, ⨆ (_ : Z ≠ Y), commV Z) := by
  rw [disjoint_iff]
  have hle : (⨆ Z ∈ S, ⨆ (_ : Z ≠ Y), commV Z) ≤ fixV Y := by
    refine iSup₂_le fun Z hZ => iSup_le fun hZY => ?_
    intro w hw y hy
    exact Xk_centralizes hV hk (hS hZ) (hS hY) hZY (hc Z hZ Y hY) y hy w hw
  refine le_bot_iff.mp ?_
  calc commV Y ⊓ (⨆ Z ∈ S, ⨆ (_ : Z ≠ Y), commV Z) ≤ commV Y ⊓ fixV Y :=
        inf_le_inf_left _ hle
    _ = ⊥ := (Xk_decomp hV (hS hY)).2
    _ ≤ ⊥ := le_rfl

theorem disjoint_biSup (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {k : ℕ}
    (hk : k = 1 ∨ k = 2) {S : Set (Subgroup (MulAut V))} (hS : S ⊆ Xk X k) (hc : CommFamily S)
    {Y : Subgroup (MulAut V)} (hY : Y ∈ S) :
    Disjoint Y (⨆ Z ∈ S, ⨆ (_ : Z ≠ Y), Z) := by
  rw [disjoint_iff]
  obtain ⟨hsup, -⟩ := Xk_decomp hV (hS hY)
  have hle : (⨆ Z ∈ S, ⨆ (_ : Z ≠ Y), Z) ≤ centSub (commV Y) := by
    refine iSup₂_le fun Z hZ => iSup_le fun hZY => ?_
    intro z hz w hw
    exact Xk_centralizes hV hk (hS hY) (hS hZ) (Ne.symm hZY) (hc Y hY Z hZ) z hz w hw
  refine le_bot_iff.mp ?_
  intro g ⟨hgY, hgZ⟩
  have hg := hle hgZ
  rw [Subgroup.mem_bot]
  have hg1 : ∀ w ∈ commV Y, g w = w := hg
  have hg2 : ∀ c ∈ fixV Y, g c = c := fun c hc => hc g hgY
  ext v
  have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨w, hw, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hg1 w hw, hg2 c hc']
  rfl

theorem rk_add_rk_le_commV {y : MulAut V} {W₀ W₁ W₂ : Subgroup V}
    (h01 : W₀ ⊓ W₁ = ⊥) (h12 : W₁ ⊓ W₂ = ⊥) (h0 : Disjoint W₀ (W₁ ⊔ W₂))
    (hy0 : ∀ w ∈ W₀, y w ∈ W₁) (hy1 : ∀ w ∈ W₁, y w ∈ W₂) :
    rk W₀ + rk W₁ ≤ rk (commV (Subgroup.zpowers y)) := by
  have hr0 := rk_map_add_rk_inf_ker (commHom y) W₀
  have hr1 := rk_map_add_rk_inf_ker (commHom y) W₁
  rw [ker_commHom] at hr0 hr1
  have hk0 : W₀ ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w ⟨hw0, hw⟩
    have hyw : y w = w := mem_fixV_zpowers_iff.mp hw
    have : w ∈ W₀ ⊓ W₁ := ⟨hw0, by rw [← hyw]; exact hy0 w hw0⟩
    rw [h01] at this
    exact this
  have hk1 : W₁ ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w ⟨hw1, hw⟩
    have hyw : y w = w := mem_fixV_zpowers_iff.mp hw
    have : w ∈ W₁ ⊓ W₂ := ⟨hw1, by rw [← hyw]; exact hy1 w hw1⟩
    rw [h12] at this
    exact this
  rw [hk0, rk_bot] at hr0
  rw [hk1, rk_bot] at hr1
  have hdisj : W₀.map (commHom y) ⊓ W₁.map (commHom y) = ⊥ := by
    refine le_bot_iff.mp ?_
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have ha1 : a = 1 := by
      have h1 : (y a)⁻¹ * (y b) * b⁻¹ ∈ W₁ ⊔ W₂ :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
          (W₁.inv_mem (hy0 a ha))) (Subgroup.mem_sup_right (hy1 b hb)))
          (Subgroup.mem_sup_left (W₁.inv_mem hb))
      have h2 : a⁻¹ = (y a)⁻¹ * (y b) * b⁻¹ := by
        have : y a * a⁻¹ = y b * b⁻¹ := hab.symm
        calc a⁻¹ = (y a)⁻¹ * (y a * a⁻¹) := by group
          _ = (y a)⁻¹ * (y b * b⁻¹) := by rw [this]
          _ = (y a)⁻¹ * (y b) * b⁻¹ := by group
      have h3 : a⁻¹ ∈ W₀ ⊓ (W₁ ⊔ W₂) := ⟨W₀.inv_mem ha, by rw [h2]; exact h1⟩
      rw [h0.eq_bot, Subgroup.mem_bot, inv_eq_one] at h3
      exact h3
    subst ha1
    simp
  have hle : W₀.map (commHom y) ⊔ W₁.map (commHom y) ≤ commV (Subgroup.zpowers y) := by
    rw [commV_zpowers_eq_map]
    exact sup_le (Subgroup.map_mono le_top) (Subgroup.map_mono le_top)
  have hsum := rk_sup_add_rk_inf (W₀.map (commHom y)) (W₁.map (commHom y))
  rw [hdisj, rk_bot] at hsum
  have := rk_mono hle
  omega

structure MaxComm (X : Subgroup (MulAut V)) (k : ℕ) (Δ : Set (Subgroup (MulAut V))) : Prop where
  subset : Δ ⊆ Xk X k
  comm : CommFamily Δ
  max : ∀ S : Set (Subgroup (MulAut V)), S ⊆ Xk X k → CommFamily S → Δ ⊆ S → S ⊆ Δ

variable {X : Subgroup (MulAut V)} {k : ℕ} {Δ : Set (Subgroup (MulAut V))}

omit [Finite V] in
theorem MaxComm.le_iSup (_h : MaxComm X k Δ) {A : Subgroup (MulAut V)} (hA : A ∈ Δ) :
    A ≤ ⨆ B ∈ Δ, B := le_iSup₂ (f := fun B (_ : B ∈ Δ) => B) A hA

omit [Finite V] in
theorem MaxComm.abelian (h : MaxComm X k Δ) {d d' : MulAut V} (hd : d ∈ ⨆ A ∈ Δ, A)
    (hd' : d' ∈ ⨆ A ∈ Δ, A) : d * d' = d' * d := by
  have h1 : ∀ A ∈ Δ, (⨆ B ∈ Δ, B) ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    intro A hA
    refine iSup₂_le fun B hB b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.comm A hA B hB a ha b hb
  have h2 : (⨆ B ∈ Δ, B) ≤
      Subgroup.centralizer ((⨆ B ∈ Δ, B : Subgroup (MulAut V)) : Set (MulAut V)) :=
    iSup₂_le fun A hA => Subgroup.le_centralizer_iff.mpr (h1 A hA)
  have := Subgroup.mem_centralizer_iff.mp (h2 hd') d hd
  exact this

omit [Finite V] in
theorem MaxComm.mem_of_le (h : MaxComm X k Δ) {Y' : Subgroup (MulAut V)} (hY' : Y' ∈ Xk X k)
    (hle : Y' ≤ ⨆ A ∈ Δ, A) : Y' ∈ Δ := by
  have hAD : ∀ C ∈ insert Y' Δ, C ≤ ⨆ A ∈ Δ, A := by
    intro C hC
    rcases hC with rfl | hC
    · exact hle
    · exact h.le_iSup hC
  have hcomm : CommFamily (insert Y' Δ) := by
    intro A hA B hB a ha b hb
    exact h.abelian (hAD A hA ha) (hAD B hB hb)
  exact h.max (insert Y' Δ) (Set.insert_subset hY' h.subset) hcomm (Set.subset_insert _ _)
    (Set.mem_insert _ _)

omit [Finite V] in
theorem conjBy_pow_eq {g : MulAut V} {A : Subgroup (MulAut V)} (h : conjBy g A = A) (n : ℕ) :
    conjBy (g ^ n) A = A := by
  induction n with
  | zero => rw [pow_zero, conjBy_one]
  | succ n ih => rw [pow_succ', ← conjBy_conjBy, ih, h]

omit [Finite V] in
theorem commV_le_biSup {S : Set (Subgroup (MulAut V))} {Y Z : Subgroup (MulAut V)} (hZ : Z ∈ S)
    (hZY : Z ≠ Y) : commV Z ≤ ⨆ Z' ∈ S, ⨆ (_ : Z' ≠ Y), commV Z' :=
  le_iSup₂_of_le Z hZ (le_iSup (fun _ : Z ≠ Y => commV Z) hZY)

theorem MaxComm.mem_of_normalizes (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2)
    (h : MaxComm X k Δ) {Y₀ : Subgroup (MulAut V)} (hY₀ : Y₀ ∈ Xk X k)
    (hn : Y₀ ≤ Subgroup.normalizer ((⨆ A ∈ Δ, A : Subgroup (MulAut V)) : Set (MulAut V))) :
    Y₀ ∈ Δ := by
  have := fact_prime_two_mul_add_one hk
  obtain ⟨y, hyY, hy1, hyz, hyord⟩ := exists_generator_of_prime_card hY₀.2.1
  have hyX : y ∈ X := fittingOf_le X (hY₀.1 hyY)
  have hyD : ∀ d, d ∈ (⨆ A ∈ Δ, A : Subgroup (MulAut V)) ↔
      y * d * y⁻¹ ∈ (⨆ A ∈ Δ, A : Subgroup (MulAut V)) :=
    Subgroup.mem_normalizer_iff.mp (hn hyY)
  have hconj : ∀ A ∈ Δ, conjBy y A ∈ Δ := by
    intro A hA
    refine h.mem_of_le (conjBy_mem_Xk hyX (h.subset hA)) ?_
    rintro _ ⟨a, ha, rfl⟩
    have haD : a ∈ (⨆ B ∈ Δ, B : Subgroup (MulAut V)) := h.le_iSup hA ha
    exact (hyD a).mp haD
  have hfix : ∀ A ∈ Δ, conjBy y A = A := by
    intro A₀ hA₀
    by_contra hne
    have hA₁ : conjBy y A₀ ∈ Δ := hconj A₀ hA₀
    have hA₂ : conjBy y (conjBy y A₀) ∈ Δ := hconj _ hA₁
    have h21 : conjBy y (conjBy y A₀) ≠ conjBy y A₀ := fun h' => hne (conjBy_injective y h')
    have h20 : conjBy y (conjBy y A₀) ≠ A₀ := by
      intro h'
      apply hne
      have h2 : conjBy (y * y) A₀ = A₀ := by rw [← conjBy_conjBy]; exact h'
      have h3 := conjBy_pow_eq h2 (k + 1)
      have h4 : (y * y) ^ (k + 1) = y := by
        rw [← pow_two, ← pow_mul]
        have : y ^ (2 * (k + 1)) = y ^ (2 * k + 1) * y := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
        rw [this, ← hyord, pow_orderOf_eq_one, one_mul]
      rw [h4] at h3
      exact h3
    have hW₁ := commV_conjBy y A₀
    have hW₂ := commV_conjBy y (conjBy y A₀)
    have hy0 : ∀ w ∈ commV A₀, y w ∈ commV (conjBy y A₀) := by
      intro w hw
      rw [hW₁]
      exact ⟨w, hw, rfl⟩
    have hy1 : ∀ w ∈ commV (conjBy y A₀), y w ∈ commV (conjBy y (conjBy y A₀)) := by
      intro w hw
      rw [hW₂]
      exact ⟨w, hw, rfl⟩
    have hd0 := disjoint_commV_biSup hV hk h.subset h.comm hA₀
    have hd1 := disjoint_commV_biSup hV hk h.subset h.comm hA₁
    have hne' : conjBy y A₀ ≠ A₀ := hne
    have h01 : commV A₀ ⊓ commV (conjBy y A₀) = ⊥ :=
      (disjoint_iff.mp (hd0.mono_right (commV_le_biSup hA₁ hne')))
    have h12 : commV (conjBy y A₀) ⊓ commV (conjBy y (conjBy y A₀)) = ⊥ :=
      (disjoint_iff.mp (hd1.mono_right (commV_le_biSup hA₂ h21)))
    have h0 : Disjoint (commV A₀) (commV (conjBy y A₀) ⊔ commV (conjBy y (conjBy y A₀))) :=
      hd0.mono_right (sup_le (commV_le_biSup hA₁ hne') (commV_le_biSup hA₂ h20))
    have hrk := rk_add_rk_le_commV h01 h12 h0 hy0 hy1
    have r0 : rk (commV A₀) = 2 * k := (h.subset hA₀).2.2
    have r1 : rk (commV (conjBy y A₀)) = 2 * k := (h.subset hA₁).2.2
    have r2 : rk (commV (Subgroup.zpowers y)) = 2 * k := by rw [hyz]; exact hY₀.2.2
    rcases hk with rfl | rfl <;> omega
  have hcomm : ∀ A ∈ Δ, ∀ a ∈ A, y * a = a * y := by
    intro A hA
    refine commute_of_normalizes_prime (p := 2 * k + 1) (h.subset hA).2.1 hyord ?_ ?_
    · intro a ha
      have := mem_conjBy_of_mem (g := y) ha
      rwa [hfix A hA] at this
    · intro a ha
      have : a ∈ conjBy y A := by rw [hfix A hA]; exact ha
      exact mem_conjBy_iff.mp this
  have hY₀ab : ∀ a ∈ Y₀, ∀ b ∈ Y₀, a * b = b * a := by
    intro a ha b hb
    rw [← hyz] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl y).zpow_zpow i j).eq
  have hY₀comm : ∀ A ∈ Δ, ∀ a ∈ A, ∀ z ∈ Y₀, z * a = a * z := by
    intro A hA a ha z hz
    rw [← hyz] at hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute y a from hcomm A hA a ha) i)).eq
  have hS : CommFamily (insert Y₀ Δ) := by
    intro A hA B hB a ha b hb
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact hY₀ab a ha b hb
    · exact hY₀comm B hB b hb a ha
    · exact (hY₀comm A hA a ha b hb).symm
    · exact h.comm A hA B hB a ha b hb
  exact h.max (insert Y₀ Δ) (Set.insert_subset hY₀ h.subset) hS (Set.subset_insert _ _)
    (Set.mem_insert _ _)

theorem MaxComm.Gk_le_normalizer (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2)
    (h : MaxComm X k Δ) :
    Gk X k ≤ Subgroup.normalizer ((⨆ A ∈ Δ, A : Subgroup (MulAut V)) : Set (MulAut V)) := by
  set D : Subgroup (MulAut V) := ⨆ A ∈ Δ, A with hD
  have hGF : Gk X k ≤ fittingOf X := iSup₂_le fun Y hY => hY.1
  have hDG : D ≤ Gk X k := iSup₂_le fun A hA =>
    le_iSup₂ (f := fun Y (_ : Y ∈ Xk X k) => Y) A (h.subset hA)
  have hDN : D ≤ Subgroup.normalizer (D : Set (MulAut V)) := Subgroup.le_normalizer
  have := fittingOf_nilpotent X
  have hnil : Group.IsNilpotent ↥(Gk X k) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hGF)
  set H : Subgroup (MulAut V) := Gk X k ⊓ Subgroup.normalizer (D : Set (MulAut V)) with hH
  by_contra hnot
  have hlt : H.subgroupOf (Gk X k) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hnot ?_
    intro g hg
    have : (⟨g, hg⟩ : ↥(Gk X k)) ∈ H.subgroupOf (Gk X k) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this.2
  obtain ⟨g, hgN, hgH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have key : ∀ g : ↥(Gk X k),
      g ∈ Subgroup.normalizer ((H.subgroupOf (Gk X k) : Subgroup ↥(Gk X k)) : Set ↥(Gk X k)) →
      ∀ d ∈ D, (g : MulAut V) * d * (g : MulAut V)⁻¹ ∈ D := by
    intro g hg d hd
    have hgmem := Subgroup.mem_normalizer_iff.mp hg
    have hgG : (g : MulAut V) ∈ Gk X k := g.2
    have hgX : (g : MulAut V) ∈ X := fittingOf_le X (hGF hgG)
    have hconjH : ∀ x ∈ H, (g : MulAut V) * x * (g : MulAut V)⁻¹ ∈ H := by
      intro x hx
      exact (hgmem ⟨x, hx.1⟩).mp hx
    have hΔconj : ∀ A ∈ Δ, conjBy (g : MulAut V) A ∈ Δ := by
      intro A hA
      refine h.mem_of_normalizes hV hk (conjBy_mem_Xk hgX (h.subset hA)) ?_
      rintro _ ⟨a, ha, rfl⟩
      have haD : a ∈ D := h.le_iSup hA ha
      have haH : a ∈ H := ⟨hDG haD, hDN haD⟩
      exact (hconjH a haH).2
    have : D ≤ D.comap (MulAut.conj (g : MulAut V)).toMonoidHom :=
      iSup₂_le fun A hA a ha => h.le_iSup (hΔconj A hA) (mem_conjBy_of_mem ha)
    exact this hd
  have hgnorm : (g : MulAut V) ∈ Subgroup.normalizer (D : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => key g hgN d hd, fun hd => ?_⟩
    have := key g⁻¹ (inv_mem hgN) _ hd
    have e : ((g⁻¹ : ↥(Gk X k)) : MulAut V) * ((g : MulAut V) * d * (g : MulAut V)⁻¹) *
        ((g⁻¹ : ↥(Gk X k)) : MulAut V)⁻¹ = d := by
      simp [mul_assoc]
    rw [e] at this
    exact this
  exact hgH ⟨g.2, hgnorm⟩

theorem Xk_commute (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2) :
    CommFamily (Xk X k) := by
  classical
  have hfin : Set.Finite {S : Set (Subgroup (MulAut V)) | S ⊆ Xk X k ∧ CommFamily S} :=
    Set.toFinite _
  obtain ⟨Δ, hΔ⟩ := hfin.exists_maximal
    ⟨∅, Set.empty_subset _, fun A hA => absurd hA (Set.notMem_empty _)⟩
  have hM : MaxComm X k Δ :=
    ⟨hΔ.1.1, hΔ.1.2, fun S hS hc hle => hΔ.2 ⟨hS, hc⟩ hle⟩
  have hsub : Xk X k ⊆ Δ := fun Y hY =>
    hM.mem_of_normalizes hV hk hY
      (le_trans (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X k) => Z) Y hY)
        (hM.Gk_le_normalizer hV hk))
  intro Y hY Z hZ y hy z hz
  exact hM.comm Y (hsub hY) Z (hsub hZ) y hy z hz

theorem D2_12_1 (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2) :
    CommFamily (Xk X k) ∧ iSupIndep (fun Y : Xk X k => (Y : Subgroup (MulAut V))) := by
  have hc := Xk_commute (X := X) hV hk
  refine ⟨hc, fun i => ?_⟩
  have := disjoint_biSup hV hk (S := Xk X k) subset_rfl hc i.2
  refine this.mono_right ?_
  refine iSup_le fun j => iSup_le fun hji => ?_
  exact le_iSup₂_of_le (j : Subgroup (MulAut V)) j.2
    (le_iSup (fun _ : (j : Subgroup (MulAut V)) ≠ i => (j : Subgroup (MulAut V)))
      (fun h => hji (Subtype.ext h)))

omit [Finite V] in
theorem commV_iSup_le {ι : Sort*} (P : ι → Subgroup (MulAut V)) :
    commV (⨆ i, P i) ≤ ⨆ i, commV (P i) := by
  let M : Subgroup V := ⨆ i, commV (P i)
  let S : Subgroup (MulAut V) :=
    { carrier := {g | ∀ v, g v * v⁻¹ ∈ M}
      one_mem' := fun v => by simp [M]
      mul_mem' := by
        intro g h hg hh v
        have : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
          simp [MulAut.mul_apply, mul_assoc]
        rw [this]
        exact M.mul_mem (hg (h v)) (hh v)
      inv_mem' := by
        intro g hg v
        have : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
          simp [mul_comm]
        rw [this]
        exact M.inv_mem (hg (g⁻¹ v)) }
  have hP : ∀ i, P i ≤ S := by
    intro i g hg v
    exact Subgroup.mem_iSup_of_mem i (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
  have hle : (⨆ i, P i) ≤ S := iSup_le hP
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  exact hle hg v

omit [Finite V] in
theorem commV_mono {P Q : Subgroup (MulAut V)} (h : P ≤ Q) : commV P ≤ commV Q := by
  rw [commV, commV]
  apply Subgroup.closure_mono
  rintro _ ⟨g, hg, v, rfl⟩
  exact ⟨g, h hg, v, rfl⟩

theorem D2_12_2 (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2) :
    commV (Gk X k) = ⨆ Y ∈ Xk X k, commV Y ∧
      iSupIndep (fun Y : Xk X k => commV (Y : Subgroup (MulAut V))) := by
  have hc := Xk_commute (X := X) hV hk
  refine ⟨le_antisymm ?_ ?_, fun i => ?_⟩
  · have := commV_iSup_le (fun Y : Xk X k => (Y : Subgroup (MulAut V)))
    calc commV (Gk X k) = commV (⨆ Y : Xk X k, (Y : Subgroup (MulAut V))) := by
          congr 1
          apply le_antisymm
          · exact iSup₂_le fun Y hY => le_iSup (fun Y : Xk X k => (Y : Subgroup (MulAut V)))
              ⟨Y, hY⟩
          · exact iSup_le fun Y => le_iSup₂ (f := fun Z (_ : Z ∈ Xk X k) => Z) Y.1 Y.2
      _ ≤ ⨆ Y : Xk X k, commV (Y : Subgroup (MulAut V)) := this
      _ ≤ ⨆ Y ∈ Xk X k, commV Y := iSup_le fun Y => le_iSup₂ (f := fun Z (_ : Z ∈ Xk X k) =>
          commV Z) Y.1 Y.2
  · exact iSup₂_le fun Y hY => commV_mono (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X k) => Z) Y hY)
  · have := disjoint_commV_biSup hV hk (S := Xk X k) subset_rfl hc i.2
    refine this.mono_right ?_
    refine iSup_le fun j => iSup_le fun hji => ?_
    exact commV_le_biSup j.2 (fun h => hji (Subtype.ext h))

omit [Finite V] in
theorem inverts_or_commutes [Finite V] {p : ℕ} [Fact p.Prime] {Y : Subgroup (MulAut V)}
    (hY : Nat.card Y = p) {t : MulAut V} (ht2 : t ^ 2 = 1)
    (hn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) :
    (∀ y ∈ Y, t * y * t⁻¹ = y) ∨ (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) := by
  obtain ⟨y₀, hy₀, hy1, hyz, hyord⟩ := exists_generator_of_prime_card hY
  have hmem : t * y₀ * t⁻¹ ∈ Subgroup.zpowers y₀ := by rw [hyz]; exact hn y₀ hy₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have h2 : y₀ = y₀ ^ (j * j) := by
    calc y₀ = t * (t * y₀ * t⁻¹) * t⁻¹ := by
          rw [htinv]
          calc y₀ = (t * t) * y₀ * (t * t) := by rw [← pow_two, ht2]; simp
            _ = t * (t * y₀ * t) * t := by group
      _ = t * y₀ ^ j * t⁻¹ := by rw [hj]
      _ = (t * y₀ * t⁻¹) ^ j := by rw [conj_zpow]
      _ = (y₀ ^ j) ^ j := by rw [hj]
      _ = y₀ ^ (j * j) := by rw [← zpow_mul]
  have h3 : y₀ ^ (j * j - 1) = 1 := by
    rw [zpow_sub_one, ← h2, mul_inv_cancel]
  have h4 : (p : ℤ) ∣ j * j - 1 := by
    rw [← hyord]
    exact (orderOf_dvd_iff_zpow_eq_one).mpr h3
  have h5 : (p : ℤ) ∣ (j - 1) * (j + 1) := by
    have : (j - 1) * (j + 1) = j * j - 1 := by ring
    rw [this]; exact h4
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  rcases hpz.dvd_or_dvd h5 with h6 | h6
  · left
    have : y₀ ^ (j - 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).mp (by rw [hyord]; exact h6)
    rw [zpow_sub_one, mul_inv_eq_one] at this
    have hc : t * y₀ * t⁻¹ = y₀ := by rw [← hj, this]
    intro y hy
    rw [← hyz] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hc]
  · right
    have : y₀ ^ (j + 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).mp (by rw [hyord]; exact h6)
    rw [zpow_add_one, mul_eq_one_iff_eq_inv] at this
    have hc : t * y₀ * t⁻¹ = y₀⁻¹ := by rw [← hj, this]
    intro y hy
    rw [← hyz] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hc, inv_zpow]

omit [Finite V] in
theorem mem_normalizer_of_conjBy_eq {g : MulAut V} {Y : Subgroup (MulAut V)}
    (h : conjBy g Y = Y) : g ∈ Subgroup.normalizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ▸ mem_conjBy_of_mem hx
  · intro hx
    have h1 : g * x * g⁻¹ ∈ conjBy g Y := by rw [h]; exact hx
    have h2 := mem_conjBy_iff.mp h1
    simpa [mul_assoc] using h2

theorem D2_12_4 (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2) {t : MulAut V} (ht : t ∈ TInv X)
    (hm : rk (commV (Subgroup.zpowers t)) = k) :
    ∀ Y ∈ Xk X k, t ∈ Subgroup.normalizer (Y : Set (MulAut V)) := by
  intro Y hY
  by_cases hc : conjBy t Y = Y
  · exact mem_normalizer_of_conjBy_eq hc
  · exfalso
    have hY' : conjBy t Y ∈ Xk X k := conjBy_mem_Xk ht.1 hY
    have hd := disjoint_commV_biSup hV hk (S := Xk X k) subset_rfl (Xk_commute hV hk) hY
    have h01 : commV Y ⊓ commV (conjBy t Y) = ⊥ :=
      disjoint_iff.mp (hd.mono_right (commV_le_biSup hY' hc))
    have hker : commV Y ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
      refine le_bot_iff.mp ?_
      intro w ⟨hw, hwt⟩
      have htw : t w = w := mem_fixV_zpowers_iff.mp hwt
      have : w ∈ commV Y ⊓ commV (conjBy t Y) := by
        refine ⟨hw, ?_⟩
        rw [commV_conjBy]
        exact ⟨w, hw, htw⟩
      rw [h01] at this
      exact this
    have hr := rk_map_add_rk_inf_ker (commHom t) (commV Y)
    rw [ker_commHom, hker, rk_bot, hY.2.2] at hr
    have hle : (commV Y).map (commHom t) ≤ commV (Subgroup.zpowers t) := by
      rw [commV_zpowers_eq_map]
      exact Subgroup.map_mono le_top
    have := rk_mono hle
    rcases hk with rfl | rfl <;> omega

theorem commV_le_fixV_of_commutes (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2)
    {t : MulAut V} (ht2 : t ^ 2 = 1) {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk X k)
    (hcomm : ∀ y ∈ Y, t * y = y * t) : commV Y ≤ fixV (Subgroup.zpowers t) := by
  have := fact_prime_two_mul_add_one hk
  have hcomm' : ∀ y ∈ Y, ∀ z ∈ Subgroup.zpowers t, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (((show Commute t y from hcomm y hy).zpow_left i)).symm.eq
  obtain ⟨hZW, -⟩ := commute_stab hcomm'
  obtain ⟨y, hyY, hy1, hyz, hyord⟩ := exists_generator_of_prime_card hY.2.1
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    rw [← hyz] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl y).zpow_zpow i j).eq
  obtain ⟨hYW, -⟩ := commute_stab hYab
  have hWt : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commV Y, x w ∈ commV Y := by
    intro x hx w hw
    exact ((hZW hx) w).mpr hw
  have hC : commV Y ⊓ fixV (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    have h1 := rk_commSub_add_rk_inf_fixV hWt
    have h2 : commSub (commV Y) (Subgroup.zpowers t) ≤ commV Y ⊓ fixV (Subgroup.zpowers t) :=
      commSub_zpowers_le_inf_fixV hV ht2 hWt
    rw [hbot, rk_bot, hY.2.2] at h1
    have h3 := rk_mono h2
    rw [hbot, rk_bot] at h3
    rcases hk with rfl | rfl <;> omega
  have hinv : ∀ g ∈ Y, ∀ f ∈ commV Y ⊓ fixV (Subgroup.zpowers t),
      g f ∈ commV Y ⊓ fixV (Subgroup.zpowers t) := by
    intro g hg f hf
    refine ⟨((hYW hg) f).mpr hf.1, ?_⟩
    show g f ∈ fixV (Subgroup.zpowers t)
    rw [mem_fixV_zpowers_iff]
    have h1 : t * g = g * t := hcomm g hg
    have h2 : t f = f := mem_fixV_zpowers_iff.mp hf.2
    calc t (g f) = (t * g) f := rfl
      _ = (g * t) f := by rw [h1]
      _ = g (t f) := rfl
      _ = g f := by rw [h2]
  have := Xk_irreducible hV hk hY hinv inf_le_left hC
  calc commV Y = commV Y ⊓ fixV (Subgroup.zpowers t) := this.symm
    _ ≤ fixV (Subgroup.zpowers t) := inf_le_right

theorem D2_12_3 (hV : ∀ v : V, v ^ 2 = 1) (hk : k = 1 ∨ k = 2) {t : MulAut V}
    (ht : t ∈ TInv X) (hm : rk (commV (Subgroup.zpowers t)) = k) :
    ((∀ g ∈ Gk X k, g * t = t * g) ∧
        commSub (commV (Gk X k)) (Subgroup.zpowers t) = ⊥) ∨
      (∃ Y ∈ Xk X k, (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) ∧
        (∀ Z ∈ Xk X k, (∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) → Z = Y) ∧
        commV (Subgroup.zpowers t) = commSub (commV Y) (Subgroup.zpowers t) ∧
        ∀ Z ∈ Xk X k, Z ≠ Y → (∀ z ∈ Z, t * z = z * t) ∧ ∀ w ∈ commV Z, t w = w) := by
  have := fact_prime_two_mul_add_one hk
  have hnorm := D2_12_4 hV hk ht hm
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hcomm := Xk_commute (X := X) hV hk
  by_cases hall : ∀ Y ∈ Xk X k, ∀ y ∈ Y, t * y = y * t
  · left
    refine ⟨?_, ?_⟩
    · intro g hg
      have hle : Gk X k ≤ Subgroup.centralizer ({t} : Set (MulAut V)) :=
        iSup₂_le fun Y hY y hy => by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          exact hall Y hY y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle hg) t (Set.mem_singleton t)).symm
    · rw [commSub_eq_bot_iff, (D2_12_2 hV hk).1]
      exact iSup₂_le fun Y hY => commV_le_fixV_of_commutes hV hk ht2 hY (hall Y hY)
  · right
    push Not at hall
    obtain ⟨Y, hY, y1, hy1, hne⟩ := hall
    have hinv_all : ∀ Z ∈ Xk X k, (∀ z ∈ Z, t * z = z * t) ∨ (∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) := by
      intro Z hZ
      have hn : ∀ y ∈ Z, t * y * t⁻¹ ∈ Z := fun y hy =>
        (Subgroup.mem_normalizer_iff.mp (hnorm Z hZ) y).mp hy
      rcases inverts_or_commutes hZ.2.1 ht2 hn with h | h
      · left
        intro z hz
        have := h z hz
        rwa [mul_inv_eq_iff_eq_mul] at this
      · exact Or.inr h
    have hinvY : ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹ := by
      rcases hinv_all Y hY with h | h
      · exact absurd (h y1 hy1) hne
      · exact h
    have key : ∀ Z ∈ Xk X k, (∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) →
        commSub (commV Z) (Subgroup.zpowers t) = commV (Subgroup.zpowers t) ∧
        commSub (fixV Z) (Subgroup.zpowers t) = ⊥ ∧
        ∀ y' ∈ X, (∀ z ∈ Z, y' * z = z * y') → y' ∈ centSub (commV Z) → y' * t = t * y' := by
      intro Z hZ hinvZ
      obtain ⟨z, hzZ, hz1, hzz, hzord⟩ := exists_generator_of_prime_card hZ.2.1
      have hzodd : Odd (orderOf z) := by rw [hzord]; exact ⟨k, rfl⟩
      have hzX : z ∈ X := fittingOf_le X (hZ.1 hzZ)
      have hrkz : rk (commV (Subgroup.zpowers z)) = 2 * rk (commV (Subgroup.zpowers t)) := by
        rw [hzz, hZ.2.2, hm]
      have := D2_11_3 hV ht hzX hz1 hzodd (hinvZ z hzZ) hrkz
      rw [hzz] at this
      refine ⟨this.1, this.2.1, fun y' hy'X hcomm' hcent => ?_⟩
      refine this.2.2 y' hy'X ?_ hcent
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm' z hzZ).symm
    obtain ⟨hkY1, hkY2, hkY3⟩ := key Y hY hinvY
    refine ⟨Y, hY, hinvY, ?_, hkY1.symm, ?_⟩
    ·
      intro Z hZ hinvZ
      by_contra hZY
      obtain ⟨hkZ1, -, -⟩ := key Z hZ hinvZ
      have hd := disjoint_commV_biSup hV hk (S := Xk X k) subset_rfl hcomm hY
      have h01 : commV Y ⊓ commV Z = ⊥ := disjoint_iff.mp (hd.mono_right (commV_le_biSup hZ hZY))
      have hstabY : t ∈ stabSub (commV Y) := by
        have hn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy =>
          (Subgroup.mem_normalizer_iff.mp (hnorm Y hY) y).mp hy
        have hn' : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y := by
          intro y hy
          have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
          rw [htinv]
          have := hn y hy
          rwa [htinv] at this
        exact mem_stabSub_commV hn hn'
      have hstabZ : t ∈ stabSub (commV Z) := by
        have hn : ∀ y ∈ Z, t * y * t⁻¹ ∈ Z := fun y hy =>
          (Subgroup.mem_normalizer_iff.mp (hnorm Z hZ) y).mp hy
        have hn' : ∀ y ∈ Z, t⁻¹ * y * t ∈ Z := by
          intro y hy
          have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
          rw [htinv]
          have := hn y hy
          rwa [htinv] at this
        exact mem_stabSub_commV hn hn'
      have hle1 : commV (Subgroup.zpowers t) ≤ commV Y := by
        rw [← hkY1]
        refine commSub_le_of_invariant fun x hx w hw => ?_
        have : Subgroup.zpowers t ≤ stabSub (commV Y) := by
          rw [Subgroup.zpowers_le]; exact hstabY
        exact ((this hx) w).mpr hw
      have hle2 : commV (Subgroup.zpowers t) ≤ commV Z := by
        rw [← hkZ1]
        refine commSub_le_of_invariant fun x hx w hw => ?_
        have : Subgroup.zpowers t ≤ stabSub (commV Z) := by
          rw [Subgroup.zpowers_le]; exact hstabZ
        exact ((this hx) w).mpr hw
      have hbot : commV (Subgroup.zpowers t) = ⊥ := by
        refine le_bot_iff.mp ?_
        intro w hw
        have : w ∈ commV Y ⊓ commV Z := ⟨hle1 hw, hle2 hw⟩
        rw [h01] at this
        exact this
      rw [hbot, rk_bot] at hm
      rcases hk with rfl | rfl <;> omega
    · intro Z hZ hZY
      have hYZc : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y := fun y hy z hz => hcomm Y hY Z hZ y hy z hz
      refine ⟨fun z hz => ?_, fun w hw => ?_⟩
      · have hzX : z ∈ X := fittingOf_le X (hZ.1 hz)
        have h1 : ∀ z' ∈ Y, z * z' = z' * z := fun z' hz' => (hYZc z' hz' z hz).symm
        have h2 : z ∈ centSub (commV Y) := Xk_centralizes hV hk hY hZ (Ne.symm hZY) hYZc z hz
        exact (hkY3 z hzX h1 h2).symm
      · have hZc : ∀ y ∈ Y, ∀ w ∈ commV Z, y w = w :=
          Xk_centralizes hV hk hZ hY hZY (fun z hz y hy => (hYZc y hy z hz).symm)
        have hle : commV Z ≤ fixV Y := fun w hw y hy => hZc y hy w hw
        have := (commSub_eq_bot_iff.mp hkY2) (hle hw)
        exact mem_fixV_zpowers_iff.mp this

theorem Xk_faithful (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk X k)
    {g : MulAut V} (hg : g ∈ Y) (hfix : ∀ w ∈ commV Y, g w = w) : g = 1 := by
  obtain ⟨hsup, -⟩ := Xk_decomp hV hY
  ext v
  have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hfix w hw, hc g hg]
  rfl

theorem D2_12_5 (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} (ht : t ∈ TInv X)
    (hm : rk (commV (Subgroup.zpowers t)) = 2) :
    (∀ Y ∈ Xk X 1, t ∈ Subgroup.normalizer (Y : Set (MulAut V))) ∨
      (∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧ conjBy t Y₂ = Y₁ ∧
        commV (Subgroup.zpowers t) =
          commSub (commV Y₁ ⊔ commV Y₂) (Subgroup.zpowers t) ∧
        ∀ Z ∈ Xk X 1, Z ≠ Y₁ → Z ≠ Y₂ →
          (∀ z ∈ Z, t * z = z * t) ∧ ∀ w ∈ commV Z, t w = w) := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have hcomm := Xk_commute (X := X) (k := 1) hV hk
  by_cases hall : ∀ Y ∈ Xk X 1, conjBy t Y = Y
  · exact Or.inl fun Y hY => mem_normalizer_of_conjBy_eq (hall Y hY)
  · right
    push Not at hall
    obtain ⟨Y₁, hY₁, hne⟩ := hall
    set Y₂ := conjBy t Y₁ with hY₂def
    have hY₂ : Y₂ ∈ Xk X 1 := conjBy_mem_Xk ht.1 hY₁
    have hconj2 : conjBy t Y₂ = Y₁ := by
      rw [hY₂def, conjBy_conjBy, htt, conjBy_one]
    have hdisjf : ∀ {Y : Subgroup (MulAut V)}, Y ∈ Xk X 1 →
        Disjoint (commV Y) (⨆ Z ∈ Xk X 1, ⨆ (_ : Z ≠ Y), commV Z) := fun hY =>
      disjoint_commV_biSup hV hk (S := Xk X 1) subset_rfl hcomm hY
    have hW₂ : commV Y₂ = (commV Y₁).map t.toMonoidHom := commV_conjBy t Y₁
    have h12 : commV Y₁ ⊓ commV Y₂ = ⊥ :=
      disjoint_iff.mp ((hdisjf hY₁).mono_right (commV_le_biSup hY₂ hne))
    have hker : commV Y₁ ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
      refine le_bot_iff.mp ?_
      intro w ⟨hw, hwt⟩
      have htw : t w = w := mem_fixV_zpowers_iff.mp hwt
      have : w ∈ commV Y₁ ⊓ commV Y₂ := by
        refine ⟨hw, ?_⟩
        rw [hW₂]
        exact ⟨w, hw, htw⟩
      rw [h12] at this
      exact this
    have hr := rk_map_add_rk_inf_ker (commHom t) (commV Y₁)
    rw [ker_commHom, hker, rk_bot, hY₁.2.2] at hr
    have hle : (commV Y₁).map (commHom t) ≤ commV (Subgroup.zpowers t) := by
      rw [commV_zpowers_eq_map]
      exact Subgroup.map_mono le_top
    have hrkle := rk_mono hle
    have heq : (commV Y₁).map (commHom t) = commV (Subgroup.zpowers t) := by
      refine eq_of_le_of_rk_le hV hle ?_
      omega
    have hsupW : commV (Subgroup.zpowers t) ≤ commV Y₁ ⊔ commV Y₂ := by
      rw [← heq]
      rintro _ ⟨w, hw, rfl⟩
      have h1 : t w ∈ commV Y₂ := by rw [hW₂]; exact ⟨w, hw, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
        (Subgroup.mem_sup_left ((commV Y₁).inv_mem hw))
    refine ⟨Y₁, hY₁, Y₂, hY₂, fun h => hne h.symm, rfl, hconj2, ?_, ?_⟩
    · apply le_antisymm
      · rw [← heq]
        rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w,
          Subgroup.mem_sup_left hw, rfl⟩
      · rw [commV_eq_commSub (Subgroup.zpowers t)]
        exact commSub_mono le_top le_rfl
    · intro Z hZ hZ1 hZ2
      have hZ' : conjBy t Z ∈ Xk X 1 := conjBy_mem_Xk ht.1 hZ
      have hZ'1 : conjBy t Z ≠ Y₁ := by
        intro h
        apply hZ2
        have := congrArg (conjBy t) h
        rwa [conjBy_conjBy, htt, conjBy_one] at this
      have hZ'2 : conjBy t Z ≠ Y₂ := by
        intro h
        apply hZ1
        have := congrArg (conjBy t) h
        rwa [conjBy_conjBy, htt, conjBy_one, hconj2] at this
      have hfixZ : ∀ w ∈ commV Z, t w = w := by
        intro w hw
        have hc : t w * w⁻¹ = 1 := by
          set c := t w * w⁻¹ with hcdef
          have hcT : c ∈ commV (Subgroup.zpowers t) :=
            Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, rfl⟩
          have hcY : c ∈ commV Y₁ ⊔ commV Y₂ := hsupW hcT
          have hcZ : c ∈ commV Z ⊔ commV (conjBy t Z) := by
            have h1 : t w ∈ commV (conjBy t Z) := by
              rw [commV_conjBy]; exact ⟨w, hw, rfl⟩
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
              (Subgroup.mem_sup_left ((commV Z).inv_mem hw))
          obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hcY
          have hd1 := hdisjf hY₁
          have hd2 := hdisjf hY₂
          have hR1 : commV Y₂ ⊔ (commV Z ⊔ commV (conjBy t Z)) ≤
              ⨆ M ∈ Xk X 1, ⨆ (_ : M ≠ Y₁), commV M :=
            sup_le (commV_le_biSup hY₂ hne) (sup_le (commV_le_biSup hZ hZ1)
              (commV_le_biSup hZ' hZ'1))
          have hR2 : commV Z ⊔ commV (conjBy t Z) ≤
              ⨆ M ∈ Xk X 1, ⨆ (_ : M ≠ Y₂), commV M :=
            sup_le (commV_le_biSup hZ hZ2) (commV_le_biSup hZ' hZ'2)
          have ha1 : a = 1 := by
            have : a ∈ commV Y₂ ⊔ (commV Z ⊔ commV (conjBy t Z)) := by
              have hb' : b⁻¹ ∈ commV Y₂ := (commV Y₂).inv_mem hb
              have : a = c * b⁻¹ := by rw [← hab]; group
              rw [this]
              exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcZ) (Subgroup.mem_sup_left hb')
            have h3 : a ∈ commV Y₁ ⊓ (⨆ M ∈ Xk X 1, ⨆ (_ : M ≠ Y₁), commV M) := ⟨ha, hR1 this⟩
            rw [hd1.eq_bot, Subgroup.mem_bot] at h3
            exact h3
          have hb1 : b = 1 := by
            have hbc : b = c := by rw [← hab, ha1, one_mul]
            have h3 : b ∈ commV Y₂ ⊓ (⨆ M ∈ Xk X 1, ⨆ (_ : M ≠ Y₂), commV M) :=
              ⟨hb, hR2 (hbc ▸ hcZ)⟩
            rw [hd2.eq_bot, Subgroup.mem_bot] at h3
            exact h3
          rw [← hab, ha1, hb1, one_mul]
        rwa [mul_inv_eq_one] at hc
      have hconjZ : conjBy t Z = Z := by
        by_contra hne'
        have hd := hdisjf hZ
        have h1 : commV Z ⊓ commV (conjBy t Z) = ⊥ :=
          disjoint_iff.mp (hd.mono_right (commV_le_biSup hZ' hne'))
        have : commV Z ≤ commV Z ⊓ commV (conjBy t Z) := by
          refine le_inf le_rfl ?_
          intro w hw
          rw [commV_conjBy]
          exact ⟨w, hw, hfixZ w hw⟩
        rw [h1] at this
        have h2 : rk (commV Z) = 0 := by
          have := rk_mono this
          rw [rk_bot] at this
          omega
        rw [hZ.2.2] at h2
        omega
      have hnZ := mem_normalizer_of_conjBy_eq hconjZ
      have hn : ∀ y ∈ Z, t * y * t⁻¹ ∈ Z := fun y hy =>
        (Subgroup.mem_normalizer_iff.mp hnZ y).mp hy
      have := fact_prime_two_mul_add_one hk
      refine ⟨?_, hfixZ⟩
      rcases inverts_or_commutes hZ.2.1 ht2 hn with h | h
      · intro z hz
        have := h z hz
        rwa [mul_inv_eq_iff_eq_mul] at this
      · exfalso
        obtain ⟨z, hzZ, hz1, hzz, hzord⟩ := exists_generator_of_prime_card hZ.2.1
        have hzz2 : z ^ 2 = 1 := by
          refine Xk_faithful hV hZ (Z.pow_mem hzZ 2) fun w hw => ?_
          have hzw : z w ∈ commV Z := by
            have : Z ≤ stabSub (commV Z) := (commute_stab (fun a ha b hb => by
              rw [← hzz] at ha hb
              obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
              obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
              exact ((Commute.refl z).zpow_zpow i j).eq)).1
            exact ((this hzZ) w).mpr hw
          have e1 : (t * z * t⁻¹) w = z w := by
            show t (z (t⁻¹ w)) = z w
            have htinv : t⁻¹ w = w := by
              have h1 := hfixZ w hw
              calc t⁻¹ w = t⁻¹ (t w) := by rw [h1]
                _ = w := by simp
            rw [htinv]
            exact hfixZ _ hzw
          have e2 : (t * z * t⁻¹) w = z⁻¹ w := by rw [h z hzZ]
          have e3 : z⁻¹ w = z w := e2.symm.trans e1
          calc (z ^ 2) w = (z * z) w := by rw [pow_two]
            _ = z (z w) := rfl
            _ = z (z⁻¹ w) := by rw [e3]
            _ = w := by simp
        have h3 : z ^ 3 = 1 := by
          have := pow_orderOf_eq_one z
          rw [hzord] at this
          simpa using this
        have : z = 1 := by
          have : z = z ^ 3 * (z ^ 2)⁻¹ := by group
          rw [this, h3, hzz2]; simp
        exact hz1 this

end CommFamily

end CFSG.Quasithin
