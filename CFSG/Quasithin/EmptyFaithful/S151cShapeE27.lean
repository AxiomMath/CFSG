module

public import CFSG.Quasithin.EmptyFaithful.S151cShapeD10
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped commutatorElement

section ShapeE27Aux151c

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem e27_isPGroup {P : Subgroup (MulAut V)} (hexp : ∀ f ∈ P, f ^ 3 = 1) :
    IsPGroup 3 P :=
  fun a => ⟨1, Subtype.ext (by simpa using hexp (a : MulAut V) a.2)⟩

omit [Finite V] in
private theorem e27_frattini_eq_center {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) :
    frattini ↥P = Subgroup.center ↥P ∧ _root_.commutator ↥P ≤ Subgroup.center ↥P ∧
      Nat.card (Subgroup.center ↥P) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := e27_isPGroup hexp
  have hfin : Finite ↥P := Nat.finite_of_card_ne_zero (by omega)
  have hZ : Nat.card (Subgroup.center ↥P) = 3 := shape4_center_card hP27 hP3 hnc
  have hq : Nat.card (↥P ⧸ Subgroup.center ↥P) = 9 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hP27, hZ] at this
    omega
  have hcomm : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hq]; norm_num)
  have hcl : _root_.commutator ↥P ≤ Subgroup.center ↥P :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center ↥P)).1 hcomm
  refine ⟨le_antisymm ?_ ?_, hcl, hZ⟩
  · have : Fact (IsPGroup 3 ↥P) := ⟨hP3⟩
    refine CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 3)
      (Subgroup.center ↥P) (fun a b => ?_) (fun a => ?_)
    · exact hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    · have : a ^ 3 = 1 := Subtype.ext (by simpa using hexp (a : MulAut V) a.2)
      rw [this]
      exact Subgroup.one_mem _
  · have : Fact (IsPGroup 3 ↥P) := ⟨hP3⟩
    have hne : _root_.commutator ↥P ≠ ⊥ := by
      intro hbot
      obtain ⟨f, hf, g, hg, hfg⟩ := hnc
      have h1 : ⁅(⟨f, hf⟩ : ↥P), (⟨g, hg⟩ : ↥P)⁆ ∈ _root_.commutator ↥P :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hfg (congrArg Subtype.val h1)
    have heq : _root_.commutator ↥P = Subgroup.center ↥P := by
      refine Subgroup.eq_of_le_of_card_ge hcl ?_
      have h1 : Nat.card (_root_.commutator ↥P) ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hcl
      have h2 : Nat.card (_root_.commutator ↥P) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
      rw [hZ]
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd h h2
      · exact h.ge
    rw [← heq]
    exact CFSG.commutator_le_frattini_of_isPGroup (p := 3)

omit [Finite V] in
private theorem e27_mem_frattiniIn_iff {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) {z : MulAut V} :
    z ∈ frattiniIn P ↔ z ∈ P ∧ ∀ y ∈ P, y * z = z * y := by
  obtain ⟨hfr, -, -⟩ := e27_frattini_eq_center hP27 hexp hnc
  unfold frattiniIn
  rw [hfr]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2)

omit [Finite V] in
private theorem e27_card_frattiniIn {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) :
    Nat.card (frattiniIn P) = 3 := by
  obtain ⟨hfr, -, hZ⟩ := e27_frattini_eq_center hP27 hexp hnc
  unfold frattiniIn
  rw [Subgroup.card_map_of_injective P.subtype_injective, hfr]
  exact hZ

omit [Finite V] in
private theorem e27_comm_mem_frattiniIn {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) {x y : MulAut V}
    (hx : x ∈ P) (hy : y ∈ P) : x * y * x⁻¹ * y⁻¹ ∈ frattiniIn P := by
  obtain ⟨hfr, hcl, -⟩ := e27_frattini_eq_center hP27 hexp hnc
  have h1 : ⁅(⟨x, hx⟩ : ↥P), (⟨y, hy⟩ : ↥P)⁆ ∈ Subgroup.center ↥P :=
    hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  rw [← hfr] at h1
  exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩

omit [Finite V] in
private theorem e27_frattiniIn_lt {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) :
    frattiniIn P < P := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun h => ?_
  have h1 := e27_card_frattiniIn hP27 hexp hnc
  rw [h, hP27] at h1
  omega

private theorem e27_card_nine {P Φ W : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hΦ3 : Nat.card Φ = 3) (hΦW : Φ ≤ W) (hWP : W ≤ P) (hW1 : W ≠ Φ) (hW2 : W ≠ P) :
    Nat.card W = 9 := by
  have h1 : Nat.card W ∣ 27 := hP27 ▸ Subgroup.card_dvd_of_le hWP
  have h2 : 3 ∣ Nat.card W := hΦ3 ▸ Subgroup.card_dvd_of_le hΦW
  have h3 := Nat.le_of_dvd (by norm_num) h1
  have hpos := Nat.card_pos (α := W)
  have hW3 : Nat.card W ≠ 3 := fun h =>
    hW1 (Subgroup.eq_of_le_of_card_ge hΦW (by rw [h, hΦ3])).symm
  have hW27 : Nat.card W ≠ 27 := fun h =>
    hW2 (Subgroup.eq_of_le_of_card_ge hWP (by rw [h, hP27]))
  generalize Nat.card W = n at *
  interval_cases n <;> omega

omit [Finite V] in
private theorem e27_inv_eq (hsq : ∀ v : V, v ^ 2 = 1) (x : V) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq x)

omit [Finite V] in
private theorem e27_sq_apply (hsq : ∀ v : V, v ^ 2 = 1) {g : MulAut V} (hg3 : g ^ 3 = 1)
    (hf : ∀ v : V, g v = v → v = 1) (v : V) : (g ^ 2) v = v * g v := by
  have e3 : ∀ u : V, g ((g ^ 2) u) = u := by
    intro u
    have := congrArg (fun m : MulAut V => m u) hg3
    simpa [pow_succ'] using this
  have e2 : g (g v) = (g ^ 2) v := by rw [pow_two]; rfl
  have h1 : g (v * g v * (g ^ 2) v) = v * g v * (g ^ 2) v := by
    rw [map_mul, map_mul, e3 v, e2]
    ac_rfl
  have h2 := hf _ h1
  have h3 : (g ^ 2) v = (v * g v)⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h3, e27_inv_eq hsq]

omit [Finite V] in
private theorem e27_eq_of_fpf (hsq : ∀ v : V, v ^ 2 = 1) {a w : MulAut V} (ha3 : a ^ 3 = 1)
    (hw3 : w ^ 3 = 1) (hcomm : w * a = a * w) (hfa : ∀ v : V, a v = v → v = 1)
    (hfw : ∀ v : V, w v = v → v = 1) (hfwa : ∀ v : V, (w * a) v = v → v = 1) : a = w := by
  have hC : Commute w a := hcomm
  have hwa3 : (w * a) ^ 3 = 1 := by rw [hC.mul_pow, hw3, ha3, mul_one]
  have hsq2 : (w * a) ^ 2 = w ^ 2 * a ^ 2 := hC.mul_pow 2
  refine MulEquiv.ext fun v => ?_
  have e1 := e27_sq_apply hsq ha3 hfa
  have e2 := e27_sq_apply hsq hw3 hfw
  have e3 := e27_sq_apply hsq hwa3 hfwa
  have key : v * w v * (a v * w (a v)) = v * w (a v) := by
    calc v * w v * (a v * w (a v)) = (w ^ 2) ((a ^ 2) v) := by
          rw [e1 v, map_mul, e2 v, e2 (a v)]
      _ = ((w * a) ^ 2) v := by rw [hsq2]; rfl
      _ = v * w (a v) := e3 v
  have key2 : (v * w (a v)) * (w v * a v) = (v * w (a v)) * 1 := by
    rw [mul_one]
    calc (v * w (a v)) * (w v * a v) = v * w v * (a v * w (a v)) := by ac_rfl
      _ = v * w (a v) := key
  have key3 : w v * a v = 1 := mul_left_cancel key2
  have key4 : a v = (w v)⁻¹ := eq_inv_of_mul_eq_one_right key3
  rw [key4, e27_inv_eq hsq]

private theorem e27_fixV_frattiniIn (hsq : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP27 : Nat.card P = 27) (hexp : ∀ f ∈ P, f ^ 3 = 1)
    (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) (hfix : fixV P = ⊥) (hrk : rk V = 6) :
    ∀ z ∈ frattiniIn P, z ≠ 1 → ∀ v : V, z v = v → v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΦ3 := e27_card_frattiniIn hP27 hexp hnc
  have hfixΦ : fixV (frattiniIn P) = ⊥ := by
    by_contra hne
    have hinv : ∀ g ∈ P, ∀ b ∈ fixV (frattiniIn P), g b ∈ fixV (frattiniIn P) := by
      intro g hg b hb z hz
      have hzg : z * g = g * z := (((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hz).2 g hg).symm
      calc z (g b) = (z * g) b := rfl
        _ = (g * z) b := by rw [hzg]
        _ = g (z b) := rfl
        _ = g b := by rw [hb z hz]
    have htop := eq_top_of_invariant_shape4 hsq hP27 hexp hnc hfix hrk hinv hne
    obtain ⟨z, hz, hz1, -, -⟩ := exists_generator_of_prime_card hΦ3
    apply hz1
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV (frattiniIn P) := by rw [htop]; exact Subgroup.mem_top v
    exact hv z hz
  intro z hz hz1 v hzv
  have hzp : Subgroup.zpowers z = frattiniIn P := zpowers_eq_of_prime_card hΦ3 hz hz1
  have hv : v ∈ fixV (Subgroup.zpowers z) := mem_fixV_zpowers_iff.mpr hzv
  rw [hzp, hfixΦ, Subgroup.mem_bot] at hv
  exact hv

private theorem e27_exists_fixed (hsq : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP27 : Nat.card P = 27) (hexp : ∀ f ∈ P, f ^ 3 = 1)
    (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) (hfix : fixV P = ⊥) (hrk : rk V = 6)
    {a : MulAut V} (haP : a ∈ P) (haΦ : a ∉ frattiniIn P) : ∃ v : V, v ≠ 1 ∧ a v = v := by
  by_contra hcon
  have hfa : ∀ v : V, a v = v → v = 1 := fun v hv => by
    by_contra h
    exact hcon ⟨v, h, hv⟩
  obtain ⟨c, hcP, hca⟩ : ∃ c ∈ P, c * a ≠ a * c := by
    by_contra hall
    push Not at hall
    exact haΦ ((e27_mem_frattiniIn_iff hP27 hexp hnc).2 ⟨haP, hall⟩)
  have hwΦ : c * a * c⁻¹ * a⁻¹ ∈ frattiniIn P := e27_comm_mem_frattiniIn hP27 hexp hnc hcP haP
  have hw1 : c * a * c⁻¹ * a⁻¹ ≠ 1 := by
    intro h
    apply hca
    have h2 : c * a * c⁻¹ = a := by
      have := mul_eq_one_iff_eq_inv.mp h
      simpa using this
    calc c * a = c * a * c⁻¹ * c := by group
      _ = a * c := by rw [h2]
  have hwP : c * a * c⁻¹ * a⁻¹ ∈ P := ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hwΦ).1
  have hwc : (c * a * c⁻¹ * a⁻¹) * a = a * (c * a * c⁻¹ * a⁻¹) :=
    (((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hwΦ).2 a haP).symm
  have hwa : (c * a * c⁻¹ * a⁻¹) * a = c * a * c⁻¹ := by group
  have hfw := e27_fixV_frattiniIn hsq hP27 hexp hnc hfix hrk _ hwΦ hw1
  have hfwa : ∀ v : V, ((c * a * c⁻¹ * a⁻¹) * a) v = v → v = 1 := by
    intro v hv
    rw [hwa] at hv
    have h1 : a (c⁻¹ v) = c⁻¹ v := by
      have := congrArg (fun u => c⁻¹ u) hv
      simpa using this
    have h2 := hfa _ h1
    have h3 : v = c (c⁻¹ v) := by simp
    rw [h3, h2, map_one]
  have heq := e27_eq_of_fpf hsq (hexp a haP) (hexp _ hwP) hwc hfa hfw hfwa
  exact haΦ (heq ▸ hwΦ)

omit [Finite V] in
private theorem e27_le_normalizer {Tb S : Subgroup (MulAut V)}
    (hS : ∀ τ ∈ Tb, ∀ x ∈ S, τ * x * τ⁻¹ ∈ S) :
    Tb ≤ Subgroup.normalizer (S : Set (MulAut V)) := by
  intro τ hτ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hS τ hτ y, fun hy => ?_⟩
  have := hS τ⁻¹ (Tb.inv_mem hτ) _ hy
  simpa [mul_assoc] using this

private theorem e27_coprime {Tb : Subgroup (MulAut V)} (hTb : IsPGroup 2 Tb) :
    Nat.Coprime 3 (Nat.card Tb) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hTb
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

private theorem e27_exists_line {Φ W Tb : Subgroup (MulAut V)} (hΦ3 : Nat.card Φ = 3)
    (hW9 : Nat.card W = 9) (hΦW : Φ ≤ W) (hexpW : ∀ x ∈ W, x ^ 3 = 1) (hTb : IsPGroup 2 Tb)
    (hTbW : ∀ τ ∈ Tb, ∀ x ∈ W, τ * x * τ⁻¹ ∈ W)
    (hTbΦ : ∀ τ ∈ Tb, ∀ x ∈ Φ, τ * x * τ⁻¹ ∈ Φ) :
    ∃ q ∈ W, q ∉ Φ ∧ Subgroup.zpowers q ⊔ Φ = W ∧
      ∀ τ ∈ Tb, ∀ x ∈ Subgroup.zpowers q, τ * x * τ⁻¹ ∈ Subgroup.zpowers q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWcomm : IsMulCommutative ↥W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hW9]; norm_num)
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup (MulAut V)) := by
    intro x hx y hy
    have h1 : (⟨x, hx⟩ : ↥W) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hWcomm.is_comm.comm _ _
    have h2 : x * y = y * x := congrArg Subtype.val h1
    rw [Subgroup.mem_bot]
    calc x * y * x⁻¹ * y⁻¹ = y * x * x⁻¹ * y⁻¹ := by rw [h2]
      _ = 1 := by group
  obtain ⟨N, -, hNW, hNinv, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := W) (Φ := ⊥) (D := Tb)
      (T := Φ) bot_le hcomm (fun x hx => by rw [hexpW x hx]; exact Subgroup.one_mem _)
      (e27_coprime hTb) hTbW (fun τ _ x hx => by rw [Subgroup.mem_bot] at hx ⊢; simp [hx]) bot_le
      hΦW hTbΦ
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hsup
    rw [← hsup, hΦ3] at hW9
    omega
  have hNW' : N ≠ W := by
    intro h
    rw [h, inf_of_le_left hΦW] at hinf
    rw [hinf, Subgroup.card_bot] at hΦ3
    omega
  have hN3 : Nat.card N = 3 := by
    have h1 : Nat.card N ∣ 9 := hW9 ▸ Subgroup.card_dvd_of_le hNW
    have h2 : Nat.card N ≠ 1 := fun h => hN1 (Subgroup.card_eq_one.mp h)
    have h3 : Nat.card N ≠ 9 := fun h =>
      hNW' (Subgroup.eq_of_le_of_card_ge hNW (by rw [h, hW9]))
    have h4 := Nat.le_of_dvd (by norm_num) h1
    have hpos := Nat.card_pos (α := N)
    generalize Nat.card N = n at *
    interval_cases n <;> omega
  obtain ⟨⟨q, hqN⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hzp : Subgroup.zpowers q = N := zpowers_eq_of_prime_card hN3 hqN hq1'
  refine ⟨q, hNW hqN, fun hqΦ => hq1' ?_, by rw [hzp, sup_comm]; exact hsup,
    by rw [hzp]; exact hNinv⟩
  have : q ∈ Φ ⊓ N := ⟨hqΦ, hqN⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact this

private theorem e27_exists_second_line {P Φ W Tb : Subgroup (MulAut V)}
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hΦP : Φ ≤ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ) (hTb : IsPGroup 2 Tb)
    (hTbP : ∀ τ ∈ Tb, ∀ x ∈ P, τ * x * τ⁻¹ ∈ P) (hTbΦ : ∀ τ ∈ Tb, ∀ x ∈ Φ, τ * x * τ⁻¹ ∈ Φ)
    (hΦW : Φ ≤ W) (hWP : W ≤ P) (hTbW : ∀ τ ∈ Tb, ∀ x ∈ W, τ * x * τ⁻¹ ∈ W) :
    ∃ W₂ : Subgroup (MulAut V), Φ ≤ W₂ ∧ W₂ ≤ P ∧ (∀ τ ∈ Tb, ∀ x ∈ W₂, τ * x * τ⁻¹ ∈ W₂) ∧
      W ⊔ W₂ = P ∧ W ⊓ W₂ = Φ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := P) (Φ := Φ)
    (D := Tb) (T := W) hΦP hcomm (fun x hx => by rw [hexp x hx]; exact Subgroup.one_mem _)
    (e27_coprime hTb) hTbP hTbΦ hΦW hWP hTbW

private theorem e27_le_Xc {X Tb Xc : Subgroup (MulAut V)} (h : Setting151c X Tb Xc)
    {Q : Subgroup (MulAut V)} (hQX : Q ≤ X) (hQinv : ∀ τ ∈ Tb, ∀ x ∈ Q, τ * x * τ⁻¹ ∈ Q)
    (hfix : fixV Q ≠ ⊥) : Q ≤ Xc := by
  have hinv : ∀ g ∈ Tb, ∀ u ∈ fixV Q, g u ∈ fixV Q := by
    intro g hg u hu y hy
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Q := hQinv g⁻¹ (Tb.inv_mem hg) y hy
    have h1 : (g⁻¹ * y * g⁻¹⁻¹) u = u := hu _ hy'
    have h2 : g⁻¹ (y (g u)) = u := by simpa using h1
    have h3 := congrArg (fun w => g w) h2
    simpa using h3
  have hpos := rk_inf_fixV_pos_of_isPGroup_two h.sq h.syl.2.1 hinv hfix
  have hne : (fixV Q ⊓ fixV Tb : Subgroup V) ≠ ⊥ := (rk_pos_iff_ne_bot' h.sq).mp hpos
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzK : z ∈ fixV Q := hz.1
  have hzT : z ∈ fixV Tb := hz.2
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hZ1 : Subgroup.zpowers z ≤ fixV Tb := Subgroup.zpowers_le.mpr hzT
  have hZ1ne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1' (Subgroup.zpowers_eq_bot.mp e)
  intro k hk
  refine h.hU _ hZ1 hZ1ne ⟨hQX hk, ?_⟩
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, hzK k hk]

private theorem e27_irred {X Tb Xc : Subgroup (MulAut V)} (h : Setting151c X Tb Xc)
    {P : Subgroup (MulAut V)} (hPX : P ≤ X) (hXeq : Tb ⊔ P = X) (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) (hfix : fixV P = ⊥)
    (hrk : rk V = 6) (hTbP : ∀ τ ∈ Tb, ∀ x ∈ P, τ * x * τ⁻¹ ∈ P) :
    IsIrredOnSection Tb P (frattiniIn P) := by
  have hΦlt := e27_frattiniIn_lt hP27 hexp hnc
  have hΦ3 := e27_card_frattiniIn hP27 hexp hnc
  have hTb : IsPGroup 2 Tb := h.syl.2.1
  have hΦP : frattiniIn P ≤ P := hΦlt.le
  have hTbΦ : ∀ τ ∈ Tb, ∀ x ∈ frattiniIn P, τ * x * τ⁻¹ ∈ frattiniIn P := by
    intro τ hτ x hx
    obtain ⟨hxP, hxc⟩ := (e27_mem_frattiniIn_iff hP27 hexp hnc).1 hx
    refine (e27_mem_frattiniIn_iff hP27 hexp hnc).2 ⟨hTbP τ hτ x hxP, fun y hy => ?_⟩
    have hy' : τ⁻¹ * y * τ⁻¹⁻¹ ∈ P := hTbP τ⁻¹ (Tb.inv_mem hτ) y hy
    have h1 : (τ⁻¹ * y * τ⁻¹⁻¹) * x = x * (τ⁻¹ * y * τ⁻¹⁻¹) := hxc _ hy'
    calc y * (τ * x * τ⁻¹) = τ * ((τ⁻¹ * y * τ⁻¹⁻¹) * x) * τ⁻¹ := by group
      _ = τ * (x * (τ⁻¹ * y * τ⁻¹⁻¹)) * τ⁻¹ := by rw [h1]
      _ = (τ * x * τ⁻¹) * y := by group
  refine ⟨hΦlt, e27_le_normalizer hTbP, e27_le_normalizer hTbΦ, ?_⟩
  intro W hΦW hWP hTbW'
  by_contra hne
  obtain ⟨hne1, hne2⟩ := not_or.mp hne
  have hW9 : Nat.card W = 9 := e27_card_nine hP27 hΦ3 hΦW hWP hne1 hne2
  have hTbW : ∀ τ ∈ Tb, ∀ x ∈ W, τ * x * τ⁻¹ ∈ W := fun τ hτ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTbW' hτ) x).mp hx
  obtain ⟨W₂, hΦW₂, hW₂P, hTbW₂, hsup, hinf⟩ := e27_exists_second_line hexp hΦP
    (fun x hx y hy => e27_comm_mem_frattiniIn hP27 hexp hnc hx hy) hTb hTbP hTbΦ hΦW hWP hTbW
  have hW₂1 : W₂ ≠ frattiniIn P := by
    intro hh
    rw [hh, sup_eq_left.mpr hΦW] at hsup
    exact hne2 hsup
  have hW₂2 : W₂ ≠ P := by
    intro hh
    rw [hh, inf_of_le_left hWP] at hinf
    exact hne1 hinf
  have hW₂9 : Nat.card W₂ = 9 := e27_card_nine hP27 hΦ3 hΦW₂ hW₂P hW₂1 hW₂2
  obtain ⟨q₁, hq₁W, hq₁Φ, hsup₁, hinv₁⟩ := e27_exists_line hΦ3 hW9 hΦW
    (fun x hx => hexp x (hWP hx)) hTb hTbW hTbΦ
  obtain ⟨q₂, hq₂W, hq₂Φ, hsup₂, hinv₂⟩ := e27_exists_line hΦ3 hW₂9 hΦW₂
    (fun x hx => hexp x (hW₂P hx)) hTb hTbW₂ hTbΦ
  have hq₁P : q₁ ∈ P := hWP hq₁W
  have hq₂P : q₂ ∈ P := hW₂P hq₂W
  have hfixne : ∀ q ∈ P, q ∉ frattiniIn P → fixV (Subgroup.zpowers q) ≠ ⊥ := by
    intro q hqP hqΦ hbot
    obtain ⟨v, hv1, hv⟩ := e27_exists_fixed h.sq hP27 hexp hnc hfix hrk hqP hqΦ
    have : v ∈ fixV (Subgroup.zpowers q) := mem_fixV_zpowers_iff.mpr hv
    rw [hbot, Subgroup.mem_bot] at this
    exact hv1 this
  have hq₁Xc : Subgroup.zpowers q₁ ≤ Xc :=
    e27_le_Xc h (Subgroup.zpowers_le.mpr (hPX hq₁P)) hinv₁ (hfixne q₁ hq₁P hq₁Φ)
  have hq₂Xc : Subgroup.zpowers q₂ ≤ Xc :=
    e27_le_Xc h (Subgroup.zpowers_le.mpr (hPX hq₂P)) hinv₂ (hfixne q₂ hq₂P hq₂Φ)
  set H : Subgroup (MulAut V) := Subgroup.zpowers q₁ ⊔ Subgroup.zpowers q₂ with hH
  have hHXc : H ≤ Xc := sup_le hq₁Xc hq₂Xc
  have hHP : H ≤ P := sup_le (Subgroup.zpowers_le.mpr hq₁P) (Subgroup.zpowers_le.mpr hq₂P)
  have hgen : P ≤ H ⊔ frattiniIn P := by
    have h1 : W ≤ H ⊔ frattiniIn P := by
      rw [← hsup₁]
      exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    have h2 : W₂ ≤ H ⊔ frattiniIn P := by
      rw [← hsup₂]
      exact sup_le (le_sup_of_le_left le_sup_right) le_sup_right
    calc P = W ⊔ W₂ := hsup.symm
      _ ≤ H ⊔ frattiniIn P := sup_le h1 h2
  have hP3 : IsPGroup 3 P := e27_isPGroup hexp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥P) := ⟨hP3⟩
  have hcomap : (H ⊔ frattiniIn P).comap P.subtype = H.subgroupOf P ⊔ frattini ↥P := by
    rw [← Subgroup.comap_sup_eq_of_le_range P.subtype
      (by rw [Subgroup.range_subtype]; exact hHP) (by rw [Subgroup.range_subtype]; exact hΦP)]
    rw [frattiniIn, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    rfl
  have htop : H.subgroupOf P ⊔ frattini ↥P = ⊤ := by
    rw [← hcomap]
    exact eq_top_iff.mpr fun y _ => hgen y.2
  have hHtop : H.subgroupOf P = ⊤ := CFSG.lemma_1_7_a (p := 3) _ htop
  have hPH : P ≤ H := fun y hy => by
    have : (⟨y, hy⟩ : ↥P) ∈ H.subgroupOf P := by rw [hHtop]; exact Subgroup.mem_top _
    exact this
  apply h.xc_ne
  rw [← hXeq]
  exact sup_le h.tb_le (hPH.trans hHXc)

omit [Finite V] in
private theorem e27_isPOnePlusTwo {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) :
    IsPOnePlusTwo 3 ↥P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ↥P := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨-, -, hZ⟩ := e27_frattini_eq_center hP27 hexp hnc
  have hq : Nat.card (↥P ⧸ Subgroup.center ↥P) = 9 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hP27, hZ] at this
    omega
  have hcomm : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hq]; norm_num)
  have hpow : ∀ x : ↥P ⧸ Subgroup.center ↥P, x ^ 3 = 1 := by
    intro x
    refine QuotientGroup.induction_on x fun y => ?_
    rw [← QuotientGroup.mk_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using hexp (y : MulAut V) y.2)
    rw [this]
    exact QuotientGroup.mk_one _
  have hnt : Nontrivial (↥P ⧸ Subgroup.center ↥P) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hq]
    norm_num
  have helem : CFSG.IsElementaryAbelian 3 (↥P ⧸ Subgroup.center ↥P) :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  exact ⟨⟨hZ, helem, hnt⟩, by rw [hP27]; norm_num,
    fun x => Subtype.ext (by simpa using hexp (x : MulAut V) x.2)⟩

end ShapeE27Aux151c

section Odd27Aux151c

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem e27_mem_zpowers_cube {g x : MulAut V} (hg3 : g ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g ∨ x = g ^ 2 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h : g ^ n = g ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul]
    have h3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg3
    rw [h3, one_zpow, mul_one]
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · left
    rw [h, hr]
    simp
  · right
    left
    rw [h, hr]
    simp
  · right
    right
    rw [h, hr]
    simp

omit [Finite V] in
private theorem e27_fpf_sq {z : MulAut V} (hz3 : z ^ 3 = 1) (hzf : ∀ v : V, z v = v → v = 1)
    (v : V) (hv : (z ^ 2) v = v) : v = 1 := by
  apply hzf
  calc z v = z ((z ^ 2) v) := by rw [hv]
    _ = (z ^ 3) v := by rw [pow_succ']; rfl
    _ = v := by rw [hz3]; rfl

private theorem e27_five_le {Q : Subgroup V} {a b c d e : V} (ha : a ∈ Q) (hb : b ∈ Q)
    (hc : c ∈ Q) (hd : d ∈ Q) (he : e ∈ Q) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : 5 ≤ Nat.card Q := by
  classical
  have hsub : ({a, b, c, d, e} : Set V) ⊆ (Q : Set V) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 : ({a, b, c, d, e} : Set V).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had, hae]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Set.ncard_insert_of_notMem (by simp [hcd, hce]), Set.ncard_pair hde]
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h1] at h2
  have h3 : (Q : Set V).ncard = Nat.card Q := (Nat.card_coe_set_eq (Q : Set V)).symm
  omega

private theorem e27_four_elt {z y : MulAut V} (hz3 : z ^ 3 = 1)
    (hzf : ∀ v : V, z v = v → v = 1) (hzy : z * y = y * z) {Q : Subgroup V}
    (hQ : Nat.card Q = 4) (hzQ : ∀ q ∈ Q, z q ∈ Q) (hyQ : ∀ q ∈ Q, y q ∈ Q) :
    ∃ k : ℕ, ∀ q ∈ Q, y q = (z ^ k) q := by
  classical
  obtain ⟨q₀, hq₀Q, hq₀1⟩ : ∃ q ∈ Q, q ≠ 1 := by
    by_contra h
    push Not at h
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 h
    rw [this, Subgroup.card_bot] at hQ
    omega
  have hz2 : ∀ v : V, (z ^ 2) v = z (z v) := fun v => by rw [pow_two]; rfl
  have hzQ2 : (z ^ 2) q₀ ∈ Q := by rw [hz2]; exact hzQ _ (hzQ _ hq₀Q)
  have hne1 : ∀ v : V, v ≠ 1 → z v ≠ 1 := fun v hv h => hv (z.injective (by rw [h, map_one]))
  have d12 : q₀ ≠ z q₀ := fun h => hq₀1 (hzf _ h.symm)
  have d13 : q₀ ≠ (z ^ 2) q₀ := fun h => hq₀1 (e27_fpf_sq hz3 hzf _ h.symm)
  have d23 : z q₀ ≠ (z ^ 2) q₀ := by
    intro h
    rw [hz2] at h
    exact d12 (z.injective h)
  have d01 : (1 : V) ≠ q₀ := fun h => hq₀1 h.symm
  have d02 : (1 : V) ≠ z q₀ := fun h => hne1 q₀ hq₀1 h.symm
  have d03 : (1 : V) ≠ (z ^ 2) q₀ := fun h => hne1 _ (hne1 q₀ hq₀1) (by rw [← hz2]; exact h.symm)
  have hall : ∀ q ∈ Q, q = 1 ∨ q = q₀ ∨ q = z q₀ ∨ q = (z ^ 2) q₀ := by
    intro q hq
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2, h3⟩ := hcon
    have := e27_five_le Q.one_mem hq₀Q (hzQ _ hq₀Q) hzQ2 hq d01 d02 d03 (Ne.symm h0) d12 d13
      (Ne.symm h1) d23 (Ne.symm h2) (Ne.symm h3)
    omega
  have hyz : ∀ j : ℕ, y * z ^ j = z ^ j * y := fun j =>
    ((Commute.pow_right (show Commute y z from hzy.symm) j)).eq
  have hyq₀ : ∃ k : ℕ, y q₀ = (z ^ k) q₀ := by
    rcases hall (y q₀) (hyQ _ hq₀Q) with h | h | h | h
    · exact absurd (y.injective (by rw [h, map_one])) hq₀1
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  obtain ⟨k, hk⟩ := hyq₀
  refine ⟨k, fun q hq => ?_⟩
  have hyzk : ∀ j : ℕ, ∀ v : V, y ((z ^ j) v) = (z ^ j) (y v) := fun j v => by
    have := congrArg (fun m : MulAut V => m v) (hyz j)
    simpa using this
  have hzk : ∀ j : ℕ, ∀ v : V, (z ^ k) ((z ^ j) v) = (z ^ j) ((z ^ k) v) := fun j v => by
    have : z ^ k * z ^ j = z ^ j * z ^ k := ((Commute.refl z).pow_pow k j).eq
    have := congrArg (fun m : MulAut V => m v) this
    simpa using this
  rcases hall q hq with rfl | rfl | rfl | rfl
  · simp
  · exact hk
  · have := hyzk 1 q₀
    simp only [pow_one] at this
    rw [this, hk]
    have := hzk 1 q₀
    simpa using this.symm
  · rw [hyzk 2 q₀, hk]
    exact (hzk 2 q₀).symm

end Odd27Aux151c

section Odd27Cube151c

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private def e27_diff (g : MulAut V) : V →* V where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

omit [Finite V] in
private theorem e27_diff_apply (g : MulAut V) (v : V) : e27_diff g v = g v * v⁻¹ := rfl

omit [Finite V] in
private theorem e27_mem_ker_diff {g : MulAut V} {v : V} : v ∈ (e27_diff g).ker ↔ g v = v := by
  rw [MonoidHom.mem_ker, e27_diff_apply, mul_inv_eq_one]

omit [Finite V] in
private theorem e27_zpowers_inv {z : MulAut V} (hz3 : z ^ 3 = 1) {B : Subgroup V}
    (hzB : ∀ b ∈ B, z b ∈ B) : ∀ g ∈ Subgroup.zpowers z, ∀ b ∈ B, g b ∈ B := by
  intro g hg b hb
  rcases e27_mem_zpowers_cube hz3 hg with rfl | rfl | rfl
  · simpa using hb
  · exact hzB b hb
  · have : (z ^ 2) b = z (z b) := by rw [pow_two]; rfl
    rw [this]
    exact hzB _ (hzB _ hb)

omit [Finite V] in
private theorem e27_zpowers_fix {y : MulAut V} {v : V} (hv : y v = v) :
    ∀ g ∈ Subgroup.zpowers y, g v = v := fun g hg =>
  (mem_fixV_zpowers_iff.mpr hv) g hg

private theorem e27_zpowers_triv_mod {y : MulAut V} {H : Subgroup V}
    (hy : ∀ v : V, y v * v⁻¹ ∈ H) :
    ∀ g ∈ Subgroup.zpowers y, ∀ w : V, g w * w⁻¹ ∈ H := by
  intro g hg w
  rw [← mem_powers_iff_mem_zpowers] at hg
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hg
  clear hg
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have e : (y ^ (n + 1)) w * w⁻¹ = (y ((y ^ n) w) * ((y ^ n) w)⁻¹) * ((y ^ n) w * w⁻¹) := by
      rw [pow_succ']
      simp [mul_comm, mul_assoc, mul_left_comm]
    rw [e]
    exact H.mul_mem (hy _) (ih w)

omit [Finite V] in
private theorem e27_commSub_inv {y h : MulAut V} (hhy : h * y = y * h) :
    ∀ d ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers y), h d ∈ commSub ⊤ (Subgroup.zpowers y) := by
  intro d hd
  refine Subgroup.closure_induction (p := fun d _ => h d ∈ commSub ⊤ (Subgroup.zpowers y))
    ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨g, hg, w, -, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcomm : h * y ^ n = y ^ n * h := ((show Commute h y from hhy).zpow_right n).eq
    have : h ((y ^ n) w * w⁻¹) = (y ^ n) (h w) * (h w)⁻¹ := by
      have h1 : h ((y ^ n) w) = (y ^ n) (h w) := by
        have := congrArg (fun m : MulAut V => m w) hcomm
        simpa using this
      rw [map_mul, map_inv, h1]
    rw [this]
    exact Subgroup.subset_closure ⟨y ^ n, Subgroup.zpow_mem_zpowers y n, h w, Subgroup.mem_top _, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

end Odd27Cube151c

section Odd27Cube2151c

variable {V : Type} [CommGroup V] [Finite V]

private theorem e27_cube_eq_one (hsq : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 64)
    {z t y : MulAut V} (hz3 : z ^ 3 = 1) (hzf : ∀ v : V, z v = v → v = 1) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hzt : z * t = t * z) (hzy : z * y = y * z) (hty : t * y = y * t)
    (hy : Odd (orderOf y)) : y ^ 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht2v : ∀ v : V, t (t v) = v := fun v => by
    have := congrArg (fun m : MulAut V => m v) ht2
    simpa [pow_two] using this
  have hzt' : ∀ v : V, z (t v) = t (z v) := fun v => by
    have := congrArg (fun m : MulAut V => m v) hzt
    simpa using this
  have hty' : ∀ v : V, t (y v) = y (t v) := fun v => by
    have := congrArg (fun m : MulAut V => m v) hty
    simpa using this
  have hnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hz1 : z ≠ 1 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    exact hv (hzf v (by rw [h]; rfl))
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hPz : IsPGroup 3 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzord]
    norm_num
  have hfixz : fixV (Subgroup.zpowers z) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun v hv => hzf v (mem_fixV_zpowers_iff.mp hv)
  have hmod : ∀ B : Subgroup V, (∀ b ∈ B, z b ∈ B) → Nat.card B ≡ 1 [MOD 3] := fun B hB =>
    card_invariant_modEq hPz hfixz (e27_zpowers_inv hz3 hB)
  set φ : V →* V := e27_diff t with hφ
  set L : Subgroup V := φ.range with hL
  set H : Subgroup V := φ.ker with hH
  have hφapp : ∀ v : V, φ v = t v * v⁻¹ := fun v => rfl
  have hφcomm : ∀ g : MulAut V, g * t = t * g → ∀ v : V, φ (g v) = g (φ v) := by
    intro g hg v
    have h1 : t (g v) = g (t v) := by
      have := congrArg (fun m : MulAut V => m v) hg
      simpa using this.symm
    simp only [hφapp, map_mul, map_inv, h1]
  have hLz : ∀ b ∈ L, z b ∈ L := by
    rintro _ ⟨v, rfl⟩
    exact ⟨z v, hφcomm z hzt v⟩
  have hHz : ∀ b ∈ H, z b ∈ H := by
    intro b hb
    rw [hH, MonoidHom.mem_ker] at hb ⊢
    rw [hφcomm z hzt, hb, map_one]
  have hLy : ∀ b ∈ L, y b ∈ L := by
    rintro _ ⟨v, rfl⟩
    exact ⟨y v, hφcomm y hty.symm v⟩
  have hLH : L ≤ H := by
    rintro _ ⟨v, rfl⟩
    rw [hH, MonoidHom.mem_ker]
    have e : φ (φ v) = (v ^ 2) * ((t v) ^ 2)⁻¹ := by
      simp only [hφapp, map_mul, map_inv, ht2v, pow_two, mul_inv, inv_inv]
      ac_rfl
    rw [e, hsq v, hsq (t v), inv_one, mul_one]
  have h64 : Nat.card H * Nat.card L = 64 := by
    have := Subgroup.card_mul_index H
    rw [hH, Subgroup.index_ker, ← hL, hcard] at this
    exact this
  have hL1 : Nat.card L ≠ 1 := by
    intro h
    have hbot : L = ⊥ := Subgroup.card_eq_one.mp h
    apply ht1
    refine MulEquiv.ext fun v => ?_
    have : φ v ∈ L := ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot, hφapp, mul_inv_eq_one] at this
    exact this
  have hLmod := hmod L hLz
  have hLcard : Nat.card L = 4 := by
    have hLH' : Nat.card L ≤ Nat.card H := Subgroup.card_le_of_le hLH
    have hdvd : Nat.card L ∣ 2 ^ 6 := ⟨Nat.card H, by rw [mul_comm, h64]; norm_num⟩
    obtain ⟨i, hi, hiL⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hiL] at hLmod hL1 hLH' h64 ⊢
    generalize Nat.card H = h at *
    unfold Nat.ModEq at hLmod
    interval_cases i <;> omega
  have hHcard : Nat.card H = 16 := by
    rw [hLcard] at h64
    omega
  obtain ⟨k, hk⟩ := e27_four_elt hz3 hzf hzy hLcard hLz hLy
  have hz3k : z ^ (3 * k) = 1 := by rw [pow_mul, hz3, one_pow]
  set y₁ : MulAut V := y * z ^ (2 * k) with hy₁
  have hcyz : Commute y (z ^ (2 * k)) := Commute.pow_right (show Commute y z from hzy.symm) _
  have hLzpow : ∀ j : ℕ, ∀ b ∈ L, (z ^ j) b ∈ L := fun j b hb =>
    e27_zpowers_inv hz3 hLz (z ^ j) (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) j) b hb
  have hy₁L : ∀ ℓ ∈ L, y₁ ℓ = ℓ := by
    intro ℓ hℓ
    have h1 : y₁ ℓ = y ((z ^ (2 * k)) ℓ) := rfl
    rw [h1, hk _ (hLzpow (2 * k) ℓ hℓ)]
    have : z ^ k * z ^ (2 * k) = 1 := by rw [← pow_add]; rw [show k + 2 * k = 3 * k by ring, hz3k]
    have h2 := congrArg (fun m : MulAut V => m ℓ) this
    simpa using h2
  have hy₁odd : Odd (orderOf y₁) := by
    have h1 : orderOf y₁ ∣ orderOf y * orderOf (z ^ (2 * k)) := hcyz.orderOf_mul_dvd_mul_orderOf
    have h2 : orderOf (z ^ (2 * k)) ∣ 3 :=
      (orderOf_pow_dvd _).trans (orderOf_dvd_of_pow_eq_one hz3)
    have h3 : Odd (orderOf (z ^ (2 * k))) := Odd.of_dvd_nat (by decide : Odd 3) h2
    exact Odd.of_dvd_nat (hy.mul h3) h1
  have hzy₁ : z * y₁ = y₁ * z := by
    have h1 : Commute z y := hzy
    exact (h1.mul_right (Commute.pow_right (Commute.refl z) _)).eq
  have hty₁ : t * y₁ = y₁ * t := by
    have h1 : Commute t y := hty
    exact (h1.mul_right (Commute.pow_right (show Commute t z from hzt.symm) _)).eq
  have hy₁H : ∀ v : V, y₁ v * v⁻¹ ∈ H := by
    intro v
    rw [hH, MonoidHom.mem_ker, map_mul, map_inv, hφcomm y₁ hty₁.symm v, hy₁L _ ⟨v, rfl⟩, mul_inv_cancel]
  set P₁ : Subgroup (MulAut V) := Subgroup.zpowers y₁ with hP₁
  have hP₁odd : Odd (Nat.card P₁) := by rw [hP₁, Nat.card_zpowers]; exact hy₁odd
  obtain ⟨hDsup, hDinf⟩ := coprime_decomp hP₁odd hsq (W := ⊤) (fun g _ w _ => Subgroup.mem_top _)
  set D : Subgroup V := commSub ⊤ P₁ with hD
  have hDH : D ≤ H := by
    rw [hD, commSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, -, rfl⟩
    exact e27_zpowers_triv_mod hy₁H g hg w
  have hLC : L ≤ ⊤ ⊓ fixV P₁ := fun ℓ hℓ =>
    ⟨Subgroup.mem_top _, mem_fixV_zpowers_iff.mpr (hy₁L ℓ hℓ)⟩
  have hDL : D ⊓ L = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ D ⊓ (⊤ ⊓ fixV P₁) := ⟨hx.1, hLC hx.2⟩
    rw [hDinf] at this
    exact this
  have hDz : ∀ d ∈ D, z d ∈ D := e27_commSub_inv hzy₁
  have hDy₁ : ∀ d ∈ D, y₁ d ∈ D := e27_commSub_inv rfl
  have hDmod := hmod D hDz
  have hDLcard : Nat.card ↥(D ⊔ L) = Nat.card D * Nat.card L :=
    card_sup_of_normalizes (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp) hDL
  have hDle : Nat.card D * 4 ≤ 16 := by
    have := Subgroup.card_le_of_le (sup_le hDH hLH)
    rw [hDLcard, hLcard, hHcard] at this
    exact this
  have hDcard : Nat.card D = 1 ∨ Nat.card D = 4 := by
    have hdvd : Nat.card D ∣ 2 ^ 6 := by
      have := Subgroup.card_subgroup_dvd_card D
      rw [hcard] at this
      simpa using this
    obtain ⟨i, hi, hiD⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hiD] at hDmod hDle ⊢
    unfold Nat.ModEq at hDmod
    interval_cases i <;> omega
  have hcubeV : ∀ v : V, (y₁ ^ 3) v = v := by
    intro v
    have hv : v ∈ D ⊔ (⊤ ⊓ fixV P₁) := by rw [hDsup]; exact Subgroup.mem_top v
    obtain ⟨d, hd, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
    have hcfix : y₁ c = c := hc.2 y₁ (Subgroup.mem_zpowers y₁)
    have hcube : (y₁ ^ 3) c = c := by simp [pow_succ, hcfix]
    rw [map_mul, hcube]
    congr 1
    rcases hDcard with h1 | h4
    · have hD1 : D = ⊥ := Subgroup.card_eq_one.mp h1
      have : d = 1 := by rw [hD1] at hd; exact Subgroup.mem_bot.mp hd
      rw [this]
      simp
    · obtain ⟨k', hk'⟩ := e27_four_elt hz3 hzf hzy₁ h4 hDz hDy₁
      have hdz : ∀ j : ℕ, ∀ b ∈ D, (z ^ j) b ∈ D := fun j b hb =>
        e27_zpowers_inv hz3 hDz (z ^ j) (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) j) b hb
      have e1 : y₁ d = (z ^ k') d := hk' d hd
      have h2 : (z ^ k') d ∈ D := hdz k' d hd
      have e2 : y₁ ((z ^ k') d) = (z ^ k') ((z ^ k') d) := hk' _ h2
      have h3 : (z ^ k') ((z ^ k') d) ∈ D := hdz k' _ h2
      have e3 : y₁ ((z ^ k') ((z ^ k') d)) = (z ^ k') ((z ^ k') ((z ^ k') d)) := hk' _ h3
      have hzz : z ^ k' * (z ^ k' * z ^ k') = 1 := by
        rw [← pow_add, ← pow_add, show k' + (k' + k') = 3 * k' by ring, pow_mul, hz3, one_pow]
      have e4 : (z ^ k') ((z ^ k') ((z ^ k') d)) = d := by
        have := congrArg (fun m : MulAut V => m d) hzz
        simpa using this
      have e5 : (y₁ ^ 3) d = y₁ (y₁ (y₁ d)) := by simp [pow_succ]
      rw [e5, e1, e2, e3, e4]
  have hy₁cube : y₁ ^ 3 = 1 := MulEquiv.ext hcubeV
  have hyy : y = y₁ * z ^ k := by
    rw [hy₁, mul_assoc, ← pow_add, show 2 * k + k = 3 * k by ring, hz3k, mul_one]
  have hc2 : Commute y₁ (z ^ k) := by
    have : Commute y₁ z := hzy₁.symm
    exact this.pow_right k
  rw [hyy, hc2.mul_pow, hy₁cube, one_mul, ← pow_mul, mul_comm k 3, pow_mul, hz3, one_pow]

end Odd27Cube2151c

section Odd27Group151c

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem e27_mem_zpowers_sq {t x : MulAut V} (ht2 : t ^ 2 = 1) (hx : x ∈ Subgroup.zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul]
    have h2 : t ^ (2 : ℤ) = 1 := by exact_mod_cast ht2
    rw [h2, one_zpow, mul_one]
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with hr | hr
  · left
    rw [h, hr]
    simp
  · right
    rw [h, hr]
    simp

omit [Finite V] in
private theorem e27_mem_sup_zpowers {P : Subgroup (MulAut V)} {t j : MulAut V} (ht2 : t ^ 2 = 1)
    (htP : ∀ f ∈ P, t * f * t⁻¹ ∈ P) (hj : j ∈ P ⊔ Subgroup.zpowers t) :
    j ∈ P ∨ ∃ p ∈ P, j = p * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have hj' : j ∈ Subgroup.closure ((P : Set (MulAut V)) ∪ (Subgroup.zpowers t : Set (MulAut V))) := by
    rw [← Subgroup.sup_eq_closure]
    exact hj
  refine Subgroup.closure_induction (p := fun j _ => j ∈ P ∨ ∃ p ∈ P, j = p * t) ?_ ?_ ?_ ?_ hj'
  · rintro x (hx | hx)
    · exact Or.inl hx
    · rcases e27_mem_zpowers_sq ht2 hx with rfl | rfl
      · exact Or.inl P.one_mem
      · exact Or.inr ⟨1, P.one_mem, by simp⟩
  · exact Or.inl P.one_mem
  · intro a b _ _ ha hb
    rcases ha with ha | ⟨p, hp, rfl⟩ <;> rcases hb with hb | ⟨p', hp', rfl⟩
    · exact Or.inl (P.mul_mem ha hb)
    · exact Or.inr ⟨a * p', P.mul_mem ha hp', by rw [mul_assoc]⟩
    · refine Or.inr ⟨p * (t * b * t⁻¹), P.mul_mem hp (htP b hb), ?_⟩
      group
    · refine Or.inl ?_
      have e : p * t * (p' * t) = p * (t * p' * t⁻¹) * (t * t) := by group
      rw [e, show t * t = 1 by rw [← pow_two]; exact ht2, mul_one]
      exact P.mul_mem hp (htP p' hp')
  · intro a _ ha
    rcases ha with ha | ⟨p, hp, rfl⟩
    · exact Or.inl (P.inv_mem ha)
    · refine Or.inr ⟨t * p⁻¹ * t⁻¹, htP _ (P.inv_mem hp), ?_⟩
      calc (p * t)⁻¹ = t⁻¹ * p⁻¹ := mul_inv_rev _ _
        _ = t * p⁻¹ := by rw [htinv]
        _ = t * p⁻¹ * t⁻¹ * t := by group

end Odd27Group151c

section Odd27Group2151c

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem e27_comm_cancel {G : Type*} [Group G] {a b u v : G} (hua : u * a = a * u)
    (hub : u * b = b * u) (hva : v * a = a * v) (hvb : v * b = b * v) (huv : u * v = v * u) :
    (u * a⁻¹) * (v * b⁻¹) * (u * a⁻¹)⁻¹ * (v * b⁻¹)⁻¹ = a⁻¹ * b⁻¹ * a * b := by
  have cua : Commute u a := hua
  have cub : Commute u b := hub
  have cva : Commute v a := hva
  have cvb : Commute v b := hvb
  have cuv : Commute u v := huv
  have hX : Commute u (a⁻¹ * v * b⁻¹ * a) :=
    (((cua.inv_right).mul_right cuv).mul_right cub.inv_right).mul_right cua
  have hY : Commute v (b⁻¹ * a * b) := ((cvb.inv_right).mul_right cva).mul_right cvb
  calc (u * a⁻¹) * (v * b⁻¹) * (u * a⁻¹)⁻¹ * (v * b⁻¹)⁻¹
      = u * (a⁻¹ * v * b⁻¹ * a) * u⁻¹ * (b * v⁻¹) := by group
    _ = (a⁻¹ * v * b⁻¹ * a) * (b * v⁻¹) := by rw [hX.mul_inv_cancel]
    _ = a⁻¹ * (v * (b⁻¹ * a * b) * v⁻¹) := by group
    _ = a⁻¹ * b⁻¹ * a * b := by rw [hY.mul_inv_cancel]; group

private theorem e27_t_comm_frattini {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) {t : MulAut V}
    (hinv : ∀ f ∈ P, t * f * t⁻¹ * f ∈ frattiniIn P) :
    ∀ z ∈ frattiniIn P, t * z = z * t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΦ3 := e27_card_frattiniIn hP27 hexp hnc
  have hcen : ∀ ζ ∈ frattiniIn P, ∀ y ∈ P, y * ζ = ζ * y := fun ζ hζ y hy =>
    ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hζ).2 y hy
  have hΦP : ∀ ζ ∈ frattiniIn P, ζ ∈ P := fun ζ hζ =>
    ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hζ).1
  obtain ⟨a, haP, b, hbP, hab⟩ := hnc
  have hnc' : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f := ⟨a, haP, b, hbP, hab⟩
  set c : MulAut V := a * b * a⁻¹ * b⁻¹ with hc
  have hcΦ : c ∈ frattiniIn P := e27_comm_mem_frattiniIn hP27 hexp hnc' haP hbP
  have hc1 : c ≠ 1 := by
    intro h
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [← hc, h, one_mul]
  have hcc : ∀ y ∈ P, y * c = c * y := hcen c hcΦ
  have hζa := hinv a haP
  have hζb := hinv b hbP
  set ζa : MulAut V := t * a * t⁻¹ * a with hζa_def
  set ζb : MulAut V := t * b * t⁻¹ * b with hζb_def
  have hta : t * a * t⁻¹ = ζa * a⁻¹ := by rw [hζa_def]; group
  have htb : t * b * t⁻¹ = ζb * b⁻¹ := by rw [hζb_def]; group
  have hconj : t * c * t⁻¹ =
      (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by
    rw [hc]; group
  rw [hta, htb] at hconj
  have hua : ζa * a = a * ζa := (hcen ζa hζa a haP).symm
  have hub : ζa * b = b * ζa := (hcen ζa hζa b hbP).symm
  have hva : ζb * a = a * ζb := (hcen ζb hζb a haP).symm
  have hvb : ζb * b = b * ζb := (hcen ζb hζb b hbP).symm
  have huv : ζa * ζb = ζb * ζa := hcen ζb hζb ζa (hΦP ζa hζa)
  rw [e27_comm_cancel hua hub hva hvb huv] at hconj
  have hcc' : a⁻¹ * b⁻¹ * a * b = c := by
    have h1 : a * b = c * (b * a) := by rw [hc]; group
    have hcom : Commute c (a⁻¹ * b⁻¹) :=
      ((show Commute c a from (hcc a haP).symm).inv_right).mul_right
        ((show Commute c b from (hcc b hbP).symm).inv_right)
    calc a⁻¹ * b⁻¹ * a * b = (a⁻¹ * b⁻¹) * (a * b) := by group
      _ = (a⁻¹ * b⁻¹) * (c * (b * a)) := by rw [h1]
      _ = ((a⁻¹ * b⁻¹) * c) * (b * a) := by group
      _ = (c * (a⁻¹ * b⁻¹)) * (b * a) := by rw [hcom.eq.symm]
      _ = c := by group
  have htc : t * c = c * t := by
    have h1 : t * c * t⁻¹ = c := by rw [hconj, hcc']
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h1]
  intro z hz
  have hΦ : Subgroup.zpowers c = frattiniIn P := zpowers_eq_of_prime_card hΦ3 hcΦ hc1
  rw [← hΦ] at hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ((show Commute t c from htc).zpow_right n).eq

omit [Finite V] in
private theorem e27_odd_comm_frattini {P : Subgroup (MulAut V)} (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) {z : MulAut V}
    (hzΦ : z ∈ frattiniIn P) (hz1 : z ≠ 1) (hzgen : Subgroup.zpowers z = frattiniIn P)
    {y : MulAut V} (hyP : ∀ f ∈ P, y * f * y⁻¹ ∈ P) (hyP' : ∀ f ∈ P, y⁻¹ * f * y ∈ P)
    (hyodd : Odd (orderOf y)) : y * z = z * y := by
  have hcen : ∀ ζ ∈ frattiniIn P, ∀ y ∈ P, y * ζ = ζ * y := fun ζ hζ y hy =>
    ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hζ).2 y hy
  have hzP : z ∈ P := ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hzΦ).1
  have hz3 : z ^ 3 = 1 := hexp z hzP
  have hyz : y * z * y⁻¹ ∈ frattiniIn P := by
    refine (e27_mem_frattiniIn_iff hP27 hexp hnc).2 ⟨hyP z hzP, fun f hf => ?_⟩
    have h1 := hcen z hzΦ (y⁻¹ * f * y) (hyP' f hf)
    calc f * (y * z * y⁻¹) = y * ((y⁻¹ * f * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * f * y)) * y⁻¹ := by rw [h1]
      _ = (y * z * y⁻¹) * f := by group
  have hyz' : y * z * y⁻¹ ∈ Subgroup.zpowers z := by rw [hzgen]; exact hyz
  rcases e27_mem_zpowers_cube hz3 hyz' with h | h | h
  · exfalso
    apply hz1
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this
  · calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [h]
  · exfalso
    have hz4 : z ^ 4 = z := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hz3, one_mul, pow_one]
    have e : y * y * z * (y * y)⁻¹ = z := by
      calc y * y * z * (y * y)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ := by group
        _ = y * z ^ 2 * y⁻¹ := by rw [h]
        _ = (y * z * y⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        _ = (z ^ 2) ^ 2 := by rw [h]
        _ = z := by rw [← pow_mul]; exact hz4
    have hy2z : (y * y) * z = z * (y * y) := by
      calc (y * y) * z = (y * y * z * (y * y)⁻¹) * (y * y) := by group
        _ = z * (y * y) := by rw [e]
    obtain ⟨k, hk⟩ := hyodd
    have hyk : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    have hyy : y = (y * y) ^ (k + 1) := by
      calc y = y ^ (2 * k + 1) * y := by rw [hyk, one_mul]
        _ = y ^ ((2 * k + 1) + 1) := (pow_succ _ _).symm
        _ = y ^ (2 * (k + 1)) := by rw [show (2 * k + 1) + 1 = 2 * (k + 1) by ring]
        _ = (y * y) ^ (k + 1) := by rw [pow_mul, pow_two]
    have hcz : Commute z (y * y) := hy2z.symm
    have hzy : z * y = y * z := by
      have h1 : Commute z ((y * y) ^ (k + 1)) := hcz.pow_right (k + 1)
      rw [← hyy] at h1
      exact h1.eq
    have h2 : y * z * y⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul, hzy]
    rw [h2] at h
    apply hz1
    have h3 : z * z = z * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel h3

end Odd27Group2151c

section Odd27Group3151c

variable {V : Type} [CommGroup V] [Finite V]

private theorem e27_false_of_cube_one {X : Subgroup (MulAut V)} (hX : IsQuotientOfSQTKTC ↥X)
    {P : Subgroup (MulAut V)} (hPX : P ≤ X) (hP27 : Nat.card P = 27)
    (hexp : ∀ f ∈ P, f ^ 3 = 1) (hnc : ∃ f ∈ P, ∃ g ∈ P, f * g ≠ g * f) {t z y : MulAut V}
    (htX : t ∈ X) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hinv : ∀ f ∈ P, t * f * t⁻¹ * f ∈ frattiniIn P) (htP : ∀ f ∈ P, t * f * t⁻¹ ∈ P)
    (hzΦ : z ∈ frattiniIn P) (hz1 : z ≠ 1) (htz : t * z = z * t) (hyX : y ∈ X)
    (hyP : ∀ f ∈ P, y * f * y⁻¹ ∈ P) (hyP' : ∀ f ∈ P, y⁻¹ * f * y ∈ P) (hy3 : y ^ 3 = 1)
    (hyn : y ∉ P) (hty : t * y = y * t) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzP : z ∈ P := ((e27_mem_frattiniIn_iff hP27 hexp hnc).1 hzΦ).1
  have hy1 : y ≠ 1 := fun h => hyn (h ▸ P.one_mem)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hzy_card : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
  have hzord : orderOf z = 3 := orderOf_eq_prime (hexp z hzP) hz1
  have hzz_card : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  set Q : Subgroup (MulAut V) := P ⊔ Subgroup.zpowers y with hQ
  have hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set (MulAut V)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => hyP f hf, fun hf => ?_⟩
    have := hyP' _ hf
    have e : y⁻¹ * (y * f * y⁻¹) * y = f := by group
    rwa [e] at this
  have hinf : P ⊓ Subgroup.zpowers y = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    by_contra hg1
    have hgp : Subgroup.zpowers g = Subgroup.zpowers y :=
      zpowers_eq_of_prime_card hzy_card hg.2 hg1
    apply hyn
    have : y ∈ Subgroup.zpowers g := by rw [hgp]; exact Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.mpr hg.1) this
  have hQcard : Nat.card Q = 81 := by
    rw [hQ, card_sup_of_normalizes hyNorm hinf, hP27, hzy_card]
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 4) (by rw [hQcard]; norm_num)
  have hPQ : P ≤ Q := le_sup_left
  have hyQ : y ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hQX : Q ≤ X := sup_le hPX (Subgroup.zpowers_le.mpr hyX)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have htQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro q hq
    have hq' : q ∈ Subgroup.closure ((P : Set (MulAut V)) ∪
        (Subgroup.zpowers y : Set (MulAut V))) := by
      rw [← Subgroup.sup_eq_closure]
      exact hq
    refine Subgroup.closure_induction (p := fun q _ => t * q * t⁻¹ ∈ Q) ?_ ?_ ?_ ?_ hq'
    · rintro x (hx | hx)
      · exact hPQ (htP x hx)
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have h1 : t * y ^ n * t⁻¹ = y ^ n := by
          have := ((show Commute t y from hty).zpow_right n).eq
          rw [mul_inv_eq_iff_eq_mul]
          exact this
        rw [h1]
        exact Subgroup.zpow_mem _ hyQ n
    · simp
    · intro a b _ _ ha hb
      have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [this]
      exact Q.mul_mem ha hb
    · intro a _ ha
      have : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
      rw [this]
      exact Q.inv_mem ha
  have hAn : ∀ a ∈ Subgroup.zpowers t, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := by
    intro a ha q hq
    rcases e27_mem_zpowers_sq ht2 ha with rfl | rfl
    · simpa using hq
    · exact htQ q hq
  have hfaith : ∀ a ∈ Subgroup.zpowers t, (∀ q ∈ Q, a * q = q * a) → a = 1 := by
    intro a ha hcomm
    rcases e27_mem_zpowers_sq ht2 ha with h | h
    · exact h
    · exfalso
      rw [h] at hcomm
      have hall : ∀ f ∈ P, f ∈ frattiniIn P := by
        intro f hf
        have h0 : t * f * t⁻¹ = f := by
          calc t * f * t⁻¹ = f * t * t⁻¹ := by rw [hcomm f (hPQ hf)]
            _ = f := by group
        have h1 : t * f * t⁻¹ * f = f * f := by rw [h0]
        have h2 := hinv f hf
        rw [h1] at h2
        have h3 : f * f * (f * f) = f := by
          have hf3 : f * f * f = 1 := by simpa [pow_succ] using hexp f hf
          calc f * f * (f * f) = (f * f * f) * f := by group
            _ = f := by rw [hf3, one_mul]
        rw [← h3]
        exact (frattiniIn P).mul_mem h2 h2
      obtain ⟨a, haP, b, hbP, hab⟩ := hnc
      exact hab (((e27_mem_frattiniIn_iff hP27 hexp ⟨a, haP, b, hbP, hab⟩).1 (hall b hbP)).2 a haP)
  have hcyc : IsCyclic ↥(Q ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) :=
    isCyclic_inf_centralizer_of_faithful (X := X) (P := Q) (A := Subgroup.zpowers t) (p := 3)
      (by norm_num) hQX hQp (isElemAbelian2_zpowers151c ht2) (Subgroup.zpowers_le.mpr htX) hAn hX
      hfaith (a := t) (Subgroup.mem_zpowers t) ht1
  set K : Subgroup (MulAut V) := Q ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) with hK
  have hzK : z ∈ K := ⟨hPQ hzP, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]; exact htz⟩
  have hyK : y ∈ K := ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]; exact hty⟩
  have hz_le : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.mpr hzK
  have hy_le : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr hyK
  have hA'card : Nat.card ((Subgroup.zpowers z).subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz_le).toEquiv, hzz_card]
  have hD'card : Nat.card ((Subgroup.zpowers y).subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hy_le).toEquiv, hzy_card]
  have heq : (Subgroup.zpowers z).subgroupOf K = (Subgroup.zpowers y).subgroupOf K :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [hA'card, hD'card])
  have hymem : (⟨y, hyK⟩ : ↥K) ∈ (Subgroup.zpowers y).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)
  rw [← heq] at hymem
  have hyz : y ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hymem
  exact hyn ((Subgroup.zpowers_le.mpr hzP) hyz)

end Odd27Group3151c

section Odd27Main151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

private theorem e27_odd_mem (B : OneBlock151c X Tb Xc J r) (hF27 : Nat.card (fittingOf J) = 27)
    (hexp : ∀ f ∈ fittingOf J, f ^ 3 = 1)
    (hnc : ∃ f ∈ fittingOf J, ∃ g ∈ fittingOf J, f * g ≠ g * f)
    (ht : ∃ t ∈ J, orderOf t = 2 ∧
      (∀ f ∈ fittingOf J, t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf J)).map (fittingOf J).subtype) ∧
      J = fittingOf J ⊔ Subgroup.zpowers t) (hrk : rk V = 6) :
    ∀ x ∈ X, Odd (orderOf x) → x ∈ fittingOf J := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htJ, ht2o, hinv, hJ⟩ := ht
  have hcard : Nat.card V = 64 := by rw [card_eq_two_pow_rk B.sq, hrk]; norm_num
  have hfix : fixV (fittingOf J) = ⊥ :=
    fixV_fittingOf_eq_bot B.sq B.hyp.o2 B.hyp.comm_fitting
  have hPX : fittingOf J ≤ X := (fittingOf_le J).trans B.le
  have hPn : ∀ x ∈ X, ∀ f ∈ fittingOf J, x * f * x⁻¹ ∈ fittingOf J := fun x hx f hf =>
    conj_mem_fittingOf_of_normalIn151c B.normal hx hf
  have hPn' : ∀ x ∈ X, ∀ f ∈ fittingOf J, x⁻¹ * f * x ∈ fittingOf J := fun x hx f hf => by
    simpa using hPn x⁻¹ (X.inv_mem hx) f hf
  have htX : t ∈ X := B.le htJ
  have ht2 : t ^ 2 = 1 := by rw [← ht2o]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2o; omega
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have htP : ∀ f ∈ fittingOf J, t * f * t⁻¹ ∈ fittingOf J := hPn t htX
  have hinv' : ∀ f ∈ fittingOf J, t * f * t⁻¹ * f ∈ frattiniIn (fittingOf J) := hinv
  have hΦ3 := e27_card_frattiniIn hF27 hexp hnc
  obtain ⟨z, hzΦ, hz1, hzgen, -⟩ := exists_generator_of_prime_card hΦ3
  have hzP : z ∈ fittingOf J := ((e27_mem_frattiniIn_iff hF27 hexp hnc).1 hzΦ).1
  have hz3 : z ^ 3 = 1 := hexp z hzP
  have hzf := e27_fixV_frattiniIn B.sq hF27 hexp hnc hfix hrk z hzΦ hz1
  have htz : t * z = z * t := e27_t_comm_frattini hF27 hexp hnc hinv' z hzΦ
  intro x hx hxodd
  by_contra hxP
  have ht'J : x * t * x⁻¹ ∈ J := B.normal x hx t htJ
  have ht'2 : (x * t * x⁻¹) ^ 2 = 1 := by
    have : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by rw [pow_two, pow_two]; group
    rw [this, ht2]
    group
  have ht'1 : x * t * x⁻¹ ≠ 1 := fun h => ht1 (by
    have := congrArg (fun w => x⁻¹ * w * x) h
    simpa [mul_assoc] using this)
  have ht'P : x * t * x⁻¹ ∉ fittingOf J := by
    intro h
    apply ht'1
    have h3 := hexp _ h
    calc x * t * x⁻¹ = (x * t * x⁻¹) ^ 3 * ((x * t * x⁻¹) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, ht'2]; group
  have hJ' : x * t * x⁻¹ ∈ fittingOf J ⊔ Subgroup.zpowers t := hJ ▸ ht'J
  obtain ⟨p, hpP, hp⟩ : ∃ p ∈ fittingOf J, x * t * x⁻¹ = p * t := by
    rcases e27_mem_sup_zpowers ht2 htP hJ' with h | h
    · exact absurd h ht'P
    · exact h
  have hptpt : (p * t) * (p * t) = 1 := by
    rw [hp, pow_two] at ht'2
    exact ht'2
  have htp : t * p * t⁻¹ = p⁻¹ := by
    calc t * p * t⁻¹ = t * p * t := by rw [htinv]
      _ = p⁻¹ := eq_inv_of_mul_eq_one_right (by
        calc p * (t * p * t) = (p * t) * (p * t) := by group
          _ = 1 := hptpt)
  have htp' : t * p⁻¹ * t⁻¹ = p := by
    rw [show t * p⁻¹ * t⁻¹ = (t * p * t⁻¹)⁻¹ by group, htp, inv_inv]
  have hp3 : p ^ 3 = 1 := hexp p hpP
  have hp3' : p * p * p = 1 := by simpa [pow_succ] using hp3
  set c : MulAut V := p * x with hc
  have hcX : c ∈ X := X.mul_mem (hPX hpP) hx
  have hct : t * c = c * t := by
    have h1 : c * t * c⁻¹ = t := by
      calc c * t * c⁻¹ = p * (x * t * x⁻¹) * p⁻¹ := by rw [hc]; group
        _ = p * (p * t) * p⁻¹ := by rw [hp]
        _ = p * p * (t * p⁻¹ * t⁻¹) * t := by group
        _ = p * p * p * t := by rw [htp']
        _ = t := by rw [hp3', one_mul]
    calc t * c = (c * t * c⁻¹) * c := by rw [h1]
      _ = c * t := by group
  have hcn : c ∉ fittingOf J := by
    intro hcP
    apply hxP
    have : x = p⁻¹ * c := by rw [hc]; group
    rw [this]
    exact (fittingOf J).mul_mem ((fittingOf J).inv_mem hpP) hcP
  have hcodd : Odd (orderOf c) := by
    have hxpow : ∀ n : ℕ, ∀ f ∈ fittingOf J, x ^ n * f * (x ^ n)⁻¹ ∈ fittingOf J := by
      intro n
      induction n with
      | zero => intro f hf; simpa using hf
      | succ n ih =>
        intro f hf
        have : x ^ (n + 1) * f * (x ^ (n + 1))⁻¹ = x * (x ^ n * f * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']
          group
        rw [this]
        exact hPn x hx _ (ih f hf)
    have hcpow : ∀ n : ℕ, ∃ q ∈ fittingOf J, c ^ n = q * x ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, (fittingOf J).one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨q, hq, hqe⟩ := ih
        refine ⟨q * (x ^ n * p * (x ^ n)⁻¹), (fittingOf J).mul_mem hq (hxpow n p hpP), ?_⟩
        rw [pow_succ, hqe, hc]
        group
    obtain ⟨q, hq, hqe⟩ := hcpow (orderOf x)
    rw [pow_orderOf_eq_one x, mul_one] at hqe
    have h3 : c ^ (orderOf x * 3) = 1 := by rw [pow_mul, hqe]; exact hexp q hq
    exact Odd.of_dvd_nat (hxodd.mul (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one h3)
  have hczP : c * z = z * c :=
    e27_odd_comm_frattini hF27 hexp hnc hzΦ hz1 hzgen (hPn c hcX) (hPn' c hcX) hcodd
  have hc3 : c ^ 3 = 1 :=
    e27_cube_eq_one B.sq hcard hz3 hzf ht2 ht1 htz.symm hczP.symm hct hcodd
  exact e27_false_of_cube_one B.setting.sqtk hPX hF27 hexp hnc htX ht2 ht1 hinv' htP hzΦ hz1 htz
    hcX (hPn c hcX) (hPn' c hcX) hc3 hcn hct

end Odd27Main151c

section ShapeE27151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem shape_E27 (B : OneBlock151c X Tb Xc J r) (hF27 : Nat.card (fittingOf J) = 27)
    (hexp : ∀ f ∈ fittingOf J, f ^ 3 = 1) (hnc : ∃ f ∈ fittingOf J, ∃ g ∈ fittingOf J, f * g ≠ g * f)
    (ht : ∃ t ∈ J, orderOf t = 2 ∧
      (∀ f ∈ fittingOf J, t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf J)).map (fittingOf J).subtype) ∧
      J = fittingOf J ⊔ Subgroup.zpowers t) (_hr : r = 2) (hrk : rk V = 6) :
    ACase7 X Tb J := by
  have hOdd : ∀ x ∈ X, Odd (orderOf x) → x ∈ fittingOf J := e27_odd_mem B hF27 hexp hnc ht hrk
  have hPX : fittingOf J ≤ X := (fittingOf_le J).trans B.le
  have hPeq : oTwoUpper X = fittingOf J := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hOdd x hx.1 hx.2) fun f hf => ?_
    refine mem_oTwoUpper_of_odd (hPX hf) ?_
    exact Odd.of_dvd_nat (n := 3) ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one (hexp f hf))
  have hXeq : Tb ⊔ fittingOf J = X := by
    have h := F112W.sup_oTwoUpper_eq_of_isSylowTwoOf (B.syl : IsSylowTwoOf Tb X)
    rwa [hPeq] at h
  have hTbP : ∀ τ ∈ Tb, ∀ x ∈ fittingOf J, τ * x * τ⁻¹ ∈ fittingOf J := by
    intro τ hτ x hx
    have hn := le_normalizer_oTwoUpper X
    rw [hPeq] at hn
    exact (Subgroup.mem_normalizer_iff.mp (hn (B.tb_le hτ)) x).mp hx
  have hfix : fixV (fittingOf J) = ⊥ := fixV_fittingOf_eq_bot B.sq B.hyp.o2 B.hyp.comm_fitting
  have hcard : Nat.card V = 64 := by rw [card_eq_two_pow_rk B.sq, hrk]; norm_num
  unfold ACase7 AExtraspecialThree
  rw [hPeq]
  refine ⟨hcard, e27_isPOnePlusTwo hF27 hexp hnc, ?_,
    e27_irred B.setting hPX hXeq hF27 hexp hnc hfix hrk hTbP⟩
  obtain ⟨t, -, ht2, hinv, hJ⟩ := ht
  exact ⟨t, ht2, hinv, hJ⟩

end ShapeE27151c

end CFSG.Quasithin
