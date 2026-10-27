module

public import CFSG.Quasithin.Background.P4InspSpBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.G11 CFSG.QuasithinUnique

namespace S143W

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem vec_add_self (u : V) : u + u = 0 := by
  rw [← two_smul (ZMod 2) u]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

private theorem vec_neg_eq (u : V) : -u = u := neg_eq_of_add_eq_zero_left (vec_add_self u)

private theorem B_symm {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B) (x y : V) :
    B x y = B y x := by
  have h := hB.1 (x + y)
  simp only [map_add, LinearMap.add_apply, hB.1 x, hB.1 y, zero_add, add_zero] at h
  revert h
  generalize B x y = a
  generalize B y x = b
  revert a b
  decide

private theorem eq_zero_of_forall_B {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B)
    {z : V} (h : ∀ x, B x z = 0) : z = 0 :=
  hB.2 z fun y => by rw [B_symm hB]; exact h y

private theorem exists_B_eq_one {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B)
    {v : V} (hv : v ≠ 0) : ∃ y, B y v = 1 := by
  by_contra hcon
  apply hv
  apply eq_zero_of_forall_B hB
  intro x
  rcases zmod2_cases (B x v) with h0 | h1
  · exact h0
  · exact absurd ⟨x, h1⟩ hcon

private theorem eq_zero_or_eq_of_perp {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B)
    {v : V} (hv : v ≠ 0) {z : V} (h : ∀ w, B w v = 0 → B w z = 0) : z = 0 ∨ z = v := by
  obtain ⟨y₀, hy₀⟩ := exists_B_eq_one hB hv
  have key : ∀ y, B y z = B y₀ z * B y v := by
    intro y
    have h1 : B (y + B y v • y₀) v = 0 := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hy₀,
        mul_one]
      generalize B y v = a
      revert a
      decide
    have h2 := h _ h1
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    generalize B y z = a at h2 ⊢
    generalize B y v = b at h2 ⊢
    generalize B y₀ z = c at h2 ⊢
    revert a b c
    decide
  have hz : z - B y₀ z • v = 0 := by
    apply eq_zero_of_forall_B hB
    intro x
    rw [map_sub, map_smul, smul_eq_mul, key x, sub_self]
  rcases zmod2_cases (B y₀ z) with h0 | h1
  · left
    rw [h0, zero_smul, sub_zero] at hz
    exact hz
  · right
    rw [h1, one_smul, sub_eq_zero] at hz
    exact hz

private theorem eq_transvection {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B)
    {γ : GLV V} (hγ : γ ∈ spSub B) {v : V} (hv : v ≠ 0)
    (hfix : ∀ x : V, B x v = 0 → γ x = x) (hne : γ ≠ 1) :
    ∀ x : V, γ x = x + B x v • v := by
  have hiso : ∀ x y, B (γ x) (γ y) = B x y := hγ
  have hperp : ∀ y, γ y - y = 0 ∨ γ y - y = v := by
    intro y
    apply eq_zero_or_eq_of_perp hB hv
    intro w hw
    have h1 : γ w = w := hfix w hw
    have h2 : B w (γ y) = B w y := by
      have := hiso w y
      rwa [h1] at this
    rw [map_sub, h2, sub_self]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, γ y₀ ≠ y₀ := by
    by_contra hcon
    have hall : ∀ y, γ y = y := fun y => by
      by_contra h'
      exact hcon ⟨y, h'⟩
    exact hne (LinearEquiv.ext hall)
  have hy₀v : γ y₀ - y₀ = v := by
    rcases hperp y₀ with h | h
    · exact absurd (sub_eq_zero.1 h) hy₀
    · exact h
  have hBy₀ : B y₀ v = 1 := by
    rcases zmod2_cases (B y₀ v) with h0 | h1
    · exact absurd (hfix y₀ h0) hy₀
    · exact h1
  intro x
  rcases zmod2_cases (B x v) with h0 | h1
  · rw [h0, zero_smul, add_zero]
    exact hfix x h0
  · have hB0 : B (x + y₀) v = 0 := by
      rw [map_add, LinearMap.add_apply, h1, hBy₀]
      decide
    have h3 := hfix (x + y₀) hB0
    rw [map_add] at h3
    have e1 : γ x = x + y₀ - γ y₀ := eq_sub_of_add_eq h3
    calc γ x = x + y₀ - γ y₀ := e1
      _ = x - (γ y₀ - y₀) := by abel
      _ = x + v := by rw [hy₀v, sub_eq_add_neg, vec_neg_eq]
      _ = x + B x v • v := by rw [h1, one_smul]

private theorem comm_transvection {B : LinearMap.BilinForm (ZMod 2) V} (hB : IsSymplectic B)
    {v : V} (hv : v ≠ 0) {γ e : GLV V} (hγ : ∀ x, γ x = x + B x v • v) (he : e ∈ spSub B)
    (hev : B (e v) v = 0) (hne : e v ≠ v) :
    (e * γ * e⁻¹ * γ⁻¹) ^ 2 = 1 ∧ e * γ * e⁻¹ * γ⁻¹ ≠ 1 := by
  have hiso : ∀ x y, B (e x) (e y) = B x y := he
  have hvv : B v v = 0 := hB.1 v
  have hcc : B (e v) (e v) = 0 := hB.1 _
  have hvc : B v (e v) = 0 := by rw [B_symm hB]; exact hev
  have hγγ : ∀ x, γ (γ x) = x := by
    intro x
    have h1 : B (γ x) v = B x v := by
      rw [hγ x]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvv,
        mul_zero, add_zero]
    rw [hγ (γ x), h1, hγ x, add_assoc, vec_add_self, add_zero]
  have hγ2 : γ * γ = 1 := LinearEquiv.ext fun x => hγγ x
  have hinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
  have hinvapp : ∀ x, e (e⁻¹ x) = x := fun x => LinearEquiv.apply_symm_apply e x
  have hB_inv : ∀ x y, B (e⁻¹ x) y = B x (e y) := by
    intro x y
    rw [← hiso (e⁻¹ x) y, hinvapp]
  set g : GLV V := e * γ * e⁻¹ * γ⁻¹ with hgdef
  have hg : ∀ x, g x = x + B x v • v + B x (e v) • e v := by
    intro x
    have hBy : B (γ x) (e v) = B x (e v) := by
      rw [hγ x]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvc,
        mul_zero, add_zero]
    calc g x = e (γ (e⁻¹ (γ x))) := by rw [hgdef, hinv]; rfl
      _ = γ x + B (γ x) (e v) • e v := by
          rw [hγ (e⁻¹ (γ x)), map_add, map_smul, hinvapp, hB_inv]
      _ = x + B x v • v + B x (e v) • e v := by rw [hBy, hγ x]
  have hgg : ∀ x, g (g x) = x := by
    intro x
    have hB1 : B (g x) v = B x v := by
      rw [hg x]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvv,
        hev, mul_zero, add_zero]
    have hB2 : B (g x) (e v) = B x (e v) := by
      rw [hg x]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvc,
        hcc, mul_zero, add_zero]
    rw [hg (g x), hB1, hB2, hg x]
    calc x + B x v • v + B x (e v) • e v + B x v • v + B x (e v) • e v
        = x + ((B x v • v + B x v • v) + (B x (e v) • e v + B x (e v) • e v)) := by abel
      _ = x := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
  refine ⟨?_, ?_⟩
  · rw [pow_two]
    exact LinearEquiv.ext fun x => hgg x
  · have hc0 : e v ≠ 0 := fun h => hv (e.injective (h.trans (map_zero e).symm))
    obtain ⟨x₁, hx₁c, hx₁v⟩ : ∃ x₁, B x₁ (e v) = 0 ∧ B x₁ v = 1 := by
      by_contra hcon
      rcases eq_zero_or_eq_of_perp hB hc0 (z := v) (fun w hw => by
        rcases zmod2_cases (B w v) with h0 | h1
        · exact h0
        · exact absurd ⟨w, hw, h1⟩ hcon) with h | h
      · exact hv h
      · exact hne h.symm
    intro hg1
    have h := hg x₁
    rw [hg1, hx₁c, hx₁v, zero_smul, one_smul, add_zero] at h
    exact hv (by simpa using (show x₁ = x₁ + v from h).symm)

private theorem not_six_pairwise [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : IsSymplectic B) (hd : Module.finrank (ZMod 2) V = 4) (w : Fin 6 → V)
    (hw : ∀ i j, i ≠ j → B (w i) (w j) = 1) : False := by
  have hfin : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hBw : ∀ i j, B (w i) (w j) = if i = j then 0 else 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [hB.1]
    · simp [hij, hw i j hij]
  have hli : LinearIndependent (ZMod 2) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∀ j, ∑ k, g k * B (w k) (w j) = 0 := by
      intro j
      have := congrArg (fun u => B u (w j)) hg
      simpa [map_sum, LinearMap.sum_apply] using this
    have e0 := key 0
    have e1 := key 1
    have e2 := key 2
    have e3 := key 3
    have e4 := key 4
    have e5 := key 5
    simp only [hBw, Fin.sum_univ_six] at e0 e1 e2 e3 e4 e5
    intro i
    revert e0 e1 e2 e3 e4 e5
    fin_cases i
    all_goals
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      generalize g 0 = a0
      generalize g 1 = a1
      generalize g 2 = a2
      generalize g 3 = a3
      generalize g 4 = a4
      generalize g 5 = a5
      revert a0 a1 a2 a3 a4 a5
      decide
  have := hli.fintype_card_le_finrank
  simp [hd] at this

theorem fixedPointFree_of_card_nine [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : IsSymplectic B) (hd : Module.finrank (ZMod 2) V = 4) {E : Subgroup (GLV V)}
    (hE : E ≤ spSub B) (h9 : Nat.card E = 9) : ∀ x : V, (∀ e ∈ E, e x = x) → x = 0 := by
  intro c hc
  by_contra hc0
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hnd := G11.P4InspSp.p4inspsp_nondeg hB
  have htrans : ∀ u : V, u ≠ 0 → ∃ g : ↥(spSub B), g • c = u := by
    intro u hu
    obtain ⟨f, hf⟩ := exists_B_eq_one hB hc0
    obtain ⟨f', hf'⟩ := exists_B_eq_one hB hu
    obtain ⟨g, hg, hgc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_isometry_apply_pair (B := B)
        hB.1 hnd hf hf'
    exact ⟨⟨g, TauCeti.BilinForm.mem_isometryGroup_iff.1 hg⟩, hgc⟩
  have horb : MulAction.orbit ↥(spSub B) c = {u : V | u ≠ 0} := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      exact hc0 ((g : GLV V).injective (h.trans (map_zero _).symm))
    · exact htrans u
  have hV : Nat.card V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
    norm_num
  have hcardorb : Nat.card ↥(MulAction.orbit ↥(spSub B) c) = 15 := by
    rw [horb]
    show Nat.card {u : V // u ≠ 0} = 15
    classical
    have := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hV]
  have hstab : Nat.card ↥(MulAction.stabilizer ↥(spSub B) c) = 48 := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(spSub B) c)
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hcardorb,
      G11.P4InspSp.p4inspsp_card_spSub_four hB hd] at h1
    omega
  have hEle : E.subgroupOf (spSub B) ≤ MulAction.stabilizer ↥(spSub B) c := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    exact hc g.1 (Subgroup.mem_subgroupOf.1 hg)
  have h1 := Subgroup.card_dvd_of_le hEle
  rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, h9] at h1
  omega

private theorem commute_of_orderOf_five {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    {x : G} (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) (h9 : Nat.card E = 9) (hx : orderOf x = 5) :
    ∀ e ∈ E, x * e = e * x := by
  classical
  have : Fintype ↥E := Fintype.ofFinite _
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  let f : Function.End ↥E := fun e => ⟨x * e * x⁻¹, hxE e e.2⟩
  have hfn : ∀ n : ℕ, ∀ e : ↥E, ((f ^ n) e : G) = x ^ n * e * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro e
      simp only [pow_zero, inv_one, one_mul, mul_one]
      rfl
    | succ n ih =>
      intro e
      rw [pow_succ']
      show x * ((f ^ n) e : G) * x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext e
    apply Subtype.ext
    rw [hfn, pow_one, hx5]
    simp only [inv_one, one_mul, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf
  have hcard : Fintype.card ↑(Function.fixedPoints f) =
      Nat.card ↥(E ⊓ Subgroup.centralizer {x}) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1, p.1.2, ?_⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩
        left_inv := fun p => rfl
        right_inv := fun c => rfl }
    · show (p.1 : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 : f p.1 = p.1 := p.2
      have h2 : h * (p.1 : G) * h⁻¹ = p.1 := congrArg Subtype.val h1
      calc h * (p.1 : G) = h * (p.1 : G) * h⁻¹ * h := by group
        _ = p.1 * h := by rw [h2]
    · apply Subtype.ext
      have h1 : (c : G) ∈ Subgroup.centralizer ({x} : Set G) := c.2.2
      rw [Subgroup.mem_centralizer_iff] at h1
      have h2 : x * (c.1 : G) = c.1 * x := h1 x rfl
      show x * (c.1 : G) * x⁻¹ = c.1
      rw [h2]
      group
  rw [hcard, ← Nat.card_eq_fintype_card, h9] at hmod
  have hC : E ⊓ Subgroup.centralizer {x} = E := by
    have hdvd : Nat.card ↥(E ⊓ Subgroup.centralizer {x}) ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ Subgroup.centralizer {x} ≤ E)
      rwa [h9] at this
    obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hle : E ⊓ Subgroup.centralizer {x} ≤ E := inf_le_left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h9]
    interval_cases i
    · exfalso
      rw [hCi] at hmod
      exact absurd hmod (by decide)
    · exfalso
      rw [hCi] at hmod
      exact absurd hmod (by decide)
    · omega
  intro e he
  have : e ∈ E ⊓ Subgroup.centralizer {x} := by rw [hC]; exact he
  have h1 : e ∈ Subgroup.centralizer ({x} : Set G) := this.2
  rw [Subgroup.mem_centralizer_iff] at h1
  exact h1 x rfl

theorem eq_one_of_fixes_perp [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : IsSymplectic B) (hd : Module.finrank (ZMod 2) V = 4) {Γ : Subgroup (GLV V)}
    (hΓ : Γ ≤ spSub B) {E : Subgroup (GLV V)} (hEΓ : E ≤ Γ)
    (hEn : ∀ γ ∈ Γ, ∀ e ∈ E, γ * e * γ⁻¹ ∈ E) (h9 : Nat.card E = 9)
    (hno : ∀ N : Subgroup (GLV V), N ≤ E → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      Nat.card N ≠ 3)
    {S : Subgroup (GLV V)} (hS : IsSylowTwoOf S Γ) {v : V} (hv : v ≠ 0)
    (hvS : ∀ s ∈ S, s v = v) :
    ∀ γ ∈ Γ, (∀ x : V, B x v = 0 → γ x = x) → γ = 1 := by
  intro γ hγΓ hfix
  by_contra hne
  have : Finite (GLV V) := G11.P4InspSp.p4inspsp_finite_glv
  have hEB : E ≤ spSub B := hEΓ.trans hΓ
  have hγ : ∀ x, γ x = x + B x v • v := eq_transvection hB (hΓ hγΓ) hv hfix hne
  have hR3 : ∀ e ∈ E, e v = v ∨ B (e v) v = 1 := by
    intro e he
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hev, hB1⟩ := hcon
    have hB0 : B (e v) v = 0 := by
      rcases zmod2_cases (B (e v) v) with h0 | h1
      · exact h0
      · exact absurd h1 hB1
    obtain ⟨hg2, hg1⟩ := comm_transvection hB hv hγ (hEB he) hB0 hev
    have hgE : e * γ * e⁻¹ * γ⁻¹ ∈ E := by
      have : e * γ * e⁻¹ * γ⁻¹ = e * (γ * e⁻¹ * γ⁻¹) := by group
      rw [this]
      exact E.mul_mem he (hEn γ hγΓ e⁻¹ (E.inv_mem he))
    have hg9 : (e * γ * e⁻¹ * γ⁻¹) ^ 9 = 1 := by
      have h := congrArg Subtype.val
        (pow_card_eq_one' (G := ↥E) (x := ⟨e * γ * e⁻¹ * γ⁻¹, hgE⟩))
      rw [h9] at h
      exact h
    apply hg1
    calc e * γ * e⁻¹ * γ⁻¹ = (e * γ * e⁻¹ * γ⁻¹) ^ 9 := by
          rw [show (9 : ℕ) = 2 * 4 + 1 from rfl, pow_succ, pow_mul, hg2, one_pow, one_mul]
      _ = 1 := hg9
  set A : Subgroup (GLV V) := E ⊓ MulAction.stabilizer (GLV V) v with hAdef
  have hAE : A ≤ E := inf_le_left
  have hAmem : ∀ a : GLV V, a ∈ A ↔ a ∈ E ∧ a v = v := fun a => by
    rw [hAdef, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    rfl
  have hAcard : Nat.card A = 3 := by
    have hdvd : Nat.card A ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le hAE
      rwa [h9] at this
    obtain ⟨i, hi, hAi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases i
    ·
      exfalso
      have hA1 : A = ⊥ := Subgroup.card_eq_one.1 (by simpa using hAi)
      have : Fintype ↥E := Fintype.ofFinite _
      obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 6) (β := ↥E)
        (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, h9]; norm_num)
      refine not_six_pairwise hB hd (fun i => (ι i : GLV V) v) (fun i j hij => ?_)
      set a : GLV V := (ι i : GLV V) with ha
      set b : GLV V := (ι j : GLV V) with hb
      have haE : a ∈ E := (ι i).2
      have hbE : b ∈ E := (ι j).2
      have hbaE : b⁻¹ * a ∈ E := E.mul_mem (E.inv_mem hbE) haE
      have hne' : (b⁻¹ * a) v ≠ v := by
        intro h
        have hmem : b⁻¹ * a ∈ A := (hAmem _).2 ⟨hbaE, h⟩
        rw [hA1, Subgroup.mem_bot, inv_mul_eq_one] at hmem
        exact hij (ι.injective (Subtype.ext hmem.symm))
      have hiso : ∀ x y, B (b⁻¹ x) (b⁻¹ y) = B x y := (spSub B).inv_mem (hEB hbE)
      have hbv : b⁻¹ (b v) = v := by
        have : (b⁻¹ * b) v = v := by rw [inv_mul_cancel]; rfl
        exact this
      have h1 : B (a v) (b v) = B ((b⁻¹ * a) v) v := by
        rw [← hiso (a v) (b v), hbv]
        rfl
      show B (a v) (b v) = 1
      rw [h1]
      rcases hR3 _ hbaE with h | h
      · exact absurd h hne'
      · exact h
    · simpa using hAi
    ·
      exfalso
      have hAE' : A = E := Subgroup.eq_of_le_of_card_ge hAE (by rw [h9]; omega)
      exact hv (fixedPointFree_of_card_nine hB hd hEB h9 v fun e he => by
        have : e ∈ A := by rw [hAE']; exact he
        exact ((hAmem e).1 this).2)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    have : IsMulCommutative E :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h9]; norm_num)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
  obtain ⟨hSΓ, hS2, hSidx⟩ := hS
  have hSA : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A := by
    intro s hs a ha
    rw [hAmem] at ha ⊢
    refine ⟨hEn s (hSΓ hs) a ha.1, ?_⟩
    have hsv : s⁻¹ v = v := by
      calc s⁻¹ v = s⁻¹ (s v) := by rw [hvS s hs]
        _ = v := LinearEquiv.symm_apply_apply s v
    show s (a (s⁻¹ v)) = v
    rw [hsv, ha.2, hvS s hs]
  have hmemN : ∀ g : GLV V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → (∀ a ∈ A, g⁻¹ * a * g ∈ A) →
      g ∈ Subgroup.normalizer (A : Set (GLV V)) := by
    intro g h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have h3 := h2 _ hh
    have h4 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rwa [h4] at h3
  set N : Subgroup (GLV V) := Γ ⊓ Subgroup.normalizer (A : Set (GLV V)) with hNdef
  have hNΓ : N ≤ Γ := inf_le_left
  have hEN : E ≤ N := by
    intro e he
    refine ⟨hEΓ he, hmemN e (fun a ha => ?_) (fun a ha => ?_)⟩
    · have hcom : e * a = a * e := hEcomm e he a (hAE ha)
      have : e * a * e⁻¹ = a := by rw [hcom]; group
      rw [this]
      exact ha
    · have hcom : e * a = a * e := hEcomm e he a (hAE ha)
      have : e⁻¹ * a * e = a := by
        calc e⁻¹ * a * e = e⁻¹ * (a * e) := by group
          _ = a := by rw [← hcom]; group
      rw [this]
      exact ha
  have hSN : S ≤ N := fun s hs =>
    ⟨hSΓ hs, hmemN s (hSA s hs) (fun a ha => by simpa using hSA s⁻¹ (S.inv_mem hs) a ha)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
  have hnΓ : Nat.card Γ = 2 ^ k * (S.subgroupOf Γ).index := by
    rw [← hk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv,
      Subgroup.card_mul_index]
  have hn720 : Nat.card Γ ∣ 720 := by
    have := Subgroup.card_dvd_of_le hΓ
    rwa [G11.P4InspSp.p4inspsp_card_spSub_four hB hd] at this
  have h9n : 9 ∣ Nat.card Γ := by
    have := Subgroup.card_dvd_of_le hEΓ
    rwa [h9] at this
  set m := (S.subgroupOf Γ).index with hmdef
  have hm45 : m ∣ 45 := by
    have h1 : m ∣ 720 := (Dvd.intro_left _ hnΓ.symm).trans hn720
    have hcop : Nat.Coprime m 16 := by
      have : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hSidx
      exact (Nat.Coprime.pow_left 4 this).symm
    exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
  have h9m : 9 ∣ m := by
    have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    rw [hnΓ] at h9n
    exact hcop.dvd_of_dvd_mul_left h9n
  have hm : m = 9 ∨ m = 45 := by
    obtain ⟨t, ht⟩ := h9m
    rw [ht] at hm45
    have ht5 : t ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using hm45)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 ht5 with h | h
    · left; rw [ht, h]
    · right; rw [ht, h]
  have h2N : 2 ^ k ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hSN
    rwa [hk] at this
  have h9N : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hEN
    rwa [h9] at this
  have hnN : Nat.card Γ ∣ Nat.card N := by
    have hc29 : Nat.Coprime (2 ^ k) 9 := Nat.Coprime.pow_left k (by norm_num)
    rcases hm with hm | hm
    · rw [hnΓ, hm]
      exact hc29.mul_dvd_of_dvd_of_dvd h2N h9N
    · have h5 : 5 ∣ Nat.card Γ := by
        rw [hnΓ, hm]
        exact Dvd.dvd.mul_left (by norm_num) _
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
      have hxo : orderOf (x : GLV V) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
      have hxcomm := commute_of_orderOf_five (E := E) (x := (x : GLV V))
        (fun e he => hEn x x.2 e he) h9 hxo
      have hxN : (x : GLV V) ∈ N := by
        refine ⟨x.2, hmemN _ (fun a ha => ?_) (fun a ha => ?_)⟩
        · have hcom : (x : GLV V) * a = a * x := hxcomm a (hAE ha)
          have : (x : GLV V) * a * (x : GLV V)⁻¹ = a := by rw [hcom]; group
          rw [this]
          exact ha
        · have hcom : (x : GLV V) * a = a * x := hxcomm a (hAE ha)
          have : (x : GLV V)⁻¹ * a * (x : GLV V) = a := by
            calc (x : GLV V)⁻¹ * a * (x : GLV V) = (x : GLV V)⁻¹ * (a * x) := by group
              _ = a := by rw [← hcom]; group
          rw [this]
          exact ha
      have h5N : 5 ∣ Nat.card N := by
        have := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).2 hxN)
        rwa [Nat.card_zpowers, hxo] at this
      have hc5 : Nat.Coprime (2 ^ k * 9) 5 :=
        Nat.Coprime.mul_left (Nat.Coprime.pow_left k (by norm_num)) (by norm_num)
      have hnΓ' : Nat.card Γ = 2 ^ k * 9 * 5 := by rw [hnΓ, hm]; ring
      rw [hnΓ']
      exact hc5.mul_dvd_of_dvd_of_dvd (hc29.mul_dvd_of_dvd_of_dvd h2N h9N) h5N
  have hNeq : N = Γ := Subgroup.eq_of_le_of_card_ge hNΓ (Nat.le_of_dvd Nat.card_pos hnN)
  refine hno A hAE (fun g hg n hn => ?_) hAcard
  have hgN : g ∈ N := by rw [hNeq]; exact hg
  exact (Subgroup.mem_normalizer_iff.1 hgN.2 n).1 hn

end S143W

end CFSG.Quasithin
