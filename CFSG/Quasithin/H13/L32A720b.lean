module

public import CFSG.Quasithin.H13.L32A712
public import CFSG.Quasithin.H13.L32A714b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A
open scoped commutatorElement

section Lattice

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_subgroup {P : Subgroup G → Prop} (h : ∃ Y, P Y) :
    ∃ Y, P Y ∧ ∀ Y', P Y' → Y' ≤ Y → Y' = Y := by
  classical
  have hex : ∃ n, ∃ Y, P Y ∧ Nat.card Y = n := by
    obtain ⟨Y, hY⟩ := h
    exact ⟨_, Y, hY, rfl⟩
  obtain ⟨Y, hY, hYn⟩ := Nat.find_spec hex
  refine ⟨Y, hY, fun Y' hY' hle => ?_⟩
  by_contra hne
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
  have := Nat.find_min' hex ⟨Y', hY', rfl⟩
  omega

theorem exists_maximal_subgroup {P : Subgroup G → Prop} (h : ∃ Y, P Y) :
    ∃ Y, P Y ∧ ∀ Y', P Y' → Y ≤ Y' → Y' = Y := by
  classical
  have hex : ∃ n, ∃ Y, P Y ∧ Nat.card G - Nat.card Y = n := by
    obtain ⟨Y, hY⟩ := h
    exact ⟨_, Y, hY, rfl⟩
  obtain ⟨Y, hY, hYn⟩ := Nat.find_spec hex
  refine ⟨Y, hY, fun Y' hY' hle => ?_⟩
  by_contra hne
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
  have hle' := Subgroup.card_le_card_group Y'
  have := Nat.find_min' hex ⟨Y', hY', rfl⟩
  omega

end Lattice

section Coprime

variable {G : Type} [Group G]

theorem exists_pow_mul_eq {N : Subgroup G} {a δ : G} (ha : a ∈ Subgroup.normalizer (N : Set G))
    (hδ : δ ∈ N) (n : ℕ) : ∃ ν ∈ N, (a * δ) ^ n = a ^ n * ν := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨ν, hν, e⟩ := ih
    refine ⟨a⁻¹ * ν * a * δ, ?_, ?_⟩
    · have h1 : a⁻¹ * ν * a ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) ν).mp hν
        simpa using this
      exact N.mul_mem h1 hδ
    · rw [pow_succ, e, pow_succ]
      group

theorem mem_of_pow_odd_mem {N : Subgroup G} {a : G} {m : ℕ} (hm : Odd m) (ham : a ^ m ∈ N)
    {e : ℕ} (hae : a ^ 2 ^ e ∈ N) : a ∈ N := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simpa using hae
  have hcop : Nat.Coprime m (2 ^ e) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨k, rfl⟩ := hm
    omega
  have h1 : 1 < 2 ^ e := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp he)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  obtain ⟨q, hq⟩ : ∃ q, m * u = 1 + 2 ^ e * q :=
    ⟨m * u / 2 ^ e, by have := Nat.div_add_mod (m * u) (2 ^ e); omega⟩
  have e4 : (a ^ m) ^ u = a * (a ^ 2 ^ e) ^ q := by
    rw [← pow_mul, ← pow_mul, hq, pow_add, pow_one]
  have e5 : a = (a ^ m) ^ u * ((a ^ 2 ^ e) ^ q)⁻¹ := by
    rw [e4]
    group
  rw [e5]
  exact N.mul_mem (N.pow_mem ham _) (N.inv_mem (N.pow_mem hae _))

theorem conj_mem_of_odd {N A₀ A : Subgroup G} {h : G} {m : ℕ} (hm : Odd m) (hhm : h ^ m = 1)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hhN : h ∈ Subgroup.normalizer (N : Set G))
    (hA₀A : A₀ ≤ A) (h2e : ∀ a ∈ A₀, ∃ e : ℕ, a ^ 2 ^ e ∈ N)
    (h1 : ∀ x ∈ A, x⁻¹ * (h * x * h⁻¹) ∈ A₀) (h2 : ∀ a ∈ A₀, a⁻¹ * (h * a * h⁻¹) ∈ N) :
    ∀ x ∈ A, x⁻¹ * (h * x * h⁻¹) ∈ N := by
  intro x hx
  set a := x⁻¹ * (h * x * h⁻¹) with ha
  have haA₀ : a ∈ A₀ := h1 x hx
  have haN : a ∈ Subgroup.normalizer (N : Set G) := hAN (hA₀A haA₀)
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ ∈ N, h * a * h⁻¹ = a * δ :=
    ⟨a⁻¹ * (h * a * h⁻¹), h2 a haA₀, by group⟩
  have hx' : h * x * h⁻¹ = x * a := by rw [ha]; group
  have key : ∀ n : ℕ, ∃ ν ∈ N, h ^ n * x * (h ^ n)⁻¹ = x * a ^ n * ν := by
    intro n
    induction n with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨ν, hν, e⟩ := ih
      obtain ⟨ν', hν', e'⟩ := exists_pow_mul_eq haN hδ n
      have hhν : h * ν * h⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hhN ν).mp hν
      refine ⟨ν' * (h * ν * h⁻¹), N.mul_mem hν' hhν, ?_⟩
      calc h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ = h * (h ^ n * x * (h ^ n)⁻¹) * h⁻¹ := by
            rw [pow_succ']
            group
        _ = h * (x * a ^ n * ν) * h⁻¹ := by rw [e]
        _ = (h * x * h⁻¹) * (h * a * h⁻¹) ^ n * (h * ν * h⁻¹) := by
            rw [conj_pow]
            group
        _ = (x * a) * (a * δ) ^ n * (h * ν * h⁻¹) := by rw [hx', hδe]
        _ = (x * a) * (a ^ n * ν') * (h * ν * h⁻¹) := by rw [e']
        _ = x * a ^ (n + 1) * (ν' * (h * ν * h⁻¹)) := by
            rw [pow_succ']
            group
  obtain ⟨ν, hν, e⟩ := key m
  rw [hhm] at e
  have ham : a ^ m ∈ N := by
    have e2 : a ^ m = ν⁻¹ := by
      have e3 : x = x * a ^ m * ν := by simpa using e
      calc a ^ m = x⁻¹ * (x * a ^ m * ν) * ν⁻¹ := by group
        _ = x⁻¹ * x * ν⁻¹ := by rw [← e3]
        _ = ν⁻¹ := by group
    rw [e2]
    exact N.inv_mem hν
  obtain ⟨k, hk⟩ := h2e a haA₀
  exact mem_of_pow_odd_mem hm ham hk

theorem forall_conj_mem_of_closure {Y N : Subgroup G} {S : Set G}
    (hY : Subgroup.closure S ≤ Subgroup.normalizer (Y : Set G))
    (hN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G))
    (hS : ∀ s ∈ S, ∀ y ∈ Y, y⁻¹ * (s * y * s⁻¹) ∈ N) :
    ∀ k ∈ Subgroup.closure S, ∀ y ∈ Y, y⁻¹ * (k * y * k⁻¹) ∈ N := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => intro y _; simp
  | mul k₁ k₂ hk₁ hk₂ ih₁ ih₂ =>
    intro y hy
    have hy₂ : k₂ * y * k₂⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hY hk₂) y).mp hy
    have hn₂ := ih₂ y hy
    have hn₁ := ih₁ y hy
    have hn₂' : k₁ * (y⁻¹ * (k₂ * y * k₂⁻¹)) * k₁⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hN hk₁) _).mp hn₂
    have e : y⁻¹ * (k₁ * k₂ * y * (k₁ * k₂)⁻¹) =
        (y⁻¹ * (k₁ * y * k₁⁻¹)) * (k₁ * (y⁻¹ * (k₂ * y * k₂⁻¹)) * k₁⁻¹) := by group
    rw [e]
    exact N.mul_mem hn₁ hn₂'
  | inv k hk ih =>
    intro y hy
    have hy' : k⁻¹ * y * k⁻¹⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hY (inv_mem hk)) y).mp hy
    have h1 := ih _ hy'
    have e : y⁻¹ * (k⁻¹ * y * k⁻¹⁻¹) = ((k⁻¹ * y * k⁻¹⁻¹)⁻¹ * (k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹))⁻¹ := by
      group
    rw [e]
    exact N.inv_mem h1

end Coprime

section Chief

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_frattiniOf {Y : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    {x : G} (hx : x ∈ frattiniOf Y) : g * x * g⁻¹ ∈ frattiniOf Y := by
  obtain ⟨f, hf, rfl⟩ := hx
  set φ := Y.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have h1 : φ f ∈ frattini ↥Y := by
    have hc := (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini ↥Y).Characteristic)) φ
    rw [← hc]
    exact ⟨f, hf, rfl⟩
  refine ⟨φ f, h1, ?_⟩
  simp [hφ]

omit [Finite G] in
theorem le_normalizer_frattiniOf {H Y : Subgroup G} (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    H ≤ Subgroup.normalizer (frattiniOf Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_frattiniOf (hHY hg), fun h => ?_⟩
  have := conj_mem_frattiniOf (Subgroup.inv_mem _ (hHY hg)) h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem isElemSection_frattiniOf {Y N : Subgroup G} (hY2 : IsPGroup 2 ↥Y) (hNY : N ≤ Y) :
    IsElemSection Y (N ⊔ frattiniOf Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥Y) := ⟨hY2⟩
  refine ⟨sup_le hNY (Subgroup.map_subtype_le _), fun x hx x' hx' => ⟨?_, ?_⟩⟩
  · have h1 : ⁅(⟨x, hx⟩ : ↥Y), (⟨x', hx'⟩ : ↥Y)⁆ ∈ frattini ↥Y :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    refine Subgroup.mem_sup_right ⟨_, h1, ?_⟩
    rw [map_commutatorElement, commutatorElement_def]
    rfl
  · refine Subgroup.mem_sup_right ⟨(⟨x, hx⟩ : ↥Y) ^ 2,
      CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥Y) (p := 2) (⟨x, hx⟩ : ↥Y), ?_⟩
    rw [map_pow]
    rfl

theorem sup_frattiniOf_lt {Y N : Subgroup G} (hNY : N < Y) : N ⊔ frattiniOf Y < Y := by
  refine lt_of_le_of_ne (sup_le hNY.le (Subgroup.map_subtype_le _)) fun he => ?_
  have h1 : N.subgroupOf Y ⊔ frattini ↥Y = ⊤ := by
    have h2 : (N ⊔ frattiniOf Y).subgroupOf Y = ⊤ := by
      rw [he]
      exact Subgroup.subgroupOf_self Y
    rw [Subgroup.subgroupOf_sup hNY.le (show frattiniOf Y ≤ Y from Subgroup.map_subtype_le _)] at h2
    have h3 : (frattiniOf Y).subgroupOf Y = frattini ↥Y := map_subtype_subgroupOf' (frattini ↥Y)
    rwa [h3] at h2
  have h4 := frattini_nongenerating h1
  apply hNY.ne
  refine le_antisymm hNY.le fun y hy => ?_
  have : (⟨y, hy⟩ : ↥Y) ∈ N.subgroupOf Y := h4 ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem mem_normalizer_sup_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← conjSub_eq_self_iff, Quasithin.conjSub, Subgroup.map_sup]
  change Quasithin.conjSub g A ⊔ Quasithin.conjSub g B = _
  rw [conjSub_eq_self_iff.mpr hA, conjSub_eq_self_iff.mpr hB]

theorem exists_chief {H U Y : Subgroup G} (hUY : U < Y) (hY2 : IsPGroup 2 ↥Y)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hHU : H ≤ Subgroup.normalizer (U : Set G)) :
    ∃ Y₀ : Subgroup G, U ≤ Y₀ ∧ Y₀ < Y ∧ H ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      IsElemSection Y Y₀ ∧
      ∀ X : Subgroup G, Y₀ ≤ X → X ≤ Y → H ≤ Subgroup.normalizer (X : Set G) → X = Y₀ ∨ X = Y := by
  have hne : ∃ Z : Subgroup G, U ≤ Z ∧ Z < Y ∧ H ≤ Subgroup.normalizer (Z : Set G) ∧
      IsElemSection Y Z := by
    refine ⟨U ⊔ frattiniOf Y, le_sup_left, sup_frattiniOf_lt hUY, fun g hg => ?_,
      isElemSection_frattiniOf hY2 hUY.le⟩
    exact mem_normalizer_sup_of (hHU hg) (le_normalizer_frattiniOf hHY hg)
  obtain ⟨Y₀, ⟨hUY₀, hY₀Y, hHY₀, hsec⟩, hmax⟩ := exists_maximal_subgroup hne
  refine ⟨Y₀, hUY₀, hY₀Y, hHY₀, hsec, fun X hY₀X hXY hHX => ?_⟩
  by_cases hXe : X = Y
  · exact Or.inr hXe
  left
  have hXsec : IsElemSection Y X := ⟨hXY, fun x hx x' hx' =>
    ⟨hY₀X (hsec.2 x hx x' hx').1, hY₀X (hsec.2 x hx x' hx').2⟩⟩
  exact hmax X ⟨hUY₀.trans hY₀X, lt_of_le_of_ne hXY hXe, hHX, hXsec⟩ hY₀X

end Chief

namespace HeisMod

variable {W : Type} [CommGroup W]

theorem fix_of_comm_inv (hW2 : ∀ w : W, w * w = 1) {g z T : MulAut W} (hgz : g * z = z * g)
    (hz3 : z ^ 3 = 1) (hT2 : T * T = 1) (hTz : T * z * T = z⁻¹) (hTg : T * g * T = g⁻¹)
    (hfix : ∀ w : W, g w = w → z (w * T w) = w * T w) : ∀ w : W, g w = w → z w = w := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  have eT : ∀ w, T (T w) = w := fun w => by rw [← MulAut.mul_apply, hT2, MulAut.one_apply]
  have ez3 : ∀ w, z (z (z w)) = w := fun w => by
    have := DFunLike.congr_fun hz3 w
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply] at this
  have ezi : ∀ v, z⁻¹ v = z (z v) := fun v => by
    rw [← ez3 (z⁻¹ v), MulAut.apply_inv_self]
  have eTz : ∀ w, T (z w) = z (z (T w)) := fun w => by
    have h1 := DFunLike.congr_fun hTz (T w)
    rw [MulAut.mul_apply, MulAut.mul_apply, eT] at h1
    rw [h1, ezi]
  have ezT : ∀ w, z (T w) = T (z (z w)) := fun w => by
    have h1 := eTz (z (z w))
    rw [ez3] at h1
    rw [h1, ez3]
  have egz : ∀ w, g (z w) = z (g w) := fun w => comm_apply hgz w
  have eTg : ∀ u, g u = u → g (T u) = T u := fun u hu => by
    have h1 := DFunLike.congr_fun hTg u
    rw [MulAut.mul_apply, MulAut.mul_apply] at h1
    have hgi : g⁻¹ u = u := by
      calc g⁻¹ u = g⁻¹ (g u) := by rw [hu]
        _ = u := MulAut.inv_apply_self _ g u
    have h2 := congrArg T h1
    rw [eT, hgi] at h2
    exact h2
  have hD1 : ∀ u, g u = u → z (u * z u) = u * z u → u * z u = 1 := by
    intro u _ h
    rw [map_mul] at h
    have h1 : z (z u) = u := by
      have h2 : z u * z (z u) = z u * u := h.trans (mul_comm _ _)
      exact mul_left_cancel h2
    have h3 : u = z u := by
      have := congrArg z h1
      rwa [ez3] at this
    rw [← h3]
    exact hW2 u
  have hDT : ∀ u, g u = u → ∃ u', g u' = u' ∧ T (u * z u) = u' * z u' := by
    intro u hu
    refine ⟨z (z (T u)), ?_, ?_⟩
    · rw [egz, egz, eTg u hu]
    · rw [map_mul, eTz, ez3]
      exact mul_comm _ _
  have hDmul : ∀ u u', g u = u → g u' = u' →
      ∃ u'', g u'' = u'' ∧ (u * z u) * (u' * z u') = u'' * z u'' := by
    intro u u' hu hu'
    refine ⟨u * u', by rw [map_mul, hu, hu'], ?_⟩
    rw [map_mul]
    ac_rfl
  have hDTfix : ∀ u, g u = u → T (u * z u) = u * z u := by
    intro u hu
    obtain ⟨u', hu', e⟩ := hDT u hu
    obtain ⟨u'', hu'', e'⟩ := hDmul u u' hu hu'
    have hgv : g (u * z u) = u * z u := by rw [map_mul, egz, hu]
    have h2 := hfix (u * z u) hgv
    rw [e, e'] at h2
    have h3 := hD1 u'' hu'' h2
    rw [← e', ← e] at h3
    calc T (u * z u) = (u * z u)⁻¹ := eq_inv_of_mul_eq_one_right h3
      _ = u * z u := hinv _
  intro w hw
  have hzD : z (w * z w) = w * z w := by
    have hzw : g (z w) = z w := by rw [egz, hw]
    have hzzw : g (z (z w)) = z (z w) := by rw [egz, hzw]
    have e1 : z (z (w * z w)) = z (z w) * z (z (z w)) := by rw [map_mul, map_mul]
    have h2 : z (w * z w) = z (z (w * z w)) := by
      calc z (w * z w) = z (T (w * z w)) := by rw [hDTfix w hw]
        _ = T (z (z (w * z w))) := ezT _
        _ = T (z (z w) * z (z (z w))) := by rw [e1]
        _ = z (z w) * z (z (z w)) := hDTfix _ hzzw
        _ = z (z (w * z w)) := e1.symm
    exact (z.injective h2).symm
  have h1 := hD1 w hw hzD
  calc z w = w⁻¹ := eq_inv_of_mul_eq_one_right h1
    _ = w := hinv w

theorem eq_one_of_lines (hW2 : ∀ w : W, w * w = 1) {A B : MulAut W} (hA3 : A ^ 3 = 1)
    (hB3 : B ^ 3 = 1) (hAB : A * B = B * A)
    (hl : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) →
      ∀ w : W, g w = w → A w = w ∧ B w = w) :
    ∀ w : W, A w = w ∧ B w = w := by
  have cube : ∀ g : MulAut W, g ^ 3 = 1 → ∀ v, g (g (g v)) = v := fun g hg v => by
    have := DFunLike.congr_fun hg v
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply] at this
  have hc : Commute A B := hAB
  have hAB3 : (A * B) ^ 3 = 1 := by rw [hc.mul_pow, hA3, hB3, one_mul]
  have hABB3 : (A * B * B) ^ 3 = 1 := by
    rw [mul_assoc, (hc.mul_right hc).mul_pow, hA3, ← sq, ← pow_mul, mul_comm, pow_mul, hB3,
      one_pow, one_mul]
  have eA3 := cube A hA3
  have eB3 := cube B hB3
  have eAB : ∀ v, A (B v) = B (A v) := fun v => comm_apply hAB v
  have hfixN : ∀ g : MulAut W, g ^ 3 = 1 → ∀ v, g (v * g v * g (g v)) = v * g v * g (g v) := by
    intro g hg v
    rw [map_mul, map_mul, cube g hg]
    ac_rfl
  have hN : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) → g ^ 3 = 1 := by
    rintro g (rfl | rfl | rfl | rfl)
    · exact hA3
    · exact hB3
    · exact hAB3
    · exact hABB3
  have hlN : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) → ∀ v,
      A (v * g v * g (g v)) = v * g v * g (g v) ∧ B (v * g v * g (g v)) = v * g v * g (g v) :=
    fun g hg v => hl g hg _ (hfixN g (hN g hg) v)
  intro w
  set v₀ := w * B w * B (B w) with hv₀
  have hBv₀ : B v₀ = v₀ := hfixN B hB3 w
  have hAE : A (v₀ * A v₀ * A (A v₀)) = v₀ * A v₀ * A (A v₀) := hfixN A hA3 v₀
  have hBE : B (v₀ * A v₀ * A (A v₀)) = v₀ * A v₀ * A (A v₀) := by
    rw [map_mul, map_mul, ← eAB, ← eAB, ← eAB, hBv₀]
  have r3 : (A * B) ((A * B) w) = A (A (B (B w))) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ← eAB (B w)]
  have r4 : (A * B * B) ((A * B * B) w) = A (A (B w)) := by
    simp only [MulAut.mul_apply]
    rw [← eAB (B (B w)), ← eAB (B (B (B w))), eB3 (B w)]
  have hid : v₀ * A v₀ * A (A v₀) =
      w * ((w * A w * A (A w)) * (w * B w * B (B w)) * (w * (A * B) w * (A * B) ((A * B) w)) *
        (w * (A * B * B) w * (A * B * B) ((A * B * B) w))) := by
    rw [r3, r4]
    simp only [hv₀, MulAut.mul_apply, map_mul]
    calc w * B w * B (B w) * (A w * A (B w) * A (B (B w))) *
          (A (A w) * A (A (B w)) * A (A (B (B w))))
        = (w * w) * (w * w) * (w * B w * B (B w) * (A w * A (B w) * A (B (B w))) *
          (A (A w) * A (A (B w)) * A (A (B (B w))))) := by rw [hW2 w, one_mul, one_mul]
      _ = _ := by ac_rfl
  have hfixP : ∀ x y : W, A x = x ∧ B x = x → A y = y ∧ B y = y →
      A (x * y) = x * y ∧ B (x * y) = x * y := fun x y hx hy =>
    ⟨by rw [map_mul, hx.1, hy.1], by rw [map_mul, hx.2, hy.2]⟩
  have hfixI : ∀ x : W, A x = x ∧ B x = x → A x⁻¹ = x⁻¹ ∧ B x⁻¹ = x⁻¹ := fun x hx =>
    ⟨by rw [map_inv, hx.1], by rw [map_inv, hx.2]⟩
  have hprod := hfixP _ _ (hfixP _ _ (hfixP _ _ (hlN A (Or.inl rfl) w)
    (hlN B (Or.inr (Or.inl rfl)) w)) (hlN (A * B) (Or.inr (Or.inr (Or.inl rfl))) w))
    (hlN (A * B * B) (Or.inr (Or.inr (Or.inr rfl))) w)
  have hw : w = (v₀ * A v₀ * A (A v₀)) *
      ((w * A w * A (A w)) * (w * B w * B (B w)) * (w * (A * B) w * (A * B) ((A * B) w)) *
        (w * (A * B * B) w * (A * B * B) ((A * B * B) w)))⁻¹ := by
    rw [hid, mul_inv_cancel_right]
  rw [hw]
  exact hfixP _ _ ⟨hAE, hBE⟩ (hfixI _ hprod)

theorem eq_one_of_fix_commV (hW2 : ∀ w : W, w * w = 1) {A B T Y : MulAut W} (hA3 : A ^ 3 = 1)
    (hB3 : B ^ 3 = 1) (hAB : A * B = B * A) (hT2 : T * T = 1) (hTA : T * A * T = A⁻¹)
    (hTB : T * B * T = B⁻¹) (hY : ∀ w : W, Y (w * T w) = w * T w)
    (hline : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) →
      ∀ w : W, g w = w → (Y * g * Y⁻¹) w = w → A w = w ∧ B w = w) :
    A = 1 ∧ B = 1 := by
  have hc : Commute A B := hAB
  have hTT : T⁻¹ = T := inv_eq_of_mul_eq_one_left hT2
  have hTmul : ∀ X Z : MulAut W, T * (X * Z) * T = (T * X * T) * (T * Z * T) := fun X Z => by
    calc T * (X * Z) * T = T * X * (T * T) * Z * T := by rw [hT2]; group
      _ = (T * X * T) * (T * Z * T) := by group
  have hBBA : A * B * B = B * B * A := by rw [hAB, mul_assoc, hAB, ← mul_assoc]
  have hTinv : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) → T * g * T = g⁻¹ := by
    rintro g (rfl | rfl | rfl | rfl)
    · exact hTA
    · exact hTB
    · rw [hTmul, hTA, hTB, hAB]
      group
    · rw [hTmul, hTmul, hTA, hTB, hBBA]
      group
  have hgA : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) → g * A = A * g := by
    rintro g (rfl | rfl | rfl | rfl)
    · rfl
    · exact hAB.symm
    · exact ((Commute.refl A).mul_right hc).eq.symm
    · exact (((Commute.refl A).mul_right hc).mul_right hc).eq.symm
  have hgB : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) → g * B = B * g := by
    rintro g (rfl | rfl | rfl | rfl)
    · exact hAB
    · rfl
    · exact (hc.symm.mul_right (Commute.refl B)).eq.symm
    · exact ((hc.symm.mul_right (Commute.refl B)).mul_right (Commute.refl B)).eq.symm
  have hl : ∀ g : MulAut W, (g = A ∨ g = B ∨ g = A * B ∨ g = A * B * B) →
      ∀ w : W, g w = w → A w = w ∧ B w = w := by
    intro g hg
    have hfix : ∀ w : W, g w = w → A (w * T w) = w * T w ∧ B (w * T w) = w * T w := by
      intro w hw
      have hTg := hTinv g hg
      have hgT : g (T w) = T w := by
        have h1 := DFunLike.congr_fun hTg w
        rw [MulAut.mul_apply, MulAut.mul_apply] at h1
        have hgi : g⁻¹ w = w := by
          calc g⁻¹ w = g⁻¹ (g w) := by rw [hw]
            _ = w := MulAut.inv_apply_self _ g w
        have h2 := congrArg T h1
        rwa [← MulAut.mul_apply _ T T, hT2, MulAut.one_apply, hgi] at h2
      have hgv : g (w * T w) = w * T w := by rw [map_mul, hw, hgT]
      have hYv := hY w
      have hYi : Y⁻¹ (w * T w) = w * T w := by
        calc Y⁻¹ (w * T w) = Y⁻¹ (Y (w * T w)) := by rw [hYv]
          _ = w * T w := MulAut.inv_apply_self _ Y _
      refine hline g hg _ hgv ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, hYi, hgv, hYv]
    have hA := fix_of_comm_inv hW2 (hgA g hg) hA3 hT2 hTA (hTinv g hg) fun w hw => (hfix w hw).1
    have hB := fix_of_comm_inv hW2 (hgB g hg) hB3 hT2 hTB (hTinv g hg) fun w hw => (hfix w hw).2
    exact fun w hw => ⟨hA w hw, hB w hw⟩
  have h := eq_one_of_lines hW2 hA3 hB3 hAB hl
  exact ⟨MulEquiv.ext fun w => (h w).1, MulEquiv.ext fun w => (h w).2⟩

end HeisMod

end CFSG.Quasithin.H13.L32A
