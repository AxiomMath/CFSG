module

public import CFSG.Quasithin.H13.L32AHStr

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem card_modEq_card_inf_centralizer {p : ℕ} [Fact p.Prime] {y : G} (hy : y ^ p = 1)
    {D : Subgroup G} (hyD : y ∈ Subgroup.normalizer (D : Set G)) :
    Nat.card ↥D ≡ Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G)) [MOD p] := by
  classical
  have _ : Fintype ↥D := Fintype.ofFinite _
  let f : Function.End ↥D := fun d =>
    ⟨y * d * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyD d).mp d.2⟩
  have hfn : ∀ n : ℕ, ∀ d : ↥D, (((f ^ n) d : ↥D) : G) = y ^ n * d * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro d
      show (d : G) = y ^ 0 * d * (y ^ 0)⁻¹
      simp
    | succ n ih =>
      intro d
      rw [pow_succ]
      show (((f ^ n) (f d) : ↥D) : G) = _
      rw [ih]
      show y ^ n * (y * d * y⁻¹) * (y ^ n)⁻¹ = y ^ (n + 1) * d * (y ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  have hfp : f ^ p ^ 1 = 1 := by
    funext d
    apply Subtype.ext
    rw [pow_one, hfn, hy, one_mul, inv_one, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hfp
  have hfix : Fintype.card (Function.fixedPoints f) =
      Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun d => ⟨d.1.1, d.1.2, ?_⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.mp c.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have hd : y * d.1.1 * y⁻¹ = d.1.1 := congrArg Subtype.val d.2
      show (d.1.1 : G) ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d.1.1 * y = (y * d.1.1 * y⁻¹) * y := by rw [hd]
        _ = y * d.1.1 := by group
    · apply Subtype.ext
      show y * c.1 * y⁻¹ = c.1
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
      rw [← h1]
      group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem card_modEq_card_of_fix {p : ℕ} [Fact p.Prime] {y : G} (hy : y ^ p = 1)
    {D₁ D₂ : Subgroup G} (h12 : D₁ ≤ D₂) (hy1 : y ∈ Subgroup.normalizer (D₁ : Set G))
    (hy2 : y ∈ Subgroup.normalizer (D₂ : Set G))
    (hC : D₂ ⊓ Subgroup.centralizer ({y} : Set G) ≤ D₁) :
    Nat.card ↥D₂ ≡ Nat.card ↥D₁ [MOD p] := by
  have h1 := card_modEq_card_inf_centralizer hy hy1
  have h2 := card_modEq_card_inf_centralizer hy hy2
  have e : D₂ ⊓ Subgroup.centralizer ({y} : Set G) = D₁ ⊓ Subgroup.centralizer ({y} : Set G) :=
    le_antisymm (le_inf hC inf_le_right) (inf_le_inf_right _ h12)
  rw [e] at h2
  exact h2.trans h1.symm

theorem exists_mul_mem_centralizer {p : ℕ} [Fact p.Prime] {y : G} (hy : y ^ p = 1)
    {N : Subgroup G} (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hp : ¬ p ∣ Nat.card ↥N)
    {g : G} (hg : g⁻¹ * y * g * y⁻¹ ∈ N) :
    ∃ n ∈ N, g * n ∈ Subgroup.centralizer ({y} : Set G) := by
  classical
  have _ : Fintype ↥N := Fintype.ofFinite _
  let f : Function.End ↥N := fun n => ⟨g⁻¹ * y * g * n * y⁻¹, by
    rw [show g⁻¹ * y * g * (n : G) * y⁻¹ = (g⁻¹ * y * g * y⁻¹) * (y * n * y⁻¹) by group]
    exact mul_mem hg ((Subgroup.mem_normalizer_iff.mp hyN n).mp n.2)⟩
  have hfn : ∀ k : ℕ, ∀ n : ↥N,
      (((f ^ k) n : ↥N) : G) = g⁻¹ * y ^ k * g * n * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro n
      show (n : G) = g⁻¹ * y ^ 0 * g * n * (y ^ 0)⁻¹
      simp
    | succ k ih =>
      intro n
      rw [pow_succ]
      show (((f ^ k) (f n) : ↥N) : G) = _
      rw [ih]
      show g⁻¹ * y ^ k * g * (g⁻¹ * y * g * n * y⁻¹) * (y ^ k)⁻¹ =
        g⁻¹ * y ^ (k + 1) * g * n * (y ^ (k + 1))⁻¹
      rw [pow_succ]
      group
  have hfp : f ^ p ^ 1 = 1 := by
    funext n
    apply Subtype.ext
    rw [pow_one, hfn, hy]
    show g⁻¹ * 1 * g * n * 1⁻¹ = n
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hfp
  by_contra hne
  push Not at hne
  have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨n, hn⟩
    apply hne n n.2
    have h1 : g⁻¹ * y * g * (n : G) * y⁻¹ = n := congrArg Subtype.val hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (n : G) * y = g * (g⁻¹ * y * g * n * y⁻¹) * y := by rw [h1]
      _ = y * (g * n) := by group
  rw [h0, ← Nat.card_eq_fintype_card] at hmod
  exact hp (Nat.modEq_zero_iff_dvd.mp hmod)

theorem relIndex_inf_centralizer_eq {p : ℕ} [Fact p.Prime] {y : G} (hy : y ^ p = 1)
    {N P : Subgroup G} (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hp : ¬ p ∣ Nat.card ↥N)
    (hP : ∀ g ∈ P, g⁻¹ * y * g * y⁻¹ ∈ N) :
    (P ⊓ Subgroup.centralizer ({y} : Set G)).relIndex P =
      (N ⊓ Subgroup.centralizer ({y} : Set G)).relIndex N := by
  set C := P ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hPN
  have hsup : C ⊔ N = P := by
    refine le_antisymm (sup_le inf_le_left hNP) fun g hg => ?_
    obtain ⟨n, hn, hgn⟩ := exists_mul_mem_centralizer hy hyN hp (hP g hg)
    have hgnC : g * n ∈ C := Subgroup.mem_inf.mpr ⟨mul_mem hg (hNP hn), hgn⟩
    rw [show g = (g * n) * n⁻¹ by group]
    exact mul_mem (Subgroup.mem_sup_left hgnC) (Subgroup.mem_sup_right (inv_mem hn))
  have h1 := B6.relIndex_inf_eq_relIndex_sup hCN
  rw [hsup] at h1
  rw [← h1]
  congr 1
  ext x
  simp only [hC, Subgroup.mem_inf]
  exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h3, h2⟩ => ⟨⟨hNP h3, h2⟩, h3⟩⟩

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {g : G} {H : Subgroup G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

@[expose] def fixMod (s : G) (X U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ Subgroup.normalizer (U : Set G) ∧ s * x * s⁻¹ * x⁻¹ ∈ U}
  one_mem' := ⟨one_mem _, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haX, haN, ha⟩ ⟨hbX, hbN, hb⟩
    refine ⟨mul_mem haX hbX, mul_mem haN hbN, ?_⟩
    rw [show s * (a * b) * s⁻¹ * (a * b)⁻¹ =
      (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) by group]
    exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp haN _).mp hb)
  inv_mem' := by
    rintro a ⟨haX, haN, ha⟩
    refine ⟨inv_mem haX, inv_mem haN, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) _).mp (inv_mem ha)
    rwa [show a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ = s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ by group] at h

omit [Finite G] in
theorem mem_fixMod {s : G} {X U : Subgroup G} {x : G} :
    x ∈ fixMod s X U ↔ x ∈ X ∧ x ∈ Subgroup.normalizer (U : Set G) ∧ s * x * s⁻¹ * x⁻¹ ∈ U :=
  Iff.rfl

omit [Finite G] in
theorem fixMod_le (s : G) (X U : Subgroup G) : fixMod s X U ≤ X := fun _ hx => hx.1

omit [Finite G] in
theorem mem_fixMod_mul {s s' : G} {X U : Subgroup G} {x : G}
    (hs : s ∈ Subgroup.normalizer (U : Set G)) (hx : x ∈ fixMod s X U)
    (hx' : x ∈ fixMod s' X U) : x ∈ fixMod (s * s') X U := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  rw [show s * s' * x * (s * s')⁻¹ * x⁻¹ =
    s * (s' * x * s'⁻¹ * x⁻¹) * s⁻¹ * (s * x * s⁻¹ * x⁻¹) by group]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp hs _).mp hx'.2.2) hx.2.2

omit [Finite G] in
theorem mem_fixMod_pow {s : G} {X U : Subgroup G} {x : G}
    (hs : s ∈ Subgroup.normalizer (U : Set G)) (hx : x ∈ fixMod s X U) (n : ℕ) :
    x ∈ fixMod (s ^ n) X U := by
  induction n with
  | zero => exact ⟨hx.1, hx.2.1, by simp⟩
  | succ n ih =>
    rw [pow_succ']
    exact mem_fixMod_mul hs hx ih

omit [Finite G] in
theorem fixMod_conj {s k : G} {X U : Subgroup G} (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkU : k ∈ Subgroup.normalizer (U : Set G)) :
    fixMod (k * s * k⁻¹) X U = conjSub k (fixMod s X U) := by
  ext x
  rw [mem_conjSub, mem_fixMod, mem_fixMod]
  have hX : x ∈ X ↔ k⁻¹ * x * k ∈ X := by
    have := Subgroup.mem_normalizer_iff.mp (inv_mem hkX) x
    rwa [inv_inv] at this
  have hN : x ∈ Subgroup.normalizer (U : Set G) ↔
      k⁻¹ * x * k ∈ Subgroup.normalizer (U : Set G) := by
    constructor
    · intro h
      exact mul_mem (mul_mem (inv_mem hkU) h) hkU
    · intro h
      have := mul_mem (mul_mem hkU h) (inv_mem hkU)
      rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at this
  have hC : k * s * k⁻¹ * x * (k * s * k⁻¹)⁻¹ * x⁻¹ ∈ U ↔
      s * (k⁻¹ * x * k) * s⁻¹ * (k⁻¹ * x * k)⁻¹ ∈ U := by
    rw [show k * s * k⁻¹ * x * (k * s * k⁻¹)⁻¹ * x⁻¹ =
      k * (s * (k⁻¹ * x * k) * s⁻¹ * (k⁻¹ * x * k)⁻¹) * k⁻¹ by group]
    have := Subgroup.mem_normalizer_iff.mp hkU (s * (k⁻¹ * x * k) * s⁻¹ * (k⁻¹ * x * k)⁻¹)
    exact this.symm
  rw [hX, hN, hC]

theorem relIndex_fixMod_le_two {s : G} {X U D : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hD : ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ D)
    (hDU : (D ⊓ U).relIndex D ≤ 2) : (fixMod s X U).relIndex X ≤ 2 := by
  set F := fixMod s X U with hF
  have hFX : F ≤ X := fixMod_le s X U
  have hcard := Subgroup.relIndex_mul_card F X
  rw [inf_eq_left.mpr hFX] at hcard
  have hpos : 0 < Nat.card ↥F := Nat.card_pos
  by_cases hall : ∀ x ∈ X, x ∈ F
  · have : F.relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hall
    omega
  push Not at hall
  obtain ⟨x₁, hx₁X, hx₁F⟩ := hall
  have hd₁ : s * x₁ * s⁻¹ * x₁⁻¹ ∉ U := fun h => hx₁F ⟨hx₁X, hXU hx₁X, h⟩
  have hDU2 : Nat.card ↥D = 2 * Nat.card ↥(D ⊓ U) := by
    have h1 := Subgroup.relIndex_mul_card (D ⊓ U) D
    rw [inf_eq_left.mpr inf_le_left] at h1
    have hne : (D ⊓ U).relIndex D ≠ 1 := fun h => hd₁ (Subgroup.mem_inf.mp
      (Subgroup.relIndex_eq_one.mp h (hD x₁ hx₁X))).2
    have hne0 : (D ⊓ U).relIndex D ≠ 0 := by
      show ((D ⊓ U).subgroupOf D).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    have h2 : (D ⊓ U).relIndex D = 2 := by omega
    rw [h2] at h1
    exact h1.symm
  have hsub : (X : Set G) ⊆ (F : Set G) ∪ (fun y => x₁ * y) '' (F : Set G) := by
    intro x hx
    by_cases hxF : x ∈ F
    · exact Or.inl hxF
    right
    have hd : s * x * s⁻¹ * x⁻¹ ∉ U := fun h => hxF ⟨hx, hXU hx, h⟩
    have hm := L32NSet14.mul_mem_of_card_eq_two_mul inf_le_left hDU2
      (Nat.card_pos (α := ↥(D ⊓ U))).ne' (inv_mem (hD x₁ hx₁X)) (hD x hx)
      (fun h => hd₁ (inv_mem_iff.mp (Subgroup.mem_inf.mp h).2))
      (fun h => hd (Subgroup.mem_inf.mp h).2)
    have hmU := (Subgroup.mem_inf.mp hm).2
    refine ⟨x₁⁻¹ * x, ⟨mul_mem (inv_mem hx₁X) hx, mul_mem (inv_mem (hXU hx₁X)) (hXU hx), ?_⟩,
      by simp⟩
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem (hXU hx₁X)) _).mp hmU
    rwa [show x₁⁻¹ * ((s * x₁ * s⁻¹ * x₁⁻¹)⁻¹ * (s * x * s⁻¹ * x⁻¹)) * x₁⁻¹⁻¹ =
      s * (x₁⁻¹ * x) * s⁻¹ * (x₁⁻¹ * x)⁻¹ by group] at h
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hu := Set.ncard_union_le (F : Set G) ((fun y => x₁ * y) '' (F : Set G))
  have him : ((fun y => x₁ * y) '' (F : Set G)).ncard ≤ (F : Set G).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hXc : (X : Set G).ncard = Nat.card ↥X := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have hFc : (F : Set G).ncard = Nat.card ↥F := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have h3 : Nat.card ↥X ≤ 2 * Nat.card ↥F := by omega
  rw [← hcard] at h3
  have h4 : F.relIndex X * Nat.card ↥F ≤ 2 * Nat.card ↥F := h3
  exact Nat.le_of_mul_le_mul_right h4 hpos

theorem fixMod_eq_of_pow_five {s : G} (hs5 : s ^ 5 = 1) {X U : Subgroup G}
    (hsX : s ∈ Subgroup.normalizer (X : Set G)) (hsU : s ∈ Subgroup.normalizer (U : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (h5 : ¬ 5 ∣ Nat.card ↥X)
    (h4 : (fixMod s X U).relIndex X ≤ 4) : fixMod s X U = X := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set F := fixMod s X U with hF
  have hFX : F ≤ X := fixMod_le s X U
  have hconj : ∀ g : G, g ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer (U : Set G) → g * s * g⁻¹ = s → ∀ x ∈ F, g * x * g⁻¹ ∈ F := by
    intro g hgX hgU hgs x hx
    have h := fixMod_conj (s := s) hgX hgU
    rw [hgs] at h
    rw [hF, h]
    exact mul_mem_conjSub hx
  have hsF : s ∈ Subgroup.normalizer (F : Set G) :=
    mem_normalizer_of_conj_mem (hconj s hsX hsU (by group))
      (fun x hx => by
        have h := hconj s⁻¹ (inv_mem hsX) (inv_mem hsU) (by group) x hx
        rwa [inv_inv] at h)
  have hC : X ⊓ Subgroup.centralizer ({s} : Set G) ≤ F := by
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    refine ⟨hxX, hXU hxX, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    rw [show s * x * s⁻¹ * x⁻¹ = (s * x) * (x * s)⁻¹ by group, hxC, mul_inv_cancel]
    exact one_mem _
  have hp1 : ¬ 5 ∣ Nat.card ↥F := fun h => h5 (h.trans (Subgroup.card_dvd_of_le hFX))
  have hmod := card_modEq_card_of_fix hs5 hFX hsF hsX hC
  have hcard := Subgroup.relIndex_mul_card F X
  rw [inf_eq_left.mpr hFX] at hcard
  rw [← hcard] at hmod
  unfold Nat.ModEq at hmod
  have hF5 : Nat.card ↥F % 5 ≠ 0 := fun h => hp1 (Nat.dvd_of_mod_eq_zero h)
  have hne0 : F.relIndex X ≠ 0 := by
    show (F.subgroupOf X).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h1 : F.relIndex X = 1 := by
    interval_cases hr : F.relIndex X <;> omega
  exact le_antisymm hFX (Subgroup.relIndex_eq_one.mp h1)

omit [Finite G] in
theorem pow_mul_inv_pow_mem {N : Subgroup G} {q n : G} (hq : q ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) (j : ℕ) : (n * q) ^ j * (q ^ j)⁻¹ ∈ N := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show (n * q) ^ (j + 1) * (q ^ (j + 1))⁻¹ =
      ((n * q) ^ j * (q ^ j)⁻¹) * (q ^ j * n * (q ^ j)⁻¹) by rw [pow_succ, pow_succ]; group]
    exact mul_mem ih ((Subgroup.mem_normalizer_iff.mp (pow_mem hq j) n).mp hn)

theorem oTwoUpper_le_of_mem_perm5 {H N : Subgroup G} {φ : ↥H →* Equiv.Perm (Fin 5)}
    (hs : Function.Surjective φ) (hk : φ.ker = CFSG.Open.pCore 2 ↥H) (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {y : G} (hyN : y ∈ N)
    (hy5 : φ ⟨y, hNH hyN⟩ ^ 5 = 1) (hy1 : φ ⟨y, hNH hyN⟩ ≠ 1) : oTwoUpper H ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (N.subgroupOf H).map φ with hM
  have hNn : (N.subgroupOf H).Normal := ⟨fun n hn h => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN h h.2 n hn⟩
  have hMn : M.Normal := hNn.map φ hs
  have hyA : φ ⟨y, hNH hyN⟩ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : Equiv.Perm.sign (φ ⟨y, hNH hyN⟩) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φ ⟨y, hNH hyN⟩)) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hAM : alternatingGroup (Fin 5) ≤ M := by
    have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hMAn : (M.subgroupOf (alternatingGroup (Fin 5))).Normal := hMn.subgroupOf _
    rcases hMAn.eq_bot_or_eq_top with hb | ht
    · exfalso
      have hmem : (⟨_, hyA⟩ : ↥(alternatingGroup (Fin 5))) ∈
          M.subgroupOf (alternatingGroup (Fin 5)) :=
        Subgroup.mem_subgroupOf.mpr ⟨⟨y, hNH hyN⟩, Subgroup.mem_subgroupOf.mpr hyN, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact hy1 (congrArg Subtype.val hmem)
    · intro σ hσ
      have : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈
          M.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [ht]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx2 : φ (⟨x, hx⟩ ^ 2) ∈ M := by
    apply hAM
    rw [Equiv.Perm.mem_alternatingGroup, map_pow, map_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φ ⟨x, hx⟩)) with h | h <;> rw [h] <;> decide
  obtain ⟨n, hnN, hnx⟩ := hx2
  have hq : n⁻¹ * ⟨x, hx⟩ ^ 2 ∈ CFSG.Open.pCore 2 ↥H := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
  have hqQ : ((n⁻¹ * ⟨x, hx⟩ ^ 2 : ↥H) : G) ∈ pCoreOf 2 H := mem_pCoreOf_iff'.mpr hq
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hqQ⟩
  have hm' : ((n⁻¹ * ⟨x, hx⟩ ^ 2 : ↥H) : G) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  refine ⟨m + 1, ?_⟩
  have hqH := (n⁻¹ * ⟨x, hx⟩ ^ 2 : ↥H).2
  have hqN : ((n⁻¹ * ⟨x, hx⟩ ^ 2 : ↥H) : G) ∈ Subgroup.normalizer (N : Set G) :=
    mem_normalizer_of_conj_mem (hN _ hqH) (fun w hw => by
      have := hN _ (inv_mem hqH) w hw
      rwa [inv_inv] at this)
  have h1 := pow_mul_inv_pow_mem hqN (Subgroup.mem_subgroupOf.mp hnN) (2 ^ m)
  rw [hm', inv_one, mul_one] at h1
  have e : (n : G) * ((n⁻¹ * ⟨x, hx⟩ ^ 2 : ↥H) : G) = x ^ 2 := by simp
  rw [e, ← pow_mul, ← pow_succ'] at h1
  exact h1

end CFSG.Quasithin.H13.L32A
