module

public import CFSG.Quasithin.Background.A4
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.Sp4Z

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def cmap (g u : G) : G := g * u * g⁻¹ * u⁻¹

@[expose] def imC (U : Subgroup G) (g : G) : Subgroup G :=
  Subgroup.closure {x | ∃ u ∈ U, cmap g u = x}

theorem cmap_mem_imC {U : Subgroup G} {g u : G} (hu : u ∈ U) : cmap g u ∈ imC U g :=
  Subgroup.subset_closure ⟨u, hu, rfl⟩

section Abelian

variable {U : Subgroup G} (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
include hU

omit hU in
theorem conj_mem {g u : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (hu : u ∈ U) :
    g * u * g⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.1 hg u).1 hu

omit hU in
theorem cmap_mem {g u : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (hu : u ∈ U) :
    cmap g u ∈ U :=
  Subgroup.mul_mem _ (conj_mem hg hu) (Subgroup.inv_mem _ hu)

theorem cmap_mul {g x y : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (hx : x ∈ U)
    (hy : y ∈ U) : cmap g (x * y) = cmap g x * cmap g y := by
  have hgy := conj_mem hg hy
  have hc : (g * y * g⁻¹) * x⁻¹ = x⁻¹ * (g * y * g⁻¹) := hU _ hgy _ (Subgroup.inv_mem _ hx)
  have hxy : x * y = y * x := hU x hx y hy
  calc cmap g (x * y) = g * (x * y) * g⁻¹ * (y * x)⁻¹ := by rw [cmap, ← hxy]
    _ = (g * x * g⁻¹) * ((g * y * g⁻¹) * x⁻¹) * y⁻¹ := by group
    _ = (g * x * g⁻¹) * (x⁻¹ * (g * y * g⁻¹)) * y⁻¹ := by rw [hc]
    _ = cmap g x * cmap g y := by simp only [cmap]; group

omit hU in
theorem cmap_mul_left (g h u : G) : cmap (g * h) u = cmap g (h * u * h⁻¹) * cmap h u := by
  simp only [cmap]
  group

theorem cmap_inv {g u : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (hu : u ∈ U) :
    cmap g⁻¹ u = cmap g (g⁻¹ * u⁻¹ * g) := by
  have h1 : g⁻¹ * u * g ∈ U := by
    have := conj_mem (Subgroup.inv_mem _ hg) hu
    rwa [inv_inv] at this
  have hc : (g⁻¹ * u * g) * u⁻¹ = u⁻¹ * (g⁻¹ * u * g) := hU _ h1 _ (Subgroup.inv_mem _ hu)
  calc cmap g⁻¹ u = (g⁻¹ * u * g) * u⁻¹ := by simp only [cmap, inv_inv]
    _ = u⁻¹ * (g⁻¹ * u * g) := hc
    _ = cmap g (g⁻¹ * u⁻¹ * g) := by simp only [cmap]; group

omit hU in
theorem imC_mul_le {g h : G} (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    imC U (g * h) ≤ imC U g ⊔ imC U h := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, cmap_mul_left]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (cmap_mem_imC (conj_mem hh hu)))
    (Subgroup.mem_sup_right (cmap_mem_imC hu))

theorem imC_inv_le {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    imC U g⁻¹ ≤ imC U g := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, cmap_inv hU hg hu]
  have h1 : g⁻¹ * u⁻¹ * g ∈ U := by
    have := conj_mem (Subgroup.inv_mem _ hg) (Subgroup.inv_mem _ hu)
    rwa [inv_inv] at this
  exact cmap_mem_imC h1

omit hU in
theorem imC_eq_bot {q : G} (hq : ∀ x ∈ U, q * x = x * q) : imC U q = ⊥ := by
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot, cmap, hq u hu, mul_inv_cancel_right, mul_inv_cancel]

theorem imC_le_of_mem_closure {a b : G} {Q : Subgroup G}
    (ha : a ∈ Subgroup.normalizer (U : Set G)) (hb : b ∈ Subgroup.normalizer (U : Set G))
    (hQ : ∀ q ∈ Q, ∀ x ∈ U, q * x = x * q) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} ∪ (Q : Set G))) : imC U x ≤ imC U a ⊔ imC U b := by
  have hQN : Q ≤ Subgroup.normalizer (U : Set G) := fun q hq => by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hQ q hq u hu, mul_inv_cancel_right]
      exact hu
    · intro hu
      have h1 := hQ q hq _ hu
      have h2 : q * u * q⁻¹ = u := by
        calc q * u * q⁻¹ = q⁻¹ * (q * (q * u * q⁻¹)) := by group
          _ = q⁻¹ * ((q * u * q⁻¹) * q) := by rw [h1]
          _ = u := by group
      rwa [h2] at hu
  have hN : Subgroup.closure ({a, b} ∪ (Q : Set G)) ≤ Subgroup.normalizer (U : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (hy | hy)
    · rcases hy with rfl | rfl
      · exact ha
      · exact hb
    · exact hQN hy
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · rcases hy with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · rw [imC_eq_bot (hQ y hy)]
      exact bot_le
  | one =>
    rw [imC_eq_bot (fun x _ => by rw [one_mul, mul_one])]
    exact bot_le
  | mul y z hy hz ihy ihz =>
    exact (imC_mul_le (hN hz)).trans (sup_le ihy ihz)
  | inv y hy ihy =>
    exact (imC_inv_le hU (hN hy)).trans ihy

end Abelian

theorem le_of_commutator_eq {U L X : Subgroup G} (hUL : ⁅U, L⁆ = U)
    (hX : ∀ l ∈ L, imC U l ≤ X) : U ≤ X := by
  rw [← hUL, Subgroup.commutator_le]
  intro u hu l hl
  have h1 : ⁅u, l⁆ = (cmap l u)⁻¹ := by
    rw [commutatorElement_def, cmap]
    group
  rw [h1]
  exact Subgroup.inv_mem _ (hX l hl (cmap_mem_imC hu))

section Fox

@[expose] def evalW (a b : G) : List Bool → G
  | [] => 1
  | s :: w => (if s then b else a) * evalW a b w

variable {V : Type*} [AddCommGroup V]

@[expose] def actV (ρa ρb : V →+ V) : List Bool → V → V
  | [] => fun v => v
  | s :: w => fun v => (if s then ρb else ρa) (actV ρa ρb w v)

@[expose] def foxV (ρa ρb : V →+ V) : List Bool → V → V × V
  | [] => fun _ => (0, 0)
  | s :: w => fun v =>
    foxV ρa ρb w v + (if s then ((0 : V), actV ρa ρb w v) else (actV ρa ρb w v, (0 : V)))

variable {U : Subgroup G} (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
  {a b : G} (ha : a ∈ Subgroup.normalizer (U : Set G)) (hb : b ∈ Subgroup.normalizer (U : Set G))
  {ρa ρb : V →+ V} (β : ↥U →* Multiplicative V)
  (hβa : ∀ u v : ↥U, (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (β v) = ρa (Multiplicative.toAdd (β u)))
  (hβb : ∀ u v : ↥U, (v : G) = b * u * b⁻¹ →
    Multiplicative.toAdd (β v) = ρb (Multiplicative.toAdd (β u)))
  (hker : ∀ z : ↥U, β z = 1 → a * z = z * a ∧ b * z = z * b)

omit hU in
include ha hb in
theorem evalW_mem_normalizer (w : List Bool) :
    evalW a b w ∈ Subgroup.normalizer (U : Set G) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons s w ih =>
    cases s
    · exact Subgroup.mul_mem _ ha ih
    · exact Subgroup.mul_mem _ hb ih

omit hU in
include ha hb hβa hβb in
theorem toAdd_conj_evalW (w : List Bool) (u : ↥U) :
    Multiplicative.toAdd (β ⟨evalW a b w * u * (evalW a b w)⁻¹,
      conj_mem (evalW_mem_normalizer ha hb w) u.2⟩) =
      actV ρa ρb w (Multiplicative.toAdd (β u)) := by
  induction w generalizing u with
  | nil =>
    show Multiplicative.toAdd (β ⟨1 * u * 1⁻¹, _⟩) = Multiplicative.toAdd (β u)
    congr 2
    apply Subtype.ext
    simp
  | cons s w ih =>
    have hhN := evalW_mem_normalizer ha hb w
    have h1 := ih u
    cases s
    · have h2 := hβa ⟨evalW a b w * u * (evalW a b w)⁻¹, conj_mem hhN u.2⟩
        ⟨evalW a b (false :: w) * u * (evalW a b (false :: w))⁻¹,
          conj_mem (evalW_mem_normalizer ha hb (false :: w)) u.2⟩
        (by
          show a * evalW a b w * u * (a * evalW a b w)⁻¹ =
            a * (evalW a b w * u * (evalW a b w)⁻¹) * a⁻¹
          group)
      rw [h2, h1]
      rfl
    · have h2 := hβb ⟨evalW a b w * u * (evalW a b w)⁻¹, conj_mem hhN u.2⟩
        ⟨evalW a b (true :: w) * u * (evalW a b (true :: w))⁻¹,
          conj_mem (evalW_mem_normalizer ha hb (true :: w)) u.2⟩
        (by
          show b * evalW a b w * u * (b * evalW a b w)⁻¹ =
            b * (evalW a b w * u * (evalW a b w)⁻¹) * b⁻¹
          group)
      rw [h2, h1]
      rfl

include hU ha hb hβa hβb hker in
theorem cmap_evalW (w : List Bool) (u x y : ↥U)
    (hx : Multiplicative.toAdd (β x) = (foxV ρa ρb w (Multiplicative.toAdd (β u))).1)
    (hy : Multiplicative.toAdd (β y) = (foxV ρa ρb w (Multiplicative.toAdd (β u))).2) :
    cmap (evalW a b w) u = cmap a x * cmap b y := by
  have hka : ∀ z : ↥U, β z = 1 → cmap a z = 1 := fun z hz => by
    rw [cmap, (hker z hz).1, mul_inv_cancel_right, mul_inv_cancel]
  have hkb : ∀ z : ↥U, β z = 1 → cmap b z = 1 := fun z hz => by
    rw [cmap, (hker z hz).2, mul_inv_cancel_right, mul_inv_cancel]
  have hwa : ∀ z z' : ↥U, β z = β z' → cmap a z = cmap a z' := by
    intro z z' hzz
    have h1 : β (z * z'⁻¹) = 1 := by rw [map_mul, map_inv, hzz, mul_inv_cancel]
    have h2 := cmap_mul hU ha (z * z'⁻¹).2 z'.2
    rw [show ((z * z'⁻¹ : ↥U) : G) * z' = z by simp, hka _ h1, one_mul] at h2
    exact h2
  have hwb : ∀ z z' : ↥U, β z = β z' → cmap b z = cmap b z' := by
    intro z z' hzz
    have h1 : β (z * z'⁻¹) = 1 := by rw [map_mul, map_inv, hzz, mul_inv_cancel]
    have h2 := cmap_mul hU hb (z * z'⁻¹).2 z'.2
    rw [show ((z * z'⁻¹ : ↥U) : G) * z' = z by simp, hkb _ h1, one_mul] at h2
    exact h2
  induction w generalizing x y with
  | nil =>
    have hx1 : β x = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hx]
      rfl
    have hy1 : β y = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hy]
      rfl
    rw [hka x hx1, hkb y hy1, one_mul]
    simp only [evalW, cmap]
    group
  | cons s w ih =>
    have hhN := evalW_mem_normalizer ha hb w
    set u' : ↥U := ⟨evalW a b w * u * (evalW a b w)⁻¹, conj_mem hhN u.2⟩ with hu'
    have hβu' : Multiplicative.toAdd (β u') = actV ρa ρb w (Multiplicative.toAdd (β u)) :=
      toAdd_conj_evalW ha hb β hβa hβb w u
    cases s
    ·
      have hx' : Multiplicative.toAdd (β (x * u'⁻¹)) =
          (foxV ρa ρb w (Multiplicative.toAdd (β u))).1 := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hx, hβu']
        show (foxV ρa ρb w _).1 + actV ρa ρb w _ + -actV ρa ρb w _ = _
        rw [add_neg_cancel_right]
      have hy' : Multiplicative.toAdd (β y) = (foxV ρa ρb w (Multiplicative.toAdd (β u))).2 := by
        rw [hy]
        show (foxV ρa ρb w _).2 + 0 = _
        rw [add_zero]
      have hih := ih (x * u'⁻¹) y hx' hy'
      have hcx : cmap a x = cmap a (x * u'⁻¹ : ↥U) * cmap a u' := by
        rw [← cmap_mul hU ha (x * u'⁻¹).2 u'.2]
        congr 1
        simp
      show cmap (a * evalW a b w) u = cmap a x * cmap b y
      rw [cmap_mul_left, hih, hcx]
      have hc1 := hU _ (cmap_mem ha u'.2) _ (cmap_mem ha (x * u'⁻¹).2)
      calc cmap a (evalW a b w * u * (evalW a b w)⁻¹) * (cmap a (x * u'⁻¹ : ↥U) * cmap b y)
          = (cmap a u' * cmap a (x * u'⁻¹ : ↥U)) * cmap b y := (mul_assoc _ _ _).symm
        _ = (cmap a (x * u'⁻¹ : ↥U) * cmap a u') * cmap b y := by rw [hc1]
    ·
      have hx' : Multiplicative.toAdd (β x) = (foxV ρa ρb w (Multiplicative.toAdd (β u))).1 := by
        rw [hx]
        show (foxV ρa ρb w _).1 + 0 = _
        rw [add_zero]
      have hy' : Multiplicative.toAdd (β (y * u'⁻¹)) =
          (foxV ρa ρb w (Multiplicative.toAdd (β u))).2 := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hy, hβu']
        show (foxV ρa ρb w _).2 + actV ρa ρb w _ + -actV ρa ρb w _ = _
        rw [add_neg_cancel_right]
      have hih := ih x (y * u'⁻¹) hx' hy'
      have hcy : cmap b y = cmap b (y * u'⁻¹ : ↥U) * cmap b u' := by
        rw [← cmap_mul hU hb (y * u'⁻¹).2 u'.2]
        congr 1
        simp
      show cmap (b * evalW a b w) u = cmap a x * cmap b y
      rw [cmap_mul_left, hih, hcy]
      have hc1 := hU _ (cmap_mem hb u'.2) _ (cmap_mem ha x.2)
      have hc2 := hU _ (cmap_mem hb u'.2) _ (cmap_mem hb (y * u'⁻¹).2)
      calc cmap b (evalW a b w * u * (evalW a b w)⁻¹) * (cmap a x * cmap b (y * u'⁻¹ : ↥U))
          = (cmap b u' * cmap a x) * cmap b (y * u'⁻¹ : ↥U) := (mul_assoc _ _ _).symm
        _ = (cmap a x * cmap b u') * cmap b (y * u'⁻¹ : ↥U) := by rw [hc1]
        _ = cmap a x * (cmap b u' * cmap b (y * u'⁻¹ : ↥U)) := mul_assoc _ _ _
        _ = cmap a x * (cmap b (y * u'⁻¹ : ↥U) * cmap b u') := by rw [hc2]

include hU ha hb hβa hβb hker in
theorem cmap_eq_one_of_relation (w : List Bool)
    (hw : ∀ x ∈ U, evalW a b w * x = x * evalW a b w) (u x : ↥U)
    (hfb : (foxV ρa ρb w (Multiplicative.toAdd (β u))).2 = 0)
    (hx : Multiplicative.toAdd (β x) = (foxV ρa ρb w (Multiplicative.toAdd (β u))).1) :
    cmap a x = 1 := by
  have h1 := cmap_evalW hU ha hb β hβa hβb hker w u x 1 hx (by rw [map_one, hfb]; rfl)
  have h2 : cmap (evalW a b w) u = 1 := by
    rw [cmap, hw u u.2, mul_inv_cancel_right, mul_inv_cancel]
  rw [h2] at h1
  have h3 : cmap b ((1 : ↥U) : G) = 1 := by
    simp [cmap]
  rw [h3, mul_one] at h1
  exact h1.symm

end Fox

section Card

theorem card_sup_le_of_comm {H K : Subgroup G} [Finite H] [Finite K]
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  open scoped Pointwise in
  have hset : (K : Set G) * (H : Set G) = (H : Set G) * (K : Set G) := by
    ext y
    constructor
    · rintro ⟨k, hk, h, hh, rfl⟩
      exact ⟨h, hh, k, hk, hHK h hh k hk⟩
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨k, hk, h, hh, (hHK h hh k hk).symm⟩
  have h1 := CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hset
  have hsurj : Function.Surjective (fun p : ↥H × ↥K =>
      (⟨(p.1 : G) * p.2, by
        rw [← SetLike.mem_coe, h1]
        exact Set.mul_mem_mul p.1.2 p.2.2⟩ : ↥(H ⊔ K))) := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, h1] at hx
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective _ hsurj

theorem card_imC_le {U : Subgroup G} (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) {S : Type*} [Finite S] (φ : ↥U → S)
    (hφ : Function.Surjective φ) (hdep : ∀ x y : ↥U, φ x = φ y → cmap g x = cmap g y) :
    Nat.card ↥(imC U g) ≤ Nat.card S := by
  classical
  have hset : (imC U g : Set G) = {x | ∃ u ∈ U, cmap g u = x} := by
    refine le_antisymm ?_ Subgroup.subset_closure
    have hsub : ∃ H : Subgroup G, (H : Set G) = {x | ∃ u ∈ U, cmap g u = x} := by
      refine ⟨{ carrier := {x | ∃ u ∈ U, cmap g u = x}
                mul_mem' := ?_
                one_mem' := ⟨1, U.one_mem, by simp [cmap]⟩
                inv_mem' := ?_ }, rfl⟩
      · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, U.mul_mem hx hy, cmap_mul hU hg hx hy⟩
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨x⁻¹, U.inv_mem hx, ?_⟩
        have h1 := cmap_mul hU hg hx (U.inv_mem hx)
        rw [mul_inv_cancel] at h1
        have h2 : cmap g 1 = 1 := by simp [cmap]
        rw [h2] at h1
        exact (eq_inv_of_mul_eq_one_right h1.symm)
    obtain ⟨H, hH⟩ := hsub
    rw [imC, ← hH, Subgroup.closure_eq]
  let σ : S → ↥U := Function.surjInv hφ
  have hσ : ∀ s, φ (σ s) = s := Function.surjInv_eq hφ
  let f : S → ↥(imC U g) := fun s =>
    ⟨cmap g (σ s : G), by
      rw [← SetLike.mem_coe, hset]
      exact ⟨(σ s : G), (σ s).2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, hset] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨φ ⟨u, hu⟩, Subtype.ext ?_⟩
    exact hdep _ _ (hσ _)
  exact Nat.card_le_card_of_surjective f hf

end Card

section More

variable {U : Subgroup G} {a : G} {V : Type*} [AddCommGroup V]

theorem cmap_eq_of_eq (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (ha : a ∈ Subgroup.normalizer (U : Set G)) (β : ↥U →* Multiplicative V)
    (hker : ∀ z : ↥U, β z = 1 → a * z = z * a) {x y : ↥U} (hxy : β x = β y) :
    cmap a x = cmap a y := by
  have h1 : β (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 := cmap_mul hU ha (x * y⁻¹).2 y.2
  rw [show ((x * y⁻¹ : ↥U) : G) * y = x by simp] at h2
  rw [h2, cmap, hker _ h1, mul_inv_cancel_right, mul_inv_cancel, one_mul]

omit [AddCommGroup V] in
theorem imC_le {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) : imC U g ≤ U :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hu, hx⟩ => hx ▸ cmap_mem hg hu

omit [AddCommGroup V] in
theorem map_evalW {H : Type*} [Group H] (f : G →* H) (a b : G) (w : List Bool) :
    f (evalW a b w) = evalW (f a) (f b) w := by
  induction w with
  | nil => exact map_one f
  | cons s w ih =>
    cases s
    · show f (a * evalW a b w) = f a * evalW (f a) (f b) w
      rw [map_mul, ih]
    · show f (b * evalW a b w) = f b * evalW (f a) (f b) w
      rw [map_mul, ih]

end More

end CFSG.Quasithin.H13.Sp4Z
