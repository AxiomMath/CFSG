module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section


namespace CFSG.SignalizerFunctorTheorem.Quadratic

namespace IndepPair

section Basic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem mem_map_iff {g : LGL p V} {U : Submodule (ZMod p) V} {w : V} :
    w ∈ U.map (g : V →ₗ[ZMod p] V) ↔ g⁻¹ w ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : g⁻¹ ((g : V →ₗ[ZMod p] V) u) = u := inv_apply_apply' g u
    rw [this]
    exact hu
  · intro h
    exact ⟨g⁻¹ w, h, apply_inv_apply' g w⟩

theorem irr_cj {A : Subgroup (LGL p V)}
    (h : ∀ U : Submodule (ZMod p) V, U ≤ commSub A → (∀ g ∈ A, ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = commSub A) (x : LGL p V) :
    ∀ U : Submodule (ZMod p) V, U ≤ commSub (cj x A) → (∀ g ∈ cj x A, ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = commSub (cj x A) := by
  intro U hU hinv
  rw [commSub_cj] at hU ⊢
  have hU' : U.comap (x : V →ₗ[ZMod p] V) ≤ commSub A := by
    intro u hu
    have h1 : x u ∈ (commSub A).map (x : V →ₗ[ZMod p] V) := hU hu
    have h2 := mem_map_iff.mp h1
    rwa [inv_apply_apply'] at h2
  have hinv' : ∀ g ∈ A, ∀ u ∈ U.comap (x : V →ₗ[ZMod p] V),
      g u ∈ U.comap (x : V →ₗ[ZMod p] V) := by
    intro g hg u hu
    have hg' : x * g * x⁻¹ ∈ cj x A := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have h1 : (x * g * x⁻¹) (x u) ∈ U := hinv _ hg' (x u) hu
    have e : (x * g * x⁻¹) (x u) = x (g u) := by
      change x (g (x⁻¹ (x u))) = x (g u)
      rw [inv_apply_apply']
    rw [e] at h1
    exact h1
  rcases h _ hU' hinv' with h0 | h1
  · left
    rw [Submodule.eq_bot_iff]
    intro u hu
    have h2 : x⁻¹ u ∈ U.comap (x : V →ₗ[ZMod p] V) := by
      rw [Submodule.mem_comap]
      change x (x⁻¹ u) ∈ U
      rwa [apply_inv_apply']
    rw [h0, Submodule.mem_bot] at h2
    have h3 : u = x (x⁻¹ u) := (apply_inv_apply' x u).symm
    rw [h3, h2, map_zero]
  · right
    apply le_antisymm hU
    intro w hw
    have h2 := mem_map_iff.mp hw
    rw [← h1, Submodule.mem_comap] at h2
    change x (x⁻¹ w) ∈ U at h2
    rwa [apply_inv_apply'] at h2

theorem cj_le_of_mem {E E₁ : Subgroup (LGL p V)} (h : E₁ ≤ E) {x : LGL p V} (hx : x ∈ E) :
    cj x E₁ ≤ E := by
  intro y hy
  rw [mem_cj] at hy
  have := E.mul_mem (E.mul_mem hx (h hy)) (E.inv_mem hx)
  have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  rwa [e] at this

structure PairHyp (r : ℕ) (E₁ E₂ : Subgroup (LGL p V)) : Prop where
  prime : r.Prime
  ne : r ≠ p
  pgroup : IsPGroup r (E₁ ⊔ E₂ : Subgroup (LGL p V))
  irr₁ : ∀ U : Submodule (ZMod p) V, U ≤ commSub E₁ → (∀ g ∈ E₁, ∀ u ∈ U, g u ∈ U) →
    U = ⊥ ∨ U = commSub E₁
  irr₂ : ∀ U : Submodule (ZMod p) V, U ≤ commSub E₂ → (∀ g ∈ E₂, ∀ u ∈ U, g u ∈ U) →
    U = ⊥ ∨ U = commSub E₂
  not_le₁ : ¬ commSub E₁ ≤ commSub E₂
  not_le₂ : ¬ commSub E₂ ≤ commSub E₁
  card₁ : 2 < Nat.card E₁
  card₂ : 2 < Nat.card E₂

structure Concl (E₁ E₂ : Subgroup (LGL p V)) : Prop where
  comm : ∀ g ∈ E₁, ∀ g' ∈ E₂, g * g' = g' * g
  inf_eq : commSub E₁ ⊓ commSub E₂ = ⊥

def IHyp (r : ℕ) (E₁ E₂ : Subgroup (LGL p V)) : Prop :=
  ∀ F₁ F₂ : Subgroup (LGL p V), PairHyp r F₁ F₂ →
    Nat.card ↥(F₁ ⊔ F₂) < Nat.card ↥(E₁ ⊔ E₂) → Concl F₁ F₂

theorem PairHyp.symm {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (h : PairHyp r E₁ E₂) :
    PairHyp r E₂ E₁ where
  prime := h.prime
  ne := h.ne
  pgroup := by rw [sup_comm]; exact h.pgroup
  irr₁ := h.irr₂
  irr₂ := h.irr₁
  not_le₁ := h.not_le₂
  not_le₂ := h.not_le₁
  card₁ := h.card₂
  card₂ := h.card₁

theorem Concl.symm {E₁ E₂ : Subgroup (LGL p V)} (h : Concl E₁ E₂) : Concl E₂ E₁ where
  comm g hg g' hg' := (h.comm g' hg' g hg).symm
  inf_eq := by rw [inf_comm]; exact h.inf_eq

theorem IHyp.symm {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (h : IHyp r E₁ E₂) : IHyp r E₂ E₁ :=
  fun F₁ F₂ hF hlt => h F₁ F₂ hF (by rwa [sup_comm E₂ E₁] at hlt)

end Basic

section Fin

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fact p.Prime] [Finite V]

theorem inv_mem_of_invariant {U : Submodule (ZMod p) V} {g : LGL p V}
    (h : ∀ u ∈ U, g u ∈ U) : ∀ u ∈ U, g⁻¹ u ∈ U := by
  have hle : U.map (g : V →ₗ[ZMod p] V) ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have heq : U.map (g : V →ₗ[ZMod p] V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g U)
  intro u hu
  have hu' : u ∈ U.map (g : V →ₗ[ZMod p] V) := by rw [heq]; exact hu
  exact mem_map_iff.mp hu'

omit [Finite V] in
theorem eq_one_of_pgroup {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) {Z : Subgroup (LGL p V)}
    (hZ : IsPGroup r Z) {g : LGL p V} (hg : g ∈ Z) {W : Submodule (ZMod p) V}
    (h1 : ∀ w ∈ W, g w = w) (h2 : ∀ v : V, g v - v ∈ W) : g = 1 := by
  obtain ⟨k, hk⟩ := hZ ⟨g, hg⟩
  have hk' : g ^ (r ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hp : g ^ p = 1 := pow_eq_one_of_trivial h1 h2
  have hcop : Nat.Coprime p (r ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes (Fact.out : p.Prime) hr).mpr hrp.symm)
  have h3 : orderOf g ∣ Nat.gcd p (r ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_of_pow_eq_one hk')
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Fact p.Prime] [Finite V] in
theorem exists_normal_coatom {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {H : Subgroup G} (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ M.Normal ∧ H ≤ M := by
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  exact ⟨M, hM.1, Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent) hM, hHM⟩

omit [Fact p.Prime] in
theorem card_sup_cj_lt {r : ℕ} (hr : r.Prime) {E E₁ : Subgroup (LGL p V)} (hE : IsPGroup r E)
    (hle : E₁ ≤ E) (hne : E₁ ≠ E) {g g' : LGL p V} (hg : g ∈ E) (hg' : g' ∈ E) :
    Nat.card ↥(cj g E₁ ⊔ cj g' E₁) < Nat.card ↥E := by
  have : Fact r.Prime := ⟨hr⟩
  have : Group.IsNilpotent ↥E := hE.isNilpotent
  have hH : E₁.subgroupOf E ≠ ⊤ := fun h => hne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨M, hMtop, hMn, hHM⟩ := exists_normal_coatom hH
  have hcj : ∀ h ∈ E, cj h E₁ ≤ M.map E.subtype := by
    intro h hh y hy
    have hyE : y ∈ E := cj_le_of_mem hle hh hy
    rw [mem_cj] at hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hyE⟩, ?_, rfl⟩
    have h1 : (⟨h⁻¹ * y * h, hle hy⟩ : E) ∈ M := hHM (Subgroup.mem_subgroupOf.mpr hy)
    have h2 := hMn.conj_mem _ h1 ⟨h, hh⟩
    convert h2 using 1
    apply Subtype.ext
    simp [mul_assoc]
  have hsup : cj g E₁ ⊔ cj g' E₁ ≤ M.map E.subtype := sup_le (hcj g hg) (hcj g' hg')
  have hMle : M.map E.subtype ≤ E := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  by_contra hcon
  have hcard : Nat.card E ≤ Nat.card (M.map E.subtype) :=
    (not_lt.mp hcon).trans (Subgroup.card_le_of_le hsup)
  have hEq : M.map E.subtype = E := Subgroup.eq_of_le_of_card_ge hMle hcard
  apply hMtop
  rw [eq_top_iff]
  intro x _
  have h1 : (x : LGL p V) ∈ M.map E.subtype := by
    rw [hEq]
    exact x.2
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp h1
  have h2 : m = x := Subtype.ext hmx
  rwa [h2] at hm

omit [Finite V] in
theorem caseA {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (hinv : ∀ g ∈ E₂, ∀ u ∈ commSub E₁, g u ∈ commSub E₁) : Concl E₁ E₂ := by
  have hinf : commSub E₁ ⊓ commSub E₂ = ⊥ := by
    rcases hP.irr₂ (commSub E₁ ⊓ commSub E₂) inf_le_right
      (fun g hg u hu => ⟨hinv g hg u hu.1, map_mem_commSub E₂ hg hu.2⟩) with h | h
    · exact h
    · exfalso
      apply hP.not_le₂
      rw [← h]
      exact inf_le_left
  have htriv : ∀ g ∈ E₂, ∀ u ∈ commSub E₁, g u = u := by
    intro g hg u hu
    have h1 : g u - u ∈ commSub E₁ ⊓ commSub E₂ :=
      ⟨Submodule.sub_mem _ (hinv g hg u hu) hu, sub_mem_commSub E₂ hg u⟩
    rw [hinf, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  refine ⟨?_, hinf⟩
  intro g hg g' hg'
  have hgE : g ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left hg
  have hg'E : g' ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_right hg'
  have hκ : g * g' * g⁻¹ * g'⁻¹ ∈ E₁ ⊔ E₂ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgE hg'E)
      (Subgroup.inv_mem _ hgE)) (Subgroup.inv_mem _ hg'E)
  have h1 : g * g' * g⁻¹ * g'⁻¹ = 1 := by
    refine eq_one_of_pgroup hP.prime hP.ne hP.pgroup hκ (W := commSub E₁) ?_ ?_
    · intro u hu
      have e1 : g'⁻¹ u = u := htriv _ (E₂.inv_mem hg') u hu
      have e2 : g⁻¹ u ∈ commSub E₁ := map_mem_commSub E₁ (E₁.inv_mem hg) hu
      have e3 : g' (g⁻¹ u) = g⁻¹ u := htriv _ hg' _ e2
      change g (g' (g⁻¹ (g'⁻¹ u))) = u
      rw [e1, e3, apply_inv_apply']
    · intro v
      change g (g' (g⁻¹ (g'⁻¹ v))) - v ∈ commSub E₁
      have a1 : g (g' (g⁻¹ (g'⁻¹ v))) - g' (g⁻¹ (g'⁻¹ v)) ∈ commSub E₁ :=
        sub_mem_commSub E₁ hg _
      have a2 : g⁻¹ (g'⁻¹ v) - g'⁻¹ v ∈ commSub E₁ := sub_mem_commSub E₁ (E₁.inv_mem hg) _
      have a3 : g' (g⁻¹ (g'⁻¹ v) - g'⁻¹ v) ∈ commSub E₁ := hinv g' hg' _ a2
      have e : g' (g⁻¹ (g'⁻¹ v) - g'⁻¹ v) = g' (g⁻¹ (g'⁻¹ v)) - v := by
        rw [map_sub, apply_inv_apply']
      rw [e] at a3
      have a4 := Submodule.add_mem _ a1 a3
      have e2 : g (g' (g⁻¹ (g'⁻¹ v))) - v =
          g (g' (g⁻¹ (g'⁻¹ v))) - g' (g⁻¹ (g'⁻¹ v)) + (g' (g⁻¹ (g'⁻¹ v)) - v) := by abel
      rw [e2]
      exact a4
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

theorem apply_IH {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂) (IH : IHyp r E₁ E₂)
    {a b : LGL p V} (ha : a ∈ E₁ ⊔ E₂) (hb : b ∈ E₁ ⊔ E₂)
    (hab : ¬ ∀ u ∈ commSub E₁, (a⁻¹ * b) u ∈ commSub E₁) : Concl (cj a E₁) (cj b E₁) := by
  have h12 : ¬ (commSub E₁).map (a : V →ₗ[ZMod p] V) ≤
      (commSub E₁).map (b : V →ₗ[ZMod p] V) := by
    intro h
    apply hab
    have h1 : ∀ u ∈ commSub E₁, (b⁻¹ * a) u ∈ commSub E₁ := by
      intro u hu
      have : b⁻¹ (a u) ∈ commSub E₁ := mem_map_iff.mp (h (Submodule.mem_map_of_mem hu))
      exact this
    have h2 := inv_mem_of_invariant h1
    have e : (b⁻¹ * a)⁻¹ = a⁻¹ * b := by group
    rw [e] at h2
    exact h2
  have h21 : ¬ (commSub E₁).map (b : V →ₗ[ZMod p] V) ≤
      (commSub E₁).map (a : V →ₗ[ZMod p] V) := by
    intro h
    apply hab
    intro u hu
    have : a⁻¹ (b u) ∈ commSub E₁ := mem_map_iff.mp (h (Submodule.mem_map_of_mem hu))
    exact this
  have hne : E₁ ≠ E₁ ⊔ E₂ := fun h =>
    hP.not_le₂ (commSub_mono _ _ (le_sup_right.trans h.ge))
  refine IH _ _ ⟨hP.prime, hP.ne, hP.pgroup.to_le (sup_le (cj_le_of_mem le_sup_left ha)
    (cj_le_of_mem le_sup_left hb)), irr_cj hP.irr₁ a, irr_cj hP.irr₁ b, ?_, ?_, ?_, ?_⟩
    (card_sup_cj_lt hP.prime hP.pgroup le_sup_left hne ha hb)
  · rw [commSub_cj, commSub_cj]
    exact h12
  · rw [commSub_cj, commSub_cj]
    exact h21
  · rw [card_cj]
    exact hP.card₁
  · rw [card_cj]
    exact hP.card₁

theorem caseB_key {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (IH : IHyp r E₁ E₂) {y : LGL p V} (hy : y ∈ E₂)
    (hy' : ¬ ∀ u ∈ commSub E₁, y u ∈ commSub E₁) :
    commSub E₁ ⊓ (commSub E₁).map (y : V →ₗ[ZMod p] V) = ⊥ ∧
      ∀ g ∈ E₁, ∀ u ∈ (commSub E₁).map (y : V →ₗ[ZMod p] V), g u = u := by
  have C := apply_IH hP IH (a := 1) (b := y) (one_mem _) (Subgroup.mem_sup_right hy)
    (by simpa using hy')
  rw [cj_one] at C
  have hinf : commSub E₁ ⊓ (commSub E₁).map (y : V →ₗ[ZMod p] V) = ⊥ := by
    have := C.inf_eq
    rwa [commSub_cj] at this
  refine ⟨hinf, ?_⟩
  intro g hg u hu
  have hnorm : g ∈ Subgroup.normalizer ((cj y E₁ : Subgroup (LGL p V)) : Set (LGL p V)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (C.comm g hg h hh).symm)
  have hu' : u ∈ commSub (cj y E₁) := by
    rw [commSub_cj]
    exact hu
  have h1 : g u ∈ (commSub E₁).map (y : V →ₗ[ZMod p] V) := by
    rw [← commSub_cj]
    exact map_mem_commSub_of_mem_normalizer _ hnorm hu'
  have h2 : g u - u ∈ commSub E₁ := sub_mem_commSub E₁ hg u
  have h3 : g u - u ∈ (commSub E₁).map (y : V →ₗ[ZMod p] V) := Submodule.sub_mem _ h1 hu
  have h4 : g u - u ∈ commSub E₁ ⊓ (commSub E₁).map (y : V →ₗ[ZMod p] V) := ⟨h2, h3⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h4
  exact h4

omit [Fact p.Prime] [Finite V] in
theorem map_le_sup {E₁ E₂ : Subgroup (LGL p V)} {x : LGL p V} (hx : x ∈ E₂) :
    (commSub E₁).map (x : V →ₗ[ZMod p] V) ≤ commSub E₁ ⊔ commSub E₂ := by
  rintro _ ⟨u, hu, rfl⟩
  change x u ∈ commSub E₁ ⊔ commSub E₂
  have e : x u = u + (x u - u) := by abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
    (Submodule.mem_sup_right (sub_mem_commSub E₂ hx u))

theorem caseB_dim {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (IH : IHyp r E₁ E₂)
    (hd : Module.finrank (ZMod p) (commSub E₂) ≤ Module.finrank (ZMod p) (commSub E₁))
    {x : LGL p V} (hx : x ∈ E₂) (hx' : ¬ ∀ u ∈ commSub E₁, x u ∈ commSub E₁) :
    Module.finrank (ZMod p) (commSub E₂) = Module.finrank (ZMod p) (commSub E₁) ∧
      commSub E₁ ⊓ commSub E₂ = ⊥ ∧
      commSub E₁ ⊔ (commSub E₁).map (x : V →ₗ[ZMod p] V) = commSub E₁ ⊔ commSub E₂ ∧
      Module.finrank (ZMod p) ↥(commSub E₁ ⊔ commSub E₂) =
        Module.finrank (ZMod p) (commSub E₁) + Module.finrank (ZMod p) (commSub E₁) := by
  obtain ⟨hkey, -⟩ := caseB_key hP IH hx hx'
  have hxW := map_le_sup (E₁ := E₁) hx
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (commSub E₁)
    ((commSub E₁).map (x : V →ₗ[ZMod p] V))
  rw [hkey, finrank_bot, add_zero, LinearEquiv.finrank_map_eq] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSub E₁) (commSub E₂)
  have h3 : Module.finrank (ZMod p) ↥(commSub E₁ ⊔ (commSub E₁).map (x : V →ₗ[ZMod p] V)) ≤
      Module.finrank (ZMod p) ↥(commSub E₁ ⊔ commSub E₂) :=
    Submodule.finrank_mono (sup_le le_sup_left hxW)
  have h4 : Module.finrank (ZMod p) ↥(commSub E₁ ⊓ commSub E₂) = 0 := by omega
  have h5 : commSub E₁ ⊓ commSub E₂ = ⊥ := Submodule.finrank_eq_zero.mp h4
  have h6 : commSub E₁ ⊔ (commSub E₁).map (x : V →ₗ[ZMod p] V) = commSub E₁ ⊔ commSub E₂ :=
    Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hxW) (by omega)
  exact ⟨by omega, h5, h6, by omega⟩

theorem caseB_same {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (IH : IHyp r E₁ E₂)
    (hd : Module.finrank (ZMod p) (commSub E₂) ≤ Module.finrank (ZMod p) (commSub E₁))
    {x : LGL p V} (hx : x ∈ E₂) (hx' : ¬ ∀ u ∈ commSub E₁, x u ∈ commSub E₁) :
    ∀ y ∈ E₂, (¬ ∀ u ∈ commSub E₁, y u ∈ commSub E₁) →
      ∀ u ∈ commSub E₁, (x⁻¹ * y) u ∈ commSub E₁ := by
  intro y hy hy'
  by_contra hxy
  have C := apply_IH hP IH (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_right hy) hxy
  have hinf : (commSub E₁).map (x : V →ₗ[ZMod p] V) ⊓ (commSub E₁).map (y : V →ₗ[ZMod p] V) =
      ⊥ := by
    have := C.inf_eq
    rwa [commSub_cj, commSub_cj] at this
  obtain ⟨-, hk1⟩ := caseB_key hP IH hx hx'
  obtain ⟨-, hk2⟩ := caseB_key hP IH hy hy'
  obtain ⟨-, -, -, hfW⟩ := caseB_dim hP IH hd hx hx'
  have hxW := map_le_sup (E₁ := E₁) hx
  have hyW := map_le_sup (E₁ := E₁) hy
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq ((commSub E₁).map (x : V →ₗ[ZMod p] V))
    ((commSub E₁).map (y : V →ₗ[ZMod p] V))
  rw [hinf, finrank_bot, add_zero, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq] at h1
  have h2 : (commSub E₁).map (x : V →ₗ[ZMod p] V) ⊔ (commSub E₁).map (y : V →ₗ[ZMod p] V) =
      commSub E₁ ⊔ commSub E₂ :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hxW hyW) (by omega)
  have htriv : ∀ g ∈ E₁, ∀ w ∈ commSub E₁ ⊔ commSub E₂, g w = w := by
    intro g hg w hw
    rw [← h2] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hk1 g hg a ha, hk2 g hg b hb]
  have hbot : E₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    exact eq_one_of_pgroup hP.prime hP.ne hP.pgroup (Subgroup.mem_sup_left hg) (htriv g hg)
      (fun v => Submodule.mem_sup_left (sub_mem_commSub E₁ hg v))
  have h3 := hP.card₁
  rw [hbot, Subgroup.card_bot] at h3
  omega

theorem caseB_stab {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (IH : IHyp r E₁ E₂)
    (hd : Module.finrank (ZMod p) (commSub E₂) ≤ Module.finrank (ZMod p) (commSub E₁))
    {x : LGL p V} (hx : x ∈ E₂) (hx' : ¬ ∀ u ∈ commSub E₁, x u ∈ commSub E₁)
    {k : LGL p V} (hk : k ∈ E₂) (hk' : ∀ u ∈ commSub E₁, k u ∈ commSub E₁) : k = 1 := by
  obtain ⟨-, hinf, hW, -⟩ := caseB_dim hP IH hd hx hx'
  have key4 := caseB_same hP IH hd hx hx'
  have hk1 : ∀ u ∈ commSub E₁, k u = u := by
    intro u hu
    have h1 : k u - u ∈ commSub E₁ ⊓ commSub E₂ :=
      ⟨Submodule.sub_mem _ (hk' u hu) hu, sub_mem_commSub E₂ hk u⟩
    rw [hinf, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hxV2 : ∀ w ∈ (commSub E₁).map (x : V →ₗ[ZMod p] V), w ∈ commSub E₂ → w = 0 := by
    intro w hw hw2
    have hw1 := mem_map_iff.mp hw
    have hw2' : x⁻¹ w ∈ commSub E₂ := map_mem_commSub E₂ (E₂.inv_mem hx) hw2
    have h3 : x⁻¹ w ∈ commSub E₁ ⊓ commSub E₂ := ⟨hw1, hw2'⟩
    rw [hinf, Submodule.mem_bot] at h3
    have h4 : w = x (x⁻¹ w) := (apply_inv_apply' x w).symm
    rw [h4, h3, map_zero]
  have hk2 : ∀ w ∈ (commSub E₁).map (x : V →ₗ[ZMod p] V), k w = w := by
    intro w hw
    have hkx : ¬ ∀ u ∈ commSub E₁, (k * x) u ∈ commSub E₁ := by
      intro h
      apply hx'
      intro u hu
      have h5 := inv_mem_of_invariant hk' _ (h u hu)
      have e : k⁻¹ ((k * x) u) = x u := by
        change k⁻¹ (k (x u)) = x u
        exact inv_apply_apply' k (x u)
      rw [e] at h5
      exact h5
    have hmem : k w ∈ (commSub E₁).map (x : V →ₗ[ZMod p] V) := by
      rw [mem_map_iff]
      have hv : x⁻¹ w ∈ commSub E₁ := mem_map_iff.mp hw
      have h6 := key4 (k * x) (E₂.mul_mem hk hx) hkx (x⁻¹ w) hv
      change x⁻¹ (k (x (x⁻¹ w))) ∈ commSub E₁ at h6
      rwa [apply_inv_apply'] at h6
    have h5 : k w - w ∈ (commSub E₁).map (x : V →ₗ[ZMod p] V) := Submodule.sub_mem _ hmem hw
    exact sub_eq_zero.mp (hxV2 _ h5 (sub_mem_commSub E₂ hk w))
  refine eq_one_of_pgroup hP.prime hP.ne hP.pgroup (Subgroup.mem_sup_right hk)
    (W := commSub E₁ ⊔ commSub E₂) ?_ ?_
  · intro w hw
    rw [← hW] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hk1 a ha, hk2 b hb]
  · intro v
    exact Submodule.mem_sup_right (sub_mem_commSub E₂ hk v)

theorem caseB {r : ℕ} {E₁ E₂ : Subgroup (LGL p V)} (hP : PairHyp r E₁ E₂)
    (IH : IHyp r E₁ E₂) (hn : ¬ ∀ g ∈ E₂, ∀ u ∈ commSub E₁, g u ∈ commSub E₁)
    (hd : Module.finrank (ZMod p) (commSub E₂) ≤ Module.finrank (ZMod p) (commSub E₁)) :
    False := by
  obtain ⟨x, hx, hx'⟩ : ∃ x ∈ E₂, ¬ ∀ u ∈ commSub E₁, x u ∈ commSub E₁ := by
    by_contra hcon
    exact hn fun g hg => by
      by_contra hg'
      exact hcon ⟨g, hg, hg'⟩
  have key4 := caseB_same hP IH hd hx hx'
  have hstab := fun k hk hk' => caseB_stab hP IH hd hx hx' (k := k) hk hk'
  have hall : ∀ g ∈ E₂, g = 1 ∨ g = x := by
    intro g hg
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      have hng : ¬ ∀ u ∈ commSub E₁, g u ∈ commSub E₁ := fun h => hg1 (hstab g hg h)
      have h1 := key4 g hg hng
      have h2 : x⁻¹ * g = 1 := hstab _ (E₂.mul_mem (E₂.inv_mem hx) hg) h1
      exact (inv_mul_eq_one.mp h2).symm
  have h3 : 2 < (E₂ : Set (LGL p V)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact hP.card₂
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).mp h3
  rcases hall a ha with rfl | rfl <;> rcases hall b hb with rfl | rfl <;>
    rcases hall c hc with rfl | rfl <;>
    first | exact hab rfl | exact hac rfl | exact hbc rfl

theorem concl_aux {r : ℕ} : ∀ (n : ℕ) (E₁ E₂ : Subgroup (LGL p V)),
    Nat.card ↥(E₁ ⊔ E₂) = n → PairHyp r E₁ E₂ → Concl E₁ E₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E₁ E₂ hn hP
    have IH : IHyp r E₁ E₂ := fun F₁ F₂ hF hlt => ih _ (hn ▸ hlt) F₁ F₂ rfl hF
    by_cases hA : ∀ g ∈ E₂, ∀ u ∈ commSub E₁, g u ∈ commSub E₁
    · exact caseA hP hA
    by_cases hB : ∀ g ∈ E₁, ∀ u ∈ commSub E₂, g u ∈ commSub E₂
    · exact (caseA hP.symm hB).symm
    exfalso
    rcases le_total (Module.finrank (ZMod p) (commSub E₂))
        (Module.finrank (ZMod p) (commSub E₁)) with hd | hd
    · exact caseB hP IH hA hd
    · exact caseB hP.symm IH.symm hB hd

end Fin

end IndepPair

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem indep_pair {E₁ E₂ : Subgroup (LGL p V)} {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    (hE : IsPGroup r (E₁ ⊔ E₂ : Subgroup (LGL p V)))
    (h1 : ∀ U : Submodule (ZMod p) V, U ≤ commSub E₁ → (∀ g ∈ E₁, ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = commSub E₁)
    (h2 : ∀ U : Submodule (ZMod p) V, U ≤ commSub E₂ → (∀ g ∈ E₂, ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = commSub E₂)
    (h3 : ¬ commSub E₁ ≤ commSub E₂) (h3' : ¬ commSub E₂ ≤ commSub E₁)
    (h4 : 2 < Nat.card E₁) (h4' : 2 < Nat.card E₂) :
    (∀ g ∈ E₁, ∀ g' ∈ E₂, g * g' = g' * g) ∧ commSub E₁ ⊓ commSub E₂ = ⊥ := by
  have h := IndepPair.concl_aux (r := r) _ E₁ E₂ rfl ⟨hr, hrp, hE, h1, h2, h3, h3', h4, h4'⟩
  exact ⟨h.comm, h.inf_eq⟩

end CFSG.SignalizerFunctorTheorem.Quadratic
