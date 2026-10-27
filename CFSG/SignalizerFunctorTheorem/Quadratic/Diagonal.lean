module

public import CFSG.SignalizerFunctorTheorem.Quadratic.SL2

public section

open scoped MatrixGroups Function

namespace CFSG.SignalizerFunctorTheorem.Quadratic

private structure DiagSetup (p r : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (𝓔 : Set (Subgroup (LGL p V))) (X : Subgroup (LGL p V)) : Prop where
  hp : p = 2 ∨ p = 3
  sys : IsBlockSystem p 𝓔
  hr : r.Prime
  h2 : r ≠ 2
  h3 : r ≠ 3
  hXr : IsElemAb r X
  hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔

section Aux

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

private theorem mem_normalizer_iff_cj_eq {H : Subgroup (LGL p V)} {x : LGL p V} :
    x ∈ Subgroup.normalizer (H : Set (LGL p V)) ↔ cj x H = H := by
  constructor
  · exact cj_eq_of_mem_normalizer
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : x * y * x⁻¹ ∈ cj x H ↔ x⁻¹ * (x * y * x⁻¹) * x ∈ H := mem_cj
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [h, e] at h1
    exact h1.symm

variable {𝓔 : Set (Subgroup (LGL p V))} {X : Subgroup (LGL p V)} {r : ℕ}

private theorem mem_centralizer_of_forall {d : LGL p V} (hdX : ∀ x ∈ X, x * d * x⁻¹ = d) :
    d ∈ Subgroup.centralizer (X : Set (LGL p V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * d = x * d * x⁻¹ * x := by group
    _ = d * x := by rw [hdX x hx]

private theorem exists_inner (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {h : LGL p V} (hh : h ∈ ⨆ E' ∈ 𝓔, E') :
    ∃ e₀ ∈ E, ∀ g ∈ E, h * g * h⁻¹ = e₀ * g * e₀⁻¹ := by
  let T : Subgroup (LGL p V) :=
    { carrier := {h | ∃ e₀ ∈ E, ∀ g ∈ E, h * g * h⁻¹ = e₀ * g * e₀⁻¹}
      one_mem' := ⟨1, E.one_mem, fun g _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩
        refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, fun g hg => ?_⟩
        have hg' : e₂ * g * e₂⁻¹ ∈ E := E.mul_mem (E.mul_mem he₂ hg) (E.inv_mem he₂)
        calc a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
          _ = a * (e₂ * g * e₂⁻¹) * a⁻¹ := by rw [h₂ g hg]
          _ = e₁ * (e₂ * g * e₂⁻¹) * e₁⁻¹ := h₁ _ hg'
          _ = (e₁ * e₂) * g * (e₁ * e₂)⁻¹ := by group
      inv_mem' := by
        rintro a ⟨e, he, h⟩
        refine ⟨e⁻¹, E.inv_mem he, fun g hg => ?_⟩
        have hg' : e⁻¹ * g * e ∈ E := E.mul_mem (E.mul_mem (E.inv_mem he) hg) he
        have h2 : a * (e⁻¹ * g * e) * a⁻¹ = g := by rw [h _ hg']; group
        calc a⁻¹ * g * a⁻¹⁻¹ = a⁻¹ * (a * (e⁻¹ * g * e) * a⁻¹) * a⁻¹⁻¹ := by rw [h2]
          _ = e⁻¹ * g * e⁻¹⁻¹ := by group }
  have hle : (⨆ E' ∈ 𝓔, E') ≤ T := by
    refine iSup₂_le fun E' hE' h hh => ?_
    by_cases hEE : E' = E
    · subst hEE
      exact ⟨h, hh, fun g _ => rfl⟩
    · refine ⟨1, E.one_mem, fun g hg => ?_⟩
      have hc := S.sys.commute E' hE' E hE hEE h hh g hg
      calc h * g * h⁻¹ = g * h * h⁻¹ := by rw [hc]
        _ = 1 * g * 1⁻¹ := by simp
  exact hle hh

end Aux

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

@[expose] noncomputable def trace (X : Subgroup (LGL p V)) : V →ₗ[ZMod p] V := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  exact ∑ x : X, ((x : LGL p V) : V →ₗ[ZMod p] V)

section

variable {𝓔 : Set (Subgroup (LGL p V))} {X : Subgroup (LGL p V)} {r : ℕ}

private theorem card_linearEquiv_dvd (hp : p = 2 ∨ p = 3) {W : Submodule (ZMod p) V}
    (hW : Nat.card W = p ^ 2) : Nat.card (W ≃ₗ[ZMod p] W) ∣ 48 := by
  have hfin : Module.finrank (ZMod p) W = 2 := by
    have h := card_eq_pow_finrank W
    rw [hW] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) W hfin
  let e : GL (Fin 2) (ZMod p) ≃* (W ≃ₗ[ZMod p] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) W)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  rcases hp with rfl | rfl <;> simp [Fin.prod_univ_two, ZMod.card]

theorem block_fixed_of_normalizes (hp : p = 2 ∨ p = 3) {E : Subgroup (LGL p V)} (hE : IsBlock p E)
    (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) {x : LGL p V} (hxr : x ^ r = 1)
    (hxE : cj x E = E) :
    (∀ w ∈ commSub E, x w = w) ∧ ∀ e ∈ E, x * e * x⁻¹ = e := by
  have hW : (commSub E).map (x : V →ₗ[ZMod p] V) = commSub E := by
    rw [← commSub_cj, hxE]
  let σ : commSub E ≃ₗ[ZMod p] commSub E :=
    LinearEquiv.ofSubmodules (x : V ≃ₗ[ZMod p] V) (commSub E) (commSub E) hW
  have hσ : ∀ (k : ℕ) (w : commSub E), (((σ ^ k) w : commSub E) : V) = (x ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, pow_succ]
      change (((σ ^ k) (σ w) : commSub E) : V) = (x ^ k) (x w)
      rw [ih]
      rfl
  have hσr : σ ^ r = 1 := by
    ext w
    rw [hσ, hxr]
    rfl
  have hcop : Nat.Coprime r 48 := by
    have h2c : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).mpr h2
    have h3c : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr h3
    have : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 4 h2c) h3c
  have hord1 : orderOf σ ∣ r := orderOf_dvd_of_pow_eq_one hσr
  have hord2 : orderOf σ ∣ 48 :=
    (orderOf_dvd_natCard σ).trans (card_linearEquiv_dvd hp hE.card_comm)
  have hσ1 : σ = 1 := by
    have : orderOf σ ∣ Nat.gcd r 48 := Nat.dvd_gcd hord1 hord2
    rw [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  have hfix : ∀ w ∈ commSub E, x w = w := by
    intro w hw
    have := hσ 1 ⟨w, hw⟩
    rw [hσ1] at this
    simpa using this.symm
  refine ⟨hfix, fun e he => ?_⟩
  have hxe : x * e * x⁻¹ ∈ E := by
    have : x * e * x⁻¹ ∈ cj x E := Subgroup.mem_map.mpr ⟨e, he, by simp [MulAut.conj_apply]⟩
    rwa [hxE] at this
  have hxinv : ∀ w ∈ commSub E, x⁻¹ w = w := by
    intro w hw
    have h : x⁻¹ (x w) = w := inv_apply_apply' x w
    rwa [hfix w hw] at h
  have key : (x * e * x⁻¹) * e⁻¹ = 1 := by
    apply hE.faithful _ (E.mul_mem hxe (E.inv_mem he))
    intro w hw
    have hu : e⁻¹ w ∈ commSub E := map_mem_commSub E (E.inv_mem he) hw
    have h1 : x⁻¹ (e⁻¹ w) = e⁻¹ w := hxinv _ hu
    have h2 : e (e⁻¹ w) = w := apply_inv_apply' e w
    change x (e (x⁻¹ (e⁻¹ w))) = w
    rw [h1, h2]
    exact hfix w hw
  exact mul_inv_eq_one.mp key

private theorem trace_apply (X : Subgroup (LGL p V)) [Fintype X] (w : V) :
    trace X w = ∑ x : X, (x : LGL p V) w := by
  classical
  unfold trace
  simp only [LinearMap.sum_apply]
  congr
  exact Subsingleton.elim _ _

theorem trace_mem_fixSub (w : V) : trace X w ∈ fixSub X := by
  classical
  have : Fintype X := Fintype.ofFinite X
  rw [trace_apply]
  intro y hy
  rw [map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : X)) _ _ (fun x => rfl)

theorem trace_injOn (hp : p = 2 ∨ p = 3) (h𝓔 : IsBlockSystem p 𝓔) (hr : r.Prime) (h2 : r ≠ 2)
    (h3 : r ≠ 3) (hXr : IsElemAb r X) (hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔)
    {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔) {w : V} (hw : w ∈ commSub E) (h0 : trace X w = 0) :
    w = 0 := by
  classical
  have : Fintype X := Fintype.ofFinite X
  set N : Subgroup (LGL p V) := Subgroup.normalizer (E : Set (LGL p V)) with hN
  have hfix : ∀ x : X, (x : LGL p V) ∈ N → (x : LGL p V) w = w := fun x hxN =>
    (block_fixed_of_normalizes hp (h𝓔.isBlock E hE) hr h2 h3 (hXr.2 x x.2)
      (cj_eq_of_mem_normalizer hxN)).1 w hw
  let R : Submodule (ZMod p) V := ⨆ (j : 𝓔) (_ : j ≠ ⟨E, hE⟩), commSub (j : Subgroup (LGL p V))
  have hdisj : Disjoint (commSub E) R := h𝓔.indep ⟨E, hE⟩
  have hmem : ∀ x : X, (x : LGL p V) ∉ N → (x : LGL p V) w ∈ R := by
    intro x hxN
    have hne : (⟨cj (x : LGL p V) E, hX x x.2 E hE⟩ : 𝓔) ≠ ⟨E, hE⟩ := by
      intro h
      apply hxN
      exact mem_normalizer_iff_cj_eq.mpr (congrArg Subtype.val h)
    have hxw : (x : LGL p V) w ∈ commSub (cj (x : LGL p V) E) := by
      rw [commSub_cj]
      exact Submodule.mem_map_of_mem hw
    have hle : commSub (cj (x : LGL p V) E) ≤ R :=
      le_iSup₂_of_le (⟨cj (x : LGL p V) E, hX x x.2 E hE⟩ : 𝓔) hne le_rfl
    exact hle hxw
  set n := (Finset.univ.filter (fun x : X => (x : LGL p V) ∈ N)).card with hn
  have hsplit : trace X w = n • w +
      ∑ x ∈ Finset.univ.filter (fun x : X => (x : LGL p V) ∉ N), (x : LGL p V) w := by
    rw [trace_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : X => (x : LGL p V) ∈ N) (fun x : X => (x : LGL p V) w)]
    congr 1
    rw [Finset.sum_congr rfl (fun x hx => hfix x (Finset.mem_filter.mp hx).2)]
    simp [hn]
  have hndvd : ¬ p ∣ n := by
    have hcard : n = Nat.card (N.subgroupOf X) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    have hdvd : n ∣ Nat.card X := hcard ▸ Subgroup.card_subgroup_dvd_card _
    have : Fact r.Prime := ⟨hr⟩
    have hXp : IsPGroup r X := fun x => ⟨1, by simpa using Subtype.ext (hXr.2 x x.2)⟩
    obtain ⟨m, hm⟩ := hXp.exists_card_eq
    intro hpn
    have hpr : p ∣ r ^ m := hm ▸ hpn.trans hdvd
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hpr)
    rcases hp with rfl | rfl
    · exact h2 this.symm
    · exact h3 this.symm
  have hsum_mem : ∑ x ∈ Finset.univ.filter (fun x : X => (x : LGL p V) ∉ N),
      (x : LGL p V) w ∈ R :=
    Submodule.sum_mem _ (fun x hx => hmem x (Finset.mem_filter.mp hx).2)
  have h1 : n • w = -(∑ x ∈ Finset.univ.filter (fun x : X => (x : LGL p V) ∉ N),
      (x : LGL p V) w) := by
    rw [hsplit] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h2' : n • w ∈ R := by
    rw [h1]
    exact Submodule.neg_mem _ hsum_mem
  have h3' : n • w ∈ commSub E := nsmul_mem hw n
  have h4 : n • w = 0 := (Submodule.disjoint_def.mp hdisj) _ h3' h2'
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)] at h4
  rcases smul_eq_zero.mp h4 with h | h
  · exact absurd ((CharP.cast_eq_zero_iff (ZMod p) p n).mp h) hndvd
  · exact h


end

section Diag

variable {𝓔 : Set (Subgroup (LGL p V))} {X : Subgroup (LGL p V)} {r : ℕ}

private theorem DiagSetup.fixed (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {x : LGL p V} (hx : x ∈ X) (hxE : cj x E = E) :
    (∀ w ∈ commSub E, x w = w) ∧ ∀ e ∈ E, x * e * x⁻¹ = e :=
  block_fixed_of_normalizes S.hp (S.sys.isBlock E hE) S.hr S.h2 S.h3 (S.hXr.2 x hx) hxE

private noncomputable def orbitSet (X E : Subgroup (LGL p V)) : Finset (Subgroup (LGL p V)) :=
  (Set.toFinite {E' | ∃ x ∈ X, cj x E = E'}).toFinset

private theorem mem_orbitSet {E E' : Subgroup (LGL p V)} :
    E' ∈ orbitSet X E ↔ ∃ x ∈ X, cj x E = E' := by
  unfold orbitSet
  rw [Set.Finite.mem_toFinset]
  rfl

open Classical in
private noncomputable def diagFam (X E : Subgroup (LGL p V)) (e : LGL p V) :
    Subgroup (LGL p V) → LGL p V := fun E' =>
  if h : ∃ x ∈ X, cj x E = E' then h.choose * e * h.choose⁻¹ else 1

private theorem diagFam_cj (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {e : LGL p V} (he : e ∈ E) {x : LGL p V} (hx : x ∈ X) :
    diagFam X E e (cj x E) = x * e * x⁻¹ := by
  classical
  have h : ∃ x' ∈ X, cj x' E = cj x E := ⟨x, hx, rfl⟩
  simp only [diagFam, h, ↓reduceDIte]
  obtain ⟨hx'X, hx'E⟩ := h.choose_spec
  set x' := h.choose with hx'
  have hstab : cj (x'⁻¹ * x) E = E := by rw [cj_mul, ← hx'E, cj_inv_cj]
  have key := (S.fixed hE (X.mul_mem (X.inv_mem hx'X) hx) hstab).2 e he
  calc x' * e * x'⁻¹ = x' * ((x'⁻¹ * x) * e * (x'⁻¹ * x)⁻¹) * x'⁻¹ := by rw [key]
    _ = x * e * x⁻¹ := by group

private theorem orbit_mem (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {E' : Subgroup (LGL p V)} (h : E' ∈ orbitSet X E) : E' ∈ 𝓔 := by
  obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp h
  exact S.hX x hx E hE

private theorem self_mem_orbit (E : Subgroup (LGL p V)) : E ∈ orbitSet X E :=
  mem_orbitSet.mpr ⟨1, X.one_mem, cj_one E⟩

private theorem diagFam_self (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {e : LGL p V} (he : e ∈ E) : diagFam X E e E = e := by
  have := diagFam_cj S hE he X.one_mem
  rwa [cj_one, one_mul, inv_one, mul_one] at this

private theorem diagFam_mem (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {e : LGL p V} (he : e ∈ E) {E' : Subgroup (LGL p V)} (h : E' ∈ orbitSet X E) :
    diagFam X E e E' ∈ E' := by
  obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp h
  rw [diagFam_cj S hE he hx]
  exact Subgroup.mem_map.mpr ⟨e, he, by simp [MulAut.conj_apply]⟩

private theorem diagFam_comm (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    {e e' : LGL p V} (he : e ∈ E) (he' : e' ∈ E) :
    ((orbitSet X E : Finset (Subgroup (LGL p V))) : Set (Subgroup (LGL p V))).Pairwise
      fun E₁ E₂ => Commute (diagFam X E e E₁) (diagFam X E e' E₂) := by
  intro E₁ h₁ E₂ h₂ hne
  exact S.sys.commute E₁ (orbit_mem S hE h₁) E₂ (orbit_mem S hE h₂) hne _
    (diagFam_mem S hE he h₁) _ (diagFam_mem S hE he' h₂)

omit [Finite V] in
private theorem noncommProd_apply (h𝓔 : IsBlockSystem p 𝓔) (f : Subgroup (LGL p V) → LGL p V) :
    ∀ (s : Finset (Subgroup (LGL p V))) (_ : ∀ E ∈ s, E ∈ 𝓔) (_ : ∀ E ∈ s, f E ∈ E)
      (comm : (s : Set (Subgroup (LGL p V))).Pairwise (Commute on f)) (v : V),
      (s.noncommProd f comm) v = v + ∑ E ∈ s, (f E v - v) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro hs hf comm v; simp
  | insert a s ha ih =>
    intro hs hf comm v
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    change f a ((s.noncommProd f _) v) = _
    rw [ih (fun E hE => hs E (Finset.mem_insert_of_mem hE))
      (fun E hE => hf E (Finset.mem_insert_of_mem hE))
      (comm.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))) v,
      Finset.sum_insert ha, map_add, map_sum]
    have : ∀ E ∈ s, f a (f E v - v) = f E v - v := by
      intro E hE
      exact h𝓔.trivial_on a (hs a (Finset.mem_insert_self a s)) E
        (hs E (Finset.mem_insert_of_mem hE)) (fun h => ha (h ▸ hE)) (f a)
        (hf a (Finset.mem_insert_self a s)) _
        (sub_mem_commSub E (hf E (Finset.mem_insert_of_mem hE)) v)
    rw [Finset.sum_congr rfl this]
    abel

omit [Finite V] in
private theorem noncommProd_apply_of_mem (h𝓔 : IsBlockSystem p 𝓔)
    (f : Subgroup (LGL p V) → LGL p V) (s : Finset (Subgroup (LGL p V)))
    (hs : ∀ E ∈ s, E ∈ 𝓔) (hf : ∀ E ∈ s, f E ∈ E)
    (comm : (s : Set (Subgroup (LGL p V))).Pairwise (Commute on f))
    {E₀ : Subgroup (LGL p V)} (hE₀ : E₀ ∈ s) {w : V} (hw : w ∈ commSub E₀) :
    (s.noncommProd f comm) w = f E₀ w := by
  classical
  rw [noncommProd_apply h𝓔 f s hs hf comm w, Finset.sum_eq_single E₀]
  · abel
  · intro E hE hne
    rw [h𝓔.trivial_on E (hs E hE) E₀ (hs E₀ hE₀) hne (f E) (hf E hE) w hw, sub_self]
  · intro h
    exact absurd hE₀ h

private noncomputable def diagHom (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔) :
    E →* LGL p V where
  toFun e := (orbitSet X E).noncommProd (diagFam X E e) (diagFam_comm S hE e.2 e.2)
  map_one' := by
    rw [Finset.noncommProd_eq_pow_card _ _ _ (1 : LGL p V)]
    · simp
    · intro E' hE'
      obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp hE'
      have := diagFam_cj S hE (1 : E).2 hx
      simpa using this
  map_mul' e e' := by
    have := Finset.noncommProd_mul_distrib (s := orbitSet X E) (diagFam X E e.1)
      (diagFam X E e'.1) (diagFam_comm S hE e.2 e.2) (diagFam_comm S hE e'.2 e'.2)
      (diagFam_comm S hE e'.2 e.2)
    rw [← this]
    apply Finset.noncommProd_congr rfl
    intro E' hE'
    obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp hE'
    simp only [Pi.mul_apply]
    rw [diagFam_cj S hE (e * e').2 hx, diagFam_cj S hE e.2 hx, diagFam_cj S hE e'.2 hx]
    simp only [Subgroup.coe_mul]
    group

private theorem diagHom_apply (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    (e : E) (v : V) :
    diagHom S hE e v = v + ∑ E' ∈ orbitSet X E, (diagFam X E e E' v - v) :=
  noncommProd_apply S.sys (diagFam X E e) (orbitSet X E) (fun _ h => orbit_mem S hE h)
    (fun _ h => diagFam_mem S hE e.2 h) (diagFam_comm S hE e.2 e.2) v

private theorem diagHom_apply_block (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)}
    (hE : E ∈ 𝓔) (e : E) {E₀ : Subgroup (LGL p V)} (hE₀ : E₀ ∈ orbitSet X E) {w : V}
    (hw : w ∈ commSub E₀) : diagHom S hE e w = diagFam X E e E₀ w :=
  noncommProd_apply_of_mem S.sys (diagFam X E e) (orbitSet X E) (fun _ h => orbit_mem S hE h)
    (fun _ h => diagFam_mem S hE e.2 h) (diagFam_comm S hE e.2 e.2) hE₀ hw

private theorem diagHom_mem (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    (e : E) : diagHom S hE e ∈ ⨆ E' ∈ 𝓔, E' := by
  refine Finset.noncommProd_induction (orbitSet X E) (diagFam X E e) (diagFam_comm S hE e.2 e.2)
    (fun g => g ∈ ⨆ E' ∈ 𝓔, E') (fun a b ha hb => Subgroup.mul_mem _ ha hb) (Subgroup.one_mem _)
    (fun E' h => ?_)
  exact (le_iSup₂ (f := fun E' (_ : E' ∈ 𝓔) => E') E' (orbit_mem S hE h))
    (diagFam_mem S hE e.2 h)

private theorem diagHom_conj (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    (e : E) {g : LGL p V} (hg : g ∈ E) :
    diagHom S hE e * g * (diagHom S hE e)⁻¹ = e * g * (e : LGL p V)⁻¹ := by
  classical
  have hEs : E ∈ orbitSet X E := self_mem_orbit E
  let R := ((orbitSet X E).erase E).noncommProd (diagFam X E e)
    (fun _ hx _ hy hxy => diagFam_comm S hE e.2 e.2 (Finset.mem_of_mem_erase hx)
      (Finset.mem_of_mem_erase hy) hxy)
  have hsplit : diagHom S hE e = e * R := by
    have := Finset.mul_noncommProd_erase (orbitSet X E) hEs (diagFam X E e)
      (diagFam_comm S hE e.2 e.2)
    rw [diagFam_self S hE e.2] at this
    exact this.symm
  have hR : Commute g R := by
    apply Finset.noncommProd_commute
    intro E' hE'
    have hne : E ≠ E' := fun h => (Finset.mem_erase.mp hE').1 h.symm
    exact S.sys.commute E hE E' (orbit_mem S hE (Finset.mem_of_mem_erase hE')) hne g hg _
      (diagFam_mem S hE e.2 (Finset.mem_of_mem_erase hE'))
  have hRg : R * g * R⁻¹ = g := by
    rw [← hR.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hsplit]
  calc (e * R : LGL p V) * g * ((e : LGL p V) * R)⁻¹
      = e * (R * g * R⁻¹) * (e : LGL p V)⁻¹ := by group
    _ = e * g * (e : LGL p V)⁻¹ := by rw [hRg]

private theorem diagHom_comm_X (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    (e : E) {y : LGL p V} (hy : y ∈ X) : y * diagHom S hE e * y⁻¹ = diagHom S hE e := by
  classical
  apply LinearEquiv.ext
  intro v
  change y (diagHom S hE e (y⁻¹ v)) = diagHom S hE e v
  rw [diagHom_apply S hE e (y⁻¹ v), diagHom_apply S hE e v, map_add, map_sum]
  have h1 : y (y⁻¹ v) = v := apply_inv_apply' y v
  have hconj : ∀ E' ∈ orbitSet X E, ∀ u : V,
      y (diagFam X E e E' (y⁻¹ u)) = diagFam X E e (cj y E') u := by
    intro E' hE' u
    obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp hE'
    have h2 : y * diagFam X E e (cj x E) * y⁻¹ = diagFam X E e (cj y (cj x E)) := by
      rw [← cj_mul, diagFam_cj S hE e.2 hx, diagFam_cj S hE e.2 (X.mul_mem hy hx)]
      group
    exact congrArg (fun g : LGL p V => g u) h2
  have hsum : ∑ E' ∈ orbitSet X E, (diagFam X E e (cj y E') v - v) =
      ∑ E' ∈ orbitSet X E, (diagFam X E e E' v - v) := by
    refine Finset.sum_nbij' (fun E' => cj y E') (fun E' => cj y⁻¹ E') ?_ ?_ ?_ ?_ ?_
    · intro E' hE'
      obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp hE'
      exact mem_orbitSet.mpr ⟨y * x, X.mul_mem hy hx, cj_mul y x E⟩
    · intro E' hE'
      obtain ⟨x, hx, rfl⟩ := mem_orbitSet.mp hE'
      exact mem_orbitSet.mpr ⟨y⁻¹ * x, X.mul_mem (X.inv_mem hy) hx, cj_mul y⁻¹ x E⟩
    · intro E' _
      exact cj_inv_cj y E'
    · intro E' _
      exact cj_cj_inv y E'
    · intro E' _
      rfl
  have hterm : ∀ E' ∈ orbitSet X E, y (diagFam X E e E' (y⁻¹ v) - y⁻¹ v) =
      diagFam X E e (cj y E') v - v := by
    intro E' hE'
    rw [map_sub, hconj E' hE' v, h1]
  rw [h1, Finset.sum_congr rfl hterm, hsum]

private theorem diagHom_trace (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔)
    (e : E) {w : V} (hw : w ∈ commSub E) :
    diagHom S hE e (trace X w) = trace X ((e : LGL p V) w) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  rw [trace_apply, trace_apply, map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hxw : (x : LGL p V) w ∈ commSub (cj (x : LGL p V) E) := by
    rw [commSub_cj]
    exact Submodule.mem_map_of_mem hw
  have hxO : cj (x : LGL p V) E ∈ orbitSet X E := mem_orbitSet.mpr ⟨x, x.2, rfl⟩
  rw [diagHom_apply_block S hE e hxO hxw, diagFam_cj S hE e.2 x.2]
  change (x : LGL p V) ((e : LGL p V) ((x : LGL p V)⁻¹ ((x : LGL p V) w))) =
    (x : LGL p V) ((e : LGL p V) w)
  rw [inv_apply_apply']

theorem exists_diag (hp : p = 2 ∨ p = 3) (h𝓔 : IsBlockSystem p 𝓔) (hr : r.Prime) (h2 : r ≠ 2)
    (h3 : r ≠ 3) (hXr : IsElemAb r X) (hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔)
    {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔) {e : LGL p V} (he : e ∈ E) :
    ∃ d : LGL p V, (∀ x ∈ X, x * d * x⁻¹ = d) ∧ d ∈ (⨆ E' ∈ 𝓔, E') ∧
      (∀ g ∈ E, d * g * d⁻¹ = e * g * e⁻¹) ∧
      (∀ w ∈ commSub E, d (trace X w) = trace X (e w)) ∧ (∀ k : ℕ, e ^ k = 1 → d ^ k = 1) := by
  have S : DiagSetup p r 𝓔 X := ⟨hp, h𝓔, hr, h2, h3, hXr, hX⟩
  refine ⟨diagHom S hE ⟨e, he⟩, fun x hx => diagHom_comm_X S hE ⟨e, he⟩ hx,
    diagHom_mem S hE ⟨e, he⟩, fun g hg => diagHom_conj S hE ⟨e, he⟩ hg,
    fun w hw => diagHom_trace S hE ⟨e, he⟩ hw, fun k hk => ?_⟩
  have : (⟨e, he⟩ : E) ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [← map_pow, this, map_one]

omit [Fact p.Prime] [Finite V] in
private theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P A : Subgroup G} (hP : IsSyl q P H) (hAH : A ≤ H) (hA : IsPGroup q A) :
    ∃ h ∈ H, ∀ a ∈ A, h⁻¹ * a * h ∈ P := by
  obtain ⟨P', rfl⟩ := hP
  have hA' : IsPGroup q (A.subgroupOf H) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q
  refine ⟨g, g.2, fun a ha => ?_⟩
  have haQ : (⟨a, hAH ha⟩ : H) ∈ (Q : Subgroup H) := hQ ha
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haQ
  exact ⟨_, haQ, by simp⟩

theorem diag_gen (hp : p = 2 ∨ p = 3) (h𝓔 : IsBlockSystem p 𝓔) (hr : r.Prime) (h2 : r ≠ 2)
    (h3 : r ≠ 3) (hXr : IsElemAb r X) (hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔)
    {P : Subgroup (LGL p V)} (hP : IsSyl p P (⨆ E ∈ 𝓔, E)) :
    (⨆ E ∈ 𝓔, E) ≤ ((⨆ E ∈ 𝓔, E) ⊓ Subgroup.centralizer (X : Set (LGL p V))) ⊔ P := by
  have S : DiagSetup p r 𝓔 X := ⟨hp, h𝓔, hr, h2, h3, hXr, hX⟩
  set H : Subgroup (LGL p V) := ⨆ E ∈ 𝓔, E with hH
  set M : Subgroup (LGL p V) := (H ⊓ Subgroup.centralizer (X : Set (LGL p V))) ⊔ P with hM
  refine iSup₂_le fun E hE => ?_
  have hEH : E ≤ H := le_iSup₂ (f := fun E' (_ : E' ∈ 𝓔) => E') E hE
  obtain ⟨A, hAE, hAcard, hgen⟩ := (h𝓔.isBlock E hE).gen
  have hApg : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])
  obtain ⟨h, hhH, hhA⟩ := exists_conj_le_sylow hP (hAE.trans hEH) hApg
  obtain ⟨e₁, he₁, hinner⟩ := exists_inner S hE (H.inv_mem hhH)
  have hdiag : ∀ e'' ∈ E, ∀ y ∈ P ⊓ E, e'' * y * e''⁻¹ ∈ M := by
    intro e'' he'' y hy
    obtain ⟨d, hdX, hdH, hdg, -, -⟩ := exists_diag hp h𝓔 hr h2 h3 hXr hX hE he''
    have hdM : d ∈ M :=
      Subgroup.mem_sup_left ⟨hdH, mem_centralizer_of_forall hdX⟩
    rw [← hdg y hy.2]
    exact M.mul_mem (M.mul_mem hdM (Subgroup.mem_sup_right hy.1)) (M.inv_mem hdM)
  have hle : (⨆ e ∈ E, cj e A) ≤ M := by
    refine iSup₂_le fun e' he' a ha => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have h1 : h⁻¹ * a₀ * h ∈ P := hhA a₀ ha₀
    have h1' : e₁ * a₀ * e₁⁻¹ ∈ P := by
      have := hinner a₀ (hAE ha₀)
      rw [inv_inv] at this
      rw [← this]
      exact h1
    have h2' : e₁ * a₀ * e₁⁻¹ ∈ E := E.mul_mem (E.mul_mem he₁ (hAE ha₀)) (E.inv_mem he₁)
    have h3' := hdiag (e' * e₁⁻¹) (E.mul_mem he' (E.inv_mem he₁)) _ ⟨h1', h2'⟩
    have e : (e' * e₁⁻¹) * (e₁ * a₀ * e₁⁻¹) * (e' * e₁⁻¹)⁻¹ = e' * a₀ * e'⁻¹ := by group
    rw [e] at h3'
    exact h3'
  rw [← hgen]
  exact hle

private theorem trace_plane (S : DiagSetup p r 𝓔 X) {E : Subgroup (LGL p V)} (hE : E ∈ 𝓔) :
    (commSub E).map (trace X) ≤ fixSub X ∧ Nat.card ((commSub E).map (trace X)) = p ^ 2 := by
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨u, -, rfl⟩ := Submodule.mem_map.mp hw
    exact trace_mem_fixSub u
  · have hbij : Function.Bijective (fun u : commSub E =>
        (⟨trace X (u : V), Submodule.mem_map_of_mem u.2⟩ : (commSub E).map (trace X))) := by
      constructor
      · intro u u' h
        have h1 : trace X (u : V) = trace X (u' : V) := congrArg Subtype.val h
        have := trace_injOn S.hp S.sys S.hr S.h2 S.h3 S.hXr S.hX hE
          (Submodule.sub_mem _ u.2 u'.2) (by rw [map_sub, h1, sub_self])
        exact Subtype.ext (sub_eq_zero.mp this)
      · rintro ⟨_, ⟨u, hu, rfl⟩⟩
        exact ⟨⟨u, hu⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact (S.sys.isBlock E hE).card_comm

theorem diag_two (hp : p = 2) (h𝓔 : IsBlockSystem p 𝓔) (hne : 𝓔.Nonempty) (hr : r.Prime)
    (h2 : r ≠ 2) (h3 : r ≠ 3) (hXr : IsElemAb r X)
    (hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔) :
    ∃ W : Submodule (ZMod p) V, W ≤ fixSub X ∧ Nat.card W = p ^ 2 ∧
      ∃ d ∈ (⨆ E ∈ 𝓔, E) ⊓ Subgroup.centralizer (X : Set (LGL p V)),
        d ^ 3 = 1 ∧ (∀ w ∈ W, d w ∈ W) ∧ ∀ w ∈ W, d w = w → w = 0 := by
  obtain ⟨E, hE⟩ := hne
  have hp' : p = 2 ∨ p = 3 := Or.inl hp
  have S : DiagSetup p r 𝓔 X := ⟨hp', h𝓔, hr, h2, h3, hXr, hX⟩
  obtain ⟨hW1, hW2⟩ := trace_plane S hE
  obtain ⟨e, heE, he3, hefix⟩ := (h𝓔.isBlock E hE).exists_order_three hp
  obtain ⟨d, hdX, hdH, -, hdtr, hdpow⟩ := exists_diag hp' h𝓔 hr h2 h3 hXr hX hE heE
  refine ⟨(commSub E).map (trace X), hW1, hW2, d, ⟨hdH, mem_centralizer_of_forall hdX⟩,
    hdpow 3 he3, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    rw [hdtr u hu]
    exact Submodule.mem_map_of_mem (map_mem_commSub E heE hu)
  · intro w hw hfix
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    rw [hdtr u hu] at hfix
    have h1 : trace X ((e : LGL p V) u - u) = 0 := by rw [map_sub, hfix, sub_self]
    have h2' := trace_injOn hp' h𝓔 hr h2 h3 hXr hX hE
      (Submodule.sub_mem _ (map_mem_commSub E heE hu) hu) h1
    have h3' : u = 0 := hefix u hu (sub_eq_zero.mp h2')
    rw [h3', map_zero]

private theorem exists_basis_comm {E : Subgroup (LGL p V)} (hE : IsBlock p E) :
    ∃ b : Fin 2 → V, LinearIndependent (ZMod p) b ∧
      Submodule.span (ZMod p) (Set.range b) = commSub E := by
  have hfin : Module.finrank (ZMod p) (commSub E) = 2 := by
    have h := card_eq_pow_finrank (commSub E)
    rw [hE.card_comm] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (commSub E) hfin
  refine ⟨fun i => (b i : V), ?_, ?_⟩
  · exact b.linearIndependent.map' (commSub E).subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i => (b i : V)) = (commSub E).subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem diag_three (hp : p = 3) (h𝓔 : IsBlockSystem p 𝓔) (hne : 𝓔.Nonempty) (hr : r.Prime)
    (h2 : r ≠ 2) (h3 : r ≠ 3) (hXr : IsElemAb r X)
    (hX : ∀ x ∈ X, ∀ E ∈ 𝓔, cj x E ∈ 𝓔) :
    ∃ W : Submodule (ZMod p) V, W ≤ fixSub X ∧ Nat.card W = p ^ 2 ∧
      ∃ D : Subgroup (LGL p V), D ≤ (⨆ E ∈ 𝓔, E) ⊓ Subgroup.centralizer (X : Set (LGL p V)) ∧
        ∃ φ : D →* SL(2, ZMod p), Function.Surjective φ := by
  obtain ⟨E, hE⟩ := hne
  have hp' : p = 2 ∨ p = 3 := Or.inr hp
  have S : DiagSetup p r 𝓔 X := ⟨hp', h𝓔, hr, h2, h3, hXr, hX⟩
  obtain ⟨hW1, hW2⟩ := trace_plane S hE
  have hinj : Function.Injective (diagHom S hE) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hfix : ∀ w ∈ commSub E, (e : LGL p V) w = w := by
      intro w hw
      have h1 := diagHom_trace S hE e hw
      rw [he] at h1
      have h1' : trace X w = trace X ((e : LGL p V) w) := h1
      have h2' : trace X ((e : LGL p V) w - w) = 0 := by rw [map_sub, ← h1', sub_self]
      have := trace_injOn hp' h𝓔 hr h2 h3 hXr hX hE
        (Submodule.sub_mem _ (map_mem_commSub E e.2 hw) hw) h2'
      exact sub_eq_zero.mp this
    exact Subtype.ext ((h𝓔.isBlock E hE).faithful e e.2 hfix)
  obtain ⟨b, hb, hspan⟩ := exists_basis_comm (h𝓔.isBlock E hE)
  obtain ⟨Φ, -⟩ := (h𝓔.isBlock E hE).exists_mulEquiv b hb hspan
  refine ⟨(commSub E).map (trace X), hW1, hW2, (diagHom S hE).range, ?_,
    Φ.toMonoidHom.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom, ?_⟩
  · intro g hg
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨diagHom_mem S hE e, mem_centralizer_of_forall (fun x hx => diagHom_comm_X S hE e hx)⟩
  · exact Φ.surjective.comp (MonoidHom.ofInjective hinj).symm.surjective

end Diag

end CFSG.SignalizerFunctorTheorem.Quadratic
