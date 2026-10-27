module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Semilinear
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

private theorem perm_apply_inv_self {α : Type*} (a : Equiv.Perm α) (u : α) :
    a (a⁻¹ u) = u := by
  rw [Equiv.Perm.inv_def]
  exact a.apply_symm_apply u

private theorem zero_of_isSemilinear {K : Type*} [Field K] {σ : RingAut K}
    {a : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a) : a 0 = 0 := by
  simpa using ha.2 0 0

private theorem isSemilinear_one {K : Type*} [Field K] :
    IsSemilinear (1 : RingAut K) (1 : Equiv.Perm (Fin 2 → K)) := by
  unfold IsSemilinear
  exact ⟨fun _ _ => rfl, fun _ _ => by simp⟩

private theorem isSemilinear_mul {K : Type*} [Field K] {σ τ : RingAut K}
    {a b : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a) (hb : IsSemilinear τ b) :
    IsSemilinear (σ * τ) (a * b) := by
  unfold IsSemilinear
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · simp only [Equiv.Perm.mul_apply, hb.1, ha.1]
  · simp only [Equiv.Perm.mul_apply, hb.2, ha.2, RingAut.mul_apply]

private theorem inv_add_of_isSemilinear {K : Type*} [Field K] {σ : RingAut K}
    {a : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a) (u u' : Fin 2 → K) :
    a⁻¹ (u + u') = a⁻¹ u + a⁻¹ u' := by
  apply a.injective
  rw [perm_apply_inv_self, ha.1, perm_apply_inv_self, perm_apply_inv_self]

private theorem inv_smul_of_isSemilinear {K : Type*} [Field K] {σ : RingAut K}
    {a : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a) (c : K) (u : Fin 2 → K) :
    a⁻¹ (σ c • u) = c • a⁻¹ u := by
  apply a.injective
  rw [perm_apply_inv_self, ha.2, perm_apply_inv_self]

private theorem isSemilinear_inv {K : Type*} [Field K] {a : Equiv.Perm (Fin 2 → K)}
    (ha : IsSemilinear (1 : RingAut K) a) : IsSemilinear (1 : RingAut K) a⁻¹ := by
  unfold IsSemilinear
  refine ⟨inv_add_of_isSemilinear ha, fun c u => ?_⟩
  simpa using inv_smul_of_isSemilinear ha c u

private theorem isSemilinear_conj {K : Type*} [Field K] {σ : RingAut K}
    {a g : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a)
    (hg : IsSemilinear (1 : RingAut K) g) :
    IsSemilinear (1 : RingAut K) (a⁻¹ * g * a) := by
  unfold IsSemilinear
  refine ⟨fun u u' => ?_, fun c u => ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    rw [ha.1, hg.1, inv_add_of_isSemilinear ha]
  · simp only [Equiv.Perm.mul_apply, RingAut.one_apply]
    rw [ha.2, hg.2]
    simp only [RingAut.one_apply]
    exact inv_smul_of_isSemilinear ha c _

private theorem ringAut_eq_of_isSemilinear {K : Type*} [Field K] {σ τ : RingAut K}
    {a : Equiv.Perm (Fin 2 → K)} (ha : IsSemilinear σ a) (hb : IsSemilinear τ a) : σ = τ := by
  have hu : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  apply RingEquiv.ext
  intro c
  have h1 : a (c • a⁻¹ ![1, 0]) = σ c • ![1, 0] := by
    rw [ha.2, perm_apply_inv_self]
  have h2 : a (c • a⁻¹ ![1, 0]) = τ c • ![1, 0] := by
    rw [hb.2, perm_apply_inv_self]
  exact smul_left_injective K hu (h1.symm.trans h2)

private theorem pow_two_pow_injective (K : Type*) [Field K] [CharP K 2] (k : ℕ) :
    Function.Injective (fun x : K => x ^ 2 ^ k) := by
  intro x y hxy
  apply (iterateFrobenius K 2 k).injective
  simpa [iterateFrobenius_def] using hxy

private theorem pow_apply_of_eigen {K : Type*} [Field K] {g : Equiv.Perm (Fin 2 → K)}
    (hg : IsSemilinear (1 : RingAut K) g) {v : Fin 2 → K} {μ : K} (hv : g v = μ • v) (n : ℕ) :
    (g ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hg.2, RingAut.one_apply, hv, smul_smul, pow_succ]

private theorem exists_comb_of_det_ne_zero {K : Type*} [Field K] {v₁ v₂ : Fin 2 → K}
    (hd : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) (w : Fin 2 → K) :
    ∃ a b : K, w = a • v₁ + b • v₂ := by
  have hD : (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0) * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)⁻¹ = 1 :=
    mul_inv_cancel₀ hd
  refine ⟨(w 0 * v₂ 1 - w 1 * v₂ 0) * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)⁻¹,
    (v₁ 0 * w 1 - v₁ 1 * w 0) * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)⁻¹, ?_⟩
  funext i
  fin_cases i
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
    linear_combination (-(w 0)) * hD
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one]
    linear_combination (-(w 1)) * hD

private theorem exists_smul_of_det_eq_zero {K : Type*} [Field K] {v₁ v₂ : Fin 2 → K}
    (hv₁ : v₁ ≠ 0) (hd : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 = 0) : ∃ c : K, v₂ = c • v₁ := by
  by_cases h0 : v₁ 0 = 0
  · have h1 : v₁ 1 ≠ 0 := by
      intro h1
      apply hv₁
      funext i
      fin_cases i <;> simp [h0, h1]
    have hv20 : v₂ 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_left h1
    refine ⟨v₂ 1 / v₁ 1, ?_⟩
    funext i
    fin_cases i
    · simp [h0, hv20]
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
      rw [div_mul_cancel₀ (v₂ 1) h1]
  · refine ⟨v₂ 0 / v₁ 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
      rw [div_mul_cancel₀ (v₂ 0) h0]
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hd

private theorem scalar_of_two_eigenvectors {K : Type*} [Field K] [CharP K 2]
    {g : Equiv.Perm (Fin 2 → K)} (hg : IsSemilinear (1 : RingAut K) g) {k : ℕ} {c : K}
    (hgk : ∀ v, (g ^ 2 ^ k) v = c • v) {v₁ v₂ : Fin 2 → K} {μ₁ μ₂ : K}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (he₁ : g v₁ = μ₁ • v₁) (he₂ : g v₂ = μ₂ • v₂)
    (hd : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) : ∃ d : K, ∀ v, g v = d • v := by
  have hc₁ : μ₁ ^ 2 ^ k = c := by
    have h := hgk v₁
    rw [pow_apply_of_eigen hg he₁] at h
    exact smul_left_injective K hv₁ h
  have hc₂ : μ₂ ^ 2 ^ k = c := by
    have h := hgk v₂
    rw [pow_apply_of_eigen hg he₂] at h
    exact smul_left_injective K hv₂ h
  have hμ : μ₁ = μ₂ := pow_two_pow_injective K k (hc₁.trans hc₂.symm)
  subst hμ
  have hlin : ∀ (a : K) (v : Fin 2 → K), g (a • v) = a • g v := by
    intro a v
    rw [hg.2, RingAut.one_apply]
  refine ⟨μ₁, fun w => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_comb_of_det_ne_zero hd w
  rw [hg.1, hlin, hlin, he₁, he₂]
  module

private theorem card_projectivization_mod_two (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Nat.card (Projectivization K (Fin 2 → K)) % 2 = 1 := by
  have h := Projectivization.card K (Fin 2 → K)
  rw [Nat.card_fun, Nat.card_fin] at h
  have h2 : 2 ∣ Nat.card K := by
    have hc : addOrderOf (1 : K) = 2 := CharP.eq K (CharP.addOrderOf_one K) inferInstance
    have := addOrderOf_dvd_natCard (1 : K)
    rwa [hc] at this
  have hq0 : 0 < Nat.card K := Nat.card_pos
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h3 : 2 ∣ Nat.card K ^ 2 := dvd_pow h2 two_ne_zero
  have h4 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq0
  have h5 : (Nat.card K ^ 2 - 1) % 2 = 1 := by omega
  have h6 : (Nat.card K - 1) % 2 = 1 := by omega
  have h7 : Odd (Nat.card (Projectivization K (Fin 2 → K)) * (Nat.card K - 1)) := by
    rw [← h]
    exact Nat.odd_iff.mpr h5
  exact Nat.odd_iff.mp (Nat.odd_mul.mp h7).1

private def linOf {K : Type*} [Field K] {g : Equiv.Perm (Fin 2 → K)}
    (hg : IsSemilinear (1 : RingAut K) g) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun := g
  map_add' := hg.1
  map_smul' := fun c v => by simpa using hg.2 c v

private theorem linOf_apply {K : Type*} [Field K] {g : Equiv.Perm (Fin 2 → K)}
    (hg : IsSemilinear (1 : RingAut K) g) (v : Fin 2 → K) : linOf hg v = g v := rfl

private theorem linOf_injective {K : Type*} [Field K] {g : Equiv.Perm (Fin 2 → K)}
    (hg : IsSemilinear (1 : RingAut K) g) : Function.Injective (linOf hg) := by
  intro a b h
  rw [linOf_apply, linOf_apply] at h
  exact g.injective h

private theorem mk_congr_vec {K : Type*} [Field K] {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : v = w) : Projectivization.mk K v hv = Projectivization.mk K w hw := by
  subst h
  rfl

private abbrev lineAction {K : Type*} [Field K] (G : Subgroup (Equiv.Perm (Fin 2 → K)))
    (hlin : ∀ g ∈ G, IsSemilinear (1 : RingAut K) g) :
    MulAction G (Projectivization K (Fin 2 → K)) where
  smul g x := Projectivization.map (linOf (hlin g.1 g.2)) (linOf_injective _) x
  one_smul x := by
    induction x using Projectivization.ind with
    | _ v hv =>
      change Projectivization.map _ _ (Projectivization.mk K v hv) = _
      rw [Projectivization.map_mk]
      exact mk_congr_vec _ _ rfl
  mul_smul g h x := by
    induction x using Projectivization.ind with
    | _ v hv =>
      change Projectivization.map _ _ (Projectivization.mk K v hv) =
        Projectivization.map _ _ (Projectivization.map _ _ (Projectivization.mk K v hv))
      simp only [Projectivization.map_mk]
      exact mk_congr_vec _ _ rfl

private theorem lineAction_smul_mk_iff {K : Type*} [Field K]
    (G : Subgroup (Equiv.Perm (Fin 2 → K))) (hlin : ∀ g ∈ G, IsSemilinear (1 : RingAut K) g)
    (g : G) {v : Fin 2 → K} (hv : v ≠ 0) :
    (lineAction G hlin).smul g (Projectivization.mk K v hv) = Projectivization.mk K v hv ↔
      ∃ a : Kˣ, a • v = g.1 v := by
  change Projectivization.map _ _ (Projectivization.mk K v hv) = _ ↔ _
  rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff, linOf_apply]

private theorem exists_common_eigenline {K : Type*} [Field K] [Finite K] [CharP K 2]
    (G : Subgroup (Equiv.Perm (Fin 2 → K)))
    (hlin : ∀ g ∈ G, IsSemilinear (1 : RingAut K) g)
    (hpow : ∀ g ∈ G, ∃ (k : ℕ) (c : K), ∀ v, (g ^ 2 ^ k) v = c • v) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ g ∈ G, ∃ μ : K, g v = μ • v := by
  classical
  letI := lineAction G hlin
  have hscal : ∀ z : G, (∃ c : K, ∀ v, z.1 v = c • v) →
      ∀ ℓ : Projectivization K (Fin 2 → K), z • ℓ = ℓ := by
    rintro z ⟨c, hc⟩ ℓ
    have hc0 : c ≠ 0 := by
      intro h0
      have hu : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
      apply hu
      apply z.1.injective
      rw [hc, h0, zero_smul, zero_of_isSemilinear (hlin z.1 z.2)]
    induction ℓ using Projectivization.ind with
    | _ v hv =>
      exact (lineAction_smul_mk_iff G hlin z hv).mpr
        ⟨Units.mk0 c hc0, by rw [Units.smul_def, Units.val_mk0, hc v]⟩
  let ψ : G →* Equiv.Perm (Projectivization K (Fin 2 → K)) := MulAction.toPermHom G _
  have hP : IsPGroup 2 (ψ.range) := by
    intro x
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨k, c, hc⟩ := hpow y.1 y.2
    refine ⟨k, Subtype.ext ?_⟩
    have hz : ψ (y ^ 2 ^ k) = 1 := by
      ext ℓ
      rw [Equiv.Perm.one_apply]
      exact hscal (y ^ 2 ^ k) ⟨c, hc⟩ ℓ
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, ← map_pow]
    exact hz
  have hmod := IsPGroup.card_modEq_card_fixedPoints hP (Projectivization K (Fin 2 → K))
  have hodd := card_projectivization_mod_two K
  have hne : Nat.card (MulAction.fixedPoints ψ.range (Projectivization K (Fin 2 → K))) ≠ 0 := by
    intro h0
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨ℓ, hℓ⟩ : (MulAction.fixedPoints ψ.range (Projectivization K (Fin 2 → K))).Nonempty := by
    rw [← Set.nonempty_coe_sort]
    exact (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  obtain ⟨v, hv, rfl⟩ : ∃ (v : Fin 2 → K) (hv : v ≠ 0), ℓ = Projectivization.mk K v hv := by
    induction ℓ using Projectivization.ind with
    | _ v hv => exact ⟨v, hv, rfl⟩
  refine ⟨v, hv, fun g hg => ?_⟩
  have hfix := MulAction.mem_fixedPoints.mp hℓ
    ⟨ψ ⟨g, hg⟩, MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩⟩
  have hfix' : (lineAction G hlin).smul ⟨g, hg⟩ (Projectivization.mk K v hv) =
      Projectivization.mk K v hv := hfix
  obtain ⟨a, ha⟩ := (lineAction_smul_mk_iff G hlin ⟨g, hg⟩ hv).mp hfix'
  exact ⟨(a : K), by rw [← Units.smul_def]; exact ha.symm⟩

private def linPerms (K : Type*) [Field K] : Subgroup (Equiv.Perm (Fin 2 → K)) where
  carrier := {g | IsSemilinear (1 : RingAut K) g}
  one_mem' := isSemilinear_one
  mul_mem' := fun {a b} ha hb => by
    have h := isSemilinear_mul ha hb
    rwa [mul_one] at h
  inv_mem' := fun {a} ha => isSemilinear_inv ha

private theorem isCyclic_ringAut (K : Type*) [Field K] [Finite K] : IsCyclic (RingAut K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpchar, n, hp, _hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := hpchar
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : RingAut K ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
              algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

private theorem finite_ringAut (K : Type*) [Field K] [Finite K] : Finite (RingAut K) :=
  Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    (fun σ τ h => RingEquiv.ext (fun x => congrFun h x))

theorem exists_invariant_line {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hdesc : ∀ (σ : RingAut K) (Φ : Equiv.Perm (Fin 2 → K)), IsSemilinear σ Φ →
      (∃ c : K, ∀ v, (Φ ^ orderOf σ) v = c • v) → ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ μ : K, Φ v = μ • v)
    (H : Subgroup (Equiv.Perm (Fin 2 → K)))
    (hsemi : ∀ h ∈ H, ∃ σ : RingAut K, IsSemilinear σ h)
    (h2 : ∀ h ∈ H, IsSemilinear (1 : RingAut K) h →
      ∃ (k : ℕ) (c : K), ∀ v, (h ^ (2 ^ k)) v = c • v) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ h ∈ H, ∃ μ : K, h v = μ • v := by
  classical
  let G : Subgroup (Equiv.Perm (Fin 2 → K)) := H ⊓ linPerms K
  have hGmem : ∀ g ∈ G, g ∈ H ∧ IsSemilinear (1 : RingAut K) g :=
    fun g hg => Subgroup.mem_inf.mp hg
  have hGlin : ∀ g ∈ G, IsSemilinear (1 : RingAut K) g := fun g hg => (hGmem g hg).2
  have hGpow : ∀ g ∈ G, ∃ (k : ℕ) (c : K), ∀ v, (g ^ 2 ^ k) v = c • v :=
    fun g hg => h2 g (hGmem g hg).1 (hGmem g hg).2
  by_cases hA : ∃ g₀ ∈ G, ¬ ∃ d : K, ∀ v, g₀ v = d • v
  ·
    obtain ⟨g₀, hg₀G, hg₀⟩ := hA
    obtain ⟨v₀, hv₀, hinv⟩ := exists_common_eigenline G hGlin hGpow
    obtain ⟨μ₀, hμ₀⟩ := hinv g₀ hg₀G
    obtain ⟨k₀, c₀, hk₀⟩ := hGpow g₀ hg₀G
    refine ⟨v₀, hv₀, fun h hh => ?_⟩
    obtain ⟨σ, hσ⟩ := hsemi h hh
    have hconj : h⁻¹ * g₀ * h ∈ G :=
      Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) (hGmem g₀ hg₀G).1) hh,
        isSemilinear_conj hσ (hGlin g₀ hg₀G)⟩
    obtain ⟨μ₁, hμ₁⟩ := hinv _ hconj
    have hhv : h v₀ ≠ 0 := fun h0 =>
      hv₀ (h.injective (h0.trans (zero_of_isSemilinear hσ).symm))
    have hgh : g₀ (h v₀) = (σ μ₁) • h v₀ := by
      have h1 : h⁻¹ (g₀ (h v₀)) = μ₁ • v₀ := hμ₁
      calc g₀ (h v₀) = h (h⁻¹ (g₀ (h v₀))) := (perm_apply_inv_self h _).symm
        _ = h (μ₁ • v₀) := by rw [h1]
        _ = σ μ₁ • h v₀ := hσ.2 μ₁ v₀
    by_cases hdet : v₀ 0 * (h v₀) 1 - v₀ 1 * (h v₀) 0 = 0
    · exact exists_smul_of_det_eq_zero hv₀ hdet
    · exfalso
      obtain ⟨d, hd⟩ := scalar_of_two_eigenvectors (hGlin g₀ hg₀G) hk₀ hv₀ hhv hμ₀ hgh hdet
      exact hg₀ ⟨d, hd⟩
  ·
    push Not at hA
    haveI : IsCyclic (RingAut K) := isCyclic_ringAut K
    haveI : Finite (RingAut K) := finite_ringAut K
    let σf : H → RingAut K := fun h => Classical.choose (hsemi h.1 h.2)
    have hσf : ∀ h : H, IsSemilinear (σf h) h.1 := fun h => Classical.choose_spec (hsemi h.1 h.2)
    let φ : H →* RingAut K := MonoidHom.mk' σf (fun a b =>
      ringAut_eq_of_isSemilinear (hσf (a * b)) (isSemilinear_mul (hσf a) (hσf b)))
    have hφ : ∀ h : H, IsSemilinear (φ h) h.1 := hσf
    have hφ1 : ∀ h : H, φ h = 1 → IsSemilinear (1 : RingAut K) h.1 := fun h hh => by
      have := hφ h
      rwa [hh] at this
    obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := ↥φ.range)
    obtain ⟨h₁, hh₁⟩ := MonoidHom.mem_range.mp gen.2
    have hpowgen : ∀ h : H, ∃ n : ℕ, (φ h₁) ^ n = φ h := by
      intro h
      have hmem := hgen ⟨φ h, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hj' : (φ h₁) ^ j = φ h := by
        have := congrArg Subtype.val hj
        simpa [← hh₁] using this
      exact (Submonoid.mem_powers_iff _ _).mp
        (mem_powers_iff_mem_zpowers.mpr (Subgroup.mem_zpowers_iff.mpr ⟨j, hj'⟩))
    have hm : φ (h₁ ^ orderOf (φ h₁)) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    obtain ⟨d, hd⟩ := hA (h₁ ^ orderOf (φ h₁)).1
      (Subgroup.mem_inf.mpr ⟨(h₁ ^ orderOf (φ h₁)).2, hφ1 _ hm⟩)
    obtain ⟨v, hv, μ, hμ⟩ := hdesc (φ h₁) h₁.1 (hφ h₁) ⟨d, fun v => hd v⟩
    have hline : ∀ n : ℕ, ∃ ν : K, (h₁ ^ n).1 v = ν • v := by
      intro n
      induction n with
      | zero => exact ⟨1, by simp⟩
      | succ n ih =>
        obtain ⟨ν, hν⟩ := ih
        refine ⟨φ h₁ ν * μ, ?_⟩
        rw [pow_succ', Subgroup.coe_mul, Equiv.Perm.mul_apply, hν, (hφ h₁).2, hμ, smul_smul]
    refine ⟨v, hv, fun h hh => ?_⟩
    obtain ⟨n, hn⟩ := hpowgen ⟨h, hh⟩
    obtain ⟨g, hgdef⟩ : ∃ g : H, g = (h₁ ^ n)⁻¹ * ⟨h, hh⟩ := ⟨_, rfl⟩
    have hφg : φ g = 1 := by
      rw [hgdef, map_mul, map_inv, map_pow, hn, inv_mul_cancel]
    obtain ⟨d', hd'⟩ := hA g.1 (Subgroup.mem_inf.mpr ⟨g.2, hφ1 g hφg⟩)
    obtain ⟨ν, hν⟩ := hline n
    have hdecomp : h = (h₁ ^ n).1 * g.1 := by
      rw [hgdef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    refine ⟨φ (h₁ ^ n) d' * ν, ?_⟩
    rw [hdecomp, Equiv.Perm.mul_apply, hd', (hφ (h₁ ^ n)).2, hν, smul_smul]

end CFSG.Quasithin.Vol2.Ch10Reselect
