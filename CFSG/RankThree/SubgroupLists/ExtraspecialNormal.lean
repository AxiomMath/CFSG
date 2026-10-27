module

public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.RankThree.SubgroupLists.ExtraspecialCore
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem commute_of_commute_of_eigenbasis {m : Matrix (Fin 3) (Fin 3) K} {u : Fin 3 → Fin 3 → K}
    {e : Fin 3 → K} (he : Function.Injective e) (hu0 : ∀ j, u j ≠ 0)
    (hu : ∀ j, m *ᵥ u j = e j • u j) {A B : Matrix (Fin 3) (Fin 3) K} (hA : A * m = m * A)
    (hB : B * m = m * B) : A * B = B * A := by
  classical
  have hind : LinearIndependent K u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' m) e he u fun j =>
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply, hu j]), hu0 j⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank (by simp)
  have hdiag : ∀ C : Matrix (Fin 3) (Fin 3) K, C * m = m * C → ∀ j, ∃ a : K,
      C *ᵥ u j = a • u j := by
    intro C hC j
    have hmem : C *ᵥ u j ∈ Submodule.span K (Set.range u) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hmem
    have hm : m *ᵥ (C *ᵥ u j) = e j • (C *ᵥ u j) := by
      rw [Matrix.mulVec_mulVec, ← hC, ← Matrix.mulVec_mulVec, hu j, Matrix.mulVec_smul]
    rw [← hc, Matrix.mulVec_sum] at hm
    simp only [Matrix.mulVec_smul, hu, smul_smul, Finset.smul_sum] at hm
    have hzero : ∑ i, (c i * e i - e j * c i) • u i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hm, sub_self]
    have hci := (Fintype.linearIndependent_iff.mp hind) _ hzero
    refine ⟨c j, ?_⟩
    rw [← hc, Finset.sum_eq_single j]
    · intro i _ hij
      have h := hci i
      have hne : e i - e j ≠ 0 := sub_ne_zero.mpr fun h' => hij (he h')
      have : c i * (e i - e j) = 0 := by rw [mul_sub, mul_comm (c i) (e j)]; exact h
      rw [(mul_eq_zero.mp this).resolve_right hne, zero_smul]
    · simp
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on_range hspan
  intro j
  obtain ⟨a, ha⟩ := hdiag A hA j
  obtain ⟨b, hb⟩ := hdiag B hB j
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb, Matrix.mulVec_smul,
    smul_smul, mul_comm a b]

theorem isIrreducibleOn_zpowers_of_no_eigenvector {M : GL (Fin 3) K}
    (hev : ¬ ∃ v : Fin 3 → K, v ≠ 0 ∧ ∃ μ : K, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v) :
    IsIrreducibleOn (Subgroup.zpowers M) := by
  classical
  intro W hW
  have hMW : ∀ w ∈ W, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W :=
    hW M (Subgroup.mem_zpowers M)
  by_contra hne
  push Not at hne
  obtain ⟨hW0, hWt⟩ := hne
  have hpos : Module.finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hlt : Module.finrank K W < 3 := by
    have := Submodule.finrank_lt hWt
    simpa using this
  rcases (by omega : Module.finrank K W = 1 ∨ Module.finrank K W = 2) with h1 | h2
  ·
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hWw : W = K ∙ w := by
      symm
      apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
      rw [h1, finrank_span_singleton hw0]
    have hMw : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ K ∙ w := hWw ▸ hMW w hw
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hMw
    exact hev ⟨w, hw0, μ, hμ.symm⟩
  ·
    obtain ⟨u, hu⟩ : ∃ u, u ∉ W := by
      by_contra h
      push Not at h
      exact hWt (eq_top_iff.mpr fun x _ => h x)
    have hsup : W ⊔ K ∙ u = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hlt' : W < W ⊔ K ∙ u := lt_of_le_of_ne le_sup_left fun h =>
        hu (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      have hle := Submodule.finrank_le (W ⊔ K ∙ u)
      simp only [Module.finrank_fin_fun] at hle ⊢
      omega
    have hMu : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ W ⊔ K ∙ u := hsup ▸ Submodule.mem_top
    obtain ⟨w₀, hw₀, z, hz, hsum⟩ := Submodule.mem_sup.mp hMu
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hz
    let f : Module.End K (Fin 3 → K) :=
      Matrix.toLin' (M : Matrix (Fin 3) (Fin 3) K) - μ • LinearMap.id
    have hf : ∀ y, f y = (M : Matrix (Fin 3) (Fin 3) K) *ᵥ y - μ • y := fun y => by
      simp [f, Matrix.toLin'_apply]
    have hrange : LinearMap.range f ≤ W := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ W ⊔ K ∙ u := hsup ▸ Submodule.mem_top
      obtain ⟨w', hw', z', hz', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz'
      rw [hf, Matrix.mulVec_add, Matrix.mulVec_smul, ← hsum]
      have : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ w' + t • (w₀ + μ • u) - μ • (w' + t • u) =
          ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ w' - μ • w') + t • w₀ := by
        simp only [smul_add, smul_smul, mul_comm t μ]
        abel
      rw [this]
      exact W.add_mem (W.sub_mem (hMW w' hw') (W.smul_mem μ hw')) (W.smul_mem t hw₀)
    have hnsurj : ¬ Function.Surjective f := by
      intro hs
      apply hu
      obtain ⟨y, hy⟩ := hs u
      exact hy ▸ hrange ⟨y, rfl⟩
    have hninj : ¬ Function.Injective f := fun hi =>
      hnsurj (LinearMap.injective_iff_surjective.mp hi)
    rw [← LinearMap.ker_eq_bot] at hninj
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hninj
    rw [LinearMap.mem_ker, hf, sub_eq_zero] at hy
    exact hev ⟨y, hy0, μ, hy⟩

theorem commute_of_commute_of_conj_eq_smul [Finite K] {M P : GL (Fin 3) K} {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * M * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (M : Matrix (Fin 3) (Fin 3) K))
    {A B : Matrix (Fin 3) (Fin 3) K} (hA : A * M = M * A) (hB : B * M = M * B) :
    A * B = B * A := by
  classical
  have hmq : (M : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) := by
    have h := congrArg (HMul.hMul ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hP
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, Matrix.mul_smul] at h
  by_cases hev : ∃ v : Fin 3 → K, v ≠ 0 ∧ ∃ μ : K, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v
  ·
    obtain ⟨v, hv0, μ, hμ⟩ := hev
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      apply hv0
      rw [← gl_inv_mulVec_mulVec M v, hμ, Matrix.mulVec_zero]
    let u : Fin 3 → Fin 3 → K := fun j =>
      (((P⁻¹ : GL (Fin 3) K) ^ (j : ℕ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
    have hu : ∀ j : ℕ, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((((P⁻¹ : GL (Fin 3) K) ^ j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (ω ^ j * μ) • ((((P⁻¹ : GL (Fin 3) K) ^ j : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      intro j
      induction j with
      | zero => simpa using hμ
      | succ j ih =>
        rw [pow_succ', gl_mulVec_mul, Matrix.mulVec_mulVec, hmq, Matrix.smul_mulVec,
          ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, smul_smul, pow_succ]
        ring_nf
    have hu0 : ∀ j, u j ≠ 0 := by
      intro j hj
      apply hv0
      rw [← gl_mulVec_inv_mulVec (P ^ (j : ℕ)) v, ← inv_pow]
      change _ *ᵥ u j = 0
      rw [hj, Matrix.mulVec_zero]
    have hω0 : ω ≠ 0 := by
      rintro rfl
      simp at hω3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    have he : Function.Injective fun j : Fin 3 => ω ^ (j : ℕ) * μ := by
      intro i j hij
      have hij' : ω ^ (i : ℕ) = ω ^ (j : ℕ) := mul_right_cancel₀ hμ0 hij
      have hu' : (Units.mk0 ω hω0) ^ (i : ℕ) = (Units.mk0 ω hω0) ^ (j : ℕ) :=
        Units.ext (by simpa using hij')
      rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, hord] at hu'
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hu' i.2 j.2)
    exact commute_of_commute_of_eigenbasis he hu0 (fun j => hu j) hA hB
  ·
    have hirr := isIrreducibleOn_zpowers_of_no_eigenvector hev
    let := commutantField hirr
    have hcomm : ∀ C : Matrix (Fin 3) (Fin 3) K, C * M = M * C →
        C ∈ commutant (Subgroup.zpowers M) := by
      intro C hC
      rw [mem_commutant]
      let S : Subgroup (GL (Fin 3) K) :=
        { carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) * C = C * g}
          mul_mem' := fun {a b} ha hb => by
            change (a : Matrix (Fin 3) (Fin 3) K) * C = C * a at ha
            change (b : Matrix (Fin 3) (Fin 3) K) * C = C * b at hb
            change ((a * b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C = C * (a * b : GL _ _)
            rw [Units.val_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
          one_mem' := by simp
          inv_mem' := fun {a} ha => by
            change (a : Matrix (Fin 3) (Fin 3) K) * C = C * a at ha
            change ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C =
              C * ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            calc ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C =
                (a⁻¹ : GL (Fin 3) K) * (C * a * (a⁻¹ : GL (Fin 3) K)) := by
                  rw [Units.mul_inv_cancel_right]
              _ = (a⁻¹ : GL (Fin 3) K) * (a * C * (a⁻¹ : GL (Fin 3) K)) := by rw [ha]
              _ = C * (a⁻¹ : GL (Fin 3) K) := by
                  rw [Matrix.mul_assoc (a : Matrix (Fin 3) (Fin 3) K), Units.inv_mul_cancel_left] }
      have hMS : M ∈ S := hC.symm
      intro g hg
      exact (Subgroup.zpowers_le.mpr hMS) hg
    exact congrArg Subtype.val (mul_comm (⟨A, hcomm A hA⟩ : commutant (Subgroup.zpowers M))
      ⟨B, hcomm B hB⟩)

theorem isCyclic_of_forall_scalar [Finite K] {S : Type*} [Group S] [Finite S]
    (f : S →* GL (Fin 3) K) (hf : Function.Injective f)
    (hS : ∀ s, ∃ c : K,
      ((f s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    IsCyclic S := by
  classical
  let φ : S →* K :=
    { toFun := fun s => ((f s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
      map_one' := by simp
      map_mul' := fun s t => by
        obtain ⟨a, ha⟩ := hS s
        obtain ⟨b, hb⟩ := hS t
        simp only [map_mul, Units.val_mul, ha, hb, Matrix.scalar_apply,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] }
  refine isCyclic_of_injective_ringHom φ fun s t hst => hf (Units.ext ?_)
  obtain ⟨a, ha⟩ := hS s
  obtain ⟨b, hb⟩ := hS t
  have hab : a = b := by
    have := hst
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, ha, hb, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at this
    exact this
  rw [ha, hb, hab]

theorem scalar_pow_three_of_commutator {a b : GL (Fin 3) K} {c : K}
    (h : ((a * b * a⁻¹ * b⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have hdet := congrArg Matrix.det h
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  rw [← hdet]
  have : ((a * b * a⁻¹ * b⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((Matrix.GeneralLinearGroup.det (a * b * a⁻¹ * b⁻¹) : Kˣ) : K) := rfl
  rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hc : Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det b *
      (Matrix.GeneralLinearGroup.det a)⁻¹ * (Matrix.GeneralLinearGroup.det b)⁻¹ = 1 := by
    rw [mul_comm (Matrix.GeneralLinearGroup.det a)]
    group
  rw [hc, Units.val_one]

section GroupTheory

open scoped commutatorElement

variable {R : Type*} [Group R]

theorem exists_not_mem_center_commutator_mem_center [Finite R] {r : ℕ} [Fact r.Prime]
    (hR : IsPGroup r R) (hnc : ¬ IsMulCommutative R) :
    ∃ x₀ : R, x₀ ∉ Subgroup.center R ∧ ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R := by
  classical
  set Z := Subgroup.center R
  have hQnt : Nontrivial (R ⧸ Z) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a ∈ Z := (QuotientGroup.eq_one_iff a).mp (Subsingleton.elim _ _)
    exact Subgroup.mem_center_iff.mp ha b |>.symm
  have hQZ : Nontrivial (Subgroup.center (R ⧸ Z)) := (hR.to_quotient Z).center_nontrivial
  obtain ⟨q, hq⟩ := exists_ne (1 : Subgroup.center (R ⧸ Z))
  obtain ⟨x₀, hx₀q⟩ := QuotientGroup.mk_surjective (q : R ⧸ Z)
  refine ⟨x₀, fun h => hq (Subtype.ext ?_), fun y => ?_⟩
  · rw [← hx₀q, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
    exact h
  · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hx₀q,
      commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp q.2 _

@[expose] def commutatorHom (x₀ : R) (h : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) : R →* R where
  toFun y := ⁅y, x₀⁆
  map_one' := by simp
  map_mul' a b := by
    have hb := Subgroup.mem_center_iff.mp (h b)
    have key : ⁅a * b, x₀⁆ = a * ⁅b, x₀⁆ * a⁻¹ * ⁅a, x₀⁆ := by
      simp only [commutatorElement_def]
      group
    rw [key, hb a, mul_inv_cancel_right]
    exact (hb _).symm

theorem commutatorHom_apply (x₀ : R) (h : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) (y : R) :
    commutatorHom x₀ h y = ⁅y, x₀⁆ :=
  rfl

theorem mem_ker_commutatorHom (x₀ : R) (h : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) (y : R) :
    y ∈ (commutatorHom x₀ h).ker ↔ y * x₀ = x₀ * y := by
  rw [MonoidHom.mem_ker, commutatorHom_apply, commutatorElement_eq_one_iff_mul_comm]

theorem commutator_le_ker_commutatorHom (x₀ : R) (h : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) :
    commutator R ≤ (commutatorHom x₀ h).ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
    commutatorHom_apply, commutatorHom_apply]
  exact Subgroup.mem_center_iff.mp (h b) _

end GroupTheory

section Linear

open scoped commutatorElement

theorem conj_eq_smul_of_commutator_eq_scalar {y x : GL (Fin 3) K} {ω : K}
    (h : ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
      ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = Matrix.scalar (Fin 3) ω) :
    (y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
      ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ω • (x : Matrix (Fin 3) (Fin 3) K) := by
  calc (y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
        ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
        ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (x : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc _ ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
          Units.inv_mul, Matrix.mul_one]
    _ = Matrix.scalar (Fin 3) ω * (x : Matrix (Fin 3) (Fin 3) K) := by rw [h]
    _ = ω • (x : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

variable [Finite K]

omit [Finite K] in
theorem coe_commutatorElement_matrix {R : Subgroup (GL (Fin 3) K)} (y x : R) :
    (((⁅y, x⁆ : R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((x : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (((y : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (((x : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]

omit [Finite K] in
theorem exists_commutator_cube_root {R : Subgroup (GL (Fin 3) K)}
    (hZs : ∀ z ∈ Subgroup.center R, ∃ c : K,
      ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {x₀ : R} (hx₀Z : x₀ ∉ Subgroup.center R) (hcomm₀ : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) :
    (∀ y : R, ∃ c : K, (((⁅y, x₀⁆ : R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c ∧ c ^ 3 = 1) ∧
    ∃ y₀ : R, ∃ ω : K, (((⁅y₀, x₀⁆ : R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) ω ∧ ω ≠ 1 ∧ ω ^ 3 = 1 := by
  have hall : ∀ y : R, ∃ c : K, (((⁅y, x₀⁆ : R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c ∧ c ^ 3 = 1 := by
    intro y
    obtain ⟨c, hc⟩ := hZs _ (hcomm₀ y)
    refine ⟨c, hc, scalar_pow_three_of_commutator (a := (y : GL (Fin 3) K))
      (b := (x₀ : GL (Fin 3) K)) ?_⟩
    rw [← hc, coe_commutatorElement_matrix, Units.val_mul, Units.val_mul, Units.val_mul]
  refine ⟨hall, ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : R, ⁅y₀, x₀⁆ ≠ 1 := by
    by_contra h
    push Not at h
    apply hx₀Z
    rw [Subgroup.mem_center_iff]
    intro g
    have := h g
    rwa [commutatorElement_eq_one_iff_mul_comm] at this
  obtain ⟨ω, hω, hω3⟩ := hall y₀
  refine ⟨y₀, ω, hω, ?_, hω3⟩
  rintro rfl
  apply hy₀
  apply Subtype.ext
  apply Units.ext
  rw [hω, map_one]
  rfl

theorem centralizer_structure_gl3 {r : ℕ} [hr : Fact r.Prime] {R : Subgroup (GL (Fin 3) K)}
    (hRp : IsPGroup r R)
    (hZs : ∀ z ∈ Subgroup.center R, ∃ c : K,
      ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {x₀ : R} (hx₀Z : x₀ ∉ Subgroup.center R) (hcomm₀ : ∀ y : R, ⁅y, x₀⁆ ∈ Subgroup.center R) :
    r = 3 ∧ 3 ∣ Nat.card K - 1 ∧ (commutatorHom x₀ hcomm₀).ker.index = 3 ∧
      ∀ a ∈ (commutatorHom x₀ hcomm₀).ker, ∀ b ∈ (commutatorHom x₀ hcomm₀).ker,
        a * b = b * a := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hall, y₀, ω, hω, hω1, hω3⟩ := exists_commutator_cube_root hZs hx₀Z hcomm₀
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hK3 : 3 ∣ Nat.card K - 1 := by
    have hu3 : (Units.mk0 ω hω0) ^ 3 = 1 := Units.ext (by simpa using hω3)
    have hu1 : Units.mk0 ω hω0 ≠ 1 := fun h => hω1 (by simpa using congrArg Units.val h)
    have := orderOf_dvd_natCard (Units.mk0 ω hω0)
    rwa [orderOf_eq_prime hu3 hu1, Nat.card_units] at this
  have hc₀3 : ⁅y₀, x₀⁆ ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hω, ← map_pow, hω3, map_one]
    rfl
  have hc₀1 : ⁅y₀, x₀⁆ ≠ 1 := by
    intro h
    apply hω1
    have := congrArg (fun z : R => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simpa [hω, Matrix.scalar_apply] using this
  have hc₀o : orderOf ⁅y₀, x₀⁆ = 3 := orderOf_eq_prime hc₀3 hc₀1
  have hr3 : r = 3 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRp
    have hdvd : 3 ∣ r ^ m := by
      have := orderOf_dvd_natCard ⁅y₀, x₀⁆
      rwa [hc₀o, hm] at this
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr.out).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)).symm
  refine ⟨hr3, hK3, ?_, ?_⟩
  ·
    rw [Subgroup.index_ker]
    have hcyc : IsCyclic (commutatorHom x₀ hcomm₀).range := isCyclic_of_forall_scalar
      (R.subtype.comp (commutatorHom x₀ hcomm₀).range.subtype)
      (R.subtype_injective.comp (commutatorHom x₀ hcomm₀).range.subtype_injective) fun z => by
        obtain ⟨y, hy⟩ := z.2
        obtain ⟨c, hc, -⟩ := hall y
        refine ⟨c, ?_⟩
        change (((z : R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
        rw [← hy, commutatorHom_apply, hc]
    apply le_antisymm
    · refine card_le_of_pow_eq_one_of_isCyclic fun z => ?_
      obtain ⟨y, hy⟩ := z.2
      obtain ⟨c, hc, hc3⟩ := hall y
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one]
      rw [← hy, commutatorHom_apply, hc, ← map_pow, hc3, map_one]
    · have hc₀r : ⁅y₀, x₀⁆ ∈ (commutatorHom x₀ hcomm₀).range := ⟨y₀, rfl⟩
      have hord : orderOf (⟨_, hc₀r⟩ : (commutatorHom x₀ hcomm₀).range) = 3 := by
        rw [Subgroup.orderOf_mk, hc₀o]
      calc 3 = orderOf (⟨_, hc₀r⟩ : (commutatorHom x₀ hcomm₀).range) := hord.symm
        _ ≤ Nat.card (commutatorHom x₀ hcomm₀).range := orderOf_le_card
  ·
    have hconj := conj_eq_smul_of_commutator_eq_scalar (y := (y₀ : GL (Fin 3) K))
      (x := (x₀ : GL (Fin 3) K)) (by rw [← coe_commutatorElement_matrix, hω])
    intro a ha b hb
    have ha' := (mem_ker_commutatorHom x₀ hcomm₀ a).mp ha
    have hb' := (mem_ker_commutatorHom x₀ hcomm₀ b).mp hb
    have hA : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x₀ : GL (Fin 3) K) =
        (x₀ : GL (Fin 3) K) * (a : GL (Fin 3) K) := by
      have := congrArg (fun z : R => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ha'
      simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hB : ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x₀ : GL (Fin 3) K) =
        (x₀ : GL (Fin 3) K) * (b : GL (Fin 3) K) := by
      have := congrArg (fun z : R => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hb'
      simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hab := commute_of_commute_of_conj_eq_smul hω1 hω3 hconj hA hB
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_mul, Units.val_mul] using hab

omit [Finite K] in
theorem scalar_of_conj_invariant {G R : Subgroup (GL (Fin 3) K)}
    (habel : ∀ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hRG : R ≤ G) (hRn : ∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (N : Subgroup R)
    (hNc : ∀ g (hg : g ∈ G) (x : R), x ∈ N → (⟨g * x * g⁻¹, hRn g hg x x.2⟩ : R) ∈ N)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    ∀ x ∈ N, ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c := by
  intro x hx
  refine habel (N.map R.subtype) ((Subgroup.map_subtype_le N).trans hRG) ?_ ?_ _
    ⟨x, hx, rfl⟩
  · rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨_, hNc g hg y hy, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hNab a ha b hb)

omit [Finite K] in
theorem conj_mem_center {G R : Subgroup (GL (Fin 3) K)}
    (hRn : ∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (g : GL (Fin 3) K) (hg : g ∈ G) (z : R)
    (hz : z ∈ Subgroup.center R) :
    (⟨g * z * g⁻¹, hRn g hg z z.2⟩ : R) ∈ Subgroup.center R := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  apply Subtype.ext
  have hy' : g⁻¹ * (y : GL (Fin 3) K) * g ∈ R := by
    simpa using hRn g⁻¹ (G.inv_mem hg) y y.2
  have := congrArg Subtype.val (hz ⟨_, hy'⟩)
  simp only [Subgroup.coe_mul] at this ⊢
  calc (y : GL (Fin 3) K) * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * z * g⁻¹ * y := by group

omit [Finite K] in
theorem conj_mem_commutator {G R : Subgroup (GL (Fin 3) K)}
    (hRn : ∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (g : GL (Fin 3) K) (hg : g ∈ G) (x : R)
    (hx : x ∈ commutator R) :
    (⟨g * x * g⁻¹, hRn g hg x x.2⟩ : R) ∈ commutator R := by
  let φ : R →* R :=
    { toFun := fun y => ⟨g * y * g⁻¹, hRn g hg y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hmap : (commutator R).map φ ≤ commutator R := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap ⟨x, hx, rfl⟩

end Linear

open scoped commutatorElement in
theorem normal_pGroup_extraspecial_gl3_with_carrier [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (habel : ∀ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {r : ℕ} [hr : Fact r.Prime] {R : Subgroup (GL (Fin 3) K)} (hRG : R ≤ G)
    (hRn : ∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (hRp : IsPGroup r R)
    (hRs : ∃ x ∈ R, ∀ c : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    r = 3 ∧ 3 ∣ Nat.card K - 1 ∧ ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧
      IsIrreducibleMatrixRep H.subtype ∧ Nat.card H = 3 ^ 3 ∧ IsExtraspecialPGroup 3 H ∧
      ∀ x : GL (Fin 3) K, x ∈ H ↔ x ∈ R ∧ x ^ 3 = 1 := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZs := scalar_of_conj_invariant habel hRG hRn (Subgroup.center R)
    (fun g hg z hz => conj_mem_center hRn g hg z hz)
    (fun a ha b _ => (Subgroup.mem_center_iff.mp ha b).symm)
  have hRnc : ¬ IsMulCommutative R := by
    intro hc
    obtain ⟨x, hx, hxs⟩ := hRs
    obtain ⟨c, hc'⟩ := habel R hRG hRn (fun a ha b hb => congrArg Subtype.val
      (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) x hx
    exact hxs c hc'
  obtain ⟨x₀, hx₀Z, hcomm₀⟩ := exists_not_mem_center_commutator_mem_center hRp hRnc
  obtain ⟨hr3, hK3, hBi, hBc⟩ := centralizer_structure_gl3 hRp hZs hx₀Z hcomm₀
  subst hr3
  have hBcent : ∀ y : R, (∀ b ∈ (commutatorHom x₀ hcomm₀).ker, y * b = b * y) →
      y ∈ (commutatorHom x₀ hcomm₀).ker := fun y hy =>
    (mem_ker_commutatorHom x₀ hcomm₀ y).mpr
      (hy x₀ ((mem_ker_commutatorHom x₀ hcomm₀ x₀).mpr rfl))
  have hclass : commutator R ≤ Subgroup.center R := by
    intro c hc
    obtain ⟨s, hs⟩ := scalar_of_conj_invariant habel hRG hRn (commutator R)
      (fun g hg x hx => conj_mem_commutator hRn g hg x hx)
      (fun a ha b hb => hBc a (commutator_le_ker_commutatorHom x₀ hcomm₀ ha) b
        (commutator_le_ker_commutatorHom x₀ hcomm₀ hb)) c hc
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hs]
    exact (Matrix.scalar_commute s (fun r' => Commute.all s r') _).symm.eq
  have hZcyc : IsCyclic (Subgroup.center R) := isCyclic_of_forall_scalar
    (R.subtype.comp (Subgroup.center R).subtype)
    (R.subtype_injective.comp Subtype.val_injective) fun z => hZs z z.2
  have hΩ : ∀ H : Subgroup R, (∀ x, x ∈ H ↔ x ^ 3 = 1) →
      (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) → IsCyclic H := by
    intro H hH hHab
    have hHs := scalar_of_conj_invariant habel hRG hRn H (fun g hg x hx => by
      rw [hH] at hx ⊢
      apply Subtype.ext
      have hx' : (x : GL (Fin 3) K) ^ 3 = 1 := by
        rw [← SubgroupClass.coe_pow, hx, OneMemClass.coe_one]
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [conj_pow, hx', mul_one, mul_inv_cancel]) hHab
    exact isCyclic_of_forall_scalar (R.subtype.comp H.subtype)
      (R.subtype_injective.comp Subtype.val_injective) fun z => hHs z z.2
  have : (commutatorHom x₀ hcomm₀).ker.Normal := MonoidHom.normal_ker _
  obtain ⟨H₀, hH₀mem, hH₀card, hH₀ex⟩ := exists_extraspecial_omega (n := 3) (by norm_num) hRp
    hRnc (commutatorHom x₀ hcomm₀).ker hBc hBi hBcent hclass hZcyc hΩ
  have hH₀nc : ¬ ∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a := by
    intro hab
    obtain ⟨-, hcomm, -, hcard⟩ := hH₀ex
    have hbot : commutator H₀ = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _ b _
      exact Subtype.ext (hab _ a.2 _ b.2).symm
    rw [hcomm] at hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hHmem : ∀ x : GL (Fin 3) K, x ∈ H₀.map R.subtype ↔ ∃ h : x ∈ R, (⟨x, h⟩ : R) ^ 3 = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hH₀mem y).mp hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, (hH₀mem _).mpr hx, rfl⟩
  refine ⟨rfl, hK3, H₀.map R.subtype, (Subgroup.map_subtype_le _).trans hRG, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg x hx
    obtain ⟨hxR, hx3⟩ := (hHmem x).mp hx
    refine (hHmem _).mpr ⟨hRn g hg x hxR, Subtype.ext ?_⟩
    have hx' : x ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [conj_pow, hx', mul_one, mul_inv_cancel]
  ·
    rcases hnorm (H₀.map R.subtype) (by
        intro g hg x hx
        obtain ⟨hxR, hx3⟩ := (hHmem x).mp hx
        refine (hHmem _).mpr ⟨hRn g hg x hxR, Subtype.ext ?_⟩
        have hx' : x ^ 3 = 1 := by
          have := congrArg Subtype.val hx3
          simpa using this
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [conj_pow, hx', mul_one, mul_inv_cancel]) with h | h
    · exact h
    · exfalso
      apply hH₀nc
      intro a ha b hb
      obtain ⟨s, hs⟩ := h _ ⟨a, ha, rfl⟩
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      have hs' : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) s := hs
      rw [hs']
      exact (Matrix.scalar_commute s (fun r' => Commute.all s r') _).eq
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hH₀card]
  ·
    have hcard : Nat.card (H₀.map R.subtype) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective R.subtype_injective, hH₀card]
    refine CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three
      (IsPGroup.of_card hcard) (fun x => Subtype.ext ?_) hcard ?_
    · obtain ⟨hxR, hx3⟩ := (hHmem x).mp x.2
      have := congrArg Subtype.val hx3
      simpa using this
    · intro hc
      apply hH₀nc
      intro a ha b hb
      have := congrArg Subtype.val (hc.is_comm.comm ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩)
      exact Subtype.ext this
  ·
    intro x
    rw [hHmem x]
    constructor
    · rintro ⟨hx, hx3⟩
      refine ⟨hx, ?_⟩
      have := congrArg Subtype.val hx3
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
    · rintro ⟨hx, hx3⟩
      exact ⟨hx, Subtype.ext (by
        simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hx3)⟩

theorem normal_pGroup_extraspecial_gl3 [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (habel : ∀ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {r : ℕ} [hr : Fact r.Prime] {R : Subgroup (GL (Fin 3) K)} (hRG : R ≤ G)
    (hRn : ∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (hRp : IsPGroup r R)
    (hRs : ∃ x ∈ R, ∀ c : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    r = 3 ∧ 3 ∣ Nat.card K - 1 ∧ ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧
      IsIrreducibleMatrixRep H.subtype ∧ Nat.card H = 3 ^ 3 ∧ IsExtraspecialPGroup 3 H := by
  obtain ⟨hr3, hK3, H, hHG, hHn, hHirr, hHcard, hHex, -⟩ :=
    normal_pGroup_extraspecial_gl3_with_carrier hnorm habel hRG hRn hRp hRs
  exact ⟨hr3, hK3, H, hHG, hHn, hHirr, hHcard, hHex⟩

end CFSG.RankThree.SubgroupLists
