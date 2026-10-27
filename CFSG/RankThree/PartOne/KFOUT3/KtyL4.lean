module

import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
public import CFSG.RankThree.PartOne.KF.R8Group
public import CFSG.RankThree.PartOne.KFOUT3.KtyAt

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

section Linear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem span_one_of_not_mem_range {b : Qext K} (hb : b ∉ Set.range (algebraMap K (Qext K))) :
    Submodule.span K {(1 : Qext K), b} = ⊤ := by
  have hli : LinearIndependent K ![(1 : Qext K), b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hb
      refine ⟨-(s / t), ?_⟩
      have h1 : t • b = -(s • (1 : Qext K)) := eq_neg_of_add_eq_zero_right hst
      have h2 : b = (t⁻¹) • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, h1, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one]
      simp [div_eq_inv_mul]
  have hspan : Submodule.span K (Set.range ![(1 : Qext K), b]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [finrank_qext])
  have hrange : Set.range ![(1 : Qext K), b] = {(1 : Qext K), b} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [← hrange]
  exact hspan

theorem not_mem_range_of_root (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {b : Qext K} (hb : b ^ p = 1) (hb1 : b ≠ 1) :
    b ∉ Set.range (algebraMap K (Qext K)) := fun h =>
  hb1 (eq_one_of_mem_range hp (not_dvd_pred hp hp2 hpq) hb h)

theorem smul_of_commute {M : Type*} [AddCommGroup M] [Module K M] [Module (Qext K) M]
    [IsScalarTower K (Qext K) M] (f : M →ₗ[K] M) {b : Qext K}
    (hspan : Submodule.span K {(1 : Qext K), b} = ⊤) (hf : ∀ v, f (b • v) = b • f v)
    (l : Qext K) (v : M) : f (l • v) = l • f v := by
  have hl : l ∈ Submodule.span K {(1 : Qext K), b} := by rw [hspan]; trivial
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hl
  have e1 : (s • (1 : Qext K) + t • b) • v = s • v + t • (b • v) := by
    rw [add_smul, smul_assoc, smul_assoc, one_smul]
  have e2 : (s • (1 : Qext K) + t • b) • f v = s • f v + t • (b • f v) := by
    rw [add_smul, smul_assoc, smul_assoc, one_smul]
  rw [e1, e2, map_add, map_smul, map_smul, hf]

end Linear

section Small

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def T8 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    D8Mod p (Qext K) →* ↥(M8 K) :=
  d8Emb.codRestrict (M8 K) (d8Emb_mem_M8 hp hp2 hpq)

@[expose] noncomputable def blk (f : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) (i j : Fin 2) :
    Qext K →ₗ[K] Qext K :=
  (LinearMap.proj i : QV K (Fin 2) →ₗ[K] Qext K) ∘ₗ f ∘ₗ
    (LinearMap.single K (fun _ : Fin 2 => Qext K) j)

theorem blk_apply (f : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) (i j : Fin 2) (y : Qext K) :
    blk f i j y = f (Pi.single j y) i := by
  simp [blk]

theorem eq_single_add (v : QV K (Fin 2)) : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
  funext i
  fin_cases i <;> simp

theorem d8Emb_one_apply (b : rootsOfUnity p (Qext K)) (w : QV K (Fin 2)) :
    d8Emb ((1 : rootsOfUnity p (Qext K)), b) w =
      ![w 0, (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * w 1] := by
  funext i
  fin_cases i
  · simp [d8Emb_apply_zero]
  · simp [d8Emb_apply_one]

section Commuting

variable {b : rootsOfUnity p (Qext K)} (hb1 : b ≠ 1)
  (x : QV K (Fin 2) →ₗ[K] QV K (Fin 2))
  (hx : ∀ v, d8Emb ((1 : rootsOfUnity p (Qext K)), b) (x v) =
    x (d8Emb ((1 : rootsOfUnity p (Qext K)), b) v))

omit [Finite K] in
include hb1 in
theorem val_sub_one_ne_zero : (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) - 1 ≠ 0 := by
  intro h
  apply hb1
  apply Subtype.ext
  apply Units.ext
  simpa [sub_eq_zero] using h

include hb1 hx in
theorem blk_offdiag_one_zero (y : Qext K) : blk x 1 0 y = 0 := by
  have h1 : d8Emb ((1 : rootsOfUnity p (Qext K)), b) (Pi.single 0 y : QV K (Fin 2)) =
      Pi.single 0 y := by
    rw [d8Emb_one_apply]
    funext i
    fin_cases i <;> simp
  have h2 := hx (Pi.single 0 y)
  rw [h1] at h2
  have h3 := congrFun h2 1
  rw [d8Emb_one_apply] at h3
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h3
  rw [blk_apply]
  have h4 : ((((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) - 1) * x (Pi.single 0 y) 1 = 0 := by
    rw [sub_mul, h3, one_mul, sub_self]
  exact (mul_eq_zero.mp h4).resolve_left (val_sub_one_ne_zero hb1)

include hb1 hx in
theorem blk_offdiag_zero_one (y : Qext K) : blk x 0 1 y = 0 := by
  have hu : ∀ z : Qext K, d8Emb ((1 : rootsOfUnity p (Qext K)), b) (Pi.single 1 z : QV K (Fin 2)) =
      Pi.single 1 ((((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * z) := by
    intro z
    rw [d8Emb_one_apply]
    funext i
    fin_cases i <;> simp
  have key : ∀ z : Qext K, blk x 0 1 z = blk x 0 1
      ((((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * z) := by
    intro z
    have h2 := hx (Pi.single 1 z)
    rw [hu] at h2
    have h3 := congrFun h2 0
    rw [d8Emb_one_apply] at h3
    simp only [Matrix.cons_val_zero] at h3
    rw [blk_apply, blk_apply]
    exact h3
  have hne := val_sub_one_ne_zero hb1
  set bb : Qext K := (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) with hbb
  have h5 : blk x 0 1 ((bb - 1) * ((bb - 1)⁻¹ * y)) = 0 := by
    have : (bb - 1) * ((bb - 1)⁻¹ * y) = bb * ((bb - 1)⁻¹ * y) - (bb - 1)⁻¹ * y := by ring
    rw [this, map_sub, ← key, sub_self]
  rwa [mul_inv_cancel_left₀ hne] at h5

include hx in
theorem blk_commute (y : Qext K) :
    blk x 1 1 ((((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * y) =
      (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * blk x 1 1 y := by
  have hu : d8Emb ((1 : rootsOfUnity p (Qext K)), b) (Pi.single 1 y : QV K (Fin 2)) =
      Pi.single 1 ((((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * y) := by
    rw [d8Emb_one_apply]
    funext i
    fin_cases i <;> simp
  have h2 := hx (Pi.single 1 y)
  rw [hu] at h2
  have h3 := congrFun h2 1
  rw [d8Emb_one_apply] at h3
  simp only [Matrix.cons_val_one] at h3
  rw [blk_apply, blk_apply]
  exact h3.symm

include hb1 hx in
theorem eq_blocks (v : QV K (Fin 2)) : x v = fun i => blk x i i (v i) := by
  conv_lhs => rw [eq_single_add v, map_add]
  funext i
  fin_cases i
  · simp only [Pi.add_apply, Fin.zero_eta]
    rw [blk_apply, ← blk_apply x 0 1, blk_offdiag_zero_one hb1 x hx, add_zero]
  · simp only [Pi.add_apply, Fin.mk_one]
    rw [blk_apply, ← blk_apply x 1 0, blk_offdiag_one_zero hb1 x hx, zero_add]

include hx in
theorem blk_one_one_linear (hspan : Submodule.span K {(1 : Qext K),
    (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K)} = ⊤) (y : Qext K) :
    blk x 1 1 y = y * blk x 1 1 1 := by
  have := smul_of_commute (M := Qext K) (blk x 1 1) hspan
    (fun v => by simpa [smul_eq_mul] using blk_commute x hx v) y 1
  simpa [smul_eq_mul] using this

end Commuting

theorem card_centralizer_le (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {b : rootsOfUnity p (Qext K)} (hb1 : b ≠ 1) :
    Nat.card (Subgroup.centralizer
        ({T8 hp hp2 hpq ((1 : rootsOfUnity p (Qext K)), b)} : Set ↥(M8 K))) ≤
      Nat.card K ^ 4 * (Nat.card K ^ 2 - 1) := by
  classical
  have hbp : (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ^ p = 1 := by
    have := (mem_rootsOfUnity p _).mp b.2
    simpa using congrArg Units.val this
  have hbne : (((b : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ≠ 1 := fun h =>
    hb1 (Subtype.ext (Units.ext h))
  have hspan := span_one_of_not_mem_range (not_mem_range_of_root hp hp2 hpq hbp hbne)
  have hcomm : ∀ x : ↥(Subgroup.centralizer
      ({T8 hp hp2 hpq ((1 : rootsOfUnity p (Qext K)), b)} : Set ↥(M8 K))), ∀ v,
      d8Emb ((1 : rootsOfUnity p (Qext K)), b) ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
        (x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (d8Emb ((1 : rootsOfUnity p (Qext K)), b) v) := by
    intro x v
    have h1 := Subgroup.mem_centralizer_iff.mp x.2 _ (Set.mem_singleton _)
    have h2 := congrArg (fun y : ↥(M8 K) => ((y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v)) h1
    exact h2
  have hnz : ∀ x : ↥(Subgroup.centralizer
      ({T8 hp hp2 hpq ((1 : rootsOfUnity p (Qext K)), b)} : Set ↥(M8 K))),
      blk ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 1 ≠ 0 := by
    intro x h0
    have hxc := hcomm x
    set xl : QV K (Fin 2) →ₗ[K] QV K (Fin 2) :=
      ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2))
    have hlin := blk_one_one_linear xl hxc hspan
    have hone : (Pi.single 1 (1 : Qext K) : QV K (Fin 2)) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    apply hone
    apply (x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)).injective
    rw [map_zero]
    have hb := eq_blocks hb1 xl hxc (Pi.single 1 (1 : Qext K))
    funext i
    have := congrFun hb i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply]
      have h00 : (x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 (1 : Qext K)) 0 =
          blk xl 0 1 1 := (blk_apply xl 0 1 1).symm
      rw [h00]
      exact blk_offdiag_zero_one hb1 xl hxc 1
    · simp only [Fin.mk_one, Pi.zero_apply]
      have h11 : (x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 (1 : Qext K)) 1 =
          blk xl 1 1 1 := (blk_apply xl 1 1 1).symm
      rw [h11]
      exact h0
  let Ψ : ↥(Subgroup.centralizer
      ({T8 hp hp2 hpq ((1 : rootsOfUnity p (Qext K)), b)} : Set ↥(M8 K))) →
      (Qext K →ₗ[K] Qext K) × (Qext K)ˣ := fun x =>
    (blk ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 0 0,
      Units.mk0 _ (hnz x))
  have hinj : Function.Injective Ψ := by
    intro x x' h
    obtain ⟨h0, h1⟩ := Prod.mk.inj h
    have h1' : blk ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 1 =
        blk ((x'.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 1 :=
      congrArg Units.val h1
    have hlin := blk_one_one_linear _ (hcomm x) hspan
    have hlin' := blk_one_one_linear _ (hcomm x') hspan
    have hblk : ∀ y, blk ((x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 y =
        blk ((x'.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 y := by
      intro y
      rw [hlin y, hlin' y, h1']
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have e1 := eq_blocks hb1 _ (hcomm x) v
    have e2 := eq_blocks hb1 _ (hcomm x') v
    rw [show (x.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v = _ from e1,
      show (x'.1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v = _ from e2]
    funext i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [h0]
    · simp only [Fin.mk_one]
      rw [hblk]
  have : Finite (Qext K →ₗ[K] Qext K) := Module.finite_of_finite K
  have hcard := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, Nat.card_units] at hcard
  have h4 : Nat.card (Qext K →ₗ[K] Qext K) = Nat.card K ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Qext K →ₗ[K] Qext K),
      Module.finrank_linearMap K K (Qext K) (Qext K), finrank_qext]
  rw [h4, FiniteField.natCard_extension K 2 2] at hcard
  exact hcard

end Small

section Big

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem sl2_card' (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem det_restrict (A : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    LinearEquiv.det ((Matrix.SpecialLinearGroup.toLin' A).restrictScalars K :
      QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have h1 : (((Matrix.SpecialLinearGroup.toLin' A).restrictScalars K :
      QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) =
      (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) (Qext K))).restrictScalars K := rfl
  rw [h1, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.SpecialLinearGroup.det_coe,
    map_one]
  rfl

@[expose] noncomputable def rhoL4 : Matrix.SpecialLinearGroup (Fin 2) (Qext K) →* ↥(M8 K) where
  toFun A := ⟨(Matrix.SpecialLinearGroup.toLin' A).restrictScalars K,
    (mem_M8_iff _).mpr (det_restrict A)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp

theorem rho_apply (A : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) (v : QV K (Fin 2)) :
    ((rhoL4 A : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (Qext K)) v := by
  show Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) (Qext K)) v = _
  rw [Matrix.toLin'_apply]

theorem rho_injective : Function.Injective (rhoL4 (K := K)) := by
  intro A B h
  apply Subtype.ext
  have h1 : (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) (Qext K)) : (Fin 2 → Qext K) →ₗ[Qext K] _) =
      Matrix.toLin' (B : Matrix (Fin 2) (Fin 2) (Qext K)) := by
    apply LinearMap.ext
    intro v
    have := congrArg (fun g : ↥(M8 K) => ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v)) h
    simpa [rho_apply] using this
  exact Matrix.toLin'.injective h1

theorem d8Emb_diag_apply (a : rootsOfUnity p (Qext K)) (w : QV K (Fin 2)) :
    d8Emb ((a, a) : D8Mod p (Qext K)) w =
      (((a : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) • w := by
  funext i
  fin_cases i
  · simp [d8Emb_apply_zero]
  · simp [d8Emb_apply_one]

theorem rho_commute (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (a : rootsOfUnity p (Qext K)) (A : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    T8 hp hp2 hpq (a, a) * rhoL4 A = rhoL4 A * T8 hp hp2 hpq (a, a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  show d8Emb ((a, a) : D8Mod p (Qext K)) (((rhoL4 A : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
    ((rhoL4 A : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (d8Emb ((a, a) : D8Mod p (Qext K)) v)
  rw [d8Emb_diag_apply, d8Emb_diag_apply, rho_apply, rho_apply, Matrix.mulVec_smul]

theorem conj_rho_mem_range (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {a : rootsOfUnity p (Qext K)} (ha1 : a ≠ 1) (x : ↥(M8 K))
    (hx : T8 hp hp2 hpq (a, a) * x = x * T8 hp hp2 hpq (a, a))
    (A : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    x * rhoL4 A * x⁻¹ ∈ (rhoL4 (K := K)).range := by
  classical
  have hap : (((a : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ^ p = 1 := by
    have := (mem_rootsOfUnity p _).mp a.2
    simpa using congrArg Units.val this
  have hane : (((a : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ≠ 1 := fun h =>
    ha1 (Subtype.ext (Units.ext h))
  have hspan := span_one_of_not_mem_range (not_mem_range_of_root hp hp2 hpq hap hane)
  set aa : Qext K := (((a : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) with haa
  have hxv : ∀ v : QV K (Fin 2), aa • (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (aa • v) := by
    intro v
    have h1 := congrArg (fun y : ↥(M8 K) => ((y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v)) hx
    simp only [haa] at h1 ⊢
    have h2 : d8Emb ((a, a) : D8Mod p (Qext K)) ((x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
        (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (d8Emb ((a, a) : D8Mod p (Qext K)) v) := h1
    rwa [d8Emb_diag_apply, d8Emb_diag_apply] at h2
  have hxinv : ∀ v : QV K (Fin 2), aa • (x⁻¹ : ↥(M8 K)).1 v = (x⁻¹ : ↥(M8 K)).1 (aa • v) := by
    intro v
    apply (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)).injective
    have h1 : (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((x⁻¹ : ↥(M8 K)).1 v) = v := by
      have := LinearEquiv.apply_symm_apply (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v
      exact this
    have h2 : (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((x⁻¹ : ↥(M8 K)).1 (aa • v)) = aa • v := by
      have := LinearEquiv.apply_symm_apply (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (aa • v)
      exact this
    rw [h2, ← hxv, h1]
  let X : QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2) :=
    { toFun := fun v => (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v
      map_add' := map_add _
      map_smul' := fun l v => by
        simpa using smul_of_commute (M := QV K (Fin 2))
          ((x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) hspan
          (fun w => (hxv w).symm) l v }
  let X' : QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2) :=
    { toFun := fun v => (x⁻¹ : ↥(M8 K)).1 v
      map_add' := map_add _
      map_smul' := fun l v => by
        simpa using smul_of_commute (M := QV K (Fin 2))
          (((x⁻¹ : ↥(M8 K)).1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
            QV K (Fin 2) →ₗ[K] QV K (Fin 2)) hspan (fun w => (hxinv w).symm) l v }
  have hXX' : X ∘ₗ X' = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact LinearEquiv.apply_symm_apply (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v
  set F : QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2) :=
    X ∘ₗ (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) (Qext K))) ∘ₗ X' with hF
  have hdetF : LinearMap.det F = 1 := by
    rw [hF, LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin',
      Matrix.SpecialLinearGroup.det_coe, one_mul, ← LinearMap.det_comp, hXX', LinearMap.det_id]
  have hdet : (LinearMap.toMatrix' F).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact hdetF
  obtain ⟨A'', hA''⟩ : ∃ A'' : Matrix.SpecialLinearGroup (Fin 2) (Qext K),
      (A'' : Matrix (Fin 2) (Fin 2) (Qext K)) = LinearMap.toMatrix' F :=
    ⟨⟨LinearMap.toMatrix' F, hdet⟩, rfl⟩
  refine ⟨A'', ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have h1 := rho_apply A'' v
  rw [hA''] at h1
  show ((rhoL4 A'' : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
    (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (((rhoL4 A : ↥(M8 K)) :
      QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((x⁻¹ : ↥(M8 K)).1 v))
  rw [h1, rho_apply A ((x⁻¹ : ↥(M8 K)).1 v), ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem card_sl2_qext :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Qext K)) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  rw [sl2_card', FiniteField.natCard_extension K 2 2, ← pow_mul]

theorem dvd_pow_four_sub_one {q : ℕ} (h : p ∣ q + 1) : p ∣ q ^ 4 - 1 := by
  have h1 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have := Nat.sq_sub_sq q 1
    simpa using this
  have h2 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    have := Nat.sq_sub_sq (q ^ 2) 1
    rw [← pow_mul] at this
    simpa using this
  rw [h2, h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) _

theorem bigAt_diag (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {a : rootsOfUnity p (Qext K)} (ha1 : a ≠ 1) :
    BigAt p (T8 hp hp2 hpq (a, a)) (fun n => Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ≤ n) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have h4 : 4 ≤ Nat.card (Qext K) := by
    rw [FiniteField.natCard_extension K 2 2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq2 2
  have : CharP (Qext K) 2 := charP_of_injective_algebraMap (algebraMap K (Qext K)).injective 2
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :=
    KCRootAxis.sl2_isSimpleGroup h4
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :=
    KCRootAxis.sl2_isPerfect h4
  let e : Matrix.SpecialLinearGroup (Fin 2) (Qext K) ≃* (rhoL4 (K := K)).range :=
    MonoidHom.ofInjective rho_injective
  have hcard : Nat.card (rhoL4 (K := K)).range = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← Nat.card_congr e.toEquiv, card_sl2_qext]
  refine ⟨(rhoL4 (K := K)).range, ?_, ?_, ?_, ?_, ?_, hcard.ge⟩
  · exact Group.IsPerfect.range rhoL4
  · exact e.symm.isSimpleGroup
  · have hdvd : p ∣ Nat.card (rhoL4 (K := K)).range := by
      rw [hcard]
      exact Dvd.dvd.mul_left (dvd_pow_four_sub_one hpq) _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨(x : ↥(M8 K)), x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  · rintro _ ⟨A, rfl⟩
    exact rho_commute hp hp2 hpq a A
  · intro x hx σ hσ
    obtain ⟨A, rfl⟩ := hσ
    exact conj_rho_mem_range hp hp2 hpq ha1 x hx A

theorem small_lt_big {q : ℕ} (hq : 2 ≤ q) : q ^ 4 * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h4 : 2 ≤ q ^ 2 := by nlinarith
  zify [h1, h2]
  have : ((q : ℤ) ^ 4) = ((q : ℤ) ^ 2) * ((q : ℤ) ^ 2) := by ring
  nlinarith [this, show (2 : ℤ) ≤ (q : ℤ) ^ 2 by exact_mod_cast h4]

end Big

end CFSG.RankThree.PartOne.KFOUT3
