module

public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFElation
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFTwD
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreTypeA
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution

public section

namespace CFSG.StandardType

namespace IOneFieldCF

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly

variable {d : ℕ} {K : Type} [Field K]

section Weights

@[expose] def Step (cls : Fin d → Fin d → Prop) (B : Matrix (Fin d) (Fin d) K) (j i : Fin d) :
    Prop :=
  cls j i ∨ B i j ≠ 0

theorem weights_all_of_ratio {cls : Fin d → Fin d → Prop} {B : Matrix (Fin d) (Fin d) K}
    {τ : K ≃+* K} {δ : Fin d → K} {lam : K} {i₀ i₁ : Fin d}
    (hcls : ∀ i j, cls i j → δ i = δ j) (hrel : ∀ i j, B i j ≠ 0 → δ i = lam * τ (δ j))
    (hall : ∀ i, Relation.ReflTransGen (Step cls B) i₀ i) (hB : B i₁ i₀ ≠ 0)
    (h1 : δ i₁ = δ i₀) : ∀ i, δ i = δ i₀ := by
  intro i
  have key : ∀ j, Relation.ReflTransGen (Step cls B) i₀ j → δ j = δ i₀ := by
    intro j hj
    induction hj with
    | refl => rfl
    | tail _ hstep ih =>
      rcases hstep with hc | hb
      · rw [← hcls _ _ hc, ih]
      · calc δ _ = lam * τ (δ _) := hrel _ _ hb
          _ = lam * τ (δ i₀) := by rw [ih]
          _ = δ i₁ := (hrel i₁ i₀ hB).symm
          _ = δ i₀ := h1
  exact key i (hall i)

end Weights

section Coord

theorem mulVec_mem_suppSub_of_closed {S : Set (Fin d)} {M : Matrix (Fin d) (Fin d) K}
    (hM : ∀ i j, j ∈ S → M i j ≠ 0 → i ∈ S) {x : Fin d → K} (hx : x ∈ suppSub (K := K) S) :
    M *ᵥ x ∈ suppSub (K := K) S := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hxj : x j = 0
  · rw [hxj, mul_zero]
  · have hjS : j ∈ S := by
      by_contra hjn
      exact hxj (hx j hjn)
    have : M i j = 0 := by
      by_contra hne
      exact hi (hM i j hjS hne)
    rw [this, zero_mul]

variable [Finite K]

theorem inv_mulVec_mem_of_mem {S : Set (Fin d)} (M : GL (Fin d) K)
    (hM : ∀ x ∈ suppSub (K := K) S,
      (M : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ suppSub (K := K) S) {w : Fin d → K}
    (hw : w ∈ suppSub (K := K) S) :
    ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w ∈ suppSub (K := K) S := by
  let F : suppSub (K := K) S → suppSub (K := K) S := fun x =>
    ⟨(M : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K), hM x x.2⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 : (M : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) =
        (M : Matrix (Fin d) (Fin d) K) *ᵥ (y : Fin d → K) := congrArg Subtype.val hxy
    apply Subtype.ext
    have h2 := congrArg (fun v => ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) h1
    simpa [Matrix.mulVec_mulVec] using h2
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have h1 : (M : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) = w := congrArg Subtype.val hx
  have h2 : ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w = x := by
    rw [← h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [h2]
  exact x.2

end Coord

section Diag

theorem eq_diagonal_of_offDiag {M : Matrix (Fin d) (Fin d) K}
    (h : ∀ i j, i ≠ j → M i j = 0) : M = diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [h i j hij, diagonal_apply_ne _ hij]

theorem diag_ne_zero {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (i : Fin d) : t i ≠ 0 := by
  intro h0
  have hu := Matrix.isUnits_det_units D
  rw [hD, Matrix.det_diagonal, Finset.prod_eq_zero (Finset.mem_univ i) h0] at hu
  exact not_isUnit_zero hu

theorem diag_mul_apply {D M : Matrix (Fin d) (Fin d) K} (hD : ∀ i j, i ≠ j → D i j = 0)
    (i j : Fin d) : (D * M) i j = D i i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hD i k (Ne.symm hk), zero_mul])
    (by simp)]

theorem mul_diag_apply {D M : Matrix (Fin d) (Fin d) K} (hD : ∀ i j, i ≠ j → D i j = 0)
    (i j : Fin d) : (M * D) i j = M i j * D j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hD k j hk, mul_zero])
    (by simp)]

end Diag

theorem card_pow_eq_one_le {p : ℕ} (hp : 0 < p) : Nat.card {x : K // x ^ p = 1} ≤ p := by
  classical
  have hmem : ∀ x : K, x ∈ (Polynomial.nthRoots p (1 : K)).toFinset ↔ x ^ p = 1 := fun x => by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp]
  calc Nat.card {x : K // x ^ p = 1}
      = Nat.card ↥((Polynomial.nthRoots p (1 : K)).toFinset) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
    _ = (Polynomial.nthRoots p (1 : K)).toFinset.card :=
        Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ ≤ Multiset.card (Polynomial.nthRoots p (1 : K)) := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

section Comm

variable [Finite K]

theorem rel_of_comm (hd : 3 ≤ d) {B D : GL (Fin d) K} {τ : K ≃+* K}
    {f' φ : MulAut (projectiveSL d K)} (hf' : f' = conjAut d K B * fieldAut d K τ)
    (hDφ : conjAut d K D = φ) (hcomm : φ * f' = f' * φ) :
    ∃ a : Kˣ, ((D * B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (a : K) • ((B * GeneralLinearGroup.map (τ : K →+* K) D : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) := by
  have h1 : conjAut d K (D * B) * fieldAut d K τ =
      conjAut d K (B * GeneralLinearGroup.map (τ : K →+* K) D) * fieldAut d K τ := by
    calc conjAut d K (D * B) * fieldAut d K τ
        = conjAut d K D * (conjAut d K B * fieldAut d K τ) := by rw [map_mul, mul_assoc]
      _ = φ * f' := by rw [hDφ, hf']
      _ = f' * φ := hcomm
      _ = conjAut d K B * (fieldAut d K τ * conjAut d K D) := by rw [hf', hDφ, mul_assoc]
      _ = conjAut d K B * (conjAut d K (GeneralLinearGroup.map (τ : K →+* K) D) *
            fieldAut d K τ) := by rw [fieldAut_mul_conjAut]
      _ = conjAut d K (B * GeneralLinearGroup.map (τ : K →+* K) D) * fieldAut d K τ := by
          rw [map_mul, mul_assoc]
  exact eq_smul_of_conjAut_eq hd (mul_right_cancel h1)

theorem diag_rel_of_eq {B D : GL (Fin d) K} {τ : K ≃+* K} {a : K}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0)
    (ha : ((D * B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      a • ((B * GeneralLinearGroup.map (τ : K →+* K) D : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) (i j : Fin d) (hB : (B : Matrix (Fin d) (Fin d) K) i j ≠ 0) :
    (D : Matrix (Fin d) (Fin d) K) i i = a * τ ((D : Matrix (Fin d) (Fin d) K) j j) := by
  have hmap : ∀ k l : Fin d, k ≠ l →
      ((GeneralLinearGroup.map (τ : K →+* K) D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k l =
        0 := fun k l hkl => by
    rw [Matrix.GeneralLinearGroup.map_apply, hD k l hkl]
    exact map_zero _
  have h1 := congrFun (congrFun ha i) j
  rw [Units.val_mul, Units.val_mul, diag_mul_apply hD, Matrix.smul_apply,
    mul_diag_apply hmap, smul_eq_mul, Matrix.GeneralLinearGroup.map_apply] at h1
  refine mul_left_cancel₀ hB ?_
  have e : ((τ : K →+* K) ((D : Matrix (Fin d) (Fin d) K) j j)) =
      τ ((D : Matrix (Fin d) (Fin d) K) j j) := rfl
  rw [e] at h1
  linear_combination h1

end Comm


section Frame

variable [Finite K] [CharP K 2]

theorem exists_twoSubgroup_frame (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (κ : MulAut (projectiveSL d K)) {Eb : Subgroup (MulAut (projectiveSL d K))}
    (hEb : IsElemAbelian p Eb) (hcard : p < Nat.card Eb)
    (hdiag : ∀ φ ∈ Eb, ∃ D : GL (Fin d) K,
      (∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0) ∧ conjAut d K D = κ * φ * κ⁻¹)
    {f : MulAut (projectiveSL d K)} (hf : f ^ p = 1) (hfc : ∀ φ ∈ Eb, φ * f = f * φ) :
    ∃ U : Subgroup (projectiveSL d K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ φ ∈ Eb, ∀ u ∈ U, φ u ∈ U) ∧ ∀ u ∈ U, f u ∈ U := by
  classical
  have := Fact.mk hp
  have hd0 : 0 < d := by omega
  set i₀ : Fin d := ⟨0, hd0⟩ with hi₀
  set f' : MulAut (projectiveSL d K) := κ * f * κ⁻¹ with hf'
  have hf'p : f' ^ p = 1 := by rw [hf', conj_pow, hf, mul_one, mul_inv_cancel]
  have hodd : Odd (orderOf f') := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hf'p) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hp2
  obtain ⟨B, τ, hBτ⟩ := mem_semilinearAutGroup_iff.mp
    (CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd hd
      hodd)
  have hrel : ∀ D : GL (Fin d) K, (∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0) →
      (∃ φ ∈ Eb, conjAut d K D = κ * φ * κ⁻¹) →
      ∃ a : K, ∀ i j, (B : Matrix (Fin d) (Fin d) K) i j ≠ 0 →
        (D : Matrix (Fin d) (Fin d) K) i i = a * τ ((D : Matrix (Fin d) (Fin d) K) j j) := by
    rintro D hDd ⟨φ, hφ, hDφ⟩
    have hcomm : conjAut d K D * f' = f' * conjAut d K D := by
      rw [hDφ, hf']
      have h := hfc φ hφ
      calc κ * φ * κ⁻¹ * (κ * f * κ⁻¹) = κ * (φ * f) * κ⁻¹ := by group
        _ = κ * (f * φ) * κ⁻¹ := by rw [h]
        _ = κ * f * κ⁻¹ * (κ * φ * κ⁻¹) := by group
    obtain ⟨a, ha⟩ := rel_of_comm hd hBτ rfl hcomm
    exact ⟨(a : K), fun i j hij => diag_rel_of_eq hDd ha i j hij⟩
  let cls : Fin d → Fin d → Prop := fun i j => ∀ D : GL (Fin d) K,
    (∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0) →
    (∃ φ ∈ Eb, conjAut d K D = κ * φ * κ⁻¹) →
    (D : Matrix (Fin d) (Fin d) K) i i = (D : Matrix (Fin d) (Fin d) K) j j
  by_cases hall : ∀ i, Relation.ReflTransGen (Step cls (B : Matrix (Fin d) (Fin d) K)) i₀ i
  · exfalso
    obtain ⟨i₁, hi₁⟩ : ∃ i₁, (B : Matrix (Fin d) (Fin d) K) i₁ i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h1 := Matrix.det_eq_zero_of_column_eq_zero i₀ hcon
      have h2 := Matrix.isUnits_det_units B
      rw [h1] at h2
      exact not_isUnit_zero h2
    choose! Dm hDm using hdiag
    have hDdg : ∀ φ ∈ Eb, (Dm φ : Matrix (Fin d) (Fin d) K) =
        diagonal (fun i => (Dm φ : Matrix (Fin d) (Fin d) K) i i) :=
      fun φ hφ => eq_diagonal_of_offDiag (hDm φ hφ).1
    have hDne : ∀ φ ∈ Eb, ∀ i, (Dm φ : Matrix (Fin d) (Fin d) K) i i ≠ 0 :=
      fun φ hφ i => diag_ne_zero (hDdg φ hφ) i
    let Θ : Eb → K := fun φ =>
      (Dm φ : Matrix (Fin d) (Fin d) K) i₁ i₁ / (Dm φ : Matrix (Fin d) (Fin d) K) i₀ i₀
    have hΘp : ∀ φ : Eb, Θ φ ^ p = 1 := by
      intro φ
      have h1 : conjAut d K ((Dm φ) ^ p) = 1 := by
        rw [map_pow, (hDm φ φ.2).2, conj_pow, hEb.2 φ φ.2, mul_one, mul_inv_cancel]
      obtain ⟨u, hu⟩ := (conjAut_eq_one_iff hd _).mp h1
      have h2 : ∀ i, ((Dm φ : Matrix (Fin d) (Fin d) K) i i) ^ p = (u : K) := by
        intro i
        have h3 := congrFun (congrFun (congrArg (fun M : GL (Fin d) K =>
          (M : Matrix (Fin d) (Fin d) K)) hu) i) i
        simp only [Units.val_pow_eq_pow_val] at h3
        rw [hDdg φ φ.2, Matrix.diagonal_pow] at h3
        simpa using h3
      simp only [Θ, div_pow, h2 i₁, h2 i₀]
      exact div_self (Units.ne_zero u)
    have hΘinj : Function.Injective Θ := by
      intro φ₁ φ₂ hφ
      have hD₁ := hDdg φ₁ φ₁.2
      have hD₂ := hDdg φ₂ φ₂.2
      set D : GL (Fin d) K := Dm φ₁ * (Dm φ₂)⁻¹ with hD
      have hinv : (((Dm φ₂)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          diagonal (fun k => ((Dm φ₂ : Matrix (Fin d) (Fin d) K) k k)⁻¹) :=
        TypeA.coe_inv_of_diagonal hD₂
      have hDmat : (D : Matrix (Fin d) (Fin d) K) = diagonal (fun k =>
          (Dm φ₁ : Matrix (Fin d) (Fin d) K) k k * ((Dm φ₂ : Matrix (Fin d) (Fin d) K) k k)⁻¹) := by
        rw [hD, Units.val_mul]
        conv_lhs => rw [hD₁, hinv]
        rw [Matrix.diagonal_mul_diagonal]
      have hDdiag : ∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0 := by
        intro i j hij
        rw [hDmat, diagonal_apply_ne _ hij]
      have hDeq : conjAut d K D = κ * ((φ₁ : MulAut (projectiveSL d K)) *
          (φ₂ : MulAut (projectiveSL d K))⁻¹) * κ⁻¹ := by
        rw [hD, map_mul, map_inv, (hDm φ₁ φ₁.2).2, (hDm φ₂ φ₂.2).2]
        group
      have hDmem : ∃ φ ∈ Eb, conjAut d K D = κ * φ * κ⁻¹ :=
        ⟨(φ₁ : MulAut (projectiveSL d K)) * (φ₂ : MulAut (projectiveSL d K))⁻¹,
          Eb.mul_mem φ₁.2 (Eb.inv_mem φ₂.2), hDeq⟩
      obtain ⟨a, ha⟩ := hrel D hDdiag hDmem
      have hcls : ∀ i j, cls i j → (D : Matrix (Fin d) (Fin d) K) i i =
          (D : Matrix (Fin d) (Fin d) K) j j := fun i j h => h D hDdiag hDmem
      have hratio : (D : Matrix (Fin d) (Fin d) K) i₁ i₁ =
          (D : Matrix (Fin d) (Fin d) K) i₀ i₀ := by
        rw [hDmat]
        simp only [diagonal_apply_eq]
        have h1 := hDne φ₁ φ₁.2
        have h2 := hDne φ₂ φ₂.2
        have h3 : (Dm φ₁ : Matrix (Fin d) (Fin d) K) i₁ i₁ /
            (Dm φ₁ : Matrix (Fin d) (Fin d) K) i₀ i₀ =
              (Dm φ₂ : Matrix (Fin d) (Fin d) K) i₁ i₁ /
              (Dm φ₂ : Matrix (Fin d) (Fin d) K) i₀ i₀ := hφ
        have h4 := h1 i₁
        have h5 := h1 i₀
        have h6 := h2 i₁
        have h7 := h2 i₀
        field_simp at h3 ⊢
        linear_combination h3
      have hall' := weights_all_of_ratio hcls ha hall hi₁ hratio
      have hD0 : (D : Matrix (Fin d) (Fin d) K) i₀ i₀ ≠ 0 :=
        diag_ne_zero (eq_diagonal_of_offDiag hDdiag) i₀
      have hsc : D = GeneralLinearGroup.scalar (Fin d) (Units.mk0 _ hD0) := by
        apply Units.ext
        conv_lhs => rw [eq_diagonal_of_offDiag hDdiag]
        rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
        congr 1
        funext i
        exact hall' i
      have h1 : conjAut d K D = 1 := by
        rw [hsc]
        exact conjAut_scalar _
      have h2 : (φ₁ : MulAut (projectiveSL d K)) * (φ₂ : MulAut (projectiveSL d K))⁻¹ = 1 := by
        rw [hDeq] at h1
        calc (φ₁ : MulAut (projectiveSL d K)) * (φ₂ : MulAut (projectiveSL d K))⁻¹
            = κ⁻¹ * (κ * ((φ₁ : MulAut (projectiveSL d K)) *
                (φ₂ : MulAut (projectiveSL d K))⁻¹) * κ⁻¹) * κ := by group
          _ = 1 := by rw [h1]; group
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    have hinj' : Function.Injective (fun φ : Eb => (⟨Θ φ, hΘp φ⟩ : {x : K // x ^ p = 1})) :=
      fun φ₁ φ₂ h => hΘinj (congrArg Subtype.val h)
    have hle : Nat.card Eb ≤ p :=
      (Nat.card_le_card_of_injective _ hinj').trans (card_pow_eq_one_le hp.pos)
    omega
  · push Not at hall
    obtain ⟨i', hi'⟩ := hall
    set S : Set (Fin d) :=
      {i | Relation.ReflTransGen (Step cls (B : Matrix (Fin d) (Fin d) K)) i₀ i} with hS
    have hi₀S : i₀ ∈ S := Relation.ReflTransGen.refl
    have hi'S : i' ∉ S := hi'
    have hBcl : ∀ i j, j ∈ S → (B : Matrix (Fin d) (Fin d) K) i j ≠ 0 → i ∈ S :=
      fun i j hj hne => Relation.ReflTransGen.tail hj (Or.inr hne)
    have hBW : ∀ x ∈ suppSub (K := K) S,
        (B : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ suppSub (K := K) S :=
      fun x hx => mulVec_mem_suppSub_of_closed hBcl hx
    have hBW' : ∀ x ∈ suppSub (K := K) S,
        ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ suppSub (K := K) S :=
      fun x hx => inv_mulVec_mem_of_mem B hBW hx
    have hτW : ∀ v ∈ suppSub (K := K) S, (fun i => τ (v i)) ∈ suppSub (K := K) S :=
      fun v hv i hi => by simp [hv i hi]
    have hτW' : ∀ v ∈ suppSub (K := K) S, (fun i => τ.symm (v i)) ∈ suppSub (K := K) S :=
      fun v hv i hi => by simp [hv i hi]
    refine ⟨(elProj (suppSub (K := K) S)).comap κ.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro h
      apply elProj_suppSub_ne_bot (K := K) hi₀S hi'S
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := κ.toMonoidHom) κ.surjective
        (elProj (suppSub (K := K) S)), h, Subgroup.map_bot]
    · exact (isPGroup_elProj _).comap_of_injective _ κ.injective
    · intro φ hφ u hu
      obtain ⟨D, hDd, hDφ⟩ := hdiag φ hφ
      have hDW : ∀ x ∈ suppSub (K := K) S,
          (D : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ suppSub (K := K) S := fun x hx =>
        mulVec_mem_suppSub_of_closed (fun i j hj hne => by
          by_cases hij : i = j
          · exact hij ▸ hj
          · exact absurd (hDd i j hij) hne) hx
      have h1 : κ (φ u) = conjAut d K D (κ u) := by
        rw [hDφ]
        simp [MulAut.mul_apply, MulAut.inv_apply_self]
      change κ (φ u) ∈ elProj (suppSub (K := K) S)
      rw [h1]
      exact conjAut_mem_elProj D hDW (fun w hw => inv_mulVec_mem_of_mem D hDW hw) (κ u) hu
    · intro u hu
      change κ (f u) ∈ elProj (suppSub (K := K) S)
      have h1 : κ (f u) = conjAut d K B (fieldAut d K τ (κ u)) := by
        have h2 : κ (f u) = f' (κ u) := by
          simp [hf', MulAut.mul_apply, MulAut.inv_apply_self]
        rw [h2, hBτ, MulAut.mul_apply]
      rw [h1]
      exact conjAut_mem_elProj B hBW hBW' _ (fieldAut_mem_elProj τ hτW hτW' _ hu)

end Frame

section Bound

variable [Finite K] [CharP K 2]

theorem ggInnerDiagBound_projSL_dvd {r p : ℕ} (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hr : d - 2 ≤ r ∨ d ≤ 5) :
    GGInnerDiagBound p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh hEbI hEb hr' h3 hle hEh hcard hnot
  have hpow : p ^ (d - 2) ≤ Nat.card Eb := by
    rcases hr with h | h
    · exact (Nat.pow_le_pow_right hp.pos h).trans hr'
    · exact (Nat.pow_le_pow_right hp.pos (by omega)).trans h3
  obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds hp hp2 hpK Eb hEb hEbI hpow h3
  obtain ⟨f, hfEh, hfI⟩ : ∃ f ∈ Eh, f ∉ Set.range (conjAut d K) := by
    by_contra hcon
    push Not at hcon
    exact hnot fun φ hφ => hcon φ hφ
  have hdiag : ∀ φ ∈ Eb, ∃ D : GL (Fin d) K,
      (∀ i j, i ≠ j → (D : Matrix (Fin d) (Fin d) K) i j = 0) ∧
        conjAut d K D = conjAut d K A₀ * φ * (conjAut d K A₀)⁻¹ := by
    intro φ hφ
    obtain ⟨A, rfl⟩ := hEbI hφ
    refine ⟨A₀ * A * A₀⁻¹, fun i j hij => ?_, by rw [map_mul, map_mul, map_inv]⟩
    have h := hA₀ A hφ i j hij
    rwa [Units.val_mul, Units.val_mul]
  have hp3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hfc : ∀ φ ∈ Eb, φ * f = f * φ := fun φ hφ =>
    TableB.IsElemAbelian.comm hEh (hle hφ) hfEh
  obtain ⟨U, hU1, hU2, hUEb, hUf⟩ := exists_twoSubgroup_frame hd hp hp2 (conjAut d K A₀) hEb
    (lt_of_lt_of_le hp3 h3) hdiag (hEh.2 f hfEh) hfc
  have : Finite U := inferInstance
  have hstab : Eb ⊔ Subgroup.zpowers f ≤ OrthBstarOdd.stabSub U :=
    sup_le (fun φ hφ => OrthBstarOdd.mem_stabSub (hUEb φ hφ))
      (Subgroup.zpowers_le.mpr (OrthBstarOdd.mem_stabSub hUf))
  have hlt : Eb < Eb ⊔ Subgroup.zpowers f := lt_of_le_of_ne le_sup_left fun heq =>
    hfI (hEbI (heq ▸ (le_sup_right : Subgroup.zpowers f ≤ Eb ⊔ Subgroup.zpowers f)
      (Subgroup.mem_zpowers f)))
  have hle' : Eb ⊔ Subgroup.zpowers f ≤ Eh := sup_le hle (Subgroup.zpowers_le.mpr hfEh)
  have hE'Eh : Eb ⊔ Subgroup.zpowers f = Eh :=
    eq_of_lt_of_card_le hp ((isPGroup_of_isElemAbelian hEh).to_le hle') hlt hle' hcard
  exact ⟨U, hU1, hU2, fun φ hφ u hu =>
    OrthBstarOdd.apply_mem_of_mem_stabSub (hstab (hE'Eh ▸ hφ)) hu⟩

end Bound

end IOneFieldCF

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag IOneFieldCF

theorem recipeLinear_innerDiagBound_dvd {d m p : ℕ} (hp : p.Prime) (hpN : p ∣ 2 ^ m - 1)
    (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ m) Q) :
    LargeEvenRecipeLinear d (2 ^ m) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  have hI' : ∀ φ, MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) →
      φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ :=
    fun _ hφ => TypeA.mem_of_congr_recipeEquiv_mem hφ
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4 | h5
  · subst h3
    have hlift : GGTorusLift p 0 (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :=
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num)))
    exact ⟨0, hlift, ggInnerDiagBound_of_mulEquiv (TypeA.recipeEquiv 3 K) hI hI'
      (ggInnerDiagBound_projSL_dvd (by norm_num) hp hp2 hpK (Or.inr (by norm_num)))⟩
  · subst h4
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have hsec : TypeA.SLHasSections d K := TypeA.slHasSections_of_five_le h5
    exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
      (TypeA.ggTorusLift_sub_two hp hpK hd hsec),
      ggInnerDiagBound_of_mulEquiv (TypeA.recipeEquiv d K) hI hI'
        (ggInnerDiagBound_projSL_dvd hd3 hp hp2 hpK (Or.inl le_rfl))⟩

end CFSG.StandardType
