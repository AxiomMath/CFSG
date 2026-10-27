module

public import CFSG.RankThree.Classical.SemilinearFixedBasis

public section

namespace CFSG.RankThree.Classical2

open Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

section TwistedProd

variable {R : Type*} [CommRing R] {n : ℕ}

@[expose] def twistedProd (φ : R → R) (A : Matrix (Fin n) (Fin n) R) (j : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  ((List.range j).map fun i => A.map (φ^[i])).prod

theorem twistedProd_zero (φ : R → R) (A : Matrix (Fin n) (Fin n) R) : twistedProd φ A 0 = 1 := by
  simp [twistedProd]

theorem twistedProd_succ (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R) (j : ℕ) :
    twistedProd φ A (j + 1) = A * (twistedProd φ A j).map φ := by
  rw [twistedProd, List.range_succ_eq_map, List.map_cons, List.prod_cons, Function.iterate_zero,
    Matrix.map_id, List.map_map]
  congr 1
  change _ = φ.mapMatrix (twistedProd φ A j)
  rw [twistedProd, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_map,
    Function.iterate_succ']

theorem map_iterate_eq_self {α : Type*} {g : α → α} {M : Matrix (Fin n) (Fin n) α}
    (h : M.map g = M) (k : ℕ) : M.map (g^[k]) = M := by
  induction k with
  | zero => exact Matrix.map_id M
  | succ k ih => rw [Function.iterate_succ', ← Matrix.map_map, ih, h]

theorem twistedProd_add (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R) (a b : ℕ) :
    twistedProd φ A (a + b) = twistedProd φ A a * (twistedProd φ A b).map (⇑φ)^[a] := by
  induction a with
  | zero => rw [Nat.zero_add, twistedProd_zero, Matrix.one_mul, Function.iterate_zero,
      Matrix.map_id]
  | succ a ih =>
    rw [Nat.add_right_comm, twistedProd_succ, ih, twistedProd_succ, Matrix.mul_assoc]
    congr 1
    change φ.mapMatrix (twistedProd φ A a * (twistedProd φ A b).map (⇑φ)^[a]) = _
    rw [map_mul]
    congr 1
    rw [RingHom.mapMatrix_apply, Matrix.map_map, ← Function.iterate_succ']

theorem twistedProd_mul (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R) {d : ℕ}
    (hfix : (twistedProd φ A d).map (⇑φ)^[d] = twistedProd φ A d) (k : ℕ) :
    twistedProd φ A (d * k) = twistedProd φ A d ^ k := by
  induction k with
  | zero => rw [Nat.mul_zero, twistedProd_zero, pow_zero]
  | succ k ih =>
    rw [Nat.mul_succ, twistedProd_add, ih, Function.iterate_mul,
      map_iterate_eq_self hfix k, pow_succ]

theorem iterate_eq_twistedProd_mulVec (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R)
    (T : (Fin n → R) → Fin n → R) (hT : ∀ v, T v = A *ᵥ (φ ∘ v)) (j : ℕ) (v : Fin n → R) :
    T^[j] v = twistedProd φ A j *ᵥ ((⇑φ)^[j] ∘ v) := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, twistedProd_zero, Matrix.one_mulVec,
      Function.iterate_zero, Function.id_comp]
  | succ j ih =>
    have hmv : ∀ (M : Matrix (Fin n) (Fin n) R) (w : Fin n → R),
        φ ∘ (M *ᵥ w) = M.map φ *ᵥ (φ ∘ w) := fun M w => funext fun i => RingHom.map_mulVec φ M w i
    rw [Function.iterate_succ_apply', ih, hT, hmv, Matrix.mulVec_mulVec, ← twistedProd_succ,
      Function.iterate_succ', Function.comp_assoc]

theorem map_twistedProd {S : Type*} [CommRing S] (φ : R → R) (φ' : S → S) (ψ : R →+* S)
    (hψ : ∀ c, ψ (φ c) = φ' (ψ c)) (A : Matrix (Fin n) (Fin n) R) (j : ℕ) :
    (twistedProd φ A j).map ψ = twistedProd φ' (A.map ψ) j := by
  change ψ.mapMatrix (twistedProd φ A j) = _
  rw [twistedProd, map_list_prod, List.map_map, twistedProd]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1
  funext c
  exact (Function.Semiconj.iterate_right (f := ψ) (ga := φ) (gb := φ') hψ i) c

theorem list_prod_apply_mem {S : Subring R} (l : List (Matrix (Fin n) (Fin n) R))
    (hl : ∀ M ∈ l, ∀ i j, M i j ∈ S) (i j : Fin n) : l.prod i j ∈ S := by
  induction l generalizing i j with
  | nil =>
    rw [List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | cons M l ih =>
    rw [List.prod_cons, Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem (hl M (List.mem_cons_self ..) i k)
      (ih (fun M' hM' => hl M' (List.mem_cons_of_mem _ hM')) k j)

end TwistedProd

section FixedField

variable {Ω : Type*} [Field Ω]

theorem natCard_setOf_pow_eq_self [IsAlgClosed Ω] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP Ω ℓ]
    {e : ℕ} (he : e ≠ 0) : Nat.card {c : Ω | c ^ ℓ ^ e = c} = ℓ ^ e := by
  set P : Polynomial Ω := Polynomial.X ^ ℓ ^ e - Polynomial.X with hP
  have hsep : P.Separable := galois_poly_separable ℓ (ℓ ^ e) (dvd_pow_self ℓ he)
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := Ω) hsep (IsAlgClosed.splits _)
  rw [hP, FiniteField.X_pow_card_pow_sub_X_natDegree_eq Ω he hℓ.out.one_lt] at hcard
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero Ω he hℓ.out.one_lt
  have hset : P.rootSet Ω = {c : Ω | c ^ ℓ ^ e = c} := by
    ext c
    rw [Polynomial.mem_rootSet]
    change P ≠ 0 ∧ Polynomial.aeval c P = 0 ↔ c ^ ℓ ^ e = c
    rw [and_iff_right hP0, hP, map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
  rw [← hset, Nat.card_eq_fintype_card, hcard]

theorem pow_pow_eq_self {M : Type*} [Monoid M] {c : M} {a : ℕ} (h : c ^ a = c) (k : ℕ) :
    c ^ a ^ k = c := by
  induction k with
  | zero => rw [pow_zero, pow_one]
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

end FixedField

section Solution

variable {k : Type*} [Field k] {Ω : Type*} [Field Ω] {n : ℕ}

theorem exists_lang_solution (ι : k →+* Ω) (σ : k →+* k) {q : ℕ} (hσ : ∀ c, ι (σ c) = ι c ^ q)
    (A' B : Matrix (Fin n) (Fin n) k) (hB : IsUnit B.det) (hfix : A' * B.map σ = B) :
    ∃ H : GL (Fin n) Ω, (H : Matrix (Fin n) (Fin n) Ω) = B⁻¹.map ι ∧
      (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) = B.map ι ∧
      A'.map ι =
        (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) * (H : Matrix (Fin n) (Fin n) Ω).map (· ^ q) := by
  set Bu : GL (Fin n) k := (Matrix.isUnit_iff_isUnit_det B).mpr hB |>.unit with hBu
  have hBu' : (Bu : Matrix (Fin n) (Fin n) k) = B := rfl
  have hBinv : (↑Bu⁻¹ : Matrix (Fin n) (Fin n) k) = B⁻¹ := by
    rw [Matrix.coe_units_inv, hBu']
  refine ⟨Matrix.GeneralLinearGroup.map ι Bu⁻¹, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hBinv, Matrix.map_apply]
  · ext i j
    rw [← map_inv, inv_inv, Matrix.GeneralLinearGroup.map_apply, hBu', Matrix.map_apply]
  · have hσB : B.map σ * B⁻¹.map σ = 1 := by
      change σ.mapMatrix B * σ.mapMatrix B⁻¹ = 1
      rw [← map_mul, Matrix.mul_nonsing_inv B hB, map_one]
    have hA' : A' = B * B⁻¹.map σ := by
      calc A' = A' * (B.map σ * B⁻¹.map σ) := by rw [hσB, Matrix.mul_one]
        _ = (A' * B.map σ) * B⁻¹.map σ := (Matrix.mul_assoc _ _ _).symm
        _ = B * B⁻¹.map σ := by rw [hfix]
    have h1 : (↑(Matrix.GeneralLinearGroup.map ι Bu⁻¹)⁻¹ : Matrix (Fin n) (Fin n) Ω) = B.map ι := by
      ext i j
      rw [← map_inv, inv_inv, Matrix.GeneralLinearGroup.map_apply, hBu', Matrix.map_apply]
    have h2 : ((Matrix.GeneralLinearGroup.map ι Bu⁻¹ : GL (Fin n) Ω) :
        Matrix (Fin n) (Fin n) Ω).map (· ^ q) = (B⁻¹.map σ).map ι := by
      ext i j
      rw [Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply, hBinv, Matrix.map_apply,
        Matrix.map_apply, hσ]
    rw [h1, h2, hA']
    change ι.mapMatrix (B * B⁻¹.map σ) = ι.mapMatrix B * ι.mapMatrix (B⁻¹.map σ)
    rw [map_mul]

theorem exists_fixed_det_eq_one (σ : k →+* k) (hn : 1 ≤ n) (A' B : Matrix (Fin n) (Fin n) k)
    (hA' : A'.det = 1) (hB : IsUnit B.det) (hfix : A' * B.map σ = B) :
    ∃ B₁ : Matrix (Fin n) (Fin n) k, B₁.det = 1 ∧ A' * B₁.map σ = B₁ := by
  set c := B.det with hc
  have hc0 : c ≠ 0 := hB.ne_zero
  have hσc : σ c = c := by
    have h := congrArg Matrix.det hfix
    rw [Matrix.det_mul, hA', one_mul] at h
    rw [hc, RingHom.map_det]
    exact h
  set i₀ : Fin n := ⟨0, by omega⟩
  set D : Matrix (Fin n) (Fin n) k := diagonal fun i => if i = i₀ then c⁻¹ else 1 with hD
  have hσD : D.map σ = D := by
    rw [hD, diagonal_map (map_zero σ)]
    congr 1
    funext i
    split_ifs
    · rw [map_inv₀, hσc]
    · exact map_one σ
  refine ⟨B * D, ?_, ?_⟩
  · rw [Matrix.det_mul, ← hc, hD, det_diagonal, Finset.prod_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hc0
  · change A' * σ.mapMatrix (B * D) = B * D
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hσD, ← Matrix.mul_assoc, hfix]

end Solution

section Lang

variable {ℓ f : ℕ} {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {n : ℕ}

theorem exists_isUnit_det_fixed {k : Type*} [Field k] {e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) (σ : k ≃+* k) {h : ℕ} (hσ : orderOf σ = h)
    (A' : Matrix (Fin n) (Fin n) k) (hA' : IsUnit A'.det)
    (hper : ∀ v : Fin n → k, twistedProd σ A' h *ᵥ ((⇑σ)^[h] ∘ v) = v) :
    ∃ B : Matrix (Fin n) (Fin n) k, IsUnit B.det ∧ A' * B.map σ = B := by
  let Aeq : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
    Matrix.toLinearEquiv' A' (Matrix.invertibleOfIsUnitDet A' hA')
  let T : (Fin n → k) ≃+ (Fin n → k) :=
    (AddEquiv.piCongrRight fun _ => σ.toAddEquiv).trans Aeq.toAddEquiv
  have hT : ∀ v, T v = A' *ᵥ (σ ∘ v) := fun v => by
    change Aeq (fun i => σ (v i)) = _
    rw [← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    rfl
  have ha : ∀ (c : k) (v : Fin n → k), T (c • v) = σ c • T v := fun c v => by
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hah : ∀ v, (⇑T)^[h] v = v := fun v => by
    rw [iterate_eq_twistedProd_mulVec (σ : k →+* k) A' T hT h v]
    exact hper v
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    semilinear_fixed_basis hℓ he hk σ hσ (Module.finrank_fin_fun k) T ha hah
  refine ⟨(Pi.basisFun k (Fin n)).toMatrix b, ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact (Pi.basisFun k (Fin n)).isUnit_det b
  · ext i j
    have h1 := congrFun (hb j) i
    rw [hT] at h1
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, ← h1, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl

theorem matrix_frobenius_lang_of_le (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) [IsAlgClosure K Ω] (hn : 1 ≤ n) (A : GL (Fin n) Ω)
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hAL : ∀ i j, (A : Matrix (Fin n) (Fin n) Ω) i j ∈ L) :
    let q := ℓ ^ f
    let d := Module.finrank K L
    let N := ((List.range d).map fun i => (A : Matrix (Fin n) (Fin n) Ω).map (· ^ q ^ i)).prod
    let r := orderOf N
    let L' : Set Ω := {c | c ^ q ^ (d * r) = c}
    0 < r ∧ (∀ i j, N i j ∈ L) ∧
      (∃ H : GL (Fin n) Ω, (∀ i j, (H : Matrix (Fin n) (Fin n) Ω) i j ∈ L') ∧
        (∀ i j, (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) i j ∈ L') ∧
        (A : Matrix (Fin n) (Fin n) Ω) =
          (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) * (H : Matrix (Fin n) (Fin n) Ω).map (· ^ q)) ∧
      ((A : Matrix (Fin n) (Fin n) Ω).det = 1 →
        ∃ H : GL (Fin n) Ω, (H : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
          (∀ i j, (H : Matrix (Fin n) (Fin n) Ω) i j ∈ L') ∧
          (∀ i j, (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) i j ∈ L') ∧
          (A : Matrix (Fin n) (Fin n) Ω) =
            (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) * (H : Matrix (Fin n) (Fin n) Ω).map (· ^ q)) := by
  intro q d N r L'
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hq : q = ℓ ^ f := rfl
  have hq0 : q ≠ 0 := (pow_pos hℓ.pos f).ne'
  let σΩ : Ω →+* Ω := iterateFrobenius Ω ℓ f
  have hσΩ : ∀ c, σΩ c = c ^ q := fun c => iterateFrobenius_def ℓ f c
  have hσΩit : ∀ (i : ℕ) (c : Ω), (⇑σΩ)^[i] c = c ^ q ^ i := by
    intro i
    induction i with
    | zero => intro c; rw [Function.iterate_zero_apply, pow_zero, pow_one]
    | succ i ih => intro c; rw [Function.iterate_succ_apply', ih, hσΩ, ← pow_mul, ← pow_succ]
  have hN : N = twistedProd σΩ (A : Matrix (Fin n) (Fin n) Ω) d := by
    change ((List.range d).map fun i => (A : Matrix (Fin n) (Fin n) Ω).map (· ^ q ^ i)).prod = _
    rw [twistedProd]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    congr 1
    funext c
    exact (hσΩit i c).symm
  have : Finite L := Module.finite_of_finite K
  have : Fintype L := Fintype.ofFinite L
  have hLcard : Fintype.card L = q ^ d := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K), hK]
  have hLfix : ∀ c ∈ L, c ^ q ^ d = c := fun c hc => by
    have h := FiniteField.pow_card (⟨c, hc⟩ : L)
    rw [hLcard] at h
    exact congrArg Subtype.val h
  have hNL : ∀ i j, N i j ∈ L := by
    intro i j
    refine list_prod_apply_mem (S := L.toSubfield.toSubring) _ ?_ i j
    intro M hM i' j'
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hM
    exact pow_mem (hAL i' j') _
  have hNunit : IsUnit N := by
    refine List.prod_isUnit fun M hM => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hM
    have : (A : Matrix (Fin n) (Fin n) Ω).map (· ^ q ^ t) =
        ((iterateFrobenius Ω ℓ (f * t)).mapMatrix : Matrix (Fin n) (Fin n) Ω →+* _) A := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, iterateFrobenius_def,
        pow_mul]
    rw [this]
    exact (Units.isUnit A).map _
  let NL : Matrix (Fin n) (Fin n) L := fun i j => ⟨N i j, hNL i j⟩
  have hNLmap : NL.map (algebraMap L Ω) = N := rfl
  have hNLunit : IsUnit NL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h := RingHom.map_det (algebraMap L Ω) NL
    rw [h0, map_zero, RingHom.mapMatrix_apply, hNLmap] at h
    exact ((Matrix.isUnit_iff_isUnit_det N).mp hNunit).ne_zero h.symm
  have hr : orderOf N = orderOf NL := by
    rw [← hNLmap]
    exact orderOf_injective (algebraMap L Ω).mapMatrix.toMonoidHom
      (Matrix.map_injective (algebraMap L Ω).injective) NL
  have hrpos : 0 < r := by
    change 0 < orderOf N
    rw [hr, ← hNLunit.unit_spec, orderOf_units]
    exact orderOf_pos _
  have hNr : N ^ r = 1 := pow_orderOf_eq_one N
  refine ⟨hrpos, hNL, ?_⟩
  have hd : 1 ≤ d := Module.finrank_pos
  set e := f * d * r with he
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hqe : q ^ (d * r) = ℓ ^ e := by rw [hq, he, ← pow_mul, Nat.mul_assoc]
  let L'f : Subfield Ω := RingHom.eqLocusField (iterateFrobenius Ω ℓ e) (RingHom.id Ω)
  have hmemL' : ∀ c, c ∈ L'f ↔ c ∈ L' := fun c => by
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
    change _ ↔ c ^ q ^ (d * r) = c
    rw [hqe]
  have hL'card : Nat.card L'f = ℓ ^ e := by
    rw [← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : e ≠ 0)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [hmemL']
    change c ^ q ^ (d * r) = c ↔ c ^ ℓ ^ e = c
    rw [hqe]
  have hLL' : ∀ c ∈ L, c ∈ L'f := fun c hc => by
    rw [hmemL']
    change c ^ q ^ (d * r) = c
    rw [pow_mul]
    exact pow_pow_eq_self (hLfix c hc) r
  obtain ⟨σ₀, hσ₀, hσ₀ord, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ he1 hL'card
  set σ' : L'f ≃+* L'f := σ₀ ^ f with hσ'
  have hσ'pow : ∀ (j : ℕ) (c : L'f), (σ₀ ^ j) c = c ^ ℓ ^ j := by
    intro j
    induction j with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one]; rfl
    | succ j ih =>
      intro c
      rw [pow_succ]
      change (σ₀ ^ j) (σ₀ c) = _
      rw [ih, hσ₀, ← pow_mul, ← pow_succ']
  have hσ'q : ∀ c : L'f, ((σ' c : L'f) : Ω) = (c : Ω) ^ q := fun c => by
    rw [hσ', hσ'pow, SubmonoidClass.coe_pow]
  have hσ'ord : orderOf σ' = d * r := by
    have hdvd : f ∣ orderOf σ₀ := by
      rw [hσ₀ord, he, Nat.mul_assoc]
      exact Nat.dvd_mul_right f _
    rw [hσ', orderOf_pow_of_dvd (by omega) hdvd, hσ₀ord, he, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by omega)]
  let A' : Matrix (Fin n) (Fin n) L'f := fun i j => ⟨A i j, hLL' _ (hAL i j)⟩
  have hA'map : A'.map L'f.subtype = A := rfl
  have hA'unit : IsUnit A'.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h := RingHom.map_det L'f.subtype A'
    rw [h0, map_zero, RingHom.mapMatrix_apply, hA'map] at h
    exact (Matrix.GeneralLinearGroup.det_ne_zero A) h.symm
  have hint : ∀ c : L'f, L'f.subtype (σ' c) = σΩ (L'f.subtype c) := fun c => by
    rw [Subfield.coe_subtype, hσ'q, hσΩ]
  have hPd : (twistedProd σ' A' d).map L'f.subtype = N := by
    rw [map_twistedProd σ' σΩ L'f.subtype hint, hA'map, hN]
  have hσ'it : ∀ (i : ℕ) (c : L'f), (((⇑σ')^[i] c : L'f) : Ω) = (c : Ω) ^ q ^ i := by
    intro i
    induction i with
    | zero => intro c; rw [Function.iterate_zero_apply, pow_zero, pow_one]
    | succ i ih => intro c; rw [Function.iterate_succ_apply', hσ'q, ih, ← pow_mul, ← pow_succ]
  have hPfix : (twistedProd σ' A' d).map (⇑σ')^[d] = twistedProd σ' A' d := by
    refine Matrix.map_injective (f := L'f.subtype) Subtype.val_injective ?_
    ext i j
    simp only [Matrix.map_apply]
    rw [Subfield.coe_subtype, hσ'it]
    have h := congrFun (congrFun hPd i) j
    rw [Matrix.map_apply] at h
    change ((twistedProd σ' A' d i j : L'f) : Ω) ^ q ^ d = ((twistedProd σ' A' d i j : L'f) : Ω)
    rw [show ((twistedProd σ' A' d i j : L'f) : Ω) = N i j from h]
    exact hLfix _ (hNL i j)
  have hPdr : twistedProd σ' A' (d * r) = 1 := by
    have h := twistedProd_mul (σ' : L'f →+* L'f) A' hPfix r
    rw [RingEquiv.coe_toRingHom] at h
    rw [h]
    refine Matrix.map_injective (f := L'f.subtype) Subtype.val_injective ?_
    change L'f.subtype.mapMatrix (twistedProd σ' A' d ^ r) = L'f.subtype.mapMatrix 1
    rw [map_pow, map_one, RingHom.mapMatrix_apply, hPd, hNr]
  have hper : ∀ v : Fin n → L'f, twistedProd σ' A' (d * r) *ᵥ ((⇑σ')^[d * r] ∘ v) = v := by
    intro v
    rw [hPdr, Matrix.one_mulVec]
    funext i
    apply Subtype.val_injective
    rw [Function.comp_apply, hσ'it]
    exact (hmemL' _).mp (v i).2
  have hσ'q' : ∀ c, L'f.subtype ((σ' : L'f →+* L'f) c) = L'f.subtype c ^ q := hσ'q
  have hentries : ∀ M : Matrix (Fin n) (Fin n) L'f, ∀ i j, (M.map L'f.subtype) i j ∈ L' :=
    fun M i j => (hmemL' _).mp (M i j).2
  obtain ⟨B, hBunit, hBfix⟩ :=
    exists_isUnit_det_fixed hℓ he1 hL'card σ' hσ'ord A' hA'unit hper
  refine ⟨?_, fun hdet => ?_⟩
  · obtain ⟨H, hH, hHinv, hA⟩ :=
      exists_lang_solution L'f.subtype (σ' : L'f →+* L'f) hσ'q' A' B hBunit hBfix
    refine ⟨H, fun i j => ?_, fun i j => ?_, ?_⟩
    · rw [hH]
      exact hentries _ i j
    · rw [hHinv]
      exact hentries _ i j
    · rw [← hA, hA'map]
  ·
    have hA'det : A'.det = 1 := by
      apply Subtype.val_injective
      have h := RingHom.map_det L'f.subtype A'
      rw [RingHom.mapMatrix_apply, hA'map, hdet] at h
      exact h
    obtain ⟨B₁, hB₁det, hB₁fix⟩ := exists_fixed_det_eq_one (σ' : L'f →+* L'f) hn A' B hA'det
      hBunit hBfix
    have hB₁unit : IsUnit B₁.det := by rw [hB₁det]; exact isUnit_one
    obtain ⟨H, hH, hHinv, hA⟩ :=
      exists_lang_solution L'f.subtype (σ' : L'f →+* L'f) hσ'q' A' B₁ hB₁unit hB₁fix
    refine ⟨H, ?_, fun i j => ?_, fun i j => ?_, ?_⟩
    · rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_nonsing_inv, hB₁det,
        Ring.inverse_one, map_one]
    · rw [hH]
      exact hentries _ i j
    · rw [hHinv]
      exact hentries _ i j
    · rw [← hA, hA'map]

theorem matrix_frobenius_lang (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) [IsAlgClosure K Ω] (hn : 1 ≤ n) (A : GL (Fin n) Ω) :
    (∃ H : GL (Fin n) Ω,
        (A : Matrix (Fin n) (Fin n) Ω) =
          (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) * (H : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f)) ∧
      ((A : Matrix (Fin n) (Fin n) Ω).det = 1 →
        ∃ H : GL (Fin n) Ω, (H : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
          (A : Matrix (Fin n) (Fin n) Ω) =
            (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) *
              (H : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f)) := by
  set S : Set Ω := Set.range fun x : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) Ω) x.1 x.2
  have : Finite S := Set.finite_range _ |>.to_subtype
  have : Algebra.IsIntegral K Ω := (IsAlgClosure.isAlgebraic (R := K) (K := Ω)).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hAL : ∀ i j, (A : Matrix (Fin n) (Fin n) Ω) i j ∈ IntermediateField.adjoin K S :=
    fun i j => IntermediateField.subset_adjoin K S ⟨(i, j), rfl⟩
  obtain ⟨-, -, ⟨H, -, -, hH⟩, hdet⟩ :=
    matrix_frobenius_lang_of_le hℓ hf hK hn A (IntermediateField.adjoin K S) hAL
  refine ⟨⟨H, hH⟩, fun h1 => ?_⟩
  obtain ⟨H', hH'det, -, -, hH'⟩ := hdet h1
  exact ⟨H', hH'det, hH'⟩

end Lang

end CFSG.RankThree.Classical2
