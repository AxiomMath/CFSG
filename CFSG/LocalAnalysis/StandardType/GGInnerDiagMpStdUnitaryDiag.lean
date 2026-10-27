module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LieType.Universal.Unitary.Roots.Monomial

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  InnerDiagSU

namespace MpStdSU

section Normalize

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem conjSU_diagJ_mem_rootGroup (t : Fin n → F) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    (γ : Fin (n / 2) → ℤ) {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) :
    conjSU (diagJ t ht) (isJUnitary_diagJ t ht) x ∈ rootGroup σ hσ n γ := by
  suffices h : rootGroup σ hσ n γ ≤
      (rootGroup σ hσ n γ).comap (conjSU (diagJ t ht) (isJUnitary_diagJ t ht)) from h hx
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_comap]
    have e : c = Multiplicative.ofAdd (Multiplicative.toAdd c) := rfl
    rw [e, conjSU_diagJ_rootHom hσ t ht hij hi hj]
    exact rootHom_mem hσ hij hi hj hji hw _
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_comap]
    have e : c = Multiplicative.ofAdd (Multiplicative.toAdd c) := rfl
    rw [e, conjSU_diagJ_longRootHom t ht hi]
    exact longRootHom_mem hσ hi hw _
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    rintro x ⟨a, b, hab, hx⟩
    rw [Subgroup.mem_comap]
    refine heisenberg_le hσ hi hik hk hw ⟨t i * a * (t k)⁻¹, t i * b * (t (Fin.rev i))⁻¹,
      heisenberg_rel_of_unitary ht i hk hab, ?_⟩
    have h := signedPerm_mul_heisenbergMatrix (σ := σ) (π := 1) (fun _ => rfl) ht i hk rfl a b
    rw [SpecialLinear.signedPerm_one, Equiv.Perm.one_apply] at h
    rw [coe_conjSU, Units.val_mul, Units.val_mul, coe_diagJ, coe_diagJ_inv, hx, h,
      Matrix.mul_assoc, diagonal_mul_diagonal_inv t ht, Matrix.mul_one]

omit hσ in
theorem mat_inv_eq_diagonal {h : SU σ n} {t : Fin n → F} (hh : mat σ n h = diagonal t)
    (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1) : mat σ n h⁻¹ = diagonal fun s => (t s)⁻¹ := by
  have h1 : mat σ n h * mat σ n h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [hh] at h1
  have h3 : diagonal (fun s => (t s)⁻¹ * t s) = (1 : Matrix (Fin n) (Fin n) F) := by
    rw [← diagonal_one]
    congr 1
    funext s
    exact inv_mul_cancel₀ (ne_zero_of_unitary ht s)
  calc mat σ n h⁻¹ = diagonal (fun s => (t s)⁻¹ * t s) * mat σ n h⁻¹ := by
        rw [h3, Matrix.one_mul]
    _ = diagonal (fun s => (t s)⁻¹) * (diagonal t * mat σ n h⁻¹) := by
        rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    _ = diagonal fun s => (t s)⁻¹ := by rw [h1, Matrix.mul_one]

omit hσ in
theorem unitary_inv {t : Fin n → F} (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1) :
    ∀ s, σ ((t s)⁻¹) * (t (Fin.rev s))⁻¹ = 1 := fun s => by
  rw [map_inv₀, ← mul_inv, ht s, inv_one]

omit hσ in
theorem unitary_mul {t e : Fin n → F} (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    (he : ∀ s, σ (e s) * e (Fin.rev s) = 1) :
    ∀ s, σ (t s * e s) * (t (Fin.rev s) * e (Fin.rev s)) = 1 := fun s => by
  rw [map_mul]
  calc σ (t s) * σ (e s) * (t (Fin.rev s) * e (Fin.rev s))
      = (σ (t s) * t (Fin.rev s)) * (σ (e s) * e (Fin.rev s)) := by ring
    _ = 1 := by rw [ht s, he s, one_mul]

end Normalize

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem mem_ggTorus_of_mat_eq_diagonal {h : SU (unitaryInvolution F 2 f) n} {t : Fin n → F}
    (hh : mat _ n h = diagonal t)
    (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1) :
    h ∈ ggTorus (rootDatum hF n) := by
  have hσ := unitaryInvolution_involutive hF
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [conj_eq_conjSU_diagJ hh ht]
    exact conjSU_diagJ_mem_rootGroup hσ t ht γ hx
  · intro hx
    have hinv := mat_inv_eq_diagonal hh ht
    have h1 := conjSU_diagJ_mem_rootGroup hσ _ (unitary_inv ht) γ hx
    rw [← conj_eq_conjSU_diagJ hinv (unitary_inv ht)] at h1
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1

theorem mem_ggTorus_of_isDiag
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2)
    {h : SU (unitaryInvolution F 2 f) n} (hh : (mat _ n h).IsDiag) :
    h ∈ ggTorus (rootDatum hF n) := by
  let t : Fin n → F := fun i => mat _ n h i i
  have hd : mat _ n h = diagonal t := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [t]
    · simp only [diagonal_apply_ne _ hij]
      exact hh hij
  have hu : conjTr (unitaryInvolution F 2 f) (diagonal t) * antidiag n * diagonal t =
      antidiag n := by
    rw [← hd]
    exact h.property.2
  have ht : ∀ i, unitaryInvolution F 2 f (t i) * t (Fin.rev i) = 1 := by
    intro i
    have hi := congrFun (congrFun hu i) (Fin.rev i)
    simpa [conjTr, antidiag, Matrix.diagonal, Matrix.mul_apply] using hi
  exact mem_ggTorus_of_mat_eq_diagonal hF hd ht


end Torus

section Sqrt

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

omit [Finite F] in
theorem eq_one_of_mul_self_eq_one {a : F} (h : a * a = 1) : a = 1 := by
  have h2 : (a + 1) * (a + 1) = 0 := by
    have e : (a + 1) * (a + 1) = a * a + (a + a) + 1 := by ring
    rw [e, h, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h3 : a + 1 = 0 := mul_self_eq_zero.mp h2
  calc a = a + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

theorem exists_sqrt_normOne {δ : F} (hδ : σ δ * δ = 1) : ∃ y : F, σ y * y = 1 ∧ y * y = δ := by
  obtain ⟨y, hy⟩ := isSquare_of_charTwo' δ
  refine ⟨y, eq_one_of_mul_self_eq_one ?_, hy.symm⟩
  calc σ y * y * (σ y * y) = σ (y * y) * (y * y) := by rw [map_mul]; ring
    _ = 1 := by rw [← hy, hδ]

end Sqrt

section Pair

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def pairDiag (i : Fin n) (y : F) : Fin n → F := fun s =>
  if s = i ∨ s = Fin.rev i then y else 1

theorem pairDiag_rev (i : Fin n) (y : F) (s : Fin n) : pairDiag i y (Fin.rev s) = pairDiag i y s := by
  unfold pairDiag
  have h : (Fin.rev s = i ∨ Fin.rev s = Fin.rev i) ↔ (s = i ∨ s = Fin.rev i) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by rw [← h, Fin.rev_rev])
      · exact Or.inl (Fin.rev_injective h)
    · rintro (h | h)
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, Fin.rev_rev])
  simp only [h]

theorem pairDiag_self (i : Fin n) (y : F) : pairDiag i y i = y := by
  simp [pairDiag]

theorem pairDiag_rev_self (i : Fin n) (y : F) : pairDiag i y (Fin.rev i) = y := by
  simp [pairDiag]

theorem pairDiag_of_ne {i s : Fin n} (y : F) (h1 : s ≠ i) (h2 : s ≠ Fin.rev i) :
    pairDiag i y s = 1 := by
  simp [pairDiag, h1, h2]

theorem pairDiag_unitary {y : F} (hy : σ y * y = 1) (i : Fin n) :
    ∀ s, σ (pairDiag i y s) * pairDiag i y (Fin.rev s) = 1 := fun s => by
  rw [pairDiag_rev]
  unfold pairDiag
  split_ifs
  · exact hy
  · rw [map_one, one_mul]

theorem prod_pairDiag {i : Fin n} (hi : i ≠ Fin.rev i) (y : F) :
    ∏ s, pairDiag i y s = y * y := by
  rw [Finset.prod_eq_mul i (Fin.rev i) hi (fun s _ hs => pairDiag_of_ne y hs.1 hs.2) (by simp)
    (by simp), pairDiag_self, pairDiag_rev_self]

end Pair

section Corr

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem exists_corr (hn : 4 ≤ n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) {δ : F} (hδ : σ δ * δ = 1) :
    ∃ e : Fin n → F, (∀ s, σ (e s) * e (Fin.rev s) = 1) ∧ ∏ s, e s = δ ∧
      ∀ a b, (weight n a - weight n b = toStd n γ ∨ weight n a - weight n b = 2 • toStd n γ) →
        e a = e b := by
  obtain ⟨y, hy1, hy2⟩ := exists_sqrt_normOne hδ
  obtain ⟨z, hz1, hz2⟩ := exists_sqrt_normOne hy1
  have hne := toStd_ne_zero_of_mem_roots hγ
  have hrev : ∀ e : Fin n → F, (∀ s, e (Fin.rev s) = e s) → ∀ a b,
      weight n a - weight n b = 2 • toStd n γ → e a = e b := by
    intro e he a b h
    obtain ⟨hb, -⟩ := eq_rev_of_weight_sub_eq_two_smul h hne
    rw [hb, he]
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨hodd, i, hi, h⟩
  ·
    have hij' : i ≠ Fin.rev j := fun e => hji (by rw [e, Fin.rev_rev])
    have hrr : Fin.rev i ≠ Fin.rev j := fun e => hij (Fin.rev_injective e)
    refine ⟨fun s => pairDiag i z s * pairDiag j z s,
      unitary_mul (pairDiag_unitary hz1 i) (pairDiag_unitary hz1 j), ?_, ?_⟩
    · rw [Finset.prod_mul_distrib, prod_pairDiag hi, prod_pairDiag hj, hz2, hy2]
    · rintro a b (h1 | h2)
      · rcases eq_of_weight_sub_eq_sub hij hi hj hji (h1.trans h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · beta_reduce
          rw [pairDiag_self, pairDiag_of_ne z hij hij', pairDiag_self,
            pairDiag_of_ne z (Ne.symm hij) hji, mul_one, one_mul]
        · beta_reduce
          rw [pairDiag_rev_self, pairDiag_rev_self, pairDiag_of_ne z (Ne.symm hij') (Ne.symm hrr),
            pairDiag_of_ne z (fun e => hji e.symm) hrr, mul_one, one_mul]
      · exact hrev (fun s => pairDiag i z s * pairDiag j z s)
          (fun s => by simp only [pairDiag_rev]) a b h2
  ·
    refine ⟨pairDiag i y, pairDiag_unitary hy1 i, by rw [prod_pairDiag hi, hy2], ?_⟩
    have hw : weight n i ≠ 0 := by
      intro h0
      rw [h0, smul_zero] at h
      exact hne h
    rintro a b (h1 | h2)
    · obtain ⟨hb, -⟩ := eq_rev_of_weight_sub_eq_two_smul (h1.trans h) hw
      rw [hb, pairDiag_rev]
    · exact hrev _ (pairDiag_rev i y) a b h2
  ·
    set k := midIdx n hodd
    have hk : Fin.rev k = k := rev_midIdx hodd
    have hkv : 2 * k.val + 1 = n := by
      have := congrArg Fin.val hk
      simp only [Fin.val_rev] at this
      omega
    have hiv : i.val ≠ n - 1 - i.val := fun e => hi (Fin.ext (by simp only [Fin.val_rev]; omega))
    obtain ⟨j, hj, hji, hjri, hjk⟩ : ∃ j : Fin n, j ≠ Fin.rev j ∧ j ≠ i ∧ j ≠ Fin.rev i ∧ j ≠ k := by
      by_cases h0 : i.val = 0 ∨ i.val = n - 1
      · refine ⟨⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          · intro e
            have := congrArg Fin.val e
            simp only [Fin.val_rev] at this
            omega
      · refine ⟨⟨0, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          · intro e
            have := congrArg Fin.val e
            simp only [Fin.val_rev] at this
            omega
    refine ⟨pairDiag j y, pairDiag_unitary hy1 j, by rw [prod_pairDiag hj, hy2], ?_⟩
    have hik : i ≠ k := fun e => hi (by rw [e, hk])
    have h1i : pairDiag j y i = 1 := pairDiag_of_ne y (Ne.symm hji) (fun e => hjri (by
      rw [e, Fin.rev_rev]))
    have h1k : pairDiag j y k = 1 := pairDiag_of_ne y (Ne.symm hjk) (fun e => hjk (by
      rw [← hk, e, Fin.rev_rev]))
    have h1ri : pairDiag j y (Fin.rev i) = 1 := by rw [pairDiag_rev, h1i]
    rintro a b (h1 | h2)
    · rcases eq_of_weight_sub_eq_weight hi hk (h1.trans h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h1i, h1k]
      · rw [h1k, h1ri]
    · exact hrev _ (pairDiag_rev j y) a b h2

end Corr

section TorusConj

theorem normOne_prod {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ} {d : Fin n → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) : σ (∏ s, d s) * ∏ s, d s = 1 := by
  have hrev : ∏ s, d (Fin.rev s) = ∏ s, d s := Equiv.prod_comp Fin.revPerm d
  rw [map_prod, ← hrev, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun s _ => hd s

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

@[expose] noncomputable def diagSU (t : Fin n → F)
    (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1) (hp : ∏ s, t s = 1) :
    SU (unitaryInvolution F 2 f) n :=
  ⟨diagJ t ht, by rw [coe_diagJ, det_diagonal, hp], isJUnitary_diagJ t ht⟩

theorem mat_diagSU (t : Fin n → F)
    (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1) (hp : ∏ s, t s = 1) :
    mat _ n (diagSU t ht hp) = diagonal t :=
  rfl

include hF in
theorem exists_torus_conj (hn : 4 ≤ n) (d : Fin n → F)
    (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ (rootDatum hF n).roots) :
    ∃ h ∈ ggTorus (rootDatum hF n), ∀ z ∈ (rootDatum hF n).rootGroup γ,
      h * z * h⁻¹ = conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z := by
  have hσ := unitaryInvolution_involutive hF
  have hδ₀ := normOne_prod hd
  have h0 : ∏ s, d s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hδ₀
    exact zero_ne_one hδ₀
  have hδ : unitaryInvolution F 2 f (∏ s, d s)⁻¹ * (∏ s, d s)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hδ₀, inv_one]
  obtain ⟨e, he, hpe, hconst⟩ := exists_corr hn hγ hδ
  have ht := unitary_mul hd he
  have hp : ∏ s, (d s * e s) = 1 := by rw [Finset.prod_mul_distrib, hpe, mul_inv_cancel₀ h0]
  refine ⟨diagSU (fun s => d s * e s) ht hp,
    mem_ggTorus_of_mat_eq_diagonal hF (mat_diagSU _ ht hp) ht, fun z hz => ?_⟩
  rw [conj_eq_conjSU_diagJ (mat_diagSU _ ht hp) ht]
  refine conjSU_diagJ_eq_of_ratio _ d ht hd z fun a b hab hzab => ?_
  have hw : weight n a - weight n b ∈ wt2 (toStd n γ) := by
    refine hasWt_of_mem_rootGroup hσ hz a b ?_
    rw [Matrix.sub_apply, one_apply_ne hab, sub_zero]
    exact hzab
  have hab' : e a = e b := hconst a b (mem_wt2.mp hw)
  have heb : e b ≠ 0 := ne_zero_of_unitary he b
  rw [hab', mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ heb, mul_one]

end TorusConj

section Decomp

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem normOne_det {A : GL (Fin n) F} (hA : IsJUnitary σ A) :
    σ (A : Matrix (Fin n) (Fin n) F).det * (A : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_mul] at h
  have hc : (conjTr σ (A : Matrix (Fin n) (Fin n) F)).det = σ (A : Matrix (Fin n) (Fin n) F).det := by
    rw [conjTr, det_transpose]
    exact (RingHom.map_det σ.toRingHom (A : Matrix (Fin n) (Fin n) F)).symm
  rw [hc] at h
  have hJ := det_antidiag_ne_zero (F := F) n
  refine mul_right_cancel₀ hJ ?_
  linear_combination h

variable [Finite F] [CharP F 2]

theorem exists_SU_mul_diag (hn : 2 ≤ n) {A : GL (Fin n) F} (hA : IsJUnitary σ A) :
    ∃ (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (s : SU σ n),
      (s : GL (Fin n) F) = A * (diagJ d hd)⁻¹ := by
  obtain ⟨y, hy1, hy2⟩ := exists_sqrt_normOne (normOne_det hA)
  set i₀ : Fin n := ⟨0, by omega⟩
  have hi₀ : i₀ ≠ Fin.rev i₀ := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_rev, i₀] at this
    omega
  have hd := pairDiag_unitary hy1 i₀
  refine ⟨pairDiag i₀ y, hd, ⟨A * (diagJ _ hd)⁻¹, ?_, hA.mul (isJUnitary_diagJ _ hd).inv⟩, rfl⟩
  have hy0 : y * y ≠ 0 := by
    rw [hy2]
    intro h0
    have := normOne_det hA
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  rw [Units.val_mul, det_mul, coe_diagJ_inv, det_diagonal, Finset.prod_inv_distrib,
    prod_pairDiag hi₀, ← hy2, mul_inv_cancel₀ hy0]

end Decomp

end MpStdSU

end CFSG.StandardType
