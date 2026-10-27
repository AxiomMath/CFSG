module

public import CFSG.RankThree.PartOne.K1320.L4Gen

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix
open Matrix.SpecialLinearGroup (transvection)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def dvec (x : Fin 3 → Kˣ) : Fin 4 → K :=
  ![(x 0 : K), (x 1 : K), (x 2 : K), ((x 0 * x 1 * x 2)⁻¹ : Kˣ)]

omit [Finite K] [CharP K 2] in
theorem dvec_mul (x y : Fin 3 → Kˣ) (i : Fin 4) : dvec (K := K) (x * y) i =
    dvec x i * dvec y i := by
  fin_cases i
  · simp [dvec]
  · simp [dvec]
  · simp [dvec]
  · simp only [dvec, Pi.mul_apply]
    show (((x 0 * y 0) * (x 1 * y 1) * (x 2 * y 2))⁻¹ : Kˣ).val = _
    rw [show (x 0 * y 0) * (x 1 * y 1) * (x 2 * y 2) =
      (x 0 * x 1 * x 2) * (y 0 * y 1 * y 2) by simp only [mul_assoc, mul_left_comm, mul_comm],
      mul_inv, Units.val_mul]
    rfl

omit [Finite K] [CharP K 2] in
theorem dvec_zero (x : Fin 3 → Kˣ) : dvec (K := K) x 0 = (x 0 : K) := rfl
omit [Finite K] [CharP K 2] in
theorem dvec_one (x : Fin 3 → Kˣ) : dvec (K := K) x 1 = (x 1 : K) := rfl
omit [Finite K] [CharP K 2] in
theorem dvec_two (x : Fin 3 → Kˣ) : dvec (K := K) x 2 = (x 2 : K) := rfl
omit [Finite K] [CharP K 2] in
theorem dvec_three (x : Fin 3 → Kˣ) :
    dvec (K := K) x 3 = (((x 0 * x 1 * x 2)⁻¹ : Kˣ) : K) := rfl

omit [Finite K] [CharP K 2] in
theorem prod_dvec (x : Fin 3 → Kˣ) : ∏ i, dvec (K := K) x i = 1 := by
  rw [Fin.prod_univ_four, dvec_zero, dvec_one, dvec_two, dvec_three]
  have h : ((x 0 * x 1 * x 2 : Kˣ) : K) * (((x 0 * x 1 * x 2)⁻¹ : Kˣ) : K) = 1 :=
    Units.mul_inv _
  simpa only [Units.val_mul] using h

@[expose] noncomputable def diag4 (x : Fin 3 → Kˣ) : Matrix.SpecialLinearGroup (Fin 4) K :=
  ⟨Matrix.diagonal (dvec x), by rw [Matrix.det_diagonal, prod_dvec]⟩

omit [Finite K] [CharP K 2] in
theorem coe_diag4 (x : Fin 3 → Kˣ) :
    (diag4 x : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (dvec x) := rfl

@[expose] noncomputable def diagSL4 : (Fin 3 → Kˣ) →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun := diag4
  map_one' := by
    apply Subtype.ext
    rw [coe_diag4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dvec]
  map_mul' x y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag4, coe_diag4, coe_diag4,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact dvec_mul x y i

@[expose] noncomputable def diagHom (K : Type) [Field K] [Finite K] [CharP K 2] :
    (Fin 3 → Kˣ) →* ↥(M8 K) :=
  (adSL (K := K)).symm.toMonoidHom.comp diagSL4

theorem adSL_diagHom (x : Fin 3 → Kˣ) : adSL (diagHom K x) = diag4 x := by
  simp [diagHom, diagSL4]

theorem diagHom_injective : Function.Injective (diagHom K) := by
  intro x y h
  have h1 := congrArg (fun g : ↥(M8 K) => (adSL g : Matrix (Fin 4) (Fin 4) K)) h
  simp only [adSL_diagHom, coe_diag4] at h1
  funext i
  fin_cases i
  · exact Units.ext (by simpa [dvec_zero] using congrFun (congrFun h1 0) 0)
  · exact Units.ext (by simpa [dvec_one] using congrFun (congrFun h1 1) 1)
  · exact Units.ext (by simpa [dvec_two] using congrFun (congrFun h1 2) 2)

@[expose] noncomputable def trIncl (K : Type) [Field K] (r : ℕ) :
    (Fin 3 → ↥(rootsOfUnity r K)) →* (Fin 3 → Kˣ) :=
  MonoidHom.pi fun i => (rootsOfUnity r K).subtype.comp (Pi.evalMonoidHom _ i)

@[expose] noncomputable def torusF (K : Type) [Field K] [Finite K] [CharP K 2] (r : ℕ) :
    Subgroup ↥(M8 K) :=
  ((diagHom K).comp (trIncl K r)).range

@[expose] def cyc3 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cyc3_zero : cyc3 0 = 1 := by decide
theorem cyc3_one : cyc3 1 = 2 := by decide
theorem cyc3_two : cyc3 2 = 0 := by decide
theorem cyc3_three : cyc3 3 = 3 := by decide
theorem cyc3_symm_zero : cyc3.symm 0 = 2 := by decide
theorem cyc3_symm_one : cyc3.symm 1 = 0 := by decide
theorem cyc3_symm_two : cyc3.symm 2 = 1 := by decide
theorem cyc3_symm_three : cyc3.symm 3 = 3 := by decide

@[expose] noncomputable def hcyc (K : Type) [Field K] [Finite K] [CharP K 2] : ↥(M8 K) :=
  pM cyc3

@[expose] noncomputable def Rr (K : Type) [Field K] [Finite K] [CharP K 2] (r : ℕ) :
    Subgroup ↥(M8 K) :=
  (rootsOfUnity r K).map (Tl K)

theorem mem_torusF_iff {r : ℕ} {g : ↥(M8 K)} :
    g ∈ torusF K r ↔ ∃ x : Fin 3 → ↥(rootsOfUnity r K), diagHom K (trIncl K r x) = g := by
  simp [torusF, MonoidHom.mem_range]

omit [Finite K] [CharP K 2] in
theorem trIncl_injective (r : ℕ) : Function.Injective (trIncl K r) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem Tl_eq_diagHom (a : Kˣ) : Tl K a = diagHom K ![a, a, a⁻¹] := by
  apply adSL.injective
  rw [adSL_Tl, adSL_diagHom]
  apply Subtype.ext
  rw [coe_tlSL, coe_diag4]
  congr 1
  funext i
  fin_cases i
  · simp [dvec]
  · simp [dvec]
  · simp [dvec]
  · simp [dvec]

open Matrix.SpecialLinearGroup in
theorem diagHom_mem_slB_zero_one (u : Kˣ) : diagHom K ![u, u⁻¹, 1] ∈ slB K 0 1 := by
  rw [← blkA_zero_range]
  refine ⟨diag2 (u : K) u.ne_zero, ?_⟩
  apply adSL.injective
  rw [adSL_diagHom]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply, coe_diag4]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, diag2_coe', dvec]

open Matrix.SpecialLinearGroup in
theorem diagHom_mem_slB_two_three (v : Kˣ) : diagHom K ![1, 1, v] ∈ slB K 2 3 := by
  rw [← blkA_one_range]
  refine ⟨diag2 (v : K) v.ne_zero, ?_⟩
  apply adSL.injective
  rw [adSL_diagHom]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply, coe_diag4]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, diag2_coe', dvec]

omit [Finite K] in
theorem sq_units_eq_one {l : Kˣ} (h : l ^ 2 = 1) : l = 1 := by
  apply Units.ext
  apply eq_one_of_sq_eq_one
  have := congrArg Units.val h
  simpa [pow_two] using this

theorem exists_sq_units (w : Kˣ) : ∃ l : Kˣ, l ^ 2 = w := by
  have hinj : Function.Injective (fun l : Kˣ => l ^ 2) := by
    intro a b hab
    have h1 : (a * b⁻¹) ^ 2 = 1 := by
      have h2 : a ^ 2 = b ^ 2 := hab
      rw [mul_pow, inv_pow, h2, mul_inv_cancel]
    have h3 := sq_units_eq_one h1
    exact mul_inv_eq_one.1 h3
  exact (Finite.injective_iff_surjective.1 hinj) w

theorem exists_sqrt_root {r : ℕ} {w : Kˣ} (hw : w ^ r = 1) : ∃ l : Kˣ, l ^ 2 = w ∧ l ^ r = 1 := by
  obtain ⟨l, hl⟩ := exists_sq_units w
  refine ⟨l, hl, sq_units_eq_one ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hl, hw]

theorem Rr_le_torusF (r : ℕ) : Rr K r ≤ torusF K r := by
  rintro _ ⟨ζ, hζ, rfl⟩
  refine ⟨![⟨ζ, hζ⟩, ⟨ζ, hζ⟩, ⟨ζ⁻¹, inv_mem hζ⟩], ?_⟩
  rw [Tl_eq_diagHom]
  show diagHom K (trIncl K r _) = _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [CharP K 2] in
theorem natCard_rootsOfUnity_eq {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity r K) = r := by
  have : NeZero r := ⟨hr.ne_zero⟩
  rw [card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  obtain ⟨m, hm⟩ := hrq
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf,
    orderOf_pow_of_dvd hm0 (by rw [hord, hm]; exact Dvd.intro_left r rfl), hord, hm]
  exact Nat.mul_div_cancel r (Nat.pos_of_ne_zero hm0)

theorem rootsOfUnity_card {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) :
    Nat.card (Rr K r) = r := by
  rw [Rr, Subgroup.card_map_of_injective Tl_injective]
  exact natCard_rootsOfUnity_eq hr hrq

theorem torusF_isElementaryAbelian {r : ℕ} (_hr : r.Prime) :
    IsElementaryAbelian r (torusF K r) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨x, hx⟩ := mem_torusF_iff.1 a.2
    obtain ⟨y, hy⟩ := mem_torusF_iff.1 b.2
    apply Subtype.ext
    show (a : ↥(M8 K)) * (b : ↥(M8 K)) = (b : ↥(M8 K)) * (a : ↥(M8 K))
    rw [← hx, ← hy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm x y]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    obtain ⟨x, hx⟩ := mem_torusF_iff.1 a.2
    apply Subtype.ext
    show (a : ↥(M8 K)) ^ r = 1
    rw [← hx, ← map_pow, ← map_pow]
    have : x ^ r = 1 := by
      funext i
      exact Subtype.ext ((mem_rootsOfUnity r _).1 (x i).2)
    rw [this, map_one, map_one]

omit [Finite K] [CharP K 2] in
theorem dvec_perm3 (x : Fin 3 → Kˣ) :
    dvec (K := K) ![x 2, x 0, x 1] = fun a => dvec (K := K) x (cyc3.symm a) := by
  funext a
  fin_cases a
  · simp [dvec_zero, cyc3_symm_zero, dvec_two]
  · simp [dvec_one, cyc3_symm_one, dvec_zero]
  · simp [dvec_two, cyc3_symm_two, dvec_one]
  · simp only [Fin.reduceFinMk, cyc3_symm_three, dvec_three]
    show (((x 2 * x 0 * x 1)⁻¹ : Kˣ) : K) = _
    rw [show x 2 * x 0 * x 1 = x 0 * x 1 * x 2 by simp only [mul_assoc, mul_left_comm, mul_comm]]

theorem hcyc_conj_diagHom (x : Fin 3 → Kˣ) :
    hcyc K * diagHom K x * (hcyc K)⁻¹ = diagHom K ![x 2, x 0, x 1] := by
  apply adSL.injective
  rw [map_mul, map_mul, map_inv, hcyc, adSL_pM, adSL_diagHom, adSL_diagHom]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  rw [psl_conj_apply, coe_diag4, coe_diag4, dvec_perm3]
  show (Matrix.diagonal (dvec x)).submatrix (cyc3.symm : Fin 4 → Fin 4) (cyc3.symm : Fin 4 → Fin 4)
    a b = _
  rw [Matrix.submatrix_diagonal_equiv]
  rfl

theorem map_conj_slB (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (h : σ i ≠ σ j) :
    (slB K i j).map (MulAut.conj (pM σ : ↥(M8 K))).toMonoidHom = slB K (σ i) (σ j) := by
  have hij : i ≠ j := fun e => h (e ▸ rfl)
  rw [slB, slB, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨y, ⟨_, c, rfl | rfl⟩, rfl⟩
    · exact ⟨h, c, Or.inl (eM_conj_pM σ hij h c)⟩
    · exact ⟨h, c, Or.inr (eM_conj_pM σ hij.symm h.symm c)⟩
  · rintro ⟨h', c, rfl | rfl⟩
    · exact ⟨eM hij c, ⟨hij, c, Or.inl rfl⟩, eM_conj_pM σ hij h c⟩
    · exact ⟨eM hij.symm c, ⟨hij, c, Or.inr rfl⟩, eM_conj_pM σ hij.symm h.symm c⟩

theorem hcyc_conj_slB_zero_one :
    (slB K 0 1).map (MulAut.conj (hcyc K)).toMonoidHom = slB K 1 2 := by
  have := map_conj_slB (K := K) cyc3 (i := 0) (j := 1) (by rw [cyc3_zero, cyc3_one]; decide)
  rw [cyc3_zero, cyc3_one] at this
  exact this

theorem hcyc_conj_slB_two_three :
    (slB K 2 3).map (MulAut.conj (hcyc K)).toMonoidHom = slB K 0 3 := by
  have := map_conj_slB (K := K) cyc3 (i := 2) (j := 3) (by rw [cyc3_two, cyc3_three]; decide)
  rw [cyc3_two, cyc3_three] at this
  exact this

theorem hcyc_conj_Rr_le (r : ℕ) :
    (Rr K r).map (MulAut.conj (hcyc K)).toMonoidHom ≤ slB K 0 1 ⊔ slB K 2 3 := by
  rintro _ ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
  show hcyc K * Tl K ζ * (hcyc K)⁻¹ ∈ _
  rw [Tl_eq_diagHom, hcyc_conj_diagHom]
  have e : (![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 2 = ζ⁻¹ := rfl
  have e0 : (![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 0 = ζ := rfl
  have e1 : (![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 1 = ζ := rfl
  have hv : (![(![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 2, (![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 0,
      (![ζ, ζ, ζ⁻¹] : Fin 3 → Kˣ) 1] : Fin 3 → Kˣ) = ![ζ⁻¹, ζ, 1] * ![1, 1, ζ] := by
    funext i
    fin_cases i <;> simp
  rw [hv, map_mul]
  have hA := diagHom_mem_slB_zero_one (K := K) ζ⁻¹
  rw [inv_inv] at hA
  exact mul_mem (Subgroup.mem_sup_left hA)
    (Subgroup.mem_sup_right (diagHom_mem_slB_two_three ζ))

omit [Finite K] [CharP K 2] in
theorem eq_of_diagonal_comm_transvection {d : Fin 4 → K} {i j : Fin 4} (hij : i ≠ j) {c : K}
    (hc : c ≠ 0)
    (h : Matrix.diagonal d * (1 + Matrix.single i j c) =
      (1 + Matrix.single i j c) * Matrix.diagonal d) : d i = d j := by
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
  simp only [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply_same, zero_add]
    at h1
  exact mul_right_cancel₀ hc (by rw [h1, mul_comm])

theorem diagHom_comm_eM_iff (x : Fin 3 → Kˣ) {i j : Fin 4} (h : i ≠ j) {c : K} (hc : c ≠ 0) :
    diagHom K x * eM h c = eM h c * diagHom K x ↔ dvec x i = dvec x j := by
  constructor
  · intro hcomm
    have h1 := congrArg (fun g : ↥(M8 K) => (adSL g : Matrix (Fin 4) (Fin 4) K)) hcomm
    simp only [map_mul, adSL_diagHom, adSL_eM, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, coe_diag4] at h1
    exact eq_of_diagonal_comm_transvection h hc h1
  · intro hx
    apply adSL.injective
    rw [map_mul, map_mul, adSL_diagHom, adSL_eM]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, coe_diag4]
    exact diagonal_mul_transvection hx c

theorem diagHom_mem_centralizer_slB_iff (x : Fin 3 → Kˣ) {i j : Fin 4} (h : i ≠ j) :
    diagHom K x ∈ Subgroup.centralizer (slB K i j : Set ↥(M8 K)) ↔ dvec x i = dvec x j := by
  constructor
  · intro hx
    have hmem : eM h (1 : K) ∈ slB K i j :=
      Subgroup.subset_closure ⟨h, 1, Or.inl rfl⟩
    exact (diagHom_comm_eM_iff x h one_ne_zero).1 (Subgroup.mem_centralizer_iff.1 hx _ hmem).symm
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : slB K i j ≤ Subgroup.centralizer ({diagHom K x} : Set ↥(M8 K)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨hij, c, rfl | rfl⟩
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        by_cases hc : c = 0
        · subst hc
          have : eM hij (0 : K) = 1 := by
            apply adSL.injective
            rw [adSL_eM, map_one]
            apply Subtype.ext
            simp
          rw [this, one_mul, mul_one]
        · exact ((diagHom_comm_eM_iff x hij hc).2 hx).symm
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        by_cases hc : c = 0
        · subst hc
          have : eM hij.symm (0 : K) = 1 := by
            apply adSL.injective
            rw [adSL_eM, map_one]
            apply Subtype.ext
            simp
          rw [this, one_mul, mul_one]
        · exact ((diagHom_comm_eM_iff x hij.symm hc).2 hx.symm).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg))

@[expose] noncomputable def ratioHom (K : Type) [Field K] (r : ℕ) (i j : Fin 3) :
    (Fin 3 → ↥(rootsOfUnity r K)) →* ↥(rootsOfUnity r K) :=
  Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) i /
    Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) j

omit [Finite K] [CharP K 2] in
theorem ratioHom_apply (r : ℕ) (i j : Fin 3) (x : Fin 3 → ↥(rootsOfUnity r K)) :
    ratioHom K r i j x = x i / x j := rfl

omit [Finite K] [CharP K 2] in
theorem ratioHom_eq_one_iff (r : ℕ) (i j : Fin 3) (x : Fin 3 → ↥(rootsOfUnity r K)) :
    ratioHom K r i j x = 1 ↔ ((x i : rootsOfUnity r K) : Kˣ) = ((x j : rootsOfUnity r K) : Kˣ) := by
  rw [ratioHom_apply, div_eq_one, Subtype.ext_iff]

theorem relIndex_torusF_of_ker {r : ℕ} {A : Type} [Group A] (φ : (Fin 3 → ↥(rootsOfUnity r K)) →* A)
    (hφ : Function.Surjective φ) (S : Subgroup ↥(M8 K))
    (hS : ∀ x, diagHom K (trIncl K r x) ∈ S ↔ φ x = 1) :
    (torusF K r ⊓ S).relIndex (torusF K r) = Nat.card A := by
  have hinj : Function.Injective ((diagHom K).comp (trIncl K r)) :=
    diagHom_injective.comp (trIncl_injective r)
  have h1 : torusF K r ⊓ S = (φ.ker).map ((diagHom K).comp (trIncl K r)) := by
    ext g
    constructor
    · rintro ⟨hg, hgS⟩
      obtain ⟨x, rfl⟩ := mem_torusF_iff.1 hg
      exact ⟨x, (hS x).1 hgS, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, (hS x).2 hx⟩
  have h2 : torusF K r = (⊤ : Subgroup (Fin 3 → ↥(rootsOfUnity r K))).map
      ((diagHom K).comp (trIncl K r)) := MonoidHom.range_eq_map _
  have h3 : Nat.card φ.range = Nat.card A := by
    rw [MonoidHom.range_eq_top.2 hφ, Subgroup.card_top]
  rw [h1]
  conv_lhs => rw [h2]
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right,
    Subgroup.index_ker, h3]

omit [Finite K] [CharP K 2] in
theorem ratioHom_surjective (r : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    Function.Surjective (ratioHom K r i j) := by
  intro z
  refine ⟨Function.update (1 : Fin 3 → ↥(rootsOfUnity r K)) i z, ?_⟩
  rw [ratioHom_apply, Function.update_self, Function.update_of_ne hij.symm]
  simp

theorem mem_centralizer_sup {G : Type*} [Group G] {A B : Subgroup G} {g : G} :
    g ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) ↔
      g ∈ Subgroup.centralizer (A : Set G) ∧ g ∈ Subgroup.centralizer (B : Set G) := by
  constructor
  · intro h
    exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) h,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) h⟩
  · rintro ⟨hA, hB⟩
    rw [Subgroup.mem_centralizer_iff]
    have hle : A ⊔ B ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hA a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hB b hb)
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem diagHom_mem_torusF {r : ℕ} (v : Fin 3 → Kˣ) (hv : ∀ i, v i ^ r = 1) :
    diagHom K v ∈ torusF K r :=
  ⟨fun i => ⟨v i, (mem_rootsOfUnity r _).2 (hv i)⟩, rfl⟩

theorem diagHom_mem_slB_one_two (u : Kˣ) : diagHom K ![1, u, u⁻¹] ∈ slB K 1 2 := by
  rw [← hcyc_conj_slB_zero_one]
  refine ⟨diagHom K ![u, u⁻¹, 1], diagHom_mem_slB_zero_one u, ?_⟩
  show hcyc K * diagHom K ![u, u⁻¹, 1] * (hcyc K)⁻¹ = _
  rw [hcyc_conj_diagHom]
  rfl

theorem torusF_decomp_zero_one (r : ℕ) :
    torusF K r ≤ (torusF K r ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊔
      (torusF K r ⊓ slB K 0 1) := by
  rintro _ ⟨x, rfl⟩
  have hx : ∀ i, ((x i : rootsOfUnity r K) : Kˣ) ^ r = 1 := fun i =>
    (mem_rootsOfUnity r _).1 (x i).2
  set x0 : Kˣ := ((x 0 : rootsOfUnity r K) : Kˣ) with hx0
  set x1 : Kˣ := ((x 1 : rootsOfUnity r K) : Kˣ) with hx1
  set x2 : Kˣ := ((x 2 : rootsOfUnity r K) : Kˣ) with hx2
  obtain ⟨l, hl2, hlr⟩ := exists_sqrt_root (r := r) (w := x0 * x1)
    (by rw [mul_pow, hx 0, hx 1, one_mul])
  have hl2K : (l : K) * l = x0 * x1 := by
    have := congrArg Units.val hl2
    simpa [pow_two] using this
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hh00 : (x0 : K) ≠ 0 := x0.ne_zero
  have e : trIncl K r x = ![l, l, x2] * ![x0 * l⁻¹, (x0 * l⁻¹)⁻¹, 1] := by
    funext i
    apply Units.ext
    fin_cases i
    · show (x0 : K) = _
      simp
    · show (x1 : K) = _
      simp
      field_simp
      linear_combination -hl2K
    · show (x2 : K) = _
      simp
  have hy : ∀ i, (![l, l, x2] : Fin 3 → Kˣ) i ^ r = 1 := by
    intro i
    fin_cases i
    · exact hlr
    · exact hlr
    · exact hx 2
  have hz : ∀ i, (![x0 * l⁻¹, (x0 * l⁻¹)⁻¹, 1] : Fin 3 → Kˣ) i ^ r = 1 := by
    have hu : (x0 * l⁻¹) ^ r = 1 := by rw [mul_pow, inv_pow, hx 0, hlr]; simp
    intro i
    fin_cases i
    · exact hu
    · show ((x0 * l⁻¹)⁻¹) ^ r = 1
      rw [inv_pow, hu, inv_one]
    · exact one_pow r
  show diagHom K (trIncl K r x) ∈ _
  rw [e, map_mul]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨diagHom_mem_torusF _ hy,
      (diagHom_mem_centralizer_slB_iff _ (by decide)).2 rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨diagHom_mem_torusF _ hz,
      diagHom_mem_slB_zero_one _⟩))

theorem torusF_decomp_one_two (r : ℕ) :
    torusF K r ≤ (torusF K r ⊓ Subgroup.centralizer (slB K 1 2 : Set ↥(M8 K))) ⊔
      (torusF K r ⊓ slB K 1 2) := by
  rintro _ ⟨x, rfl⟩
  have hx : ∀ i, ((x i : rootsOfUnity r K) : Kˣ) ^ r = 1 := fun i =>
    (mem_rootsOfUnity r _).1 (x i).2
  set x0 : Kˣ := ((x 0 : rootsOfUnity r K) : Kˣ) with hx0
  set x1 : Kˣ := ((x 1 : rootsOfUnity r K) : Kˣ) with hx1
  set x2 : Kˣ := ((x 2 : rootsOfUnity r K) : Kˣ) with hx2
  obtain ⟨l, hl2, hlr⟩ := exists_sqrt_root (r := r) (w := x1 * x2)
    (by rw [mul_pow, hx 1, hx 2, one_mul])
  have hl2K : (l : K) * l = x1 * x2 := by
    have := congrArg Units.val hl2
    simpa [pow_two] using this
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hh10 : (x1 : K) ≠ 0 := x1.ne_zero
  have e : trIncl K r x = ![x0, l, l] * ![1, x1 * l⁻¹, (x1 * l⁻¹)⁻¹] := by
    funext i
    apply Units.ext
    fin_cases i
    · show (x0 : K) = _
      simp
    · show (x1 : K) = _
      simp
    · show (x2 : K) = _
      simp
      field_simp
      linear_combination -hl2K
  have hy : ∀ i, (![x0, l, l] : Fin 3 → Kˣ) i ^ r = 1 := by
    intro i
    fin_cases i
    · exact hx 0
    · exact hlr
    · exact hlr
  have hz : ∀ i, (![1, x1 * l⁻¹, (x1 * l⁻¹)⁻¹] : Fin 3 → Kˣ) i ^ r = 1 := by
    have hu : (x1 * l⁻¹) ^ r = 1 := by rw [mul_pow, inv_pow, hx 1, hlr]; simp
    intro i
    fin_cases i
    · exact one_pow r
    · exact hu
    · show ((x1 * l⁻¹)⁻¹) ^ r = 1
      rw [inv_pow, hu, inv_one]
  show diagHom K (trIncl K r x) ∈ _
  rw [e, map_mul]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨diagHom_mem_torusF _ hy,
      (diagHom_mem_centralizer_slB_iff _ (by decide)).2 rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨diagHom_mem_torusF _ hz,
      diagHom_mem_slB_one_two _⟩))

theorem torusF_condition {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2) (hrq : r ∣ Nat.card K - 1) :
    (torusF K r = (torusF K r ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊔
        (torusF K r ⊓ slB K 0 1) ∧
      (torusF K r ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))).relIndex (torusF K r) = r) ∧
    (torusF K r = (torusF K r ⊓ Subgroup.centralizer (slB K 1 2 : Set ↥(M8 K))) ⊔
        (torusF K r ⊓ slB K 1 2) ∧
      (torusF K r ⊓ Subgroup.centralizer (slB K 1 2 : Set ↥(M8 K))).relIndex (torusF K r) = r) ∧
    (torusF K r ⊓ Subgroup.centralizer ((slB K 0 1 ⊔ slB K 1 2 : Subgroup ↥(M8 K)) :
        Set ↥(M8 K))).relIndex (torusF K r) = r ^ 2 := by
  have hmu : Nat.card (rootsOfUnity r K) = r := natCard_rootsOfUnity_eq hr hrq
  refine ⟨⟨le_antisymm (torusF_decomp_zero_one r) (sup_le inf_le_left inf_le_left), ?_⟩,
    ⟨le_antisymm (torusF_decomp_one_two r) (sup_le inf_le_left inf_le_left), ?_⟩, ?_⟩
  · rw [relIndex_torusF_of_ker (ratioHom K r 0 1) (ratioHom_surjective r 0 1 (by decide)) _
      (fun x => ?_), hmu]
    rw [diagHom_mem_centralizer_slB_iff _ (by decide), ratioHom_eq_one_iff]
    exact Units.ext_iff.symm
  · rw [relIndex_torusF_of_ker (ratioHom K r 1 2) (ratioHom_surjective r 1 2 (by decide)) _
      (fun x => ?_), hmu]
    rw [diagHom_mem_centralizer_slB_iff _ (by decide), ratioHom_eq_one_iff]
    exact Units.ext_iff.symm
  · have hsurj : Function.Surjective ((ratioHom K r 0 1).prod (ratioHom K r 1 2)) := by
      rintro ⟨z1, z2⟩
      refine ⟨![z1 * z2, z2, 1], ?_⟩
      simp [MonoidHom.prod_apply, ratioHom_apply]
    rw [relIndex_torusF_of_ker ((ratioHom K r 0 1).prod (ratioHom K r 1 2)) hsurj _
      (fun x => ?_), Nat.card_prod, hmu, sq]
    rw [mem_centralizer_sup, diagHom_mem_centralizer_slB_iff _ (by decide),
      diagHom_mem_centralizer_slB_iff _ (by decide), MonoidHom.prod_apply, Prod.mk_eq_one,
      ratioHom_eq_one_iff, ratioHom_eq_one_iff]
    exact and_congr Units.ext_iff.symm Units.ext_iff.symm

end CFSG.RankThree.PartOne.K1320
