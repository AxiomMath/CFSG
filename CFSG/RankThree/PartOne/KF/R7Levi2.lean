module

public import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def blk4 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; 0, 0, X 0 0, X 0 1; 0, 0, X 1 0, X 1 1]

theorem blk4_one : blk4 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4]

theorem blk4_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk4 (X * Y) = blk4 X * blk4 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blk4_gram [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) (hX : X.det = 1) :
    (blk4 X)ᵀ * antidiag 4 * blk4 X = antidiag 4 := by
  rw [Matrix.det_fin_two] at hX
  ext i j
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;>
    simp [blk4, antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Fin.rev]
  all_goals first
    | linear_combination (X 0 0 * X 1 0) * h2
    | linear_combination hX + (X 0 1 * X 1 0) * h2
    | linear_combination (X 0 1 * X 1 1) * h2

theorem blk4_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk4 X = blk4 Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk4] using congrFun (congrFun h 0) 0
  · simpa [blk4] using congrFun (congrFun h 0) 1
  · simpa [blk4] using congrFun (congrFun h 1) 0
  · simpa [blk4] using congrFun (congrFun h 1) 1

variable [CharP K 2]

@[expose] noncomputable def spBlock' : SpecialLinearGroup (Fin 2) K →* ↥(spRev K) where
  toFun A :=
    ⟨{ val := blk4 (A : Matrix (Fin 2) (Fin 2) K)
       inv := blk4 ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
       val_inv := by
         rw [← blk4_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
           Matrix.SpecialLinearGroup.coe_one, blk4_one]
       inv_val := by
         rw [← blk4_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
           Matrix.SpecialLinearGroup.coe_one, blk4_one] }, by
      rw [mem_spRev_iff]
      exact blk4_gram _ A.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [blk4_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    simp [blk4_mul]

theorem coe_spBlock' (A : SpecialLinearGroup (Fin 2) K) :
    (((spBlock' A : ↥(spRev K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk4 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem spBlock'_injective : Function.Injective (spBlock' : SpecialLinearGroup (Fin 2) K →* _) := by
  intro A B h
  have h1 := congrArg (fun g : ↥(spRev K) =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  simp only [coe_spBlock'] at h1
  exact Subtype.ext (blk4_injective h1)

@[expose] noncomputable def b7' (ζ : Kˣ) : ↥(spRev K) :=
  ⟨diagU (dvec4 ζ ζ), diagU_dvec4_mem_spRev ζ ζ⟩

theorem coe_b7' (ζ : Kˣ) : ((b7' ζ : ↥(spRev K)) : GL (Fin 4) K) = diagU (dvec4 ζ ζ) := rfl

theorem centralizer_b7'_facts {ζ : Kˣ} (h2 : ζ ^ 2 ≠ 1) {g : ↥(spRev K)}
    (hg : g ∈ Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) :
    gm g 0 2 = 0 ∧ gm g 0 3 = 0 ∧ gm g 1 2 = 0 ∧ gm g 1 3 = 0 ∧ gm g 2 0 = 0 ∧ gm g 2 1 = 0 ∧
      gm g 3 0 = 0 ∧ gm g 3 1 = 0 ∧
      gm g 0 0 * gm g 3 3 + gm g 1 0 * gm g 2 3 = 1 ∧
      gm g 0 0 * gm g 3 2 + gm g 1 0 * gm g 2 2 = 0 ∧
      gm g 0 1 * gm g 3 2 + gm g 1 1 * gm g 2 2 = 1 ∧
      gm g 0 1 * gm g 3 3 + gm g 1 1 * gm g 2 3 = 0 := by
  have hcomm : (g : GL (Fin 4) K) * diagU (dvec4 ζ ζ) = diagU (dvec4 ζ ζ) * (g : GL (Fin 4) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have e02 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 2) (by simpa [dvec4] using hζ3)
  have e03 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 3) (by simpa [dvec4] using hζ3)
  have e12 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 2) (by simpa [dvec4] using hζ3)
  have e13 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3) (by simpa [dvec4] using hζ3)
  have e20 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 0)
    (by simpa [dvec4] using hζ3.symm)
  have e21 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 1)
    (by simpa [dvec4] using hζ3.symm)
  have e30 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 0)
    (by simpa [dvec4] using hζ3.symm)
  have e31 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1)
    (by simpa [dvec4] using hζ3.symm)
  have hgram := (mem_spRev_iff (K := K)).1 g.2
  have hg03 := congrFun (congrFun hgram 0) 3
  have hg02 := congrFun (congrFun hgram 0) 2
  have hg12 := congrFun (congrFun hgram 1) 2
  have hg13 := congrFun (congrFun hgram 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, Matrix.transpose_apply]
    at hg03 hg02 hg12 hg13
  simp only [e02, e03, e12, e13, e20, e21, e30, e31, mul_zero, add_zero, zero_add]
    at hg03 hg02 hg12 hg13
  refine ⟨e02, e03, e12, e13, e20, e21, e30, e31, ?_, ?_, ?_, ?_⟩
  · linear_combination hg03
  · linear_combination hg02
  · linear_combination hg12
  · linear_combination hg13

theorem det_blocks_b7' {ζ : Kˣ} (h2 : ζ ^ 2 ≠ 1) {g : ↥(spRev K)}
    (hg : g ∈ Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) :
    (gm g 0 0 * gm g 1 1 - gm g 0 1 * gm g 1 0) * (gm g 2 2 * gm g 3 3 - gm g 2 3 * gm g 3 2) = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, E1, E2, E3, E4⟩ := centralizer_b7'_facts h2 hg
  linear_combination (gm g 0 1 * gm g 3 2 + gm g 1 1 * gm g 2 2) * E1 + E3 -
    (gm g 0 1 * gm g 3 3 + gm g 1 1 * gm g 2 3) * E2

theorem spBlock'_mem_centralizer (ζ : Kˣ) (A : SpecialLinearGroup (Fin 2) K) :
    spBlock' A ∈ Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_spBlock', coe_b7', diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring

@[expose] noncomputable def phi7' {ζ : Kˣ} (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) →* Kˣ where
  toFun g := Units.mk0 (gm (g : ↥(spRev K)) 0 0 * gm (g : ↥(spRev K)) 1 1 -
      gm (g : ↥(spRev K)) 0 1 * gm (g : ↥(spRev K)) 1 0) (fun h0 => by
    have := det_blocks_b7' h2 g.2
    rw [h0, zero_mul] at this
    exact zero_ne_one this)
  map_one' := by
    apply Units.ext
    simp [gm_one]
  map_mul' g h := by
    apply Units.ext
    obtain ⟨e02, e03, e12, e13, -, -, -, -, -⟩ := centralizer_b7'_facts h2 g.2
    simp [Subgroup.coe_mul, gm_mul, Matrix.mul_apply, Fin.sum_univ_four, e02, e03, e12, e13]
    ring

theorem phi7'_apply {ζ : Kˣ} (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K)))) :
    ((phi7' h2 g : Kˣ) : K) = gm (g : ↥(spRev K)) 0 0 * gm (g : ↥(spRev K)) 1 1 -
      gm (g : ↥(spRev K)) 0 1 * gm (g : ↥(spRev K)) 1 0 := rfl

theorem ker_phi7' {ζ : Kˣ} (h2 : ζ ^ 2 ≠ 1) :
    (phi7' h2).ker =
      (spBlock' (K := K)).range.subgroupOf
        (Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e02, e03, e12, e13, e20, e21, e30, e31, E1, E2, E3, E4⟩ := centralizer_b7'_facts h2 g.2
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hdet : gm (g : ↥(spRev K)) 0 0 * gm (g : ↥(spRev K)) 1 1 -
        gm (g : ↥(spRev K)) 0 1 * gm (g : ↥(spRev K)) 1 0 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      rw [phi7'_apply] at this
      simpa using this
    have e33 : gm (g : ↥(spRev K)) 3 3 = gm (g : ↥(spRev K)) 1 1 := by
      linear_combination (gm (g : ↥(spRev K)) 1 1) * E1 - (gm (g : ↥(spRev K)) 1 0) * E4 -
        (gm (g : ↥(spRev K)) 3 3) * hdet
    have e22 : gm (g : ↥(spRev K)) 2 2 = gm (g : ↥(spRev K)) 0 0 := by
      linear_combination (gm (g : ↥(spRev K)) 0 0) * E3 - (gm (g : ↥(spRev K)) 0 1) * E2 -
        (gm (g : ↥(spRev K)) 2 2) * hdet
    have e23 : gm (g : ↥(spRev K)) 2 3 = gm (g : ↥(spRev K)) 0 1 := by
      linear_combination (-(gm (g : ↥(spRev K)) 0 1)) * E1 + (gm (g : ↥(spRev K)) 0 0) * E4 -
        (gm (g : ↥(spRev K)) 2 3) * hdet - (gm (g : ↥(spRev K)) 0 1) * h2'
    have e32 : gm (g : ↥(spRev K)) 3 2 = gm (g : ↥(spRev K)) 1 0 := by
      linear_combination (gm (g : ↥(spRev K)) 1 1) * E2 - (gm (g : ↥(spRev K)) 1 0) * E3 -
        (gm (g : ↥(spRev K)) 3 2) * hdet - (gm (g : ↥(spRev K)) 1 0) * h2'
    have hdet' : (!![gm (g : ↥(spRev K)) 0 0, gm (g : ↥(spRev K)) 0 1;
        gm (g : ↥(spRev K)) 1 0, gm (g : ↥(spRev K)) 1 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      exact hdet
    refine ⟨⟨_, hdet'⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show blk4 ((⟨_, hdet'⟩ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      gm (g : ↥(spRev K))
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk4, *]
  · rintro ⟨A, hA⟩
    apply Units.ext
    rw [phi7'_apply]
    have h00 : gm (g : ↥(spRev K)) 0 0 = gm (spBlock' A) 0 0 := by rw [← hA]
    have h01 : gm (g : ↥(spRev K)) 0 1 = gm (spBlock' A) 0 1 := by rw [← hA]
    have h10 : gm (g : ↥(spRev K)) 1 0 = gm (spBlock' A) 1 0 := by rw [← hA]
    have h11 : gm (g : ↥(spRev K)) 1 1 = gm (spBlock' A) 1 1 := by rw [← hA]
    rw [h00, h01, h10, h11]
    have hd := A.2
    rw [Matrix.det_fin_two] at hd
    show (blk4 (A : Matrix (Fin 2) (Fin 2) K) 0 0 * blk4 (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      blk4 (A : Matrix (Fin 2) (Fin 2) K) 0 1 * blk4 (A : Matrix (Fin 2) (Fin 2) K) 1 0) = ((1 : Kˣ) : K)
    simpa [blk4] using hd

theorem perfectResidual_centralizer_b7' [Finite K] (hK : 4 ≤ Nat.card K) {ζ : Kˣ}
    (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) =
      (spBlock' (K := K)).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK
  have hperf : Group.IsPerfect ↥((spBlock' (K := K)).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective spBlock'_injective).toMonoidHom)
      (MonoidHom.ofInjective spBlock'_injective).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact spBlock'_mem_centralizer ζ A) hperf (phi7' h2) (ker_phi7' h2)

@[expose] noncomputable def rho7' : Kˣ →* ↥(spRev K) :=
  (spDiag K).comp ((MonoidHom.id Kˣ).prod invMonoidHom)

theorem coe_rho7' (a : Kˣ) :
    ((rho7' a : ↥(spRev K)) : GL (Fin 4) K) = diagU (dvec4 a a⁻¹) := rfl

theorem rho7'_injective : Function.Injective (rho7' : Kˣ →* ↥(spRev K)) := by
  intro a b h
  have := spDiag_injective (K := K) h
  exact (Prod.ext_iff.1 this).1

theorem spBlock'_diag2 (a : Kˣ) : spBlock' (diag2 a) = rho7' a := by
  apply Subtype.ext
  apply Units.ext
  show blk4 (Matrix.diagonal fun i => (![a, a⁻¹] i : K)) = _
  rw [coe_rho7', diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4, dvec4]

theorem rho7'_mem_range (a : Kˣ) : (rho7' a : ↥(spRev K)) ∈ (spBlock' (K := K)).range :=
  ⟨diag2 a, spBlock'_diag2 a⟩

theorem torus7_inf_range'_eq (p : ℕ) :
    torus7 p K ⊓ (spBlock' (K := K)).range = (rootsOfUnity p K).map rho7' := by
  ext g
  constructor
  · rintro ⟨hgT, A, hA⟩
    obtain ⟨a, b, ha, hb, hab⟩ := mem_torus7_iff.1 hgT
    have h00 : gm g 0 0 = gm (spBlock' A) 0 0 := by rw [← hA]
    have h22 : gm g 2 2 = gm (spBlock' A) 2 2 := by rw [← hA]
    have hA0 : gm (spBlock' A) 0 0 = gm (spBlock' A) 2 2 := by
      show blk4 (A : Matrix (Fin 2) (Fin 2) K) 0 0 = blk4 (A : Matrix (Fin 2) (Fin 2) K) 2 2
      simp [blk4]
    have hg00 : gm g 0 0 = (a : K) := by
      show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = _
      rw [hab, diagU_val]
      simp [dvec4]
    have hg22 : gm g 2 2 = ((b⁻¹ : Kˣ) : K) := by
      show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 = _
      rw [hab, diagU_val]
      simp [dvec4]
    have hab' : a = b⁻¹ := Units.ext (by rw [← hg00, ← hg22, h00, h22, hA0])
    refine ⟨a, (mem_rootsOfUnity p _).2 ha, ?_⟩
    apply Subtype.ext
    rw [coe_rho7', hab, hab', inv_inv]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨mem_torus7_iff.2 ⟨a, a⁻¹, (mem_rootsOfUnity p _).1 ha, by
      rw [inv_pow, (mem_rootsOfUnity p _).1 ha, inv_one], coe_rho7' a⟩, rho7'_mem_range a⟩

theorem card_torus7_inf_range' {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus7 p K ⊓ (spBlock' (K := K)).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus7_inf_range'_eq, Subgroup.card_map_of_injective rho7'_injective]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def rootU7' (K : Type) [Field K] [CharP K 2] : Subgroup ↥(spRev K) :=
  ((spBlock' (K := K)).comp
    ({ toFun := fun c : Multiplicative K => tr2 (Multiplicative.toAdd c)
       map_one' := tr2_zero
       map_mul' := fun _ _ => (tr2_mul _ _).symm } :
      Multiplicative K →* SpecialLinearGroup (Fin 2) K)).range

theorem mem_rootU7'_iff {g : ↥(spRev K)} : g ∈ rootU7' K ↔ ∃ c : K, g = spBlock' (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem spBlock'_tr2_mem_rootU7' (c : K) : spBlock' (tr2 c) ∈ rootU7' K :=
  mem_rootU7'_iff.2 ⟨c, rfl⟩

theorem rootU7'_le_range : rootU7' K ≤ (spBlock' (K := K)).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootU7'_iff.1 hg
  exact ⟨tr2 c, rfl⟩

theorem isPGroup_rootU7' : IsPGroup 2 ↥(rootU7' K) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := mem_rootU7'_iff.1 hg
  have hsq : (spBlock' (tr2 c) : ↥(spRev K)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨spBlock' (tr2 c), hg⟩ : ↥(rootU7' K)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torus7_conj_rootU7' {p : ℕ} {g : ↥(spRev K)} (hg : g ∈ torus7 p K) :
    ∀ x ∈ rootU7' K, g * x * g⁻¹ ∈ rootU7' K := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootU7'_iff.1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_torus7_iff.1 hg
  have h : g * spBlock' (tr2 c) = spBlock' (tr2 ((a : K) * c * ((b⁻¹ : Kˣ) : K))) * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_spBlock', hab, diagU_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk4, tr2, Matrix.transvection, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul]
    all_goals field_simp
  have : g * spBlock' (tr2 c) * g⁻¹ = spBlock' (tr2 ((a : K) * c * ((b⁻¹ : Kˣ) : K))) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact spBlock'_tr2_mem_rootU7' _

theorem torus7_le_normalizer_rootU7' {p : ℕ} :
    torus7 p K ≤ Subgroup.normalizer (rootU7' K : Set ↥(spRev K)) := fun g hg =>
  mem_normalizer_of_conj_mem (torus7_conj_rootU7' hg) (fun y hy => by
    have := torus7_conj_rootU7' ((torus7 p K).inv_mem hg) y hy
    simpa using this)

theorem gm_spBlock' (A : SpecialLinearGroup (Fin 2) K) :
    gm (spBlock' A) = blk4 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem gm_rho7' (a : Kˣ) :
    gm (rho7' a : ↥(spRev K)) = Matrix.diagonal fun i => (dvec4 a a⁻¹ i : K) := rfl

theorem spBlock'_tr2_one_not_commute_rho7' {a : Kˣ} (ha : a ≠ 1) :
    (spBlock' (tr2 (1 : K)) : ↥(spRev K)) * rho7' a ≠ rho7' a * spBlock' (tr2 (1 : K)) := by
  intro h
  have h1 := congrArg (fun x : ↥(spRev K) => gm x 0 1) h
  have e00 : gm (spBlock' (tr2 (1 : K))) 0 0 = 1 := by
    rw [gm_spBlock']
    simp [blk4, tr2, Matrix.transvection]
  have e01 : gm (spBlock' (tr2 (1 : K))) 0 1 = 1 := by
    rw [gm_spBlock']
    simp [blk4, tr2, Matrix.transvection]
  have e11 : gm (spBlock' (tr2 (1 : K))) 1 1 = 1 := by
    rw [gm_spBlock']
    simp [blk4, tr2, Matrix.transvection]
  simp [gm_mul, gm_rho7', Matrix.mul_apply, Fin.sum_univ_four, dvec4, e00, e01, e11] at h1
  have h2 : (a⁻¹ : Kˣ) = a := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h1)
  apply ha
  have h3 : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel a
  have h4 : ((a : K) - 1) ^ 2 = 0 := by
    have : ((a : K) - 1) ^ 2 = (a : K) * a - 2 * a + 1 := by ring
    rw [this, ← Units.val_mul, h3, CharTwo.two_eq_zero, zero_mul, sub_zero, Units.val_one]
    exact CharTwo.add_self_eq_zero 1
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4))

theorem b7'_mem_torus7 {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) : b7' ζ ∈ torus7 p K :=
  mem_torus7_iff.2 ⟨ζ, ζ, hζ, hζ, rfl⟩

theorem rho7'_mem_torus7 {p : ℕ} {a : Kˣ} (ha : a ^ p = 1) :
    (rho7' a : ↥(spRev K)) ∈ torus7 p K :=
  mem_torus7_iff.2 ⟨a, a⁻¹, ha, by rw [inv_pow, ha, inv_one], coe_rho7' a⟩

theorem b7'_ne_one {ζ : Kˣ} (hζ1 : ζ ≠ 1) : b7' ζ ≠ 1 := by
  intro h1
  have := congrArg (fun x : ↥(spRev K) => gm x 0 0) h1
  simp only [gm_one, Matrix.one_apply_eq] at this
  have h00 : gm (b7' ζ) 0 0 = (ζ : K) := by
    show ((diagU (dvec4 ζ ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = _
    simp [diagU_val, dvec4]
  exact hζ1 (Units.ext (by rw [← h00]; exact this))

theorem b7_ne_one {ζ : Kˣ} (hζ1 : ζ ≠ 1) : b7 ζ ≠ 1 := by
  intro h1
  have := congrArg (fun x : ↥(spRev K) => gm x 1 1) h1
  simp only [gm_one, Matrix.one_apply_eq] at this
  have h11 : gm (b7 ζ) 1 1 = (ζ : K) := by
    show ((diagU (dvec4 1 ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
    simp [diagU_val, dvec4]
  exact hζ1 (Units.ext (by rw [← h11]; exact this))

end CFSG.RankThree.PartOne.KFU
