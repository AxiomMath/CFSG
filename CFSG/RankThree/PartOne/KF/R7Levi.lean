module

public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartOne.KF.SpSylow
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
import CFSG.RankThree.PartOne.KFOUT3.L12Levi

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem commute_diagU_apply {n : ℕ} {d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU d = diagU d * g) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) i j * (d j : K) =
      (d i : K) * (g : Matrix (Fin n) (Fin n) K) i j := by
  have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j) hg
  simpa [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] using this

theorem apply_eq_zero_of_commute_diagU {n : ℕ} {d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU d = diagU d * g) {i j : Fin n} (hij : d i ≠ d j) :
    (g : Matrix (Fin n) (Fin n) K) i j = 0 :=
  CFSG.RankThree.PartOne.KFOUT3.apply_eq_zero_of_commute_diagU' hg hij

@[expose] def blk22 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0 0, 0, 0, X 0 1; 0, 1, 0, 0; 0, 0, 1, 0; X 1 0, 0, 0, X 1 1]

theorem blk22_one : blk22 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk22]

theorem blk22_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk22 (X * Y) = blk22 X * blk22 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk22, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blk22_gram [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) (hX : X.det = 1) :
    (blk22 X)ᵀ * antidiag 4 * blk22 X = antidiag 4 := by
  rw [Matrix.det_fin_two] at hX
  ext i j
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;>
    simp [blk22, antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Fin.rev]
  all_goals first
    | linear_combination (X 0 0 * X 1 0) * h2
    | linear_combination hX + (X 0 1 * X 1 0) * h2
    | linear_combination (X 0 1 * X 1 1) * h2

theorem det_blk22 (X : Matrix (Fin 2) (Fin 2) K) : (blk22 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blk22, Fin.succAbove]
  ring

theorem blk22_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk22 X = blk22 Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk22] using congrFun (congrFun h 0) 0
  · simpa [blk22] using congrFun (congrFun h 0) 3
  · simpa [blk22] using congrFun (congrFun h 3) 0
  · simpa [blk22] using congrFun (congrFun h 3) 3

variable [CharP K 2]

@[expose] noncomputable def spBlock : SpecialLinearGroup (Fin 2) K →* ↥(spRev K) where
  toFun A :=
    ⟨{ val := blk22 (A : Matrix (Fin 2) (Fin 2) K)
       inv := blk22 ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
       val_inv := by
         rw [← blk22_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
           Matrix.SpecialLinearGroup.coe_one, blk22_one]
       inv_val := by
         rw [← blk22_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
           Matrix.SpecialLinearGroup.coe_one, blk22_one] }, by
      rw [mem_spRev_iff]
      exact blk22_gram _ A.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [blk22_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    simp [blk22_mul]

theorem coe_spBlock (A : SpecialLinearGroup (Fin 2) K) :
    (((spBlock A : ↥(spRev K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk22 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem spBlock_injective : Function.Injective (spBlock : SpecialLinearGroup (Fin 2) K →* _) := by
  intro A B h
  have h1 := congrArg (fun g : ↥(spRev K) =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  simp only [coe_spBlock] at h1
  exact Subtype.ext (blk22_injective h1)

@[expose] noncomputable def b7 (ζ : Kˣ) : ↥(spRev K) :=
  ⟨diagU (dvec4 1 ζ), diagU_dvec4_mem_spRev 1 ζ⟩

theorem coe_b7 (ζ : Kˣ) : ((b7 ζ : ↥(spRev K)) : GL (Fin 4) K) = diagU (dvec4 1 ζ) := rfl

abbrev gm (g : ↥(spRev K)) : Matrix (Fin 4) (Fin 4) K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem centralizer_b7_facts {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) {g : ↥(spRev K)}
    (hg : g ∈ Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K))) :
    gm g 0 1 = 0 ∧ gm g 0 2 = 0 ∧ gm g 3 1 = 0 ∧ gm g 3 2 = 0 ∧ gm g 1 0 = 0 ∧ gm g 2 0 = 0 ∧
      gm g 1 3 = 0 ∧ gm g 2 3 = 0 ∧ gm g 1 2 = 0 ∧ gm g 2 1 = 0 ∧ gm g 1 1 * gm g 2 2 = 1 ∧
      gm g 0 0 * gm g 3 3 + gm g 3 0 * gm g 0 3 = 1 := by
  have hcomm : (g : GL (Fin 4) K) * diagU (dvec4 1 ζ) = diagU (dvec4 1 ζ) * (g : GL (Fin 4) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ1 : (1 : Kˣ) ≠ ζ := fun h => h1 h.symm
  have hζ2 : (1 : Kˣ) ≠ ζ⁻¹ := fun h => h1 (by simpa using h.symm)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have e01 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 1) (by simpa [dvec4] using hζ1)
  have e02 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 2) (by simpa [dvec4] using hζ2)
  have e31 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1) (by simpa [dvec4] using hζ1)
  have e32 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 2) (by simpa [dvec4] using hζ2)
  have e10 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 0)
    (by simpa [dvec4] using hζ1.symm)
  have e20 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 0)
    (by simpa [dvec4] using hζ2.symm)
  have e13 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3)
    (by simpa [dvec4] using hζ1.symm)
  have e23 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 3)
    (by simpa [dvec4] using hζ2.symm)
  have e12 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 2) (by simpa [dvec4] using hζ3)
  have e21 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 1)
    (by simpa [dvec4] using hζ3.symm)
  have hgram := (mem_spRev_iff (K := K)).1 g.2
  have hg12 := congrFun (congrFun hgram 1) 2
  have hg03 := congrFun (congrFun hgram 0) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, Matrix.transpose_apply] at hg12 hg03
  refine ⟨e01, e02, e31, e32, e10, e20, e13, e23, e12, e21, ?_, ?_⟩
  · simpa [e10, e12, e13, e20, e21, e23, e01, e02, e31, e32] using hg12
  · have h := hg03
    simp only [e10, e13, e20, e23, mul_zero, add_zero] at h
    linear_combination h

theorem spBlock_mem_centralizer (ζ : Kˣ) (A : SpecialLinearGroup (Fin 2) K) :
    spBlock A ∈ Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_spBlock, coe_b7, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk22, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul]

omit [CharP K 2] in
theorem gm_one : gm (1 : ↥(spRev K)) = 1 := rfl

omit [CharP K 2] in
theorem gm_mul (g h : ↥(spRev K)) : gm (g * h) = gm g * gm h := rfl

@[expose] noncomputable def phi7 {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K))) →* Kˣ where
  toFun g := Units.mk0 (gm (g : ↥(spRev K)) 1 1) (fun h0 => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := centralizer_b7_facts h1 h2 g.2
    rw [h0, zero_mul] at h11
    exact zero_ne_one h11)
  map_one' := by
    apply Units.ext
    simp [gm_one]
  map_mul' g h := by
    apply Units.ext
    obtain ⟨-, -, -, -, h10, -, h13, -, h12, -, -, -⟩ := centralizer_b7_facts h1 h2 g.2
    simp [Subgroup.coe_mul, gm_mul, Matrix.mul_apply, Fin.sum_univ_four, h10, h12, h13]

theorem phi7_apply {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K)))) :
    ((phi7 h1 h2 g : Kˣ) : K) = gm (g : ↥(spRev K)) 1 1 := rfl

theorem ker_phi7 {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    (phi7 h1 h2).ker =
      (spBlock (K := K)).range.subgroupOf
        (Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e01, e02, e31, e32, e10, e20, e13, e23, e12, e21, h11, h03⟩ :=
    centralizer_b7_facts h1 h2 g.2
  constructor
  · intro h
    have h11' : gm (g : ↥(spRev K)) 1 1 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      rw [phi7_apply] at this
      simpa using this
    have h22 : gm (g : ↥(spRev K)) 2 2 = 1 := by
      rw [h11', one_mul] at h11
      exact h11
    have hdet : (!![gm (g : ↥(spRev K)) 0 0, gm (g : ↥(spRev K)) 0 3;
        gm (g : ↥(spRev K)) 3 0, gm (g : ↥(spRev K)) 3 3] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h03 - (gm (g : ↥(spRev K)) 3 0 * gm (g : ↥(spRev K)) 0 3) * h2'
    refine ⟨⟨_, hdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show blk22 ((⟨_, hdet⟩ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      gm (g : ↥(spRev K))
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk22, *]
  · rintro ⟨A, hA⟩
    apply Units.ext
    rw [phi7_apply]
    have : gm (g : ↥(spRev K)) 1 1 = gm (spBlock A) 1 1 := by rw [← hA]
    rw [this]
    show blk22 (A : Matrix (Fin 2) (Fin 2) K) 1 1 = ((1 : Kˣ) : K)
    simp [blk22]

theorem perfectResidual_centralizer_b7 [Finite K] (hK : 4 ≤ Nat.card K) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K))) =
      (spBlock (K := K)).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK
  have hperf : Group.IsPerfect ↥((spBlock (K := K)).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective spBlock_injective).toMonoidHom)
      (MonoidHom.ofInjective spBlock_injective).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact spBlock_mem_centralizer ζ A) hperf (phi7 h1 h2) (ker_phi7 h1 h2)

theorem isQuasisimple_perfectResidual_centralizer_b7 [Finite K] (hK : 4 ≤ Nat.card K) {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K)))) := by
  rw [perfectResidual_centralizer_b7 hK h1 h2]
  exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective spBlock_injective)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK)

theorem card_center_SL_two : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) K)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  have hbot : ∀ z : ↥(Subgroup.center (SpecialLinearGroup (Fin 2) K)), z = 1 := by
    intro z
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 z.2
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h2 : (r - 1) ^ 2 = 0 := by
        have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        rw [this, hr, CharTwo.two_eq_zero, zero_mul, sub_zero]
        exact CharTwo.add_self_eq_zero 1
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hrz, hr1]
    simp
  exact (hbot a).trans (hbot b).symm

theorem card_center_range_spBlock :
    Nat.card (Subgroup.center ↥((spBlock (K := K)).range)) = 1 := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (spBlock_injective (K := K)))]
  exact card_center_SL_two

@[expose] noncomputable def torus7 (p : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup ↥(spRev K) :=
  (d8Tor p K 4).subgroupOf (spRev K)

theorem mem_torus7_iff {p : ℕ} {g : ↥(spRev K)} :
    g ∈ torus7 p K ↔ ∃ a b : Kˣ, a ^ p = 1 ∧ b ^ p = 1 ∧
      ((g : GL (Fin 4) K)) = diagU (dvec4 a b) := by
  rw [torus7, Subgroup.mem_subgroupOf, mem_d8Tor_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v.1 : rootsOfUnity p K), (v.2 : rootsOfUnity p K),
      (mem_rootsOfUnity p _).1 v.1.2, (mem_rootsOfUnity p _).1 v.2.2, ?_⟩
    rw [← hv, d8Vec_four]
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨(⟨a, (mem_rootsOfUnity p _).2 ha⟩, ⟨b, (mem_rootsOfUnity p _).2 hb⟩), ?_⟩
    rw [h, d8Vec_four]

@[expose] noncomputable def rho7 : Kˣ →* ↥(spRev K) :=
  (spDiag K).comp (MonoidHom.inl Kˣ Kˣ)

theorem coe_rho7 (a : Kˣ) :
    ((rho7 a : ↥(spRev K)) : GL (Fin 4) K) = diagU (dvec4 a 1) := rfl

theorem rho7_injective : Function.Injective (rho7 : Kˣ →* ↥(spRev K)) := by
  intro a b h
  have := spDiag_injective (K := K) h
  exact (Prod.ext_iff.1 this).1

@[expose] noncomputable def diag2 (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal fun i => (![a, a⁻¹] i : K), by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp⟩

theorem spBlock_diag2 (a : Kˣ) : spBlock (diag2 a) = rho7 a := by
  apply Subtype.ext
  apply Units.ext
  show blk22 (Matrix.diagonal fun i => (![a, a⁻¹] i : K)) = _
  rw [coe_rho7, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk22, dvec4]

theorem rho7_mem_range (a : Kˣ) : (rho7 a : ↥(spRev K)) ∈ (spBlock (K := K)).range :=
  ⟨diag2 a, spBlock_diag2 a⟩

theorem torus7_inf_range_eq (p : ℕ) :
    torus7 p K ⊓ (spBlock (K := K)).range = (rootsOfUnity p K).map rho7 := by
  ext g
  constructor
  · rintro ⟨hgT, A, hA⟩
    obtain ⟨a, b, ha, hb, hab⟩ := mem_torus7_iff.1 hgT
    have h11 : gm g 1 1 = 1 := by
      rw [← hA]
      show blk22 (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
      simp [blk22]
    have hb1 : b = 1 := by
      have h' : gm g 1 1 = (b : K) := by
        show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
        rw [hab, diagU_val]
        simp [dvec4]
      exact Units.ext (by rw [← h', h11]; rfl)
    refine ⟨a, (mem_rootsOfUnity p _).2 ha, ?_⟩
    apply Subtype.ext
    rw [coe_rho7, hab, hb1]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨mem_torus7_iff.2 ⟨a, 1, (mem_rootsOfUnity p _).1 ha, one_pow p, coe_rho7 a⟩,
      rho7_mem_range a⟩

theorem card_torus7_inf_range {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus7 p K ⊓ (spBlock (K := K)).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus7_inf_range_eq, Subgroup.card_map_of_injective rho7_injective]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def tr2 (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.transvection 0 1 c, Matrix.det_transvection_of_ne 0 1 (by decide) c⟩

omit [CharP K 2] in
theorem tr2_zero : (tr2 (0 : K) : SpecialLinearGroup (Fin 2) K) = 1 := by
  apply Subtype.ext
  simp [tr2]

omit [CharP K 2] in
theorem tr2_mul (c d : K) :
    (tr2 c : SpecialLinearGroup (Fin 2) K) * tr2 d = tr2 (c + d) := by
  apply Subtype.ext
  simp only [tr2]
  exact Matrix.transvection_mul_transvection_same 0 1 (by decide) c d

@[expose] noncomputable def rootU7 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(spRev K) :=
  ((spBlock (K := K)).comp
    ({ toFun := fun c : Multiplicative K => tr2 (Multiplicative.toAdd c)
       map_one' := tr2_zero
       map_mul' := fun _ _ => (tr2_mul _ _).symm } :
      Multiplicative K →* SpecialLinearGroup (Fin 2) K)).range

theorem mem_rootU7_iff {g : ↥(spRev K)} : g ∈ rootU7 K ↔ ∃ c : K, g = spBlock (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem spBlock_tr2_mem_rootU7 (c : K) : spBlock (tr2 c) ∈ rootU7 K :=
  mem_rootU7_iff.2 ⟨c, rfl⟩

theorem rootU7_le_range : rootU7 K ≤ (spBlock (K := K)).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootU7_iff.1 hg
  exact ⟨tr2 c, rfl⟩

theorem isPGroup_rootU7 : IsPGroup 2 ↥(rootU7 K) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := mem_rootU7_iff.1 hg
  have hsq : (spBlock (tr2 c) : ↥(spRev K)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨spBlock (tr2 c), hg⟩ : ↥(rootU7 K)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torus7_conj_rootU7 {p : ℕ} {g : ↥(spRev K)} (hg : g ∈ torus7 p K) :
    ∀ x ∈ rootU7 K, g * x * g⁻¹ ∈ rootU7 K := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootU7_iff.1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_torus7_iff.1 hg
  have h : g * spBlock (tr2 c) = spBlock (tr2 ((a : K) * c * (a : K))) * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_spBlock, hab, diagU_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk22, tr2, Matrix.transvection, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have : g * spBlock (tr2 c) * g⁻¹ = spBlock (tr2 ((a : K) * c * (a : K))) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact spBlock_tr2_mem_rootU7 _

theorem torus7_pow_eq_one {p : ℕ} {g : ↥(spRev K)} (hg : g ∈ torus7 p K) : g ^ p = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus7_iff.1 hg
  apply Subtype.ext
  show ((g : GL (Fin 4) K)) ^ p = 1
  rw [hab, diagU_pow]
  have : dvec4 a b ^ p = 1 := by
    funext i
    fin_cases i <;> simp [dvec4, inv_pow, ha, hb]
  rw [this, diagU_one]

theorem b7_mem_torus7 {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) : b7 ζ ∈ torus7 p K :=
  mem_torus7_iff.2 ⟨1, ζ, one_pow p, hζ, rfl⟩

theorem rho7_mem_torus7 {p : ℕ} {a : Kˣ} (ha : a ^ p = 1) : (rho7 a : ↥(spRev K)) ∈ torus7 p K :=
  mem_torus7_iff.2 ⟨a, 1, ha, one_pow p, rfl⟩

theorem torus7_le_normalizer_rootU7 {p : ℕ} :
    torus7 p K ≤ Subgroup.normalizer (rootU7 K : Set ↥(spRev K)) := fun g hg =>
  mem_normalizer_of_conj_mem (torus7_conj_rootU7 hg) (fun y hy => by
    have := torus7_conj_rootU7 ((torus7 p K).inv_mem hg) y hy
    simpa using this)

theorem gm_spBlock (A : SpecialLinearGroup (Fin 2) K) :
    gm (spBlock A) = blk22 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem gm_rho7 (a : Kˣ) :
    gm (rho7 a : ↥(spRev K)) = Matrix.diagonal fun i => (dvec4 a 1 i : K) := rfl

theorem spBlock_tr2_one_not_commute_rho7 {a : Kˣ} (ha : a ≠ 1) :
    (spBlock (tr2 (1 : K)) : ↥(spRev K)) * rho7 a ≠ rho7 a * spBlock (tr2 (1 : K)) := by
  intro h
  have h1 := congrArg (fun x : ↥(spRev K) => gm x 0 3) h
  have e00 : gm (spBlock (tr2 (1 : K))) 0 0 = 1 := by
    rw [gm_spBlock]
    simp [blk22, tr2, Matrix.transvection]
  have e01 : gm (spBlock (tr2 (1 : K))) 0 1 = 0 := by
    rw [gm_spBlock]
    simp [blk22, tr2, Matrix.transvection]
  have e02 : gm (spBlock (tr2 (1 : K))) 0 2 = 0 := by
    rw [gm_spBlock]
    simp [blk22, tr2, Matrix.transvection]
  have e03 : gm (spBlock (tr2 (1 : K))) 0 3 = 1 := by
    rw [gm_spBlock]
    simp [blk22, tr2, Matrix.transvection]
  simp [gm_mul, gm_rho7, Matrix.mul_apply, Fin.sum_univ_four, dvec4, e00, e01, e02, e03] at h1
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

end CFSG.RankThree.PartOne.KFU
