module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldAlg
public import CFSG.LocalAnalysis.StandardType.GGHalfShear

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.Line63.H5

variable {K : Type} [Field K] {n : ℕ}

private theorem pow_eq_of_primitiveRoot_pow_eq {ζ a : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) (ha : a ^ 3 = 1) {p q : ℕ} (h : ζ ^ p = ζ ^ q) :
    a ^ p = a ^ q := by
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hpζ : ζ ^ p = ζ ^ (p % 3) := by
    conv_lhs => rw [← Nat.div_add_mod p 3]
    rw [pow_add, pow_mul, hζ3, one_pow, one_mul]
  have hqζ : ζ ^ q = ζ ^ (q % 3) := by
    conv_lhs => rw [← Nat.div_add_mod q 3]
    rw [pow_add, pow_mul, hζ3, one_pow, one_mul]
  have hpq : p % 3 = q % 3 :=
    hζ.pow_inj (Nat.mod_lt p (by norm_num)) (Nat.mod_lt q (by norm_num))
      (by rw [← hpζ, ← hqζ]; exact h)
  have hpa : a ^ p = a ^ (p % 3) := by
    conv_lhs => rw [← Nat.div_add_mod p 3]
    rw [pow_add, pow_mul, ha, one_pow, one_mul]
  have hqa : a ^ q = a ^ (q % 3) := by
    conv_lhs => rw [← Nat.div_add_mod q 3]
    rw [pow_add, pow_mul, ha, one_pow, one_mul]
  rw [hpa, hqa, hpq]

theorem exists_weyl_matrix (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {X Y Z : GL (Fin 6) K} (hX : X ∈ primeFormUnitary hKd (idGram K 6))
    (hZ : Z ∈ primeFormUnitary hKd (idGram K 6)) (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (hZs : Z ∉ LargeEvenScalars (Fin 6) K) :
    Z ∈ unitarySU 2 n K 6 ∧ ∃ w : ↥(unitarySU 2 n K 6),
      (w : GL (Fin 6) K) * X = X * w ∧ (w : GL (Fin 6) K) * Z = Z * w ∧
        (w : GL (Fin 6) K) * Y = Y * Z * w := by
  classical
  haveI : Finite K := hKd.finite
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨P, hP, η, ε, σ, hη, hε, hση, hσε, hη3, hε3⟩ :=
    exists_frame_data_heis hKd hpq hX hZ hX3 hZ3 hXY hXZ hYZ
  set Y' : GL (Fin 6) K := P⁻¹ * Y * P with hY'
  have hXY' : diagHom 6 η * Y' =
      GeneralLinearGroup.scalar (Fin 6) ζ * (Y' * diagHom 6 η) := by
    rw [← hη, hY']
    have e1 : (P⁻¹ * X * P) * (P⁻¹ * Y * P) = P⁻¹ * (X * Y) * P := by group
    have e2 : (P⁻¹ * Y * P) * (P⁻¹ * X * P) = P⁻¹ * (Y * X) * P := by group
    rw [e1, e2, hXY, conj_scalar_mul_six]
  have hYZ' : diagHom 6 ε * Y' = Y' * diagHom 6 ε := by
    rw [← hε, hY']
    have e1 : (P⁻¹ * Z * P) * (P⁻¹ * Y * P) = P⁻¹ * (Z * Y) * P := by group
    have e2 : (P⁻¹ * Y * P) * (P⁻¹ * Z * P) = P⁻¹ * (Y * Z) * P := by group
    rw [e1, e2, hYZ]
  have henta : ∀ i j, (Y' : Matrix (Fin 6) (Fin 6) K) i j ≠ 0 → η i = ζ * η j := by
    intro i j hij
    have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) i j) hXY'
    simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    apply Units.ext
    have h2 : (η i : K) * (Y' : Matrix (Fin 6) (Fin 6) K) i j =
        ((ζ : K) * (η j : K)) * (Y' : Matrix (Fin 6) (Fin 6) K) i j := by
      rw [h1]; ring
    exact mul_right_cancel₀ hij h2
  have heps : ∀ i j, (Y' : Matrix (Fin 6) (Fin 6) K) i j ≠ 0 → ε i = ε j := by
    intro i j hij
    have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) i j) hYZ'
    simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    apply Units.ext
    exact mul_right_cancel₀ hij (by rw [h1, mul_comm])
  have hdiv : ∀ v : Kˣ, ∃ m : ℕ, (Finset.univ.filter fun i => ε i = v).card = 3 * m := by
    intro v
    obtain ⟨h1, -, -⟩ := card_filter_shift_cube σ (fun i => ε i = v) η hζ
      (fun j => by rw [hσε]) hση hη3
    exact ⟨_, h1⟩
  have hnc : ∃ j₁ j₂, ε j₁ ≠ ε j₂ := by
    by_contra hcon
    push Not at hcon
    apply hZs
    have h1 : diagHom 6 ε = GeneralLinearGroup.scalar (Fin 6) (ε 0) :=
      diagHom_eq_scalar_iff.mpr fun k => hcon k 0
    have h2 : Z = P * (P⁻¹ * Z * P) * P⁻¹ := by group
    rw [hε, h1] at h2
    refine ⟨ε 0, ?_⟩
    rw [h2, (commute_scalar (ε 0) P).eq]
    group
  let T : Finset Kˣ := Finset.univ.image ε
  have hmemT : ∀ j : Fin 6, ε j ∈ T := fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hcardT : 2 ≤ T.card := by
    obtain ⟨j₁, j₂, hj⟩ := hnc
    have hsub : ({ε j₁, ε j₂} : Finset Kˣ) ⊆ T := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_image.mpr ⟨j₁, Finset.mem_univ j₁, rfl⟩
      · rw [Finset.mem_singleton.mp hv]
        exact Finset.mem_image.mpr ⟨j₂, Finset.mem_univ j₂, rfl⟩
    calc 2 = ({ε j₁, ε j₂} : Finset Kˣ).card := (Finset.card_pair hj).symm
      _ ≤ T.card := Finset.card_le_card hsub
  have hsum : 6 = ∑ v ∈ T, (Finset.univ.filter fun i => ε i = v).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 6)))
      (t := T) (f := ε) (fun j _ => hmemT j)
    simpa using h
  have h3le : ∀ v ∈ T, 3 ≤ (Finset.univ.filter fun i => ε i = v).card := by
    intro v hv
    obtain ⟨m, hm⟩ := hdiv v
    have hpos : 1 ≤ (Finset.univ.filter fun i => ε i = v).card := by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hv
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    omega
  have hle2 : T.card ≤ 2 := by
    have h1 := Finset.card_nsmul_le_sum T
      (fun v => (Finset.univ.filter fun i => ε i = v).card) 3 h3le
    rw [← hsum, Nat.nsmul_eq_mul] at h1
    omega
  have hTcard : T.card = 2 := le_antisymm hle2 hcardT
  obtain ⟨v₁, v₂, hv12, hT⟩ := Finset.card_eq_two.mp hTcard
  have hv1T : v₁ ∈ T := by rw [hT]; simp
  have hv2T : v₂ ∈ T := by rw [hT]; simp
  have hsum2 : (Finset.univ.filter fun i => ε i = v₁).card +
      (Finset.univ.filter fun i => ε i = v₂).card = 6 := by
    have h := hsum
    rw [hT, Finset.sum_insert (by simp [hv12]), Finset.sum_singleton] at h
    omega
  have hm1 : (Finset.univ.filter fun i => ε i = v₁).card = 3 := by
    have h1 := h3le v₁ hv1T
    have h2 := h3le v₂ hv2T
    omega
  have hm2 : (Finset.univ.filter fun i => ε i = v₂).card = 3 := by
    have h1 := h3le v₁ hv1T
    have h2 := h3le v₂ hv2T
    omega
  have hm : ∀ v ∈ T, (Finset.univ.filter fun i => ε i = v).card = 3 := by
    intro v hv
    rw [hT] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hm1
    · rw [Finset.mem_singleton.mp hv]; exact hm2
  have hcount : ∀ v ∈ T,
      (Finset.univ.filter fun i => ε i = v ∧ η i = 1).card = 1 ∧
      (Finset.univ.filter fun i => ε i = v ∧ η i = ζ).card = 1 ∧
      (Finset.univ.filter fun i => ε i = v ∧ η i = ζ ^ 2).card = 1 := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := card_filter_shift_cube σ (fun i => ε i = v) η hζ
      (fun j => by rw [hσε]) hση hη3
    have hc := hm v hv
    have h0 : (Finset.univ.filter fun i => ε i = v ∧ η i = 1).card = 1 := by omega
    exact ⟨h0, by omega, by omega⟩
  have hηmem : ∀ i, η i ∈ ({1, ζ, ζ ^ 2} : Finset Kˣ) := by
    intro i
    obtain ⟨m, hm_lt, hm_eq⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ _).mpr (hη3 i))
    rw [← hm_eq]
    interval_cases m <;> simp
  have hfiber : ∀ v ∈ T, ∀ u : Kˣ,
      (Finset.univ.filter fun i => ε i = v ∧ η i = u).card ≤ 1 := by
    intro v hv u
    obtain ⟨h0, hζc, hζ2c⟩ := hcount v hv
    by_cases hu : u ∈ ({1, ζ, ζ ^ 2} : Finset Kˣ)
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [h0]
      · rcases Finset.mem_insert.mp hu with rfl | hu
        · rw [hζc]
        · rw [Finset.mem_singleton.mp hu, hζ2c]
    · have hempty : (Finset.univ.filter fun i => ε i = v ∧ η i = u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hu (by rw [← (Finset.mem_filter.mp hi).2.2]; exact hηmem i)
      rw [hempty, Finset.card_empty]
      omega
  choose k hk using fun j =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).mpr (hη3 j))
  have hk_lt : ∀ j, k j < 3 := fun j => (hk j).1
  have hk_eq : ∀ j, ζ ^ k j = η j := fun j => (hk j).2
  let δ : Fin 6 → Kˣ := fun j => ε j ^ k j
  have hk_inj : ∀ v ∈ T, ∀ i ∈ Finset.univ.filter (fun i => ε i = v),
      ∀ j ∈ Finset.univ.filter (fun i => ε i = v), k i = k j → i = j := by
    intro v hv i hi j hj hkij
    have heta : η i = η j := by rw [← hk_eq i, ← hk_eq j, hkij]
    have hi' : i ∈ Finset.univ.filter (fun x => ε x = v ∧ η x = η i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2, rfl⟩
    have hj' : j ∈ Finset.univ.filter (fun x => ε x = v ∧ η x = η i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2, heta.symm⟩
    exact (Finset.card_le_one.mp (hfiber v hv (η i))) i hi' j hj'
  have hsumk : ∀ v ∈ T, ∑ i ∈ Finset.univ.filter (fun i => ε i = v), k i = 3 := by
    intro v hv
    have hcard : (Finset.range 3).card ≤
        ((Finset.univ.filter fun i => ε i = v).image k).card := by
      rw [Finset.card_range,
        Finset.card_image_of_injOn (fun i hi j hj hij => hk_inj v hv i hi j hj hij),
        hm v hv]
    have hsub : (Finset.univ.filter fun i => ε i = v).image k ⊆ Finset.range 3 := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hk_lt i)
    have himg : (Finset.univ.filter fun i => ε i = v).image k = Finset.range 3 :=
      (Finset.subset_iff_eq_of_card_le hcard).mp hsub
    calc ∑ i ∈ Finset.univ.filter (fun i => ε i = v), k i
        = ∑ m ∈ (Finset.univ.filter fun i => ε i = v).image k, m := by
          rw [Finset.sum_image]
          intro i hi j hj hij
          exact hk_inj v hv i hi j hj hij
      _ = ∑ m ∈ Finset.range 3, m := by rw [himg]
      _ = 3 := by norm_num [Finset.sum_range_id]
  have hεprod : ∏ j, ε j = 1 := by
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := ε) (f := fun i => ε i)]
    apply Finset.prod_eq_one
    intro v _
    by_cases hv : v ∈ T
    · have h1 : ∏ i ∈ Finset.univ.filter (fun i => ε i = v), ε i =
          ∏ i ∈ Finset.univ.filter (fun i => ε i = v), v := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [h1, Finset.prod_const, hm v hv]
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hv
      rw [← hi, hε3 i]
    · have hempty : (Finset.univ.filter fun i => ε i = v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
      rw [hempty, Finset.prod_empty]
  have hδ3 : ∀ j, δ j ^ 3 = 1 := by
    intro j
    show (ε j ^ k j) ^ 3 = 1
    rw [← pow_mul, mul_comm (k j) 3, pow_mul, hε3 j, one_pow]
  have hδprod : ∏ j, δ j = 1 := by
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := ε) (f := fun i => δ i)]
    apply Finset.prod_eq_one
    intro v _
    by_cases hv : v ∈ T
    · have h1 : ∏ i ∈ Finset.univ.filter (fun i => ε i = v), δ i =
          ∏ i ∈ Finset.univ.filter (fun i => ε i = v), v ^ k i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [show δ i = ε i ^ k i from rfl, (Finset.mem_filter.mp hi).2]
      rw [h1, Finset.prod_pow_eq_pow_sum, hsumk v hv]
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hv
      rw [← hi, hε3 i]
    · have hempty : (Finset.univ.filter fun i => ε i = v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
      rw [hempty, Finset.prod_empty]
  have hδSU : diagHom 6 δ ∈ unitarySU 2 n K 6 := by
    refine TableBUE.diagHom_mem_unitarySU hKd (fun j => ?_) hδprod
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hδ3 j, one_pow]
  have hdetZ : (((P * diagHom 6 ε * P⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    have h1 : (((P * diagHom 6 ε * P⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).det
        = ((diagHom 6 ε : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det :=
      Matrix.det_units_conj P ((diagHom 6 ε : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [h1, det_diagHom, ← Units.coe_prod, hεprod, Units.val_one]
  have hZSU : Z ∈ unitarySU 2 n K 6 := by
    refine TableBUE.mem_unitarySU_of_mem_primeFormUnitary hKd hZ ?_
    have hZeq : Z = P * diagHom 6 ε * P⁻¹ := by rw [← hε]; group
    rw [hZeq]
    exact hdetZ
  have hXeq : X = P * diagHom 6 η * P⁻¹ := by rw [← hη]; group
  have hZeq : Z = P * diagHom 6 ε * P⁻¹ := by rw [← hε]; group
  have hYeq : Y = P * Y' * P⁻¹ := by rw [hY']; group
  have hδη : diagHom 6 δ * diagHom 6 η = diagHom 6 η * diagHom 6 δ := by
    rw [← map_mul, ← map_mul, mul_comm δ η]
  have hδε : diagHom 6 δ * diagHom 6 ε = diagHom 6 ε * diagHom 6 δ := by
    rw [← map_mul, ← map_mul, mul_comm δ ε]
  have hδY' : diagHom 6 δ * Y' = Y' * diagHom 6 ε * diagHom 6 δ := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : (Y' : Matrix (Fin 6) (Fin 6) K) i j = 0
    · rw [hij]; ring
    · have heta := henta i j hij
      have heps := heps i j hij
      have hδrel : δ i = ε j * δ j := by
        have h1 : ζ ^ k i = ζ ^ (k j + 1) := by
          rw [hk_eq i, heta, ← hk_eq j, mul_comm, ← pow_succ]
        have h2 : ε j ^ k i = ε j ^ (k j + 1) :=
          pow_eq_of_primitiveRoot_pow_eq hζ (hε3 j) h1
        rw [show δ i = ε i ^ k i from rfl, show δ j = ε j ^ k j from rfl, heps, h2, pow_succ']
      have hδrelK : (δ i : K) = (ε j : K) * (δ j : K) := by rw [hδrel]; rfl
      rw [hδrelK]; ring
  have hdetW : (((P * diagHom 6 δ * P⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    have h1 : (((P * diagHom 6 δ * P⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).det
        = ((diagHom 6 δ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det :=
      Matrix.det_units_conj P ((diagHom 6 δ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [h1, det_diagHom, ← Units.coe_prod, hδprod, Units.val_one]
  let w : ↥(unitarySU 2 n K 6) :=
    ⟨P * diagHom 6 δ * P⁻¹, by
      refine TableBUE.mem_unitarySU_of_mem_primeFormUnitary hKd ?_ hdetW
      exact (primeFormUnitary hKd (idGram K 6)).mul_mem
        ((primeFormUnitary hKd (idGram K 6)).mul_mem hP
          (TableBUE.unitarySU_le_primeFormUnitary hKd hδSU))
        ((primeFormUnitary hKd (idGram K 6)).inv_mem hP)⟩
  have hwcoe : (w : GL (Fin 6) K) = P * diagHom 6 δ * P⁻¹ := rfl
  have hwX : (w : GL (Fin 6) K) * X = X * (w : GL (Fin 6) K) := by
    have e1 : (w : GL (Fin 6) K) * X = P * (diagHom 6 δ * diagHom 6 η) * P⁻¹ := by
      rw [hwcoe, hXeq]; group
    have e2 : X * (w : GL (Fin 6) K) = P * (diagHom 6 η * diagHom 6 δ) * P⁻¹ := by
      rw [hwcoe, hXeq]; group
    rw [e1, e2, hδη]
  have hwZ : (w : GL (Fin 6) K) * Z = Z * (w : GL (Fin 6) K) := by
    have e1 : (w : GL (Fin 6) K) * Z = P * (diagHom 6 δ * diagHom 6 ε) * P⁻¹ := by
      rw [hwcoe, hZeq]; group
    have e2 : Z * (w : GL (Fin 6) K) = P * (diagHom 6 ε * diagHom 6 δ) * P⁻¹ := by
      rw [hwcoe, hZeq]; group
    rw [e1, e2, hδε]
  have hwY : (w : GL (Fin 6) K) * Y = Y * Z * (w : GL (Fin 6) K) := by
    have e1 : (w : GL (Fin 6) K) * Y = P * (diagHom 6 δ * Y') * P⁻¹ := by
      rw [hwcoe, hYeq]; group
    have e2 : Y * Z * (w : GL (Fin 6) K) =
        P * (Y' * diagHom 6 ε * diagHom 6 δ) * P⁻¹ := by
      rw [hwcoe, hYeq, hZeq]; group
    rw [e1, e2, hδY']
  exact ⟨hZSU, ⟨w, hwX, hwZ, hwY⟩⟩

theorem exists_actor_monomial_decomposition [Finite K]
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (A : ↥Bs → GL (Fin 6) K)
    (hAN : ∀ b, A b ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hAb : Nat.card Ab = 27)
    {X Y Z : GL (Fin 6) K}
    (hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hYN : Y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hZN : Z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hXu : X ∈ primeFormUnitary hKd (idGram K 6))
    (hYu : Y ∈ primeFormUnitary hKd (idGram K 6))
    (hZu : Z ∈ primeFormUnitary hKd (idGram K 6))
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hXA : TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ ∈ Ab)
    (hYA : TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ ∈ Ab)
    (hZA : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ ∈ Ab)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X))
    (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y)
    (hZ3 : Z ^ 3 = 1) (hZs : Z ∉ LargeEvenScalars (Fin 6) K)
    (hAA : ∀ b, TableB.projConj (unitarySU 2 n K 6) ⟨A b, hAN b⟩ ∈ Ab) :
    ∃ (i j k : ↥Bs → ℕ) (c : ↥Bs → Kˣ),
      (∀ b, i b < 3 ∧ j b < 3 ∧ k b < 3) ∧
      ∀ b, A b = GeneralLinearGroup.scalar (Fin 6) (c b) *
        (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) := by
  classical
  have hmono : ∀ b : ↥Bs, ∃ (i j k : ℕ) (c : Kˣ),
      i < 3 ∧ j < 3 ∧ k < 3 ∧
      A b = GeneralLinearGroup.scalar (Fin 6) c *
        (X ^ i * Y ^ j * Z ^ k) := by
    intro b
    obtain ⟨i, j, k, hM, hi, hj, hk, heq⟩ :=
      CFSG.StandardType.Line63.H5.exists_mono_of_card hKd hpq hAb hXN hYN hZN hζ hXA hYA hZA
        hXY hXZ hYZ hZ3 hZs
        (TableB.projConj (unitarySU 2 n K 6) ⟨A b, hAN b⟩) (hAA b)
    obtain ⟨c, hc⟩ := CFSG.StandardType.Line63.H5.exists_scalar_mul_of_projConj_eq'
      hKd hpq (hAN b) hM heq
    exact ⟨i, j, k, c, hi, hj, hk, hc⟩
  choose i j k c hi hj hk hAeq using hmono
  exact ⟨i, j, k, c, fun b => ⟨hi b, hj b, hk b⟩, hAeq⟩

theorem not_noTransvection_of_actual_triple [Finite K]
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (φ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)) →* ↥J)
    (hφker : ∀ g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)), φ g = 1 →
      ∃ c : Kˣ, (g : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c)
    (A : ↥Bs → GL (Fin 6) K)
    (hAN : ∀ b, A b ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (conjA : ∀ b : ↥Bs, ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)) →
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)))
    (hconjA_coe : ∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n))),
      (conjA b g : GL (Fin 6) K) = A b * (g : GL (Fin 6) K) * (A b)⁻¹)
    (hact : ∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n))),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ = ((φ (conjA b g) : ↥J) : G))
    {X Y Z : GL (Fin 6) K}
    (hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hYN : Y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hZN : Z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hXu : X ∈ primeFormUnitary hKd (idGram K 6))
    (hYu : Y ∈ primeFormUnitary hKd (idGram K 6))
    (hZu : Z ∈ primeFormUnitary hKd (idGram K 6))
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X))
    (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y)
    (hZs : Z ∉ LargeEvenScalars (Fin 6) K)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAb : Nat.card Ab = 27)
    (hXA : TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ ∈ Ab)
    (hYA : TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ ∈ Ab)
    (hZA : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ ∈ Ab)
    (hAA : ∀ b, TableB.projConj (unitarySU 2 n K 6) ⟨A b, hAN b⟩ ∈ Ab)
    (hYreal : ∃ b : ↥Bs, TableB.projConj (unitarySU 2 n K 6) ⟨A b, hAN b⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩) :
    ¬ CFSG.StandardType.GGNoTransvection 3 Bs := by
  classical
  obtain ⟨i, j, k, c, hlt, hAeq⟩ :=
    exists_actor_monomial_decomposition hKd hpq A hAN hAb hXN hYN hZN hXu hYu hZu hζ hXA hYA hZA
      hXY hXZ hYZ hZ3 hZs hAA
  let M : ↥Bs → GL (Fin 6) K := fun b => X ^ (i b) * Y ^ (j b) * Z ^ (k b)
  have hM : ∀ b, M b ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    fun b => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hXN _)
      (Subgroup.pow_mem _ hYN _)) (Subgroup.pow_mem _ hZN _)
  obtain ⟨hZSU, w, hwX, hwZ, hwY⟩ :=
    exists_weyl_matrix hKd hpq hXu hZu hX3 hZ3 hζ hXY hXZ hYZ hZs
  let Zc : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)) := ⟨Z, hZSU⟩
  let wc : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n)) := ⟨(w : GL (Fin 6) K), w.2⟩
  let nJ : ↥J := φ wc
  let zJ : ↥J := φ Zc
  let nG : G := (nJ : G)
  let z : G := (zJ : G)
  have hwc_val : (wc : GL (Fin 6) K) = (w : GL (Fin 6) K) := rfl
  have hZc_val : (Zc : GL (Fin 6) K) = Z := rfl
  have hwXgl : (w : GL (Fin 6) K) * X = X * (w : GL (Fin 6) K) := hwX
  have hwZgl : (w : GL (Fin 6) K) * Z = Z * (w : GL (Fin 6) K) := hwZ
  have hwYgl : (w : GL (Fin 6) K) * Y = Y * Z * (w : GL (Fin 6) K) := hwY
  have hZc3 : Zc ^ 3 = 1 := by
    apply Subtype.ext
    simpa [Zc] using hZ3
  have hz3 : z ^ 3 = 1 := by
    have hz3J : zJ ^ 3 = 1 := by
      dsimp [zJ]
      rw [← map_pow, hZc3, map_one]
    dsimp [z]
    simpa using congrArg (fun x : ↥J => (x : G)) hz3J
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hz1J : zJ = 1 := Subtype.ext (by simpa [z] using hz1)
    obtain ⟨cc, hcc⟩ := hφker Zc (by simpa [zJ] using hz1J)
    exact hZs (by
      rw [show Z = GeneralLinearGroup.scalar (Fin 6) cc from ?_]
      · exact scalar_mem_largeEvenScalars cc
      · simpa [Zc] using hcc)
  have hZM : ∀ a b d : ℕ, Z * (X ^ a * Y ^ b * Z ^ d) = (X ^ a * Y ^ b * Z ^ d) * Z := by
    intro a b d
    have hZX : Commute Z X := hXZ.symm
    have hZY : Commute Z Y := hYZ.symm
    have hZZ : Commute Z Z := Commute.refl Z
    have h := ((hZX.pow_right a).mul_right (hZY.pow_right b)).mul_right (hZZ.pow_right d)
    simpa only [mul_assoc] using h.eq
  have hsc_comm : ∀ (r : Kˣ) (g : GL (Fin 6) K),
      GeneralLinearGroup.scalar (Fin 6) r * g = g * GeneralLinearGroup.scalar (Fin 6) r :=
    fun r g => (commute_scalar r g).symm.eq
  have hAZ : ∀ b : ↥Bs, A b * Z = Z * A b := by
    intro b
    have hZMb := hZM (i b) (j b) (k b)
    rw [hAeq b]
    calc
      (GeneralLinearGroup.scalar (Fin 6) (c b) * (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) * Z
          = GeneralLinearGroup.scalar (Fin 6) (c b) *
              ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * Z) := by group
      _ = GeneralLinearGroup.scalar (Fin 6) (c b) *
              (Z * (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) := by rw [hZMb]
      _ = (GeneralLinearGroup.scalar (Fin 6) (c b) * Z) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) := by group
      _ = (Z * GeneralLinearGroup.scalar (Fin 6) (c b)) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) := by rw [hsc_comm (c b) Z]
      _ = Z * (GeneralLinearGroup.scalar (Fin 6) (c b) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) := by group
  have hMw : ∀ b : ↥Bs,
      (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (w : GL (Fin 6) K) *
        (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ =
      ((Z ^ (j b))⁻¹ * (w : GL (Fin 6) K)) := by
    intro b
    have hWm := weyl_mono hwX hwZ hwY hXZ hYZ (i b) (j b) (k b)
    have hCZ : Commute Z (M b) := hZM (i b) (j b) (k b)
    have hZjM : Commute (Z ^ (j b)) (M b) := hCZ.pow_left (j b)
    calc
        (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (w : GL (Fin 6) K) *
            (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹
            = (Z ^ (j b))⁻¹ * (Z ^ (j b) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) * (w : GL (Fin 6) K) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by group
        _ = (Z ^ (j b))⁻¹ * ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) *
                (Z ^ (j b))) * (w : GL (Fin 6) K) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by rw [hZjM.eq]
        _ = (Z ^ (j b))⁻¹ * ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) *
                (Z ^ (j b)) * (w : GL (Fin 6) K)) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by group
        _ = (Z ^ (j b))⁻¹ * ((w : GL (Fin 6) K) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by rw [← hWm]
        _ = (Z ^ (j b))⁻¹ * (w : GL (Fin 6) K) := by group
  have hAmw : ∀ b : ↥Bs,
      A b * (wc : GL (Fin 6) K) * (A b)⁻¹ =
        (((Zc ^ (j b))⁻¹ * wc : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n))) : GL (Fin 6) K) := by
    intro b
    rw [hAeq b]
    calc
      (GeneralLinearGroup.scalar (Fin 6) (c b) * (X ^ (i b) * Y ^ (j b) * Z ^ (k b))) *
          (wc : GL (Fin 6) K) *
          (GeneralLinearGroup.scalar (Fin 6) (c b) *
            (X ^ (i b) * Y ^ (j b) * Z ^ (k b)))⁻¹
          = GeneralLinearGroup.scalar (Fin 6) (c b) *
              ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (wc : GL (Fin 6) K) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹) *
              (GeneralLinearGroup.scalar (Fin 6) (c b))⁻¹ := by group
      _ = ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (wc : GL (Fin 6) K) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹) *
              GeneralLinearGroup.scalar (Fin 6) (c b) *
              (GeneralLinearGroup.scalar (Fin 6) (c b))⁻¹ := by
            rw [hsc_comm (c b)
              ((X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (wc : GL (Fin 6) K) *
                (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹)]
      _ = (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (wc : GL (Fin 6) K) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by group
      _ = (X ^ (i b) * Y ^ (j b) * Z ^ (k b)) * (w : GL (Fin 6) K) *
              (X ^ (i b) * Y ^ (j b) * Z ^ (k b))⁻¹ := by
            rw [show (wc : GL (Fin 6) K) = (w : GL (Fin 6) K) from rfl]
      _ = (Z ^ (j b))⁻¹ * (w : GL (Fin 6) K) := hMw b
      _ = ((Zc ^ (j b))⁻¹ * wc : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n))) := by
            simp [wc, Zc]
  have hconjA : ∀ b : ↥Bs,
      conjA b wc =
        (⟨(Zc ^ (j b))⁻¹ * wc,
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ Zc.2 (j b))) wc.2⟩ :
            ↥(LargeEvenSUGroup (Fin 6) K (2 ^ n))) := by
    intro b
    apply Subtype.ext
    rw [hconjA_coe b wc]
    exact hAmw b
  have hconj_b : ∀ b : ↥Bs, nG * (b : G) * nG⁻¹ = z ^ (j b) * (b : G) := by
    intro b
    have hbn : (b : G) * nG * (b : G)⁻¹ = (z ^ (j b))⁻¹ * nG := by
      have h := hact b wc
      rw [hconjA b] at h
      have hmap : ((φ ((Zc ^ (j b))⁻¹ * wc) : ↥J) : G) = (z ^ (j b))⁻¹ * nG := by
        simp [z, zJ, nG, nJ, map_mul, map_pow, map_inv]
      exact h.trans hmap
    have hcomm_bn : (b : G) * nG * (b : G)⁻¹ * nG⁻¹ = (z ^ (j b))⁻¹ := by
      rw [hbn]
      group
    have hcomm_nb : nG * (b : G) * nG⁻¹ * (b : G)⁻¹ = z ^ (j b) := by
      calc nG * (b : G) * nG⁻¹ * (b : G)⁻¹
          = ((b : G) * nG * (b : G)⁻¹ * nG⁻¹)⁻¹ := by group
        _ = ((z ^ (j b))⁻¹)⁻¹ := by rw [hcomm_bn]
        _ = z ^ (j b) := by simp
    calc nG * (b : G) * nG⁻¹
        = (nG * (b : G) * nG⁻¹ * (b : G)⁻¹) * (b : G) := by group
      _ = z ^ (j b) * (b : G) := by rw [hcomm_nb]
  have hz_comm : ∀ b : ↥Bs, (b : G) * z = z * (b : G) := by
    intro b
    have hbZ : (b : G) * z * (b : G)⁻¹ = z := by
      have h := hact b Zc
      have hAZc : conjA b Zc = Zc := by
        apply Subtype.ext
        rw [hconjA_coe b Zc]
        change A b * Z * (A b)⁻¹ = Z
        rw [hAZ b]
        group
      rw [hAZc] at h
      simpa [z, zJ] using h
    calc (b : G) * z = ((b : G) * z * (b : G)⁻¹) * (b : G) := by group
      _ = z * (b : G) := by rw [hbZ]
  have hz_cent : z ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hz_comm ⟨b, hb⟩
  have hzBs : z ∈ Bs := hSC z hz_cent hz3
  have hna : nG * z * nG⁻¹ = z := by
    have hZw : wc * Zc = Zc * wc := by
      apply Subtype.ext
      simpa [wc, Zc] using hwZ
    have hnzJ : nJ * zJ * nJ⁻¹ = zJ := by
      calc nJ * zJ * nJ⁻¹ = φ (wc * Zc * wc⁻¹) := by
            simp [nJ, zJ, map_mul, map_inv]
        _ = φ Zc := by rw [hZw]; group
        _ = zJ := rfl
    dsimp [nG, z]
    simpa using congrArg (fun x : ↥J => (x : G)) hnzJ
  have hn_conj_mem : ∀ b : ↥Bs, nG * (b : G) * nG⁻¹ ∈ Bs := by
    intro b
    rw [hconj_b b]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hzBs (j b)) b.2
  have hn_norm : nG ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hn_conj_mem ⟨b, hb⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj nG).injective]
  have himg : ∀ b ∈ Bs, nG * b * nG⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro b hb
    rw [hconj_b ⟨b, hb⟩]
    simp [mul_assoc]
  obtain ⟨bY, hbY⟩ := hYreal
  have hproj : ∀ b : ↥Bs,
      TableB.projConj (unitarySU 2 n K 6) ⟨A b, hAN b⟩ =
        TableB.projConj (unitarySU 2 n K 6) ⟨M b, hM b⟩ := by
    intro b
    have hsub : (⟨A b, hAN b⟩ :
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
        (⟨GeneralLinearGroup.scalar (Fin 6) (c b),
          TableB.scalar_mem_normalizer _ (scalar_mem_largeEvenScalars (c b))⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
        ⟨M b, hM b⟩ := by
      apply Subtype.ext
      simpa [M] using hAeq b
    have hscalar_proj : TableB.projConj (unitarySU 2 n K 6)
        (⟨GeneralLinearGroup.scalar (Fin 6) (c b),
          TableB.scalar_mem_normalizer _ (scalar_mem_largeEvenScalars (c b))⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = 1 :=
      TableB.projConj_of_scalar _ (scalar_mem_largeEvenScalars (c b))
    rw [hsub, map_mul, hscalar_proj, one_mul]
  have hjY : j bY ≠ 0 := by
    have hprojM : TableB.projConj (unitarySU 2 n K 6) ⟨M bY, hM bY⟩ =
        TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ :=
      (hproj bY).symm.trans hbY
    obtain ⟨tt, htt⟩ := CFSG.StandardType.Line63.H5.exists_scalar_mul_of_projConj_eq'
      hKd hpq (hM bY) hYN hprojM
    have hM_eq' : X ^ (i bY) * Y ^ (j bY) * Z ^ (k bY) =
        GeneralLinearGroup.scalar (Fin 6) tt * (X ^ 0 * Y ^ 1 * Z ^ 0) := by
      simpa [M] using htt
    have hu3 : GeneralLinearGroup.scalar (Fin 6) ζ ^ 3 = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have hu1 : GeneralLinearGroup.scalar (Fin 6) ζ ≠ 1 := fun h =>
      hζ.ne_one (by norm_num) (TypeA.PGLTor.scalar_injective (by rw [h, map_one]))
    obtain ⟨-, hj1, -⟩ := mono_inj (scalar_mem_largeEvenScalars ζ) hu3 hu1 hXY hXZ hYZ hZ3 hZs
      (scalar_mem_largeEvenScalars tt) (hlt bY).2.1 (by norm_num : 1 < 3)
      (hlt bY).1 (by norm_num : 0 < 3) (hlt bY).2.2 (by norm_num : 0 < 3) hM_eq'
    omega
  clear hproj
  have hmove : ∃ b ∈ Bs, nG * b * nG⁻¹ ≠ b := by
    refine ⟨bY, bY.2, ?_⟩
    intro hfix
    have hzpow_eq : z ^ (j bY) * (bY : G) = (bY : G) := by
      rw [← hconj_b bY]
      exact hfix
    have hzpow1 : z ^ (j bY) = 1 := by
      have h1 : z ^ (j bY) * (bY : G) = 1 * (bY : G) := by simpa using hzpow_eq
      exact mul_right_cancel h1
    have hdvd : orderOf z ∣ j bY := (orderOf_dvd_iff_pow_eq_one).mpr hzpow1
    have hzorder : orderOf z = 3 := orderOf_eq_prime hz3 hz_ne
    rw [hzorder] at hdvd
    have hj0 : j bY % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    have hjlt := (hlt bY).2.1
    omega
  have hcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b := by
    intro b hb c hc
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hexp : ∀ b ∈ Bs, b ^ 3 = 1 := hBs.2
  exact GGHalf.not_noTransvection_of_shear hcomm hexp hn_norm hzBs hz_ne hna himg hmove


end CFSG.StandardType.UnitSixThreeKG

end
