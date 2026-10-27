module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SBd9

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.Quasithin

section P3

variable {K : Type} [Field K]

@[expose] def corner (c : K) : SpecialLinearGroup (Fin 3) K :=
  SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) c

theorem corner_coe (c : K) :
    (corner c : Matrix (Fin 3) (Fin 3) K) = 1 + single (0 : Fin 3) (2 : Fin 3) c := rfl

theorem corner_zero : corner (0 : K) = 1 :=
  SpecialLinearGroup.transvection_coeff_zero _

theorem corner_add (c d : K) : corner (c + d) = corner c * corner d :=
  SpecialLinearGroup.transvection_add _ c d

theorem corner_mem_unitriangular (c : K) : corner c ∈ unitriangular 3 K :=
  K1.transvection_mem_unitriangular (show (0 : Fin 3) < 2 by decide) c

theorem corner_entry (c : K) : (corner c : Matrix (Fin 3) (Fin 3) K) 0 2 = c := by
  simp [corner_coe]

theorem proj_corner_injective : Function.Injective (fun c : K => proj 3 K (corner c)) := by
  intro c d h
  have h1 := proj_injOn_unitriangular 3 (corner_mem_unitriangular c) (corner_mem_unitriangular d) h
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h1
  simpa [corner_entry] using h2

theorem mul_corner {b : SpecialLinearGroup (Fin 3) K} (hb : b ∈ upperTriangular 3 K)
    (h22 : (b : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0) (c : K) :
    b * corner c = corner ((b : Matrix (Fin 3) (Fin 3) K) 0 0 *
      ((b : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ * c) * b := by
  have h10 : (b : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hb 1 0 (by decide)
  have h20 : (b : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hb 2 0 (by decide)
  have h21 : (b : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hb 2 1 (by decide)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corner_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply, single_apply, h10, h20, h21, mul_assoc]
  field_simp
  ring

@[expose] def torus (a : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1], by simp [det_diagonal, Fin.prod_univ_three]⟩

theorem torus_coe (a : Kˣ) : (torus a : Matrix (Fin 3) (Fin 3) K) =
    diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := rfl

theorem torus_mem_upperTriangular (a : Kˣ) : torus a ∈ upperTriangular 3 K := by
  intro i j hij
  exact diagonal_apply_ne _ (ne_of_gt hij)

theorem torus_mul_corner (a : Kˣ) (c : K) :
    torus a * corner c = corner ((a : K) * c) * torus a := by
  have h := mul_corner (torus_mem_upperTriangular a) (by simp [torus_coe]) c
  simpa [torus_coe] using h

theorem diag_prod_eq_one {b : SpecialLinearGroup (Fin 3) K} (hb : b ∈ upperTriangular 3 K) :
    (b : Matrix (Fin 3) (Fin 3) K) 0 0 * (b : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (b : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  have h1 := b.2
  rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hb)] at h1
  simpa [Fin.prod_univ_three] using h1

theorem diag_ne_zero {b : SpecialLinearGroup (Fin 3) K} (hb : b ∈ upperTriangular 3 K) (i : Fin 3) :
    (b : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
  have h := diag_prod_eq_one hb
  intro h0
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 <;>
    rw [h0] at h <;> simp at h

theorem proj_mem_projUnitriangular_of_diag_eq (hK : Nat.card K = 4)
    {b : SpecialLinearGroup (Fin 3) K} (hb : b ∈ upperTriangular 3 K)
    (h : (b : Matrix (Fin 3) (Fin 3) K) 0 0 = (b : Matrix (Fin 3) (Fin 3) K) 2 2) :
    proj 3 K b ∈ projUnitriangular 3 K := by
  have hdet := diag_prod_eq_one hb
  have ha0 := diag_ne_zero hb 0
  have h22 : (b : Matrix (Fin 3) (Fin 3) K) 2 2 = (b : Matrix (Fin 3) (Fin 3) K) 0 0 := h.symm
  rw [h22] at hdet
  let ua : Kˣ := Units.mk0 ((b : Matrix (Fin 3) (Fin 3) K) 0 0) ha0
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hua : ua ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := ua)
    rwa [hcard] at this
  have ha3 : ((b : Matrix (Fin 3) (Fin 3) K) 0 0) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hua
    simpa [ua] using this
  have hd : (b : Matrix (Fin 3) (Fin 3) K) 1 1 = (b : Matrix (Fin 3) (Fin 3) K) 0 0 := by
    have h1 : (b : Matrix (Fin 3) (Fin 3) K) 0 0 * (b : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (b : Matrix (Fin 3) (Fin 3) K) 0 0 = (b : Matrix (Fin 3) (Fin 3) K) 0 0 *
          (b : Matrix (Fin 3) (Fin 3) K) 0 0 * (b : Matrix (Fin 3) (Fin 3) K) 0 0 := by
      linear_combination hdet - ha3
    exact mul_left_cancel₀ ha0 (mul_right_cancel₀ ha0 h1)
  have hua' : ua⁻¹ ^ 3 = 1 := by rw [inv_pow, hua, inv_one]
  have hs' : scalarElement ua⁻¹ hua' ∈ scalars 3 K := scalarElement_mem_scalars _ _
  have hbs : b * scalarElement ua⁻¹ hua' ∈ unitriangular 3 K := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp [scalar_apply, Matrix.mul_diagonal, hb i j hij]
    · fin_cases i <;> simp [scalar_apply, Matrix.mul_diagonal, ua, ha0, hd, h22]
  have : proj 3 K b = proj 3 K (b * scalarElement ua⁻¹ hua') := by
    rw [map_mul, proj_eq_one_iff.mpr hs', mul_one]
  rw [this]
  exact Subgroup.mem_map_of_mem _ hbs

theorem pow_mul_proj_corner {t : projectiveSL 3 K} {a : K}
    (ht : ∀ c : K, t * proj 3 K (corner c) = proj 3 K (corner (a * c)) * t) (m : ℕ) (c : K) :
    t ^ m * proj 3 K (corner c) = proj 3 K (corner (a ^ m * c)) * t ^ m := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    calc t ^ (m + 1) * proj 3 K (corner c) = t ^ m * (t * proj 3 K (corner c)) := by
          rw [pow_succ, mul_assoc]
      _ = t ^ m * (proj 3 K (corner (a * c)) * t) := by rw [ht]
      _ = (t ^ m * proj 3 K (corner (a * c))) * t := by rw [mul_assoc]
      _ = (proj 3 K (corner (a ^ m * (a * c))) * t ^ m) * t := by rw [ih (a * c)]
      _ = proj 3 K (corner (a ^ (m + 1) * c)) * t ^ (m + 1) := by
          rw [show a ^ (m + 1) * c = a ^ m * (a * c) by ring, mul_assoc, ← pow_succ]

end P3

section Projective

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_corner_of_mem_centralizer {y : projectiveSL 3 K}
    (hy : y ∈ Subgroup.centralizer (projUnitriangular 3 K : Set (projectiveSL 3 K))) :
    ∃ c : K, y = proj 3 K (corner c) := by
  have hyN : y ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) :=
    Subgroup.centralizer_le_normalizer _ hy
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2] at hyN
  obtain ⟨M, hM, rfl⟩ := hyN
  have hMT : ∀ i j : Fin 3, (i : ℕ) + 1 = (j : ℕ) →
      (M : Matrix (Fin 3) (Fin 3) K) * single i j (1 : K) =
        single i j (1 : K) * (M : Matrix (Fin 3) (Fin 3) K) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    have hT := K1.transvection_mem_unitriangular hlt (1 : K)
    have h1 := Subgroup.mem_centralizer_iff.mp hy
      (proj 3 K (SpecialLinearGroup.transvection hlt.ne (1 : K))) (Subgroup.mem_map_of_mem _ hT)
    have h2 : proj 3 K (M * SpecialLinearGroup.transvection hlt.ne (1 : K) * M⁻¹) =
        proj 3 K (SpecialLinearGroup.transvection hlt.ne (1 : K)) := by
      rw [map_mul, map_mul, map_inv, ← h1]
      group
    have h3 := proj_injOn_unitriangular 3 (conj_mem_unitriangular hM hT) hT h2
    have h4 : M * SpecialLinearGroup.transvection hlt.ne (1 : K) =
        SpecialLinearGroup.transvection hlt.ne (1 : K) * M := by
      calc M * SpecialLinearGroup.transvection hlt.ne (1 : K)
          = (M * SpecialLinearGroup.transvection hlt.ne (1 : K) * M⁻¹) * M := by group
        _ = SpecialLinearGroup.transvection hlt.ne (1 : K) * M := by rw [h3]
    have h5 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h4
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      mul_add, add_mul, mul_one, one_mul] at h5
    exact add_left_cancel h5
  obtain ⟨a, b, hab⟩ := K1.eq_smul_one_add_single_of_commute (n := 3) (by norm_num)
    (M : Matrix (Fin 3) (Fin 3) K) hMT
  have hdiag : ∀ i : Fin 3, (M : Matrix (Fin 3) (Fin 3) K) i i = a := by
    intro i
    rw [hab]
    fin_cases i <;> simp
  have hdet : a ^ 3 = 1 := by
    have h := M.2
    rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hM)] at h
    simpa [Fin.prod_univ_three, hdiag, pow_succ, mul_assoc] using h
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hdet
  let u : Kˣ := Units.mk0 a ha
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hdet)
  have hmem : scalarElement u hu3 ∈ scalars 3 K := scalarElement_mem_scalars u hu3
  refine ⟨b / a, ?_⟩
  have hmat : (M : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) (a : K) * (1 + single (0 : Fin 3) (2 : Fin 3) (b / a)) := by
    rw [hab]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, single_apply, scalar_apply]
    field_simp
  have hfac : M = scalarElement u hu3 * corner (b / a) := Subtype.ext hmat
  calc proj 3 K M = proj 3 K (scalarElement u hu3) * proj 3 K (corner (b / a)) := by
        rw [hfac, map_mul]
    _ = proj 3 K (corner (b / a)) := by rw [proj_eq_one_iff.mpr hmem, one_mul]

theorem exists_ne_one_of_mem_normalizer (hK : Nat.card K = 4) {t : projectiveSL 3 K}
    (ht : t ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)))
    (ht' : t ∉ projUnitriangular 3 K) :
    ∃ a : K, a ≠ 1 ∧ ∀ c : K, t * proj 3 K (corner c) = proj 3 K (corner (a * c)) * t := by
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2] at ht
  obtain ⟨b, hb, rfl⟩ := ht
  have h22 := diag_ne_zero hb 2
  refine ⟨(b : Matrix (Fin 3) (Fin 3) K) 0 0 * ((b : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹, ?_,
    fun c => ?_⟩
  · intro h1
    apply ht'
    refine proj_mem_projUnitriangular_of_diag_eq hK hb ?_
    field_simp at h1
    exact h1
  · rw [← map_mul, mul_corner hb h22 c, map_mul]

theorem isSylowTwoOf_projUnitriangular :
    IsSylowTwoOf (projUnitriangular 3 K) (⊤ : Subgroup (projectiveSL 3 K)) := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  exact hS ▸ isSylowTwoOf_top_of_sylow S

theorem projectiveSL_solvable_overgroup_le_normalizer (hK4 : ∃ s : Finset K, s.card = 4) :
    ∀ Ū Y : Subgroup (projectiveSL 3 K), IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (Ū : Set (projectiveSL 3 K)) := by
  intro Ū Y hŪ hUY hY
  refine SzN2.solvable_overgroup_le_normalizer_of_sylow isSylowTwoOf_projUnitriangular
    (fun Y' hY' hs => ?_) hŪ hUY hY
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2]
  have hker : (proj 3 K).ker ≤ Y'.comap (proj 3 K) := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Y'.one_mem
  have hcen : (proj 3 K).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj]
    exact scalars_le_center 3 K
  have hcomm : Group.IsSolvable ↥(proj 3 K).ker :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hcen b.2) a)
  have hsolv : Group.IsSolvable ↥(Y'.comap (proj 3 K)) := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hker)
      (((proj 3 K).comp (Y'.comap (proj 3 K)).subtype).codRestrict Y'
        fun x => Subgroup.mem_comap.mp x.2) ?_
    intro x hx
    refine ⟨⟨x.1, ?_⟩, Subtype.ext rfl⟩
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact MonoidHom.mem_ker.mpr this
  have hU : unitriangular 3 K ≤ Y'.comap (proj 3 K) := fun u hu =>
    hY' (Subgroup.mem_map_of_mem _ hu)
  have hle := SzN2.sl3_le_upperTriangular_of_solvable hK4 hU hsolv
  intro y hy
  obtain ⟨g, rfl⟩ := proj_surjective 3 K y
  exact ⟨g, hle hy, rfl⟩

end Projective

end CFSG.Quasithin.SBd9
