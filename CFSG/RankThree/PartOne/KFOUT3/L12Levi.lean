module

public import CFSG.RankThree.PartOne.KFOUT3.L12Block
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix CFSG CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LocalCores
  CFSG.LieType.Universal.Unitary

variable {f : ℕ} {K : Type} [Field K]

@[expose] def dvecB (t : Kˣ) : Fin 5 → Kˣ := ![t, t, t, 1, t ^ 2]

theorem diagU_dvecB_mem_torus {t : Kˣ} (ht : t ^ 5 = 1) :
    (diagU (dvecB t) : GL (Fin 5) K) ∈ torusSU 5 5 K := by
  have h10 : t ^ 10 = 1 := by rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, ht, one_pow]
  refine mem_torusSU_iff.mpr ⟨dvecB t, fun i => ?_, ?_, rfl⟩
  · fin_cases i <;> simp [dvecB, ← pow_mul, ht, h10]
  · simp [Fin.prod_univ_five, dvecB]
    rw [show t * t * t * t ^ 2 = t ^ 5 by group, ht]

theorem dvecB_pow_five {t : Kˣ} (ht : t ^ 5 = 1) : dvecB t ^ 5 = 1 := by
  have h10 : t ^ 10 = 1 := by rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, ht, one_pow]
  funext i
  fin_cases i <;> simp [dvecB, ← pow_mul, ht, h10]

@[expose] noncomputable def bB (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) : ↥(unitarySU 2 f K 5) :=
  ⟨diagU (dvecB t), torusSU_le_unitarySU hU h5 (diagU_dvecB_mem_torus ht)⟩

theorem bB_pow_five (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) : bB hU h5 ht ^ 5 = 1 := by
  apply Subtype.ext
  show (diagU (dvecB t) : GL (Fin 5) K) ^ 5 = 1
  rw [diagU_pow, dvecB_pow_five ht, diagU_one]

abbrev gU (g : ↥(unitarySU 2 f K 5)) : Matrix (Fin 5) (Fin 5) K :=
  ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem commute_diagU_apply' {n : ℕ} {d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU d = diagU d * g) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) i j * (d j : K) =
      (d i : K) * (g : Matrix (Fin n) (Fin n) K) i j := by
  have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j) hg
  simpa [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] using this

theorem apply_eq_zero_of_commute_diagU' {n : ℕ} {d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU d = diagU d * g) {i j : Fin n} (hij : d i ≠ d j) :
    (g : Matrix (Fin n) (Fin n) K) i j = 0 := by
  have h1 := commute_diagU_apply' hg i j
  have h2 : (g : Matrix (Fin n) (Fin n) K) i j * ((d j : K) - (d i : K)) = 0 := by
    rw [mul_sub, h1]
    ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hij

theorem sq_ne_one_of_pow_five {t : Kˣ} (ht : t ^ 5 = 1) (h1 : t ≠ 1) : t ^ 2 ≠ 1 := by
  intro h2
  apply h1
  calc t = t ^ 5 * (t ^ 2) ⁻¹ ^ 2 := by group
    _ = 1 := by rw [ht, h2]; simp

theorem pow_three_ne_one_of_pow_five {t : Kˣ} (ht : t ^ 5 = 1) (h1 : t ≠ 1) : t ^ 3 ≠ 1 := by
  intro h3
  have h2 : t ^ 2 = 1 := by
    calc t ^ 2 = t ^ 5 * (t ^ 3)⁻¹ := by group
      _ = 1 := by rw [ht, h3]; simp
  apply h1
  calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem centralizer_bB_facts (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (h1 : t ≠ 1) {g : ↥(unitarySU 2 f K 5)}
    (hg : g ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) :
    ∃ (X : Matrix (Fin 3) (Fin 3) K) (u v : K), gU g = blkB X u v ∧ gU g 3 3 = u ∧
      gU g 4 4 = v ∧ (X.map hU.bar)ᵀ * X = 1 ∧ hU.bar u * u = 1 ∧ hU.bar v * v = 1 ∧
      X.det * u * v = 1 := by
  have h2 := sq_ne_one_of_pow_five ht h1
  have hcomm : (g : GL (Fin 5) K) * diagU (dvecB t) = diagU (dvecB t) * (g : GL (Fin 5) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hA : t ≠ 1 := h1
  have hB : t ≠ t ^ 2 := by
    intro h
    apply h1
    have : t * t = t * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel this
  have hC : (1 : Kˣ) ≠ t ^ 2 := fun h => h2 h.symm
  have hne : ∀ i j : Fin 5, dvecB t i ≠ dvecB t j →
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i j = 0 := fun i j h =>
    apply_eq_zero_of_commute_diagU' hcomm h
  have e03 := hne 0 3 (by simpa [dvecB] using hA)
  have e04 := hne 0 4 (by simpa [dvecB] using hB)
  have e13 := hne 1 3 (by simpa [dvecB] using hA)
  have e14 := hne 1 4 (by simpa [dvecB] using hB)
  have e23 := hne 2 3 (by simpa [dvecB] using hA)
  have e24 := hne 2 4 (by simpa [dvecB] using hB)
  have e30 := hne 3 0 (by simpa [dvecB] using hA.symm)
  have e31 := hne 3 1 (by simpa [dvecB] using hA.symm)
  have e32 := hne 3 2 (by simpa [dvecB] using hA.symm)
  have e34 := hne 3 4 (by simpa [dvecB] using hC)
  have e40 := hne 4 0 (by simpa [dvecB] using hB.symm)
  have e41 := hne 4 1 (by simpa [dvecB] using hB.symm)
  have e42 := hne 4 2 (by simpa [dvecB] using hB.symm)
  have e43 := hne 4 3 (by simpa [dvecB] using hC.symm)
  have hblk := eq_blkB_of_zero _ e03 e04 e13 e14 e23 e24 e30 e31 e32 e34 e40 e41 e42 e43
  obtain ⟨X, u, v, hXuv⟩ : ∃ (X : Matrix (Fin 3) (Fin 3) K) (u v : K),
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = blkB X u v := ⟨_, _, _, hblk⟩
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff hU).mp g.2
  rw [hXuv] at hdet hgram
  rw [blkB_map, blkB_transpose, blkB_mul, ← blkB_one] at hgram
  obtain ⟨hX, hu, hv⟩ := blkB_injective hgram
  rw [det_blkB] at hdet
  exact ⟨X, u, v, hXuv, by simpa [blkB] using congrFun (congrFun hXuv 3) 3,
    by simpa [blkB] using congrFun (congrFun hXuv 4) 4, hX, hu, hv, hdet⟩

@[expose] noncomputable def blk12GL : GL (Fin 3) K →* GL (Fin 5) K where
  toFun A :=
    { val := blkB (A : Matrix (Fin 3) (Fin 3) K) 1 1
      inv := blkB ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1
      val_inv := by
        rw [blkB_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, blkB_one]
      inv_val := by
        rw [blkB_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, blkB_one] }
  map_one' := by
    apply Units.ext
    simp [blkB_one]
  map_mul' A B := by
    apply Units.ext
    simp [blkB_mul]

theorem coe_blk12GL (A : GL (Fin 3) K) :
    ((blk12GL A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blkB (A : Matrix (Fin 3) (Fin 3) K) 1 1 := rfl

@[expose] noncomputable def suBlock12 (hU : UnitaryFieldData 2 f K) :
    ↥(unitarySU 2 f K 3) →* ↥(unitarySU 2 f K 5) :=
  (blk12GL.comp (unitarySU 2 f K 3).subtype).codRestrict (unitarySU 2 f K 5) (fun A => by
    obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff hU).mp A.2
    refine (mem_unitarySU_iff hU).mpr ⟨?_, ?_⟩
    · show ((blk12GL (A : GL (Fin 3) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1
      rw [coe_blk12GL, det_blkB, hdet, one_mul, one_mul]
    · show (((blk12GL (A : GL (Fin 3) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map
        hU.bar)ᵀ * ((blk12GL (A : GL (Fin 3) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1
      rw [coe_blk12GL, blkB_map, blkB_transpose, blkB_mul, hgram, map_one, one_mul,
        ← blkB_one])

theorem coe_suBlock12 (hU : UnitaryFieldData 2 f K) (A : ↥(unitarySU 2 f K 3)) :
    (((suBlock12 hU A : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blkB ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := rfl

theorem suBlock12_injective (hU : UnitaryFieldData 2 f K) : Function.Injective (suBlock12 hU) := by
  intro A B h
  have h1 := congrArg (fun g : ↥(unitarySU 2 f K 5) =>
    ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h
  simp only [coe_suBlock12] at h1
  exact Subtype.ext (Units.ext (blkB_injective h1).1)

theorem coe_bB (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ} (ht : t ^ 5 = 1) :
    (((bB hU h5 ht : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blkB ((t : K) • (1 : Matrix (Fin 3) (Fin 3) K)) 1 ((t : K) ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bB, blkB, diagU_val, dvecB]

theorem suBlock12_mem_centralizer (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (A : ↥(unitarySU 2 f K 3)) :
    suBlock12 hU A ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlock12, coe_bB, blkB_mul]
  congr 1
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · rw [one_mul, mul_one]

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ} (ht : t ^ 5 = 1)
  (h1 : t ≠ 1)

include hU h5 h1 in
theorem gU_ne_zero_three {g : ↥(unitarySU 2 f K 5)}
    (hg : g ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) :
    gU g 3 3 ≠ 0 := by
  obtain ⟨X, u, v, hXuv, h3, h4, -, hu, -, -⟩ := centralizer_bB_facts hU h5 ht h1 hg
  rw [h3]
  intro h0
  rw [h0, map_zero, zero_mul] at hu
  exact zero_ne_one hu

include hU h5 h1 in
theorem gU_ne_zero_four {g : ↥(unitarySU 2 f K 5)}
    (hg : g ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) :
    gU g 4 4 ≠ 0 := by
  obtain ⟨X, u, v, hXuv, h3, h4, -, -, hv, -⟩ := centralizer_bB_facts hU h5 ht h1 hg
  rw [h4]
  intro h0
  rw [h0, map_zero, zero_mul] at hv
  exact zero_ne_one hv

include hU h5 h1 in
theorem gU_mul_entries {g k : ↥(unitarySU 2 f K 5)}
    (hg : g ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5)))
    (hk : k ∈ Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) :
    gU (g * k) 3 3 = gU g 3 3 * gU k 3 3 ∧ gU (g * k) 4 4 = gU g 4 4 * gU k 4 4 := by
  obtain ⟨X, u, v, hXuv, hg3, hg4, -⟩ := centralizer_bB_facts hU h5 ht h1 hg
  obtain ⟨Y, u', v', hYuv, hk3, hk4, -⟩ := centralizer_bB_facts hU h5 ht h1 hk
  have hmul : gU (g * k) = blkB (X * Y) (u * u') (v * v') := by
    show gU g * gU k = _
    rw [hXuv, hYuv, blkB_mul]
  refine ⟨?_, ?_⟩
  · rw [hg3, hk3]
    simpa [blkB] using congrFun (congrFun hmul 3) 3
  · rw [hg4, hk4]
    simpa [blkB] using congrFun (congrFun hmul 4) 4

@[expose] noncomputable def phi12 :
    ↥(Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) →* Kˣ × Kˣ where
  toFun g := (Units.mk0 (gU (g : ↥(unitarySU 2 f K 5)) 3 3) (gU_ne_zero_three hU h5 ht h1 g.2),
    Units.mk0 (gU (g : ↥(unitarySU 2 f K 5)) 4 4) (gU_ne_zero_four hU h5 ht h1 g.2))
  map_one' := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_) <;> simp [gU]
  map_mul' g k := by
    obtain ⟨e3, e4⟩ := gU_mul_entries hU h5 ht h1 g.2 k.2
    exact Prod.ext (Units.ext e3) (Units.ext e4)

theorem phi12_fst (g : ↥(Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5)))) :
    (((phi12 hU h5 ht h1 g).1 : Kˣ) : K) = gU (g : ↥(unitarySU 2 f K 5)) 3 3 := rfl

theorem phi12_snd (g : ↥(Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5)))) :
    (((phi12 hU h5 ht h1 g).2 : Kˣ) : K) = gU (g : ↥(unitarySU 2 f K 5)) 4 4 := rfl

theorem ker_phi12 :
    (phi12 hU h5 ht h1).ker =
      (suBlock12 hU).range.subgroupOf
        (Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h3 : gU (g : ↥(unitarySU 2 f K 5)) 3 3 = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.1 : Kˣ) : K)) h
      rw [phi12_fst] at this
      simpa using this
    have h4 : gU (g : ↥(unitarySU 2 f K 5)) 4 4 = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.2 : Kˣ) : K)) h
      rw [phi12_snd] at this
      simpa using this
    obtain ⟨X, u, v, hXuv, hg3, hg4, hX, hu, hv, hdet⟩ := centralizer_bB_facts hU h5 ht h1 g.2
    have hu1 : u = 1 := by rw [← hg3]; exact h3
    have hv1 : v = 1 := by rw [← hg4]; exact h4
    rw [hu1, hv1, mul_one, mul_one] at hdet
    have hXX : X * (X.map hU.bar)ᵀ = 1 := mul_eq_one_comm.mp hX
    let Xu : GL (Fin 3) K := Units.mk X ((X.map hU.bar)ᵀ) hXX hX
    have hXU : Xu ∈ unitarySU 2 f K 3 := (mem_unitarySU_iff hU).mpr ⟨hdet, hX⟩
    refine ⟨⟨Xu, hXU⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_suBlock12]
    show blkB X 1 1 = _
    rw [hu1, hv1] at hXuv
    exact hXuv.symm
  · rintro ⟨A, hA⟩
    have hA' : gU (g : ↥(unitarySU 2 f K 5)) = blkB ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        1 1 := by
      rw [← hA]
      rfl
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [phi12_fst, hA']
      simp [blkB]
    · rw [phi12_snd, hA']
      simp [blkB]

theorem two_le_of_dvd_five (h5 : 5 ∣ 2 ^ f + 1) : 2 ≤ f := by
  by_contra h
  have : f = 0 ∨ f = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h5

include hU in
theorem isQuasisimple_unitarySU_three (hf2 : 2 ≤ f) : IsQuasisimple ↥(unitarySU 2 f K 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.finite
  refine (isQuasisimple_statedSU_of_card (p := 2) (f := f)
    (by rw [hU.card, ← pow_mul, mul_comm]) le_rfl ?_).1
  intro h
  have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

include hU h5 h1 in
theorem perfectResidual_centralizer_bB :
    inSubgroup perfectResidual
        (Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))) =
      (suBlock12 hU).range := by
  have := hU.finite
  have hq := isQuasisimple_unitarySU_three hU (two_le_of_dvd_five h5)
  have hperf : Group.IsPerfect ↥((suBlock12 hU).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (suBlock12_injective hU)).toMonoidHom)
      (MonoidHom.ofInjective (suBlock12_injective hU)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact suBlock12_mem_centralizer hU h5 ht A) hperf (phi12 hU h5 ht h1)
    (ker_phi12 hU h5 ht h1)

include hU h5 h1 in
theorem isQuasisimple_perfectResidual_centralizer_bB :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5)))) := by
  rw [perfectResidual_centralizer_bB hU h5 ht h1]
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (suBlock12_injective hU))
    (isQuasisimple_unitarySU_three hU (two_le_of_dvd_five h5))

include hU in
theorem card_center_unitarySU_three (hf2 : 2 ≤ f) :
    Nat.card (Subgroup.center ↥(unitarySU 2 f K 3)) = Nat.gcd 3 (2 ^ f + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.finite
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  rw [(isQuasisimple_statedSU_of_card hF (n := 3) le_rfl hnq).2]
  exact (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3) (by norm_num)).2.2

include hU h5 in
theorem not_dvd_card_center_range_suBlock12 :
    ¬ 5 ∣ Nat.card (Subgroup.center ↥((suBlock12 hU).range)) := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (suBlock12_injective hU)),
    card_center_unitarySU_three hU (two_le_of_dvd_five h5)]
  intro h
  have := h.trans (Nat.gcd_dvd_left 3 _)
  omega

end CFSG.RankThree.PartOne.KFOUT3
