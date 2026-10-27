module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.GroupTheory.ConjTransport
public import CFSG.RankThree.PartOne.KF.R6Levi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  unitaryInvolution_involutive)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (torus6 diagU dvec5 b6 coe_b6 suBlock6 gu5_suBlock6 blk6
  perfectResidual_centralizer_b6 permGL permGL_mem_SU permGL_conj_diagU
  apply_eq_zero_of_commute_diagU mem_torus6_iff torus6_pow_eq_one diagU_dvec5_mem_SU
  diagU_pow diagU_one diagU_val IsCentralPQuot map_inSubgroup_perfectResidual)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem mul_diagU_comm {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {v : Fin n → Kˣ} (h : ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) K) i j = 0) :
    g * diagU v = diagU v * g := by
  apply Units.ext
  ext i j
  have h1 : ((g * diagU v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (g : Matrix (Fin n) (Fin n) K) i j * (v j : K) := by
    simp [Units.val_mul, diagU_val, Matrix.mul_diagonal]
  have h2 : ((diagU v * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (v i : K) * (g : Matrix (Fin n) (Fin n) K) i j := by
    simp [Units.val_mul, diagU_val, Matrix.diagonal_mul]
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    exact mul_comm _ _
  · rw [h i j hij, zero_mul, mul_zero]

private theorem unitaryInvolution_cube {ζ : Kˣ} (h3 : ζ ^ 3 = 1) :
    unitaryInvolution K 2 2 (ζ : K) = ζ := by
  rw [unitaryInvolution_apply]
  have h22 : (2 : ℕ) ^ 2 = 4 := rfl
  rw [h22]
  have h3' : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h41 : (4 : ℕ) = 3 + 1 := rfl
  rw [h41, pow_succ, h3', one_mul]

private theorem unitaryInvolution_five {ν : Kˣ} (h5 : ν ^ 5 = 1) :
    unitaryInvolution K 2 2 (ν : K) = (ν⁻¹ : K) ∧
      unitaryInvolution K 2 2 ((ν⁻¹ : Kˣ) : K) = (ν : K) := by
  have hν4 : ν ^ 4 = ν⁻¹ := by
    have hmul : ν ^ 4 * ν = 1 := by
      rw [← pow_succ]
      exact h5
    calc ν ^ 4 = ν ^ 4 * ν * ν⁻¹ := by group
      _ = ν⁻¹ := by rw [hmul, one_mul]
  have hνinv4 : (ν⁻¹ : Kˣ) ^ 4 = ν := by
    have h : (ν⁻¹ : Kˣ) ^ 4 = (ν ^ 4)⁻¹ := by group
    rw [h, hν4, inv_inv]
  have h22 : (2 : ℕ) ^ 2 = 4 := rfl
  constructor
  · rw [unitaryInvolution_apply, h22]
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) hν4
  · rw [unitaryInvolution_apply, h22]
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) hνinv4

omit [Finite K] [CharP K 2] in
private theorem zeta_facts {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    ζ ^ 2 ≠ 1 ∧ ζ ≠ ζ⁻¹ := by
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  refine ⟨h2, ?_⟩
  intro h
  apply h2
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel ζ

private theorem inSubgroup_perfectResidual_centralizer_suQ_eq (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} (hx3 : x ^ 3 = 1) :
    inSubgroup perfectResidual ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
          Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) =
      (inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))).map (suQ 5 hK) := by
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  rw [top_inf_eq, CFSG.GroupTheory.centralizer_zpowers_eq, ← hq.map_centralizer hx3,
    ← map_inSubgroup_perfectResidual (suQ 5 hK)
      (Subgroup.centralizer ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))]


private theorem inSubgroup_perfectResidual_map_conj {G : Type} [Group G] [Finite G]
    {ℓ : Subgroup G} {w : G} :
    inSubgroup perfectResidual (⊤ ⊓ Subgroup.centralizer
        (ℓ.map (MulAut.conj w).toMonoidHom : Set G)) =
      (inSubgroup perfectResidual (⊤ ⊓ Subgroup.centralizer (ℓ : Set G))).map
        (MulAut.conj w).toMonoidHom := by
  have h1 : (⊤ ⊓ Subgroup.centralizer (ℓ : Set G)).map (MulAut.conj w).toMonoidHom =
      ⊤ ⊓ Subgroup.centralizer (ℓ.map (MulAut.conj w).toMonoidHom : Set G) := by
    rw [top_inf_eq, top_inf_eq]
    exact (CFSG.GroupTheory.centralizer_map_conj w ℓ).symm
  rw [← h1]
  exact (map_inSubgroup_perfectResidual (MulAut.conj w).toMonoidHom
    (⊤ ⊓ Subgroup.centralizer (ℓ : Set G))).symm

private theorem exists_diag_five (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c) :
    ∃ (ν : Kˣ) (d : ↥(SU (unitaryInvolution K 2 2) 5)),
      ν ^ 5 = 1 ∧ ν ≠ ν⁻¹ ∧ d ^ 5 = 1 ∧
        (d : GL (Fin 5) K) = diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] ∧
        d ∈ (suBlock6 (unitaryInvolution K 2 2) hσσ).range := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hord : orderOf g = 15 := by
    rw [hg, Nat.card_units, hK]
    norm_num
  let ν : Kˣ := g ^ 3
  have hν5 : ν ^ 5 = 1 := by
    change (g ^ 3) ^ 5 = 1
    have h315 : 3 * 5 = 15 := rfl
    rw [← pow_mul, h315, ← hord, pow_orderOf_eq_one]
  have hν2 : ν ^ 2 ≠ 1 := by
    intro h
    have h6 : g ^ 6 = 1 := by
      have h' : g ^ (3 * 2) = 1 := by
        rw [pow_mul]
        exact h
      simpa using h'
    have hdvd : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    rw [hord] at hdvd
    norm_num at hdvd
  have hνne : ν ≠ ν⁻¹ := by
    intro h
    apply hν2
    rw [pow_two]
    nth_rewrite 2 [h]
    group
  obtain ⟨hσν, hσν'⟩ := unitaryInvolution_five hν5
  set A : SpecialLinearGroup (Fin 2) K := ⟨!![ν, 0; 0, ν⁻¹], by
    rw [Matrix.det_fin_two_of]
    simp⟩ with hA
  let d : ↥(SU (unitaryInvolution K 2 2) 5) := suBlock6 (unitaryInvolution K 2 2) hσσ A
  have hd_mat : CFSG.RankThree.PartOne.KFU.gu5 d =
      blk6 (unitaryInvolution K 2 2) (A : Matrix (Fin 2) (Fin 2) K) := by
    change CFSG.RankThree.PartOne.KFU.gu5
      (suBlock6 (unitaryInvolution K 2 2) hσσ A) = _
    rw [gu5_suBlock6]
  have hd_diag : (d : GL (Fin 5) K) = diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] := by
    apply Units.ext
    change CFSG.RankThree.PartOne.KFU.gu5 d =
      ((diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    rw [hd_mat, hA, diagU_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk6, hσν]
  have hd5 : d ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hd_diag, Subgroup.coe_one, diagU_pow]
    have hv : (![ν, ν⁻¹, 1, ν⁻¹, ν] : Fin 5 → Kˣ) ^ 5 = 1 := by
      funext i
      fin_cases i <;> simp [hν5, inv_pow]
    rw [hv, diagU_one]
  exact ⟨ν, d, hν5, hνne, hd5, hd_diag, ⟨A, rfl⟩⟩

private theorem suQ_ne_one_of_diag (hK : Nat.card K = (2 ^ 2) ^ 2) {ν : Kˣ} (hνne : ν ≠ ν⁻¹)
    {d : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hd : (d : GL (Fin 5) K) = diagU ![ν, ν⁻¹, 1, ν⁻¹, ν]) :
    suQ 5 hK d ≠ 1 := by
  have hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c :=
    unitaryInvolution_involutive (p := 2) (f := 2) hK
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  intro hone
  have hcenter : d ∈ Subgroup.center ↥(SU (unitaryInvolution K 2 2) 5) :=
    hq.central (MonoidHom.mem_ker.mpr hone)
  let A₁ : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by
    rw [Matrix.det_fin_two_of]
    norm_num⟩
  let u : ↥(SU (unitaryInvolution K 2 2) 5) := suBlock6 (unitaryInvolution K 2 2) hσσ A₁
  have hu01 : (((u : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) 0 1 = 1 := by
    change CFSG.RankThree.PartOne.KFU.gu5 u 0 1 = 1
    rw [gu5_suBlock6]
    simp [blk6, A₁]
  have hdu : ((u : GL (Fin 5) K)) * diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] =
      diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] * (u : GL (Fin 5) K) := by
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcenter u)
    simp only [Subgroup.coe_mul] at h
    rw [hd] at h
    exact h
  have h01 := apply_eq_zero_of_commute_diagU hdu (i := 0) (j := 1) (by simpa using hνne)
  rw [hu01] at h01
  exact one_ne_zero h01

private theorem commute_diag_of_mem_torus {ζ : Kˣ}
    (hζσ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (hζne : ζ ≠ ζ⁻¹) {ν : Kˣ}
    {g : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hg : ∀ t ∈ torus6 (unitaryInvolution K 2 2) 3, Commute t g) :
    (g : GL (Fin 5) K) * diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] =
      diagU ![ν, ν⁻¹, 1, ν⁻¹, ν] * (g : GL (Fin 5) K) := by
  have hu_mem : (⟨diagU (dvec5 ζ 1), diagU_dvec5_mem_SU (unitaryInvolution K 2 2) hζσ
      (by simp)⟩ : ↥(SU (unitaryInvolution K 2 2) 5)) ∈
      torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, 1, h3, by norm_num, rfl⟩
  have hv_mem : (⟨diagU (dvec5 1 ζ), diagU_dvec5_mem_SU (unitaryInvolution K 2 2) (by simp)
      hζσ⟩ : ↥(SU (unitaryInvolution K 2 2) 5)) ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨1, ζ, by norm_num, h3, rfl⟩
  have hcu : (g : GL (Fin 5) K) * diagU (dvec5 ζ 1) =
      diagU (dvec5 ζ 1) * (g : GL (Fin 5) K) := by
    have h := congrArg (fun z : ↥(SU (unitaryInvolution K 2 2) 5) => (z : GL (Fin 5) K))
      (hg _ hu_mem).symm
    simpa only [Subgroup.coe_mul] using h
  have hcv : (g : GL (Fin 5) K) * diagU (dvec5 1 ζ) =
      diagU (dvec5 1 ζ) * (g : GL (Fin 5) K) := by
    have h := congrArg (fun z : ↥(SU (unitaryInvolution K 2 2) 5) => (z : GL (Fin 5) K))
      (hg _ hv_mem).symm
    simpa only [Subgroup.coe_mul] using h
  have h1inv : ζ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
  have h1ne : (1 : Kˣ) ≠ ζ := fun h => h1 h.symm
  have h1neinv : (1 : Kˣ) ≠ ζ⁻¹ := fun h => h1inv h.symm
  have hsep : ∀ i j : Fin 5, i ≠ j →
      dvec5 ζ 1 i ≠ dvec5 ζ 1 j ∨ dvec5 1 ζ i ≠ dvec5 1 ζ j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [dvec5, hζne.symm]
  have hdiag : ∀ i j : Fin 5, i ≠ j →
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i j = 0 := by
    intro i j hij
    rcases hsep i j hij with h | h
    · exact apply_eq_zero_of_commute_diagU hcu h
    · exact apply_eq_zero_of_commute_diagU hcv h
  exact mul_diagU_comm hdiag

private theorem exists_perm_conj {ζ ν : Kˣ} {x₃ x₄ d : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    (hd : (d : GL (Fin 5) K) = diagU ![ν, ν⁻¹, 1, ν⁻¹, ν]) :
    ∃ w₀ : ↥(SU (unitaryInvolution K 2 2) 5), w₀ * x₃ * w₀⁻¹ = x₄ ∧ w₀ * d * w₀⁻¹ = d := by
  let τ : Equiv.Perm (Fin 5) := Equiv.swap 1 3
  have hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i) := by decide
  let w₀ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL τ, permGL_mem_SU (unitaryInvolution K 2 2) τ hτ⟩
  have hw0 : ((w₀ : ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) = permGL τ := rfl
  have hwx : w₀ * x₃ * w₀⁻¹ = x₄ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hw0, hx₃, hx₄, permGL_conj_diagU]
    congr 1
    funext i
    fin_cases i <;> simp [τ, dvec5, Equiv.symm_swap, Equiv.swap_apply_def]
  have hwd : w₀ * d * w₀⁻¹ = d := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hw0, hd, permGL_conj_diagU]
    congr 1
    funext i
    fin_cases i <;> simp [τ, Equiv.symm_swap, Equiv.swap_apply_def]
  exact ⟨w₀, hwx, hwd⟩

private theorem suQ_mem_kOf4 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x₃ x₄ w₀ d : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hwx : w₀ * x₃ * w₀⁻¹ = x₄) (hwd : w₀ * d * w₀⁻¹ = d)
    (hmem3 : suQ 5 hK d ∈ F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      (Subgroup.zpowers (suQ 5 hK x₃))) :
    suQ 5 hK d ∈ F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      (Subgroup.zpowers (suQ 5 hK x₄)) := by
  let P : Type := StatedProj (StatedSU 5 (2 ^ 2) K)
  have hmapzp : (Subgroup.zpowers (suQ 5 hK x₃)).map
      (MulAut.conj (suQ 5 hK w₀)).toMonoidHom = Subgroup.zpowers (suQ 5 hK x₄) := by
    rw [CFSG.GroupTheory.map_conj_zpowers]
    have h : suQ 5 hK w₀ * suQ 5 hK x₃ * (suQ 5 hK w₀)⁻¹ = suQ 5 hK x₄ := by
      rw [← map_mul, ← map_inv, ← map_mul, hwx]
    rw [h]
  have hconj := inSubgroup_perfectResidual_map_conj
    (G := P) (ℓ := Subgroup.zpowers (suQ 5 hK x₃)) (w := suQ 5 hK w₀)
  change suQ 5 hK d ∈ inSubgroup perfectResidual ((⊤ : Subgroup P) ⊓
    Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x₄) : Set P))
  rw [← hmapzp, hconj]
  refine Subgroup.mem_map.mpr ⟨suQ 5 hK d, hmem3, ?_⟩
  change MulAut.conj (suQ 5 hK w₀) (suQ 5 hK d) = suQ 5 hK d
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul, hwd]

private theorem mem_centralizer_torus (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζσ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (hζne : ζ ≠ ζ⁻¹) {ν : Kˣ}
    {d : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hd : (d : GL (Fin 5) K) = diagU ![ν, ν⁻¹, 1, ν⁻¹, ν]) :
    Subgroup.zpowers (suQ 5 hK d) ≤ Subgroup.centralizer
      (((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        Subgroup.centralizer (((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK) :
          Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) :
            Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  have hgen : suQ 5 hK d ∈ Subgroup.centralizer
      (((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        Subgroup.centralizer (((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK) :
          Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) :
            Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨g, rfl⟩ := hq.surjective z
    have hcg : ∀ t ∈ torus6 (unitaryInvolution K 2 2) 3, Commute t g := by
      intro t ht
      have htT : suQ 5 hK t ∈ (torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK) :=
        ⟨t, ht, rfl⟩
      have hcomm : Commute (suQ 5 hK t) (suQ 5 hK g) :=
        (Subgroup.mem_centralizer_iff.mp hz.2) (suQ 5 hK t) htT
      exact hq.commute_of_map_commute (torus6_pow_eq_one ht) hcomm
    have hcomm := commute_diag_of_mem_torus (ν := ν) hζσ h1 h3 hζne hcg
    rw [← hd] at hcomm
    exact Commute.map (Subtype.ext hcomm) (suQ 5 hK)
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact Subgroup.zpow_mem _ hgen n

theorem u5_exists_centP (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    {ℓ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))}
    (hℓ : ℓ = zpowers (suQ 5 hK x₃) ∨ ℓ = zpowers (suQ 5 hK x₄)) :
    ∃ D₀ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)), D₀ ≤ F08.KOf8103 ⊤ ℓ ∧
      Nat.card D₀ = 5 ∧
      D₀ ≤ centralizer (((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        centralizer (((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK) :
          Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) :
            Set (StatedProj (StatedSU 5 (2 ^ 2) K))) :
          Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
  classical
  have hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c :=
    unitaryInvolution_involutive (p := 2) (f := 2) hK
  obtain ⟨ν, d, hν5, hνne, hd5, hd_diag, hdrange⟩ := exists_diag_five hK hσσ
  have hζσ : unitaryInvolution K 2 2 (ζ : K) = ζ := unitaryInvolution_cube h3
  obtain ⟨hζ2, hζne⟩ := zeta_facts h1 h3
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hx3cube : x₃ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx₃, Subgroup.coe_one, diagU_pow]
    have hv : dvec5 ζ ζ ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [dvec5, h3, inv_pow]
    rw [hv, diagU_one]
  have hx3eq : x₃ = b6 (unitaryInvolution K 2 2) ζ hζσ := by
    apply Subtype.ext
    rw [hx₃, coe_b6]
  have hdH : d ∈ inSubgroup perfectResidual (Subgroup.centralizer
      ({x₃} : Set ↥(SU (unitaryInvolution K 2 2) 5))) := by
    rw [hx3eq, perfectResidual_centralizer_b6 (unitaryInvolution K 2 2) hσσ hK4 hζσ h1 hζ2]
    exact hdrange
  have hmem3 : suQ 5 hK d ∈ F08.KOf8103
      (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) (Subgroup.zpowers (suQ 5 hK x₃)) := by
    change suQ 5 hK d ∈ inSubgroup perfectResidual
      ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x₃) :
          Set (StatedProj (StatedSU 5 (2 ^ 2) K))))
    rw [inSubgroup_perfectResidual_centralizer_suQ_eq hK hx3cube]
    exact Subgroup.mem_map.mpr ⟨d, hdH, rfl⟩
  obtain ⟨w₀, hwx, hwd⟩ := exists_perm_conj hx₃ hx₄ hd_diag
  have hpow : (suQ 5 hK d) ^ 5 = 1 := by
    rw [← map_pow, hd5, map_one]
  have hne : suQ 5 hK d ≠ 1 := suQ_ne_one_of_diag hK hνne hd_diag
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨Subgroup.zpowers (suQ 5 hK d), ?_, ?_, ?_⟩
  · rcases hℓ with hℓ | hℓ
    · rw [hℓ]
      exact Subgroup.zpowers_le_of_mem hmem3
    · rw [hℓ]
      exact Subgroup.zpowers_le_of_mem (suQ_mem_kOf4 hK hwx hwd hmem3)
  · rw [Nat.card_zpowers, orderOf_eq_prime hpow hne]
  · exact mem_centralizer_torus hK hζσ h1 h3 hζne hd_diag

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
