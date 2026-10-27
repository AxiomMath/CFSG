module

public import CFSG.Milestones.ASVolI.F45.Engine
public import CFSG.Milestones.ASVolI.F4Polygon
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgBase
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitRadical
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Radicals

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.PgGeom

variable {K : Type} [Field K]

@[expose] def burnsideF45_V1 (K : Type) [Field K] : Subgroup (LinearFlag.projectiveSL 3 K) :=
  (LinearFlag.elationSubgroup (LinearFlag.flagSpace 3 K 1)).map (LinearFlag.proj 3 K)

@[expose] def burnsideF45_V2 (K : Type) [Field K] : Subgroup (LinearFlag.projectiveSL 3 K) :=
  (LinearFlag.elationSubgroup (LinearFlag.flagSpace 3 K 2)).map (LinearFlag.proj 3 K)

theorem burnsideF45_mulVec_single (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (A *ᵥ Pi.single j 1) i = A i j := by
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

theorem burnsideF45_single_mem_flag_one :
    (Pi.single 0 1 : Fin 3 → K) ∈ LinearFlag.flagSpace 3 K 1 := by
  rw [LinearFlag.mem_flagSpace]
  intro j hj
  have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
  simp [Pi.single_apply, hj0]

theorem burnsideF45_single_mem_flag_two {i : Fin 3} (hi : (i : ℕ) < 2) :
    (Pi.single i 1 : Fin 3 → K) ∈ LinearFlag.flagSpace 3 K 2 := by
  rw [LinearFlag.mem_flagSpace]
  intro j hj
  have hji : j ≠ i := fun h => by subst h; omega
  simp [Pi.single_apply, hji]

theorem burnsideF45_eq_q1_of_entries {A : SpecialLinearGroup (Fin 3) K}
    (h00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) (h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 = 1)
    (h12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    A = xMat ((A : Matrix (Fin 3) (Fin 3) K) 0 1) * wMat ((A : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  apply Subtype.ext
  show (A : Matrix (Fin 3) (Fin 3) K) =
    xM ((A : Matrix (Fin 3) (Fin 3) K) 0 1) * wM ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, h11, h12, h21, h22]

theorem burnsideF45_eq_q2_of_entries {A : SpecialLinearGroup (Fin 3) K}
    (h00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) (h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 = 1)
    (h20 : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    A = yMat ((A : Matrix (Fin 3) (Fin 3) K) 1 2) * wMat ((A : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  apply Subtype.ext
  show (A : Matrix (Fin 3) (Fin 3) K) =
    yM ((A : Matrix (Fin 3) (Fin 3) K) 1 2) * wM ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, wM, Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22]

theorem burnsideF45_mem_elation_one {A : SpecialLinearGroup (Fin 3) K} :
    A ∈ LinearFlag.elationSubgroup (LinearFlag.flagSpace 3 K 1) ↔
      ∃ a c : K, A = xMat a * wMat c := by
  constructor
  · intro hA
    obtain ⟨h1, h2⟩ := CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_iff.mp
      (CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_of_mem hA)
    have c0 := h2 _ burnsideF45_single_mem_flag_one
    have c1 := LinearFlag.mem_flagSpace.mp (h1 (Pi.single 1 1))
    have c2 := LinearFlag.mem_flagSpace.mp (h1 (Pi.single 2 1))
    have e00 := congrFun c0 0
    have e10 := congrFun c0 1
    have e20 := congrFun c0 2
    have e11 := c1 1 le_rfl
    have e21 := c1 2 (by decide)
    have e12 := c2 1 le_rfl
    have e22 := c2 2 (by decide)
    simp only [burnsideF45_mulVec_single, Pi.sub_apply] at e00 e10 e20 e11 e21 e12 e22
    simp [Pi.single_apply] at e00 e10 e20 e11 e21 e12 e22
    exact ⟨_, _, burnsideF45_eq_q1_of_entries e00 e10 e20 (sub_eq_zero.mp e11) e12 e21
      (sub_eq_zero.mp e22)⟩
  · rintro ⟨a, c, rfl⟩
    refine LinearFlag.mem_elationSubgroup_of_mem
      (CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_iff.mpr ⟨fun v => ?_, fun v hv => ?_⟩)
    · rw [mulVec_q1, LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j
      · exact absurd hj (by decide)
      · simp
      · simp
    · rw [LinearFlag.mem_flagSpace] at hv
      have h1 := hv 1 le_rfl
      have h2 := hv 2 (by decide)
      rw [mulVec_q1]
      ext i
      fin_cases i <;> simp [h1, h2]

theorem burnsideF45_mem_elation_two {A : SpecialLinearGroup (Fin 3) K} :
    A ∈ LinearFlag.elationSubgroup (LinearFlag.flagSpace 3 K 2) ↔
      ∃ b c : K, A = yMat b * wMat c := by
  constructor
  · intro hA
    obtain ⟨h1, h2⟩ := CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_iff.mp
      (CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_of_mem hA)
    have c0 := h2 _ (burnsideF45_single_mem_flag_two (i := 0) (by decide))
    have c1 := h2 _ (burnsideF45_single_mem_flag_two (i := 1) (by decide))
    have c2 := LinearFlag.mem_flagSpace.mp (h1 (Pi.single 2 1))
    have e00 := congrFun c0 0
    have e10 := congrFun c0 1
    have e20 := congrFun c0 2
    have e01 := congrFun c1 0
    have e11 := congrFun c1 1
    have e21 := congrFun c1 2
    have e22 := c2 2 le_rfl
    simp only [burnsideF45_mulVec_single, Pi.sub_apply] at e00 e10 e20 e01 e11 e21 e22
    simp [Pi.single_apply] at e00 e10 e20 e01 e11 e21 e22
    exact ⟨_, _, burnsideF45_eq_q2_of_entries e00 e01 e10 e11 e20 e21 (sub_eq_zero.mp e22)⟩
  · rintro ⟨b, c, rfl⟩
    refine LinearFlag.mem_elationSubgroup_of_mem
      (CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_iff.mpr ⟨fun v => ?_, fun v hv => ?_⟩)
    · rw [mulVec_q2, LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · simp
    · rw [LinearFlag.mem_flagSpace] at hv
      have h2 := hv 2 le_rfl
      rw [mulVec_q2]
      ext i
      fin_cases i <;> simp [h2]

theorem burnsideF45_mem_V1 {g : LinearFlag.projectiveSL 3 K} :
    g ∈ burnsideF45_V1 K ↔ ∃ a c : K, g = xP a * wP c := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨a, c, rfl⟩ := burnsideF45_mem_elation_one.mp hA
    exact ⟨a, c, map_mul _ _ _⟩
  · rintro ⟨a, c, rfl⟩
    exact ⟨xMat a * wMat c, burnsideF45_mem_elation_one.mpr ⟨a, c, rfl⟩, map_mul _ _ _⟩

theorem burnsideF45_mem_V2 {g : LinearFlag.projectiveSL 3 K} :
    g ∈ burnsideF45_V2 K ↔ ∃ b c : K, g = yP b * wP c := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨b, c, rfl⟩ := burnsideF45_mem_elation_two.mp hA
    exact ⟨b, c, map_mul _ _ _⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨yMat b * wMat c, burnsideF45_mem_elation_two.mpr ⟨b, c, rfl⟩, map_mul _ _ _⟩

@[expose] def burnsideF45_sMat (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def burnsideF45_sMat' (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def burnsideF45_tMat (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def burnsideF45_tMat' (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem burnsideF45_sMat_inv : (burnsideF45_sMat K)⁻¹ = burnsideF45_sMat' K := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show !![(1 : K), 0, 0; 0, 0, 1; 0, -1, 0] * !![1, 0, 0; 0, 0, -1; 0, 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideF45_tMat_inv : (burnsideF45_tMat K)⁻¹ = burnsideF45_tMat' K := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show !![(0 : K), 1, 0; -1, 0, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideF45_sMat_mem :
    burnsideF45_sMat K ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1) := by
  refine LinearFlag.mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, LinearFlag.mem_flagSpace] at hv
  rw [Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace]
  have h1 := hv 1 le_rfl
  have h2 := hv 2 (by decide)
  intro j hj
  show (!![(1 : K), 0, 0; 0, 0, 1; 0, -1, 0] *ᵥ v) j = 0
  fin_cases j
  · exact absurd hj (by decide)
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1]

theorem burnsideF45_tMat_mem :
    burnsideF45_tMat K ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2) := by
  refine LinearFlag.mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, LinearFlag.mem_flagSpace] at hv
  rw [Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace]
  have h2 := hv 2 le_rfl
  intro j hj
  show (!![(0 : K), 1, 0; -1, 0, 0; 0, 0, 1] *ᵥ v) j = 0
  fin_cases j
  · exact absurd hj (by decide)
  · exact absurd hj (by decide)
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]

theorem burnsideF45_mem_V1_of_conj {x : LinearFlag.projectiveSL 3 K}
    (hx : x ∈ LinearFlag.projUnitriangular 3 K)
    (hsx : LinearFlag.proj 3 K (burnsideF45_sMat K) * x *
      (LinearFlag.proj 3 K (burnsideF45_sMat K))⁻¹ ∈ LinearFlag.projUnitriangular 3 K) :
    x ∈ burnsideF45_V1 K := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨hl, hd⟩ := LinearFlag.mem_unitriangular.mp hA
  rw [← map_inv, ← map_mul, ← map_mul, burnsideF45_sMat_inv] at hsx
  obtain ⟨B, hB, hBeq⟩ := hsx
  obtain ⟨hlB, hdB⟩ := LinearFlag.mem_unitriangular.mp hB
  obtain ⟨c, -, hc⟩ := CFSG.QuasithinUnique.Fin257.L3.exists_smul_of_proj_eq hBeq
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h21 := hl 2 1 (by decide)
  have k00 := hdB 0
  have k21 := hlB 2 1 (by decide)
  have e00 := congrFun (congrFun hc 0) 0
  have e21 := congrFun (congrFun hc 2) 1
  have hm : ((burnsideF45_sMat K * A * burnsideF45_sMat' K : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![(1 : K), 0, 0; 0, 0, 1; 0, -1, 0] *
        (A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 0, -1; 0, 1, 0] := rfl
  rw [hm] at e00 e21
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e00 e21
  simp [h00, h10, h20, h11, h21, h22, k00, k21] at e00 e21
  subst e00
  have h12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by simpa using e21
  exact ⟨A, burnsideF45_mem_elation_one.mpr ⟨_, _, burnsideF45_eq_q1_of_entries h00 h10 h20 h11
    h12 h21 h22⟩, rfl⟩

theorem burnsideF45_mem_V2_of_conj {x : LinearFlag.projectiveSL 3 K}
    (hx : x ∈ LinearFlag.projUnitriangular 3 K)
    (htx : LinearFlag.proj 3 K (burnsideF45_tMat K) * x *
      (LinearFlag.proj 3 K (burnsideF45_tMat K))⁻¹ ∈ LinearFlag.projUnitriangular 3 K) :
    x ∈ burnsideF45_V2 K := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨hl, hd⟩ := LinearFlag.mem_unitriangular.mp hA
  rw [← map_inv, ← map_mul, ← map_mul, burnsideF45_tMat_inv] at htx
  obtain ⟨B, hB, hBeq⟩ := htx
  obtain ⟨hlB, hdB⟩ := LinearFlag.mem_unitriangular.mp hB
  obtain ⟨c, -, hc⟩ := CFSG.QuasithinUnique.Fin257.L3.exists_smul_of_proj_eq hBeq
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h21 := hl 2 1 (by decide)
  have k00 := hdB 0
  have k10 := hlB 1 0 (by decide)
  have e00 := congrFun (congrFun hc 0) 0
  have e10 := congrFun (congrFun hc 1) 0
  have hm : ((burnsideF45_tMat K * A * burnsideF45_tMat' K : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![(0 : K), 1, 0; -1, 0, 0; 0, 0, 1] *
        (A : Matrix (Fin 3) (Fin 3) K) * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := rfl
  rw [hm] at e00 e10
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e00 e10
  simp [h00, h10, h20, h11, h21, h22, k00, k10] at e00 e10
  subst e00
  have h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by simpa using e10
  exact ⟨A, burnsideF45_mem_elation_two.mpr ⟨_, _, burnsideF45_eq_q2_of_entries h00 h01 h10 h11
    h20 h21 h22⟩, rfl⟩

end Radicals

section Cores

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem burnsideF45_pCoreOf_le_projUnitriangular {d : ℕ} :
    pCoreOf p ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 K d)).map (LinearFlag.proj 3 K)) ≤
      LinearFlag.projUnitriangular 3 K := by
  set P := (LinearFlag.stabilizer (LinearFlag.flagSpace 3 K d)).map (LinearFlag.proj 3 K) with hP
  have hQp : IsPGroup p (pCoreOf p P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p P
  have hUP : LinearFlag.projUnitriangular 3 K ≤ P :=
    Subgroup.map_mono ((LinearFlag.unitriangular_le_upperTriangular 3 K).trans
      (LinearFlag.upperTriangular_le_stabilizer_flagSpace d))
  have hPN : P ≤ Subgroup.normalizer (pCoreOf p P : Set (LinearFlag.projectiveSL 3 K)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p P
  obtain ⟨S, hS⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  have hUp : IsPGroup p (LinearFlag.projUnitriangular 3 K) := hS ▸ S.isPGroup'
  have hsup : IsPGroup p (pCoreOf p P ⊔ LinearFlag.projUnitriangular 3 K :
      Subgroup (LinearFlag.projectiveSL 3 K)) :=
    hQp.to_sup_of_normal_left' hUp (hUP.trans hPN)
  have hmax := S.is_maximal' hsup (by rw [hS]; exact le_sup_right)
  rw [hS] at hmax
  exact le_sup_left.trans hmax.le

theorem burnsideF45_V1_le_pCoreOf :
    burnsideF45_V1 K ≤
      pCoreOf p ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1)).map (LinearFlag.proj 3 K)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    (Subgroup.map_mono (CFSG.AGLEmbedding.LinearThreeKit.elationSubgroup_le_stabilizer _))
    ((Subgroup.map_mono
      (CFSG.AGLEmbedding.LinearThreeKit.stabilizer_le_normalizer_elationSubgroup _)).trans
        (Subgroup.le_normalizer_map _))
    ((CFSG.AGLEmbedding.LinearThreeKit.isPGroup_elationSubgroup p _).map _)

theorem burnsideF45_V2_le_pCoreOf :
    burnsideF45_V2 K ≤
      pCoreOf p ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2)).map (LinearFlag.proj 3 K)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    (Subgroup.map_mono (CFSG.AGLEmbedding.LinearThreeKit.elationSubgroup_le_stabilizer _))
    ((Subgroup.map_mono
      (CFSG.AGLEmbedding.LinearThreeKit.stabilizer_le_normalizer_elationSubgroup _)).trans
        (Subgroup.le_normalizer_map _))
    ((CFSG.AGLEmbedding.LinearThreeKit.isPGroup_elationSubgroup p _).map _)

theorem burnsideF45_pCoreOf_stab_one :
    pCoreOf p ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1)).map (LinearFlag.proj 3 K)) =
      burnsideF45_V1 K := by
  refine le_antisymm (fun x hx => ?_) burnsideF45_V1_le_pCoreOf
  have hs : LinearFlag.proj 3 K (burnsideF45_sMat K) ∈
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1)).map (LinearFlag.proj 3 K) :=
    Subgroup.mem_map_of_mem _ burnsideF45_sMat_mem
  have hsx := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _ hs) x).mp hx
  exact burnsideF45_mem_V1_of_conj (burnsideF45_pCoreOf_le_projUnitriangular hx)
    (burnsideF45_pCoreOf_le_projUnitriangular hsx)

theorem burnsideF45_pCoreOf_stab_two :
    pCoreOf p ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2)).map (LinearFlag.proj 3 K)) =
      burnsideF45_V2 K := by
  refine le_antisymm (fun x hx => ?_) burnsideF45_V2_le_pCoreOf
  have ht : LinearFlag.proj 3 K (burnsideF45_tMat K) ∈
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2)).map (LinearFlag.proj 3 K) :=
    Subgroup.mem_map_of_mem _ burnsideF45_tMat_mem
  have htx := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _ ht) x).mp hx
  exact burnsideF45_mem_V2_of_conj (burnsideF45_pCoreOf_le_projUnitriangular hx)
    (burnsideF45_pCoreOf_le_projUnitriangular htx)

end Cores

section ModelBases

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.PgGeom

variable {K : Type} [Field K]

theorem burnsideF45_modelBase_p0 :
    ModelBase (Gr K) 3 (Sum.inl (p0 : Pt K)) (burnsideF45_V1 K) where
  Qfix w hw q hq := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hw
    obtain ⟨a, c, rfl⟩ := burnsideF45_mem_V1.mp hq
    rw [Sum.smul_inr, q1_fix_line hL]
  Qtrans b c hb hc := by
    cases b with
    | inl p => exact absurd hb (ppAxioms.dist_inl_inl_ne_three _ _)
    | inr L =>
      cases c with
      | inl p' => exact absurd hc (ppAxioms.dist_inl_inl_ne_three _ _)
      | inr L' =>
        have h1 : ¬ inc (p0 : Pt K) L := (ppAxioms.dist_inl_inr_eq_three _ _).mp hb
        have h2 : ¬ inc (p0 : Pt K) L' := (ppAxioms.dist_inl_inr_eq_three _ _).mp hc
        obtain ⟨α, γ, h1a, h1b⟩ := exists_opp_gen h1
        obtain ⟨α', γ', h2a, h2b⟩ := exists_opp_gen h2
        refine ⟨xP (α' - α) * wP (γ' - γ), burnsideF45_mem_V1.mpr ⟨_, _, rfl⟩, ?_⟩
        rw [Sum.smul_inr, q1_smul_opp h1a h1b h2a h2b (by ring) (by ring)]
  Qfree b hb q hq hqb := by
    cases b with
    | inl p => exact absurd hb (ppAxioms.dist_inl_inl_ne_three _ _)
    | inr L =>
      obtain ⟨a, c, rfl⟩ := burnsideF45_mem_V1.mp hq
      have hL : ¬ inc (p0 : Pt K) L := (ppAxioms.dist_inl_inr_eq_three _ _).mp hb
      rw [Sum.smul_inr] at hqb
      obtain ⟨rfl, rfl⟩ := q1_fix_opp hL (Sum.inr.inj hqb)
      rw [CFSG.QuasithinUnique.Fin257.L3.xP_zero, CFSG.QuasithinUnique.Fin257.L3.wP_zero, mul_one]
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hb
    obtain ⟨L', rfl, hL'⟩ := incGraph_adj_inl hc
    obtain ⟨M, rfl, hM⟩ := incGraph_adj_inl hb'
    obtain ⟨M', rfl, hM'⟩ := incGraph_adj_inl hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_p0 hL hL' hM hM' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inl, hg1], by rw [Sum.smul_inr, hg2], by rw [Sum.smul_inr, hg3]⟩

theorem burnsideF45_modelBase_l0 :
    ModelBase (Gr K) 3 (Sum.inr (l0 : Ln K)) (burnsideF45_V2 K) where
  Qfix w hw q hq := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hw
    obtain ⟨b, c, rfl⟩ := burnsideF45_mem_V2.mp hq
    rw [Sum.smul_inl, q2_fix_pt hp]
  Qtrans b c hb hc := by
    cases b with
    | inl p =>
      cases c with
      | inl p' =>
        have h1 : ¬ inc p (l0 : Ln K) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hb
        have h2 : ¬ inc p' (l0 : Ln K) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hc
        obtain ⟨a₁, a₂, ha⟩ := exists_opp_pt h1
        obtain ⟨a₁', a₂', ha'⟩ := exists_opp_pt h2
        refine ⟨yP (a₂' - a₂) * wP (a₁' - a₁), burnsideF45_mem_V2.mpr ⟨_, _, rfl⟩, ?_⟩
        rw [Sum.smul_inl, q2_smul_opp ha ha' (by ring) (by ring)]
      | inr L' => exact absurd hc (ppAxioms.dist_inr_inr_ne_three _ _)
    | inr L => exact absurd hb (ppAxioms.dist_inr_inr_ne_three _ _)
  Qfree b hb q hq hqb := by
    cases b with
    | inl p =>
      obtain ⟨b, c, rfl⟩ := burnsideF45_mem_V2.mp hq
      have hp : ¬ inc p (l0 : Ln K) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hb
      rw [Sum.smul_inl] at hqb
      obtain ⟨rfl, rfl⟩ := q2_fix_opp hp (Sum.inl.inj hqb)
      rw [CFSG.QuasithinUnique.Fin257.L3.yP_zero, CFSG.QuasithinUnique.Fin257.L3.wP_zero, mul_one]
    | inr L => exact absurd hb (ppAxioms.dist_inr_inr_ne_three _ _)
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hb
    obtain ⟨p', rfl, hp'⟩ := incGraph_adj_inr hc
    obtain ⟨q, rfl, hq⟩ := incGraph_adj_inr hb'
    obtain ⟨q', rfl, hq'⟩ := incGraph_adj_inr hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_l0 hp hp' hq hq' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inr, hg1], by rw [Sum.smul_inl, hg2], by rw [Sum.smul_inl, hg3]⟩

theorem burnsideF45_stabilizer_inl_p0 :
    MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inl (p0 : Pt K) : Pt K ⊕ Ln K) =
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1)).map (LinearFlag.proj 3 K) := by
  ext y
  rw [MulAction.mem_stabilizer_iff, Sum.smul_inl, Sum.inl.injEq]
  exact smul_p0_iff y

theorem burnsideF45_stabilizer_inr_l0 :
    MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inr (l0 : Ln K) : Pt K ⊕ Ln K) =
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2)).map (LinearFlag.proj 3 K) := by
  ext y
  rw [MulAction.mem_stabilizer_iff, Sum.smul_inr, Sum.inr.injEq]
  exact smul_l0_iff y

end ModelBases

section Marking

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem burnsideF45_mem_stabilizer_one_iff (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 1) ↔
      (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  constructor
  · intro hA
    have hmem : Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K) (Pi.single 0 1) ∈
        (LinearFlag.flagSpace 3 K 1).map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      Submodule.mem_map_of_mem burnsideF45_single_mem_flag_one
    rw [LinearFlag.mem_stabilizer.mp hA, Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace] at hmem
    have e1 := hmem 1 le_rfl
    have e2 := hmem 2 (by decide)
    rw [burnsideF45_mulVec_single] at e1 e2
    exact ⟨e1, e2⟩
  · rintro ⟨h10, h20⟩
    refine LinearFlag.mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearFlag.mem_flagSpace] at hv
    rw [Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace]
    have v1 := hv 1 le_rfl
    have v2 := hv 2 (by decide)
    intro j hj
    fin_cases j
    · exact absurd hj (by decide)
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, v1, v2]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, v1, v2]

theorem burnsideF45_mem_stabilizer_two_iff (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K 2) ↔
      (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  constructor
  · intro hA
    have hmem : ∀ i : Fin 3, (i : ℕ) < 2 →
        Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K) (Pi.single i 1) ∈
          (LinearFlag.flagSpace 3 K 2).map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      fun i hi => Submodule.mem_map_of_mem (burnsideF45_single_mem_flag_two hi)
    have m0 := hmem 0 (by decide)
    have m1 := hmem 1 (by decide)
    rw [LinearFlag.mem_stabilizer.mp hA, Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace] at m0 m1
    have e0 := m0 2 le_rfl
    have e1 := m1 2 le_rfl
    rw [burnsideF45_mulVec_single] at e0 e1
    exact ⟨e0, e1⟩
  · rintro ⟨h20, h21⟩
    refine LinearFlag.mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearFlag.mem_flagSpace] at hv
    rw [Matrix.mulVecLin_apply, LinearFlag.mem_flagSpace]
    have v2 := hv 2 le_rfl
    intro j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, v2]

private theorem burnsideF45_mem_nativeParabolic (q : ℕ) (b : Bool)
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A :
        ↥(nativeGroup .L3 q K)) ∈ nativeParabolic .L3 q K 1 b ↔
      A ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 K (if b then 2 else 1)) := by
  cases b
  · have h : (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A :
          ↥(nativeGroup .L3 q K)) ∈ nativeParabolic .L3 q K 1 false ↔
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : ↥(StatedSL 3 K)) :
          GL (Fin 3) K) ∈ rawStabilizer ((fun v =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) ''
              coordinateSpace (K := K) (flagOne .L3)) := Iff.rfl
    exact (h.trans (burnsideF4f_stab_one _)).trans (burnsideF45_mem_stabilizer_one_iff A).symm
  · have h : (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A :
          ↥(nativeGroup .L3 q K)) ∈ nativeParabolic .L3 q K 1 true ↔
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : ↥(StatedSL 3 K)) :
          GL (Fin 3) K) ∈ rawStabilizer ((fun v =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) ''
              coordinateSpace (K := K) (flagTwo .L3)) := Iff.rfl
    exact (h.trans (burnsideF4f_stab_two _)).trans (burnsideF45_mem_stabilizer_two_iff A).symm

@[expose] noncomputable def burnsideF45_projEquiv (K : Type) [Field K] :
    LinearFlag.projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
  (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 K)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)

private noncomputable def burnsideF45_theta {p f : ℕ} {H : Type} [Group H]
    (marking : Marking .L3 p f H) : LinearFlag.projectiveSL 3 marking.field ≃* H :=
  (burnsideF45_projEquiv marking.field).trans marking.identification

private theorem burnsideF45_theta_proj {p f : ℕ} {H : Type} [Group H] (marking : Marking .L3 p f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF45_theta marking (LinearFlag.proj 3 marking.field A) =
      marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :=
  rfl

private theorem burnsideF45_theta_mem_parabolic {p f : ℕ} {H : Type} [Group H]
    (marking : Marking .L3 p f H) (b : Bool) (y : LinearFlag.projectiveSL 3 marking.field) :
    burnsideF45_theta marking y ∈ marking.parabolic b ↔
      y ∈ (LinearFlag.stabilizer (LinearFlag.flagSpace 3 marking.field (if b then 2 else 1))).map
        (LinearFlag.proj 3 marking.field) := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  unfold Marking.parabolic
  rw [hbasis]
  constructor
  · rintro ⟨g, hg, hgy⟩
    obtain ⟨A, rfl⟩ :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field).surjective g
    refine ⟨A, (burnsideF45_mem_nativeParabolic _ b A).mp hg, ?_⟩
    apply (burnsideF45_theta marking).injective
    rw [burnsideF45_theta_proj]
    exact hgy
  · rintro ⟨A, hA, rfl⟩
    exact ⟨_, (burnsideF45_mem_nativeParabolic _ b A).mpr hA,
      (burnsideF45_theta_proj marking A).symm⟩

end Marking

section Main

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.PgGeom

theorem burnsideF45_facts45L_L3 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.L3.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨chart, -, hpts, hlines⟩ := hyp.lie_amalgam
  obtain ⟨marking, -, h2, h3, -⟩ := burnsideF4f_L3_marking chart
  haveI : Finite marking.field := marking.finiteField
  have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
  haveI : CharP marking.field p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      marking.exponent_pos hK
  have hsub : ∀ (M : Subgroup E) (b : Bool), Gp ⊓ M = (marking.parabolic b).map Gp.subtype →
      ∀ y, ((burnsideF45_theta marking y : ↥Gp) : E) ∈ M ↔
        burnsideF45_theta marking y ∈ marking.parabolic b := by
    intro M b hM y
    constructor
    · intro hy
      have hmem : ((burnsideF45_theta marking y : ↥Gp) : E) ∈ Gp ⊓ M :=
        ⟨(burnsideF45_theta marking y).2, hy⟩
      rw [hM] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      rwa [Subtype.ext hzy] at hz
    · intro hy
      have hmem : ((burnsideF45_theta marking y : ↥Gp) : E) ∈ Gp ⊓ M := by
        rw [hM]
        exact ⟨_, hy, rfl⟩
      exact hmem.2
  refine burnsideF45_facts45L_of_model hyp hp hm (burnsideF45_theta marking)
    (v₁ := Sum.inl (p0 : Pt marking.field)) (v₂ := Sum.inr (l0 : Ln marking.field))
    (fun y => ?_) (fun y => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_)
    (incGraph_adj_inl_inr.mpr inc_p0_l0) isGenPolygon_gr three_p0 three_l0 ?_ ?_
  · rw [hsub M₁ false (hpts.trans h2) y, burnsideF45_theta_mem_parabolic,
      ← MulAction.mem_stabilizer_iff, burnsideF45_stabilizer_inl_p0]
    exact Iff.rfl
  · rw [hsub M₂ true (hlines.trans h3) y, burnsideF45_theta_mem_parabolic,
      ← MulAction.mem_stabilizer_iff, burnsideF45_stabilizer_inr_l0]
    exact Iff.rfl
  · rw [Sum.smul_inl, Sum.smul_inr]
    exact Sum.inl_ne_inr
  · rw [Sum.smul_inl, Sum.smul_inl]
    exact fun h => h
  · rw [Sum.smul_inr, Sum.smul_inr]
    exact fun h => h
  · rw [burnsideF45_stabilizer_inl_p0, burnsideF45_pCoreOf_stab_one]
    exact burnsideF45_modelBase_p0
  · rw [burnsideF45_stabilizer_inr_l0, burnsideF45_pCoreOf_stab_two]
    exact burnsideF45_modelBase_l0

end Main

end CFSG.ASVolI
