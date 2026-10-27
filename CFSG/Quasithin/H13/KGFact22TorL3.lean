module

public import CFSG.Quasithin.H13.KGFact22Tor
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.KG22

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique

variable {K : Type} [Field K]

local notation "SL₃" => SpecialLinearGroup (Fin 3) K

@[expose] def diag3 (x y z : K) (h : x * y * z = 1) : SL₃ :=
  ⟨Matrix.diagonal ![x, y, z], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h⟩

theorem coe_diag3 (x y z : K) (h : x * y * z = 1) :
    (diag3 x y z h : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![x, y, z] :=
  rfl

theorem diag3_mul (x y z : K) (h : x * y * z = 1) (x' y' z' : K) (h' : x' * y' * z' = 1) :
    diag3 x y z h * diag3 x' y' z' h' = diag3 (x * x') (y * y') (z * z') (by
      calc x * x' * (y * y') * (z * z') = (x * y * z) * (x' * y' * z') := by ring
        _ = 1 := by rw [h, h', one_mul]) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, coe_diag3, coe_diag3, diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

theorem diag3_eq_one (h : (1 : K) * 1 * 1 = 1) : diag3 (1 : K) 1 1 h = 1 := by
  ext i j
  rw [coe_diag3, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem diag3_congr {x y z x' y' z' : K} (h : x * y * z = 1) (hx : x = x') (hy : y = y')
    (hz : z = z') : diag3 x y z h = diag3 x' y' z' (hx ▸ hy ▸ hz ▸ h) := by
  subst hx hy hz
  rfl

theorem diag3_mem_upperTriangular (x y z : K) (h : x * y * z = 1) :
    diag3 x y z h ∈ upperTriangular 3 K := fun i j hij => by
  rw [coe_diag3, diagonal_apply_ne _ (ne_of_gt hij)]

@[expose] noncomputable def tY : Kˣ →* SL₃ where
  toFun a := diag3 (a : K) 1 ((a⁻¹ : Kˣ) : K) (by simp)
  map_one' := by
    rw [← diag3_eq_one (K := K) (by simp)]
    apply diag3_congr <;> simp
  map_mul' a b := by
    rw [diag3_mul]
    apply diag3_congr <;> simp [mul_comm]

@[expose] noncomputable def tY' : Kˣ →* SL₃ where
  toFun b := diag3 (b : K) (((b⁻¹ : Kˣ) : K) ^ 2) (b : K) (by
    rw [Units.val_inv_eq_inv_val]
    field_simp)
  map_one' := by
    rw [← diag3_eq_one (K := K) (by simp)]
    apply diag3_congr <;> simp
  map_mul' a b := by
    rw [diag3_mul]
    apply diag3_congr <;> simp [mul_comm, mul_pow]

theorem tY_apply (a : Kˣ) : tY a = diag3 (a : K) 1 ((a⁻¹ : Kˣ) : K) (by simp) :=
  rfl

theorem tY'_apply (b : Kˣ) : tY' b = diag3 (b : K) (((b⁻¹ : Kˣ) : K) ^ 2) (b : K) (by
    rw [Units.val_inv_eq_inv_val]
    field_simp) :=
  rfl

theorem coe_tY (a : Kˣ) :
    ((tY a : SL₃) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(a : K), 1, ((a⁻¹ : Kˣ) : K)] :=
  rfl

theorem coe_tY' (b : Kˣ) :
    ((tY' b : SL₃) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(b : K), ((b⁻¹ : Kˣ) : K) ^ 2, (b : K)] :=
  rfl

theorem tY_mem_upperTriangular (a : Kˣ) : tY a ∈ upperTriangular 3 K := by
  rw [tY_apply]
  exact diag3_mem_upperTriangular _ _ _ _

theorem tY'_mem_upperTriangular (b : Kˣ) : tY' b ∈ upperTriangular 3 K := by
  rw [tY'_apply]
  exact diag3_mem_upperTriangular _ _ _ _

theorem tY_proj_eq_one {y : SL₃} (hy : y ∈ tY.range) (h : proj 3 K y = 1) : y = 1 := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 h
  have h11 := congrFun (congrFun hc 1) 1
  have h00 := congrFun (congrFun hc 0) 0
  rw [coe_tY] at h11 h00
  simp only [diagonal_apply_eq, scalar_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h11 h00
  have hc1 : (c : K) = 1 := h11.symm
  have ha1 : a = 1 := Units.ext (by rw [h00, hc1, Units.val_one])
  rw [ha1, map_one]

theorem tY_injective : Function.Injective (tY : Kˣ →* SL₃) := by
  intro a b h
  have := congrFun (congrFun (congrArg (fun g : SL₃ => (g : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  rw [coe_tY, coe_tY] at this
  simp only [diagonal_apply_eq, Matrix.cons_val_zero] at this
  exact Units.ext this

theorem diag_comm (a b : Kˣ) : tY a * tY' b = tY' b * tY a := by
  rw [tY_apply, tY'_apply, diag3_mul, diag3_mul]
  apply diag3_congr <;> ring

variable [CharP K 2]

@[expose] def w3 : SL₃ :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    rw [Matrix.det_fin_three]
    simp [CharTwo.neg_eq]⟩

theorem coe_w3 : ((w3 : SL₃) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

theorem w3_mul_self : (w3 : SL₃) * w3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_w3, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem w3_inv : (w3 : SL₃)⁻¹ = w3 :=
  inv_eq_of_mul_eq_one_right w3_mul_self

theorem w3_conj_diag3 (x y z : K) (h : x * y * z = 1) :
    (w3 : SL₃) * diag3 x y z h * w3⁻¹ = diag3 z y x (by rw [← h]; ring) := by
  rw [w3_inv]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_w3, coe_diag3, coe_diag3]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp

theorem w3_conj_tY (a : Kˣ) : (w3 : SL₃) * tY a * w3⁻¹ = (tY a)⁻¹ := by
  rw [← map_inv, tY_apply, tY_apply, w3_conj_diag3]
  apply diag3_congr <;> simp

theorem w3_conj_tY' (b : Kˣ) : (w3 : SL₃) * tY' b * w3⁻¹ = tY' b := by
  rw [tY'_apply, w3_conj_diag3]

theorem w3_not_mem_upperTriangular : (w3 : SL₃) ∉ upperTriangular 3 K := by
  intro h
  have := h 2 0 (by decide)
  rw [coe_w3] at this
  simp at this

theorem upperTriangular_le [Finite K] :
    upperTriangular 3 K ≤ tY.range ⊔ tY'.range ⊔ unitriangular 3 K := by
  intro b hb
  have hbU : (b : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.1 hb
  have hdet : (b : Matrix (Fin 3) (Fin 3) K) 0 0 * (b : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (b : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h1 := Matrix.det_of_isUpperTriangular hbU
    rw [b.2, Fin.prod_univ_three] at h1
    exact h1.symm
  set x := (b : Matrix (Fin 3) (Fin 3) K) 0 0 with hx
  set y := (b : Matrix (Fin 3) (Fin 3) K) 1 1 with hy
  set z := (b : Matrix (Fin 3) (Fin 3) K) 2 2 with hz
  have hx0 : x ≠ 0 := fun h => by rw [h, zero_mul, zero_mul] at hdet; exact zero_ne_one hdet
  have hy0 : y ≠ 0 := fun h => by rw [h, mul_zero, zero_mul] at hdet; exact zero_ne_one hdet
  have hz0 : z ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (y⁻¹)
  have hr0 : r ≠ 0 := fun h => by
    rw [h, mul_zero] at hr
    exact inv_ne_zero hy0 hr
  set c : Kˣ := Units.mk0 r hr0 with hc
  set a : Kˣ := Units.mk0 (x * r⁻¹) (mul_ne_zero hx0 (inv_ne_zero hr0)) with ha
  have ht : tY a * tY' c = diag3 x y z hdet := by
    rw [tY_apply, tY'_apply, diag3_mul]
    have hyr : y = (r ^ 2)⁻¹ := by rw [sq, ← hr, inv_inv]
    have hz' : z = r ^ 2 * x⁻¹ := by
      have : z = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
      rw [this, hyr]
      field_simp
    apply diag3_congr
    · simp [ha, hc]
      field_simp
    · simp [hc, hyr]
    · simp [ha, hc, hz']
      field_simp
  set ti := diag3 x⁻¹ y⁻¹ z⁻¹ (by
    rw [← mul_inv, ← mul_inv, hdet, inv_one]) with hti
  have htti : diag3 x y z hdet * ti = 1 := by
    rw [hti, diag3_mul]
    apply Subtype.ext
    rw [coe_diag3, Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hx0, hy0, hz0]
  have hu : ti * b ∈ unitriangular 3 K := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, hti, coe_diag3, Matrix.diagonal_mul, hbU hij, mul_zero]
    · rw [Matrix.SpecialLinearGroup.coe_mul, hti, coe_diag3, Matrix.diagonal_mul]
      fin_cases i <;> simp [hx0, hy0, hz0, ← hx, ← hy, ← hz]
  have hb : b = tY a * tY' c * (ti * b) := by
    rw [ht, ← mul_assoc, htti, one_mul]
  rw [hb]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
    (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨c, rfl⟩)))
    (Subgroup.mem_sup_right hu)

theorem torusOut_projectiveSL3 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    TorusOut (projUnitriangular 3 K) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : upperTriangular 3 K ≤ Subgroup.normalizer (unitriangular 3 K : Set SL₃) := by
    rw [normalizer_unitriangular]
  refine torusOut_of_hom (proj 3 K) (U := unitriangular 3 K) (B := upperTriangular 3 K)
    (Y₀ := tY.range) (Y₀' := tY'.range) (w₀ := w3) ?_ ?_ ?_ upperTriangular_le
    (isCyclic_of_surjective tY.rangeRestrict tY.rangeRestrict_surjective)
    (isCyclic_of_surjective tY'.rangeRestrict tY'.rangeRestrict_surjective)
    (fun y hy h => tY_proj_eq_one hy h) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact hBN (tY_mem_upperTriangular a)
  · rintro _ ⟨b, rfl⟩
    exact hBN (tY'_mem_upperTriangular b)
  · show Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) ≤ _
    rw [normalizer_projUnitriangular 2]
    rfl
  · rw [← Nat.card_congr (MonoidHom.ofInjective tY_injective).toEquiv, Nat.card_units, hK]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact diag_comm a b
  · intro h
    have h1 : w3 ∈ ((upperTriangular 3 K).map (proj 3 K)).comap (proj 3 K) := h
    rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 (scalars_le_upperTriangular 3 K)] at h1
    exact w3_not_mem_upperTriangular h1
  · rintro _ ⟨a, rfl⟩
    exact w3_conj_tY a
  · rintro _ ⟨b, rfl⟩
    exact w3_conj_tY' b

theorem torusOut_of_isPSL3 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsPSL 3 2 n X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : TorusOut S n := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have e' : X ≃* projectiveSL 3 K' := e.trans (Id2519.projectiveSLEquivStatedProj 3 K').symm
  refine torusOut_of_equiv e' (fun S' hS' => ?_) hS
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K') 2 (n := 3) (by norm_num)
  exact torusOut_of_sylow P (hP ▸ torusOut_projectiveSL3 hK) hS'

end CFSG.Quasithin.H13.KG22
