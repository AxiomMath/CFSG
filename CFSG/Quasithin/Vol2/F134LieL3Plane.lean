module

public import CFSG.Quasithin.SteinbergBSLinearThreeRoot

public section

namespace CFSG.Quasithin.F134.LieL3

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def projPerm (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K →* Equiv.Perm (ℙ K (Fin n → K)) :=
  QuotientGroup.lift (scalars n K)
    (MulAction.toPermHom (SpecialLinearGroup (Fin n) K) (ℙ K (Fin n → K)))
    (by rw [Projectivization.SL_mulAction_ker, scalars_eq_center])

theorem projPerm_proj {n : ℕ} (g : SpecialLinearGroup (Fin n) K) (p : ℙ K (Fin n → K)) :
    projPerm n K (proj n K g) p = g • p :=
  rfl

theorem vec_ne_zero_of_two {a b c : K} (h : c ≠ 0) : (![a, b, c] : Fin 3 → K) ≠ 0 :=
  fun h0 => h (by simpa using congrFun h0 2)

theorem vec_ne_zero_of_zero {a b c : K} (h : a ≠ 0) : (![a, b, c] : Fin 3 → K) ≠ 0 :=
  fun h0 => h (by simpa using congrFun h0 0)

theorem vec_ne_zero_of_one {a b : K} (h : b ≠ 0) : (![a, b, 0] : Fin 3 → K) ≠ 0 :=
  fun h0 => h (by simpa using congrFun h0 1)

@[expose] noncomputable def basePt (K : Type) [Field K] : ℙ K (Fin 3 → K) :=
  Projectivization.mk K ![1, 0, 0] (vec_ne_zero_of_zero one_ne_zero)

@[expose] noncomputable def linePt (a : K) : ℙ K (Fin 3 → K) :=
  Projectivization.mk K ![a, 1, 0] (vec_ne_zero_of_one one_ne_zero)

@[expose] noncomputable def offPt (a b : K) : ℙ K (Fin 3 → K) :=
  Projectivization.mk K ![a, b, 1] (vec_ne_zero_of_two one_ne_zero)

theorem point_cases (p : ℙ K (Fin 3 → K)) :
    p = basePt K ∨ (∃ a, p = linePt a) ∨ ∃ a b, p = offPt a b := by
  induction p using Projectivization.ind with
  | _ v hv =>
    by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · left
        have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          ext i
          fin_cases i <;> simp [h0, h1, h2]
        rw [basePt, Projectivization.mk_eq_mk_iff]
        refine ⟨Units.mk0 (v 0) h0, ?_⟩
        ext i
        fin_cases i <;> simp [h1, h2]
      · right
        left
        refine ⟨v 0 / v 1, ?_⟩
        rw [linePt, Projectivization.mk_eq_mk_iff]
        refine ⟨Units.mk0 (v 1) h1, ?_⟩
        ext i
        fin_cases i <;> simp [h2, mul_div_cancel₀ _ h1]
    · right
      right
      refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
      rw [offPt, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (v 2) h2, ?_⟩
      ext i
      fin_cases i <;> simp [mul_div_cancel₀ _ h2]

theorem linePt_injective : Function.Injective (linePt (K := K)) := by
  intro a a' h
  rw [linePt, linePt, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrFun hc 1
  have h0 := congrFun hc 0
  simp [Units.smul_def] at h0 h1
  rw [h1] at h0
  simpa using h0.symm

theorem offPt_injective : Function.Injective fun p : K × K => offPt p.1 p.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [offPt] at h
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have h2 := congrFun hc 2
  have h1 := congrFun hc 1
  have h0 := congrFun hc 0
  simp [Units.smul_def] at h0 h1 h2
  rw [h2] at h0 h1
  simp only [Units.val_one, one_mul] at h0 h1
  rw [h0, h1]

theorem basePt_ne_linePt (a : K) : basePt K ≠ linePt a := by
  rw [basePt, linePt, Ne, Projectivization.mk_eq_mk_iff]
  rintro ⟨c, hc⟩
  have h1 := congrFun hc 1
  simp [Units.smul_def] at h1

theorem basePt_ne_offPt (a b : K) : basePt K ≠ offPt a b := by
  rw [basePt, offPt, Ne, Projectivization.mk_eq_mk_iff]
  rintro ⟨c, hc⟩
  have h2 := congrFun hc 2
  simp [Units.smul_def] at h2

theorem linePt_ne_offPt (a a' b' : K) : linePt a ≠ offPt a' b' := by
  rw [linePt, offPt, Ne, Projectivization.mk_eq_mk_iff]
  rintro ⟨c, hc⟩
  have h2 := congrFun hc 2
  simp [Units.smul_def] at h2

theorem up3_smul_basePt (x y z : K) : up3 x y z • basePt K = basePt K := by
  rw [basePt, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change _ = (up3 x y z : Matrix (Fin 3) (Fin 3) K) *ᵥ _
  ext i
  fin_cases i <;> simp [up3_coe, upMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem up3_smul_linePt (z a : K) : up3 0 0 z • linePt a = linePt (a + z) := by
  rw [linePt, linePt, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change _ = (up3 0 0 z : Matrix (Fin 3) (Fin 3) K) *ᵥ _
  ext i
  fin_cases i <;> simp [up3_coe, upMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem up3_smul_offPt (x y a b : K) : up3 x y 0 • offPt a b = offPt (a + y) (b + x) := by
  rw [offPt, offPt, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change _ = (up3 x y 0 : Matrix (Fin 3) (Fin 3) K) *ᵥ _
  ext i
  fin_cases i <;> simp [up3_coe, upMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem projPerm_basePt_of_mem {s : projectiveSL 3 K} (hs : s ∈ projUnitriangular 3 K) :
    projPerm 3 K s (basePt K) = basePt K := by
  obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_projUnitriangular hs
  rw [projPerm_proj, up3_smul_basePt]

theorem entries_of_smul_basePt {g : SL(3, K)} (h : g • basePt K = basePt K) :
    (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  rw [basePt, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have hv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = c • ![1, 0, 0] := hc.symm
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

theorem projPerm_fix_basePt [Finite K] {Q : Subgroup (projectiveSL 3 K)} (hQ : Nat.card Q ∣ 9)
    (hK2 : Nat.card K ≠ 2) (hK8 : Nat.card K ≠ 8)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {x : projectiveSL 3 K} (hx : x ∈ Q) :
    projPerm 3 K x (basePt K) = basePt K := by
  classical
  set O : Set (ℙ K (Fin 3 → K)) := {p | ∃ y ∈ Q, projPerm 3 K y (basePt K) = p} with hOdef
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq3 : 3 ≤ Nat.card K := by omega
  have hOdvd : O.ncard ∣ 9 := by
    let _ : MulAction Q (ℙ K (Fin 3 → K)) :=
      MulAction.compHom _ ((projPerm 3 K).comp Q.subtype)
    have h1 : O = MulAction.orbit Q (basePt K) := by
      ext p
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [h1, ← MulAction.index_stabilizer]
    exact (Subgroup.index_dvd_card _).trans hQ
  have hOle : O.ncard ≤ 9 := Nat.le_of_dvd (by norm_num) hOdvd
  have hbase : basePt K ∈ O := ⟨1, Q.one_mem, by rw [map_one, Equiv.Perm.one_apply]⟩
  have hinv : ∀ u ∈ projUnitriangular 3 K, ∀ p ∈ O, projPerm 3 K u p ∈ O := by
    rintro u hu _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', s, hs, hus⟩ := hQU u hu y hy
    refine ⟨y', hy', ?_⟩
    rw [← Equiv.Perm.mul_apply, ← map_mul, hus, map_mul, Equiv.Perm.mul_apply,
      projPerm_basePt_of_mem hs]
  have hoff : ∀ a b, offPt a b ∉ O := by
    intro a b hab
    have hall : ∀ a' b', offPt a' b' ∈ O := by
      intro a' b'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular (b' - b) (a' - a) 0)) _ hab
      rwa [projPerm_proj, up3_smul_offPt, add_sub_cancel, add_sub_cancel] at this
    have hsub : insert (basePt K) (Set.range fun p : K × K => offPt p.1 p.2) ⊆ O := by
      rintro _ (rfl | ⟨⟨a', b'⟩, rfl⟩)
      · exact hbase
      · exact hall a' b'
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite O)
    rw [Set.ncard_insert_of_notMem (by rintro ⟨⟨a', b'⟩, h⟩; exact basePt_ne_offPt a' b' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective offPt_injective, Nat.card_prod] at hcard
    have : 9 ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hq3 hq3
    omega
  have hline : ∀ a, linePt a ∉ O := by
    intro a ha
    have hall : ∀ a', linePt a' ∈ O := by
      intro a'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular 0 0 (a' - a))) _ ha
      rwa [projPerm_proj, up3_smul_linePt, add_sub_cancel] at this
    have hO : O = insert (basePt K) (Set.range linePt) := by
      apply le_antisymm
      · intro p hp
        rcases point_cases p with rfl | ⟨a', rfl⟩ | ⟨a', b', rfl⟩
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨a', rfl⟩
        · exact absurd hp (hoff a' b')
      · rintro _ (rfl | ⟨a', rfl⟩)
        · exact hbase
        · exact hall a'
    rw [hO, Set.ncard_insert_of_notMem (by rintro ⟨a', h⟩; exact basePt_ne_linePt a' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective linePt_injective] at hOdvd
    have hle : Nat.card K ≤ 8 := by
      have := Nat.le_of_dvd (by norm_num) hOdvd
      omega
    obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q := ⟨_, rfl⟩
    rw [hq] at hOdvd hle hK2 hK8 hq3
    interval_cases q <;> omega
  have hxO : projPerm 3 K x (basePt K) ∈ O := ⟨x, hx, rfl⟩
  rcases point_cases (projPerm 3 K x (basePt K)) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · exact h
  · exact absurd (h ▸ hxO) (hline a)
  · exact absurd (h ▸ hxO) (hoff a b)

theorem gammaZero_proj_inv [CharP K 2] (g : SL(3, K)) :
    ∃ h : SL(3, K), gammaZero K (proj 3 K g⁻¹) = proj 3 K h ∧
      (h : Matrix (Fin 3) (Fin 3) K) 1 0 = (g : Matrix (Fin 3) (Fin 3) K) 2 1 ∧
      (h : Matrix (Fin 3) (Fin 3) K) 2 0 = (g : Matrix (Fin 3) (Fin 3) K) 2 0 := by
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
    (SpecialLinearGroup.toGL wJ) (g⁻¹⁻¹).transpose, ?_, ?_⟩
  · rw [gammaZero, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  · have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, K)))⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = wJMat := by
      rw [← map_inv, wJ_inv]
      rfl
    have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = wJMat := rfl
    rw [coe_slConjugation, h1, h2, inv_inv]
    constructor <;>
    simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three, SpecialLinearGroup.coe_transpose,
      Matrix.vecMul, dotProduct]

theorem mem_upperTriangular_of_le [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQ : Nat.card Q ∣ 9) (hK2 : Nat.card K ≠ 2) (hK8 : Nat.card K ≠ 8)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {g : SL(3, K)} (hg : proj 3 K g ∈ Q) : g ∈ upperTriangular 3 K := by
  obtain ⟨h10, h20⟩ := entries_of_smul_basePt (projPerm_fix_basePt hQ hK2 hK8 hQU hg)
  set Q' := Q.map (gammaZero K).toMonoidHom with hQ'def
  have hγU := map_projUnitriangular_gammaZero (F := K)
  have hQ'card : Nat.card Q' ∣ 9 := by
    rw [hQ'def, Subgroup.card_map_of_injective (gammaZero K).injective]
    exact hQ
  have hQ'U : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q', ∃ y ∈ Q', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    rintro u hu _ ⟨x, hx, rfl⟩
    rw [← hγU] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨y, hy, s, hs, hus⟩ := hQU u₀ hu₀ x hx
    refine ⟨gammaZero K y, ⟨y, hy, rfl⟩, gammaZero K s, ?_, ?_⟩
    · rw [← hγU]
      exact ⟨s, hs, rfl⟩
    · change gammaZero K u₀ * gammaZero K x = gammaZero K y * gammaZero K s
      rw [← map_mul, hus, map_mul]
  obtain ⟨h, hh, h1, h2⟩ := gammaZero_proj_inv g
  have hhQ' : proj 3 K h ∈ Q' := by
    rw [← hh, map_inv]
    exact ⟨_, Q.inv_mem hg, rfl⟩
  obtain ⟨h10', h20'⟩ := entries_of_smul_basePt (projPerm_fix_basePt hQ'card hK2 hK8 hQ'U hhQ')
  rw [h1] at h10'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end CFSG.Quasithin.F134.LieL3
