module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType

namespace RCSTSU

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits OTwoGen RootCentSU
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom iotaMat
  iotaMat_isBlkOn mid mem_range_mid mid_injective mid_ne_zero mid_ne_last submatrix_iotaMat)

section Matrices

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {k : ℕ}

theorem mat_ggInvSU_one : mat σ (k + 2) (ggInvSU σ (k + 2) 1) = ggInvUMatrix (k + 2) 1 F := by
  rw [mat_apply]
  exact coe_ggInvSU (n := k + 2) (l := 1) σ (by omega)

theorem commute_of_mem {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    mat σ (k + 2) x * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * mat σ (k + 2) x := by
  rw [← mat_ggInvSU_one, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx]

theorem corner_ne_zero {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) ≠ 0 := by
  intro h0
  have hrow := row_zero_of_commute (commute_of_mem hx)
  have h1 : mat σ (k + 2) x * mat σ (k + 2) x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have h2 := congrFun (congrFun h1 0) 0
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun c _ => by
    rw [hrow c]
    split_ifs <;> simp [h0])] at h2
  simp at h2

theorem eq_zero_or_eq_last_of_not_mem {c : Fin (k + 2)} (hc : c ∉ Set.range (mid (m := k))) :
    c = 0 ∨ c = Fin.last (k + 1) := by
  rw [mem_range_mid] at hc
  have := c.isLt
  rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by simp only [Fin.val_last]; omega))

theorem submatrix_mul_of_mem {x y : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (hy : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    (mat σ (k + 2) (x * y)).submatrix mid mid =
      (mat σ (k + 2) x).submatrix mid mid * (mat σ (k + 2) y).submatrix mid mid := by
  have hcx := col_last_of_commute (commute_of_mem hx)
  have hry := row_zero_of_commute (commute_of_mem hy)
  ext i j
  rw [map_mul, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective mid mid_injective _ _ (fun c hc => ?_) (fun c => rfl)
  rcases eq_zero_or_eq_last_of_not_mem hc with rfl | rfl
  · rw [hry (mid j), ite_eq_right (mid_ne_zero j), mul_zero]
  · rw [hcx (mid i), ite_eq_right (mid_ne_last i), zero_mul]

theorem corner_mul_of_mem {x y : SU σ (k + 2)}
    (hy : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    mat σ (k + 2) (x * y) (Fin.last (k + 1)) (Fin.last (k + 1)) =
      mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) *
        mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) := by
  have hcy := col_last_of_commute (commute_of_mem hy)
  rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last (k + 1))]
  · intro c _ hc
    rw [hcy c, ite_eq_right hc, mul_zero]
  · simp

variable (σ k) in
@[expose] noncomputable def cornerMid :
    centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) →* Fˣ × Matrix (Fin k) (Fin k) F where
  toFun x := (Units.mk0 _ (corner_ne_zero x.2), (mat σ (k + 2) x).submatrix mid mid)
  map_one' := by
    refine Prod.ext (Units.ext ?_) ?_
    · simp
    · simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
      exact Matrix.submatrix_one _ mid_injective
  map_mul' x y := by
    refine Prod.ext (Units.ext ?_) ?_
    · simp only [Subgroup.coe_mul, Units.val_mk0, Prod.fst_mul, Units.val_mul]
      exact corner_mul_of_mem y.2
    · simp only [Subgroup.coe_mul, Prod.snd_mul]
      exact submatrix_mul_of_mem x.2 y.2

theorem cornerMid_apply (x : centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    cornerMid σ k x = (Units.mk0 _ (corner_ne_zero x.2), (mat σ (k + 2) x).submatrix mid mid) :=
  rfl

variable (σ k) in
@[expose] noncomputable def suRad : Subgroup (SU σ (k + 2)) :=
  (cornerMid σ k).ker.map (centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))).subtype

theorem mem_suRad {x : SU σ (k + 2)} :
    x ∈ suRad σ k ↔ x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧
        (mat σ (k + 2) x).submatrix mid mid = 1 := by
  constructor
  · rintro ⟨⟨y, hy⟩, hk, rfl⟩
    have hk' : cornerMid σ k ⟨y, hy⟩ = 1 := hk
    simp only [cornerMid_apply, Prod.mk_eq_one, Units.ext_iff, Units.val_mk0,
      Units.val_one] at hk'
    exact ⟨hy, hk'.1, hk'.2⟩
  · rintro ⟨hx, h1, h2⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show cornerMid σ k ⟨x, hx⟩ = 1
    simp only [cornerMid_apply, Prod.mk_eq_one, Units.ext_iff, Units.val_mk0, Units.val_one]
    exact ⟨h1, h2⟩

theorem suRad_le_centralizer :
    suRad σ k ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
  fun _ hx => (mem_suRad.mp hx).1

theorem suRad_isPGroup : IsPGroup 2 (suRad σ k) := by
  rintro ⟨x, hx⟩
  obtain ⟨hC, h1, h2⟩ := mem_suRad.mp hx
  have hA := commute_of_mem hC
  have h00 : mat σ (k + 2) x 0 0 = 1 := by rw [← corner_eq_of_commute hA, h1]
  refine ⟨2, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  refine pow_four_eq_one_of_blocks (fun b => ?_) (fun a => ?_) (fun i j => ?_)
  · rw [row_zero_of_commute hA, h1]
    by_cases hb : b = 0
    · rw [ite_eq_left hb, hb, Matrix.one_apply_eq]
    · rw [ite_eq_right hb, Matrix.one_apply_ne (Ne.symm hb)]
  · rw [col_last_of_commute hA, h00]
    by_cases ha : a = Fin.last (k + 1)
    · rw [ite_eq_left ha, ha, Matrix.one_apply_eq]
    · rw [ite_eq_right ha, Matrix.one_apply_ne ha]
  · have := congrFun (congrFun h2 i) j
    rw [Matrix.submatrix_apply] at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (mid_injective.ne hij)]

theorem centralizer_le_normalizer_suRad :
    centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ≤
      normalizer (suRad σ k : Set (SU σ (k + 2))) :=
  ggRCST_le_normalizer_map_ker (cornerMid σ k)

theorem ggInvSU_mul_self : ggInvSU σ (k + 2) 1 * ggInvSU σ (k + 2) 1 = 1 := by
  apply mat_injective
  rw [map_mul, mat_ggInvSU_one, map_one]
  exact ggInvUMatrix_mul_self _ _

theorem range_iotaHom_le_centralizer :
    (iotaHom (σ := σ) (m := k)).range ≤
      centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := by
  rintro _ ⟨B, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_ggInvSU_one, mat_iotaHom]
  exact commute_of_isBlkOn (iotaMat_isBlkOn _)

omit [CharP F 2] in
theorem corner_iotaHom (B : SU σ k) :
    mat σ (k + 2) (iotaHom B) (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  rw [mat_iotaHom, iotaMat_isBlkOn _ _ _ (Or.inl last_not_mem_range_mid), Matrix.one_apply_eq]

theorem mem_suRad_sup_of_corner {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (h1 : mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    x ∈ suRad σ k ⊔ (iotaHom (σ := σ) (m := k)).range := by
  have hA := commute_of_mem hx
  have h00 : mat σ (k + 2) x 0 0 = 1 := by rw [← corner_eq_of_commute hA]; exact h1
  have hcol : ∀ a, mat σ (k + 2) x a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) := by
    intro a
    rw [col_last_of_commute hA, h00]
    by_cases ha : a = Fin.last (k + 1)
    · rw [ite_eq_left ha, ha, Matrix.one_apply_eq]
    · rw [ite_eq_right ha, Matrix.one_apply_ne ha]
  have hrow : ∀ b, mat σ (k + 2) x 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b := by
    intro b
    rw [row_zero_of_commute hA, h1]
    by_cases hb : b = 0
    · rw [ite_eq_left hb, hb, Matrix.one_apply_eq]
    · rw [ite_eq_right hb, Matrix.one_apply_ne (Ne.symm hb)]
  have hdet : ((mat σ (k + 2) x).submatrix mid mid).det = 1 := by
    rw [← det_eq_det_submatrix_mid hrow hcol]
    exact x.2.1
  have hBu : IsUnit ((mat σ (k + 2) x).submatrix mid mid).det := by
    rw [hdet]
    exact isUnit_one
  let Bsu : SU σ k := ⟨⟨(mat σ (k + 2) x).submatrix mid mid,
    ((mat σ (k + 2) x).submatrix mid mid)⁻¹, Matrix.mul_nonsing_inv _ hBu,
    Matrix.nonsing_inv_mul _ hBu⟩, hdet, isometry_submatrix_mid x hrow⟩
  have hmatB : mat σ k Bsu = (mat σ (k + 2) x).submatrix mid mid := rfl
  have hιC : iotaHom Bsu ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    range_iotaHom_le_centralizer ⟨Bsu, rfl⟩
  have hinv : (iotaHom Bsu)⁻¹ = iotaHom Bsu⁻¹ := (map_inv _ _).symm
  have hrC : (iotaHom Bsu)⁻¹ * x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    mul_mem (inv_mem hιC) hx
  have hrcorner :
      mat σ (k + 2) ((iotaHom Bsu)⁻¹ * x) (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
    rw [corner_mul_of_mem hx, h1, mul_one, hinv, corner_iotaHom]
  have hrmid : (mat σ (k + 2) ((iotaHom Bsu)⁻¹ * x)).submatrix mid mid = 1 := by
    rw [submatrix_mul_of_mem (inv_mem hιC) hx, hinv, mat_iotaHom, submatrix_iotaMat, ← hmatB,
      ← map_mul, inv_mul_cancel, map_one]
  have hr : (iotaHom Bsu)⁻¹ * x ∈ suRad σ k := mem_suRad.mpr ⟨hrC, hrcorner, hrmid⟩
  have hxe : x = iotaHom Bsu * ((iotaHom Bsu)⁻¹ * x) := by rw [mul_inv_cancel_left]
  rw [hxe]
  exact mul_mem (mem_sup_right ⟨Bsu, rfl⟩) (mem_sup_left hr)

theorem corner_norm {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    σ (mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1))) *
      mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  have hA := commute_of_mem hx
  have h := sum_mat_mul_mat x (Fin.last (k + 1)) 0
  simp only [Fin.rev_last, ↓reduceIte] at h
  rw [Finset.sum_eq_single (Fin.last (k + 1))] at h
  · rw [Fin.rev_last, ← corner_eq_of_commute hA] at h
    exact h
  · intro t _ ht
    rw [col_last_of_commute hA t, ite_eq_right ht, map_zero, zero_mul]
  · simp

theorem corner_pow {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) (m : ℕ) :
    mat σ (k + 2) (x ^ m) (Fin.last (k + 1)) (Fin.last (k + 1)) =
      (mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1))) ^ m := by
  have h := congrArg (fun u : Fˣ × Matrix (Fin k) (Fin k) F => (u.1 : F))
    (map_pow (cornerMid σ k) ⟨x, hx⟩ m)
  simpa [cornerMid_apply] using h

end Matrices

section Core

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f k : ℕ} {G : Type} [Group G]

omit [Finite F] in
theorem hZ_su (σ : F ≃+* F) {n : ℕ} :
    ∀ z ∈ center (SU σ n), z ^ 2 = 1 → z = 1 :=
  fun _ hz h2 => eq_one_of_mem_center_SU_of_sq_eq_one σ hz h2

theorem pow_mem_suRad_sup {c : SU (unitaryInvolution F 2 f) (k + 2)}
    (hc : c ∈ centralizer ({ggInvSU (unitaryInvolution F 2 f) (k + 2) 1} :
      Set (SU (unitaryInvolution F 2 f) (k + 2)))) :
    c ^ (2 ^ f + 1) ∈ suRad (unitaryInvolution F 2 f) k ⊔
      (iotaHom (σ := unitaryInvolution F 2 f) (m := k)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine mem_suRad_sup_of_corner (pow_mem hc _) ?_
  rw [corner_pow hc, pow_succ, ← unitaryInvolution_apply]
  exact corner_norm hc

theorem ggRCSX_le_sup (hf : 1 ≤ f) (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2))) :
    ggRCSX ψ.range (ψ (ggInvSU (unitaryInvolution F 2 f) (k + 2) 1)) ≤
      (suRad (unitaryInvolution F 2 f) k).map ψ ⊔
        (ψ.comp (iotaHom (σ := unitaryInvolution F 2 f) (m := k))).range := by
  have hodd : Odd (2 ^ f + 1) := Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)
  have h := ggRCST_ggRCSX_le_map hker (hZ_su _) ggInvSU_mul_self hodd
    (fun c hc => pow_mem_suRad_sup hc)
  rwa [Subgroup.map_sup, ← MonoidHom.range_comp] at h

omit [Finite F] [CharP F 2] in
theorem ker_comp_iotaHom_le {σ : F ≃+* F} (ψ : SU σ (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU σ (k + 2))) :
    (ψ.comp (iotaHom (σ := σ) (m := k))).ker ≤ center (SU σ k) := by
  intro B hB
  have hιB : iotaHom B ∈ center (SU σ (k + 2)) := hker hB
  rw [mem_center_iff]
  intro B'
  apply CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom_injective
  rw [map_mul, map_mul]
  exact mem_center_iff.mp hιB (iotaHom B')

omit [Finite F] [CharP F 2] in
theorem perm_three_center : ∀ z : Equiv.Perm (Fin 3),
    (∀ g : Equiv.Perm (Fin 3), g * z = z * g) → z = 1 := by
  decide +kernel

theorem exists_equiv_sl2 (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 f) ≃* SU (unitaryInvolution F 2 f) 2) ∧
      Nat.card (CFSG.LieType.Steinberg.fixedSubfield F 2 f) = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  exact ⟨⟨CFSG.LieType.Steinberg.hypEquiv hζ0 hζ⟩, CFSG.LieType.Steinberg.card_fixedSubfield hF⟩

theorem isQuasisimple_su (hF : Nat.card F = (2 ^ f) ^ 2)
    (hk : (3 ≤ k ∧ (k, 2 ^ f) ≠ (3, 2)) ∨ (k = 2 ∧ 4 ≤ 2 ^ f)) :
    CFSG.IsQuasisimple (SU (unitaryInvolution F 2 f) k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hk with ⟨hk3, hkq⟩ | ⟨rfl, hq⟩
  · exact isQuasisimple_SU hF hk3 hkq
  · obtain ⟨⟨e⟩, hcard⟩ := exists_equiv_sl2 hF
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
        (Or.inr (by rw [hcard]; exact hq)))

theorem nonempty_su2_equiv_perm (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 2 ^ f = 2) :
    Nonempty (SU (unitaryInvolution F 2 f) 2 ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨⟨e⟩, hcard⟩ := exists_equiv_sl2 hF
  obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := CFSG.LieType.Steinberg.fixedSubfield F 2 f)
    (by rw [hcard, hq])
  exact ⟨e.symm.trans e3⟩

end Core

section Derived

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f k : ℕ} {G : Type} [Group G] [Finite G]

theorem derivedAt_su (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 2 ≤ k) (hU5 : k = 3 → 2 ^ f = 2 → p ≠ 3)
    (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2))) :
    GGRootCentDerivedAt p ψ.range (ψ (ggInvSU (unitaryInvolution F 2 f) (k + 2) 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · exfalso
      have h1 := Finite.one_lt_card (α := F)
      rw [hF] at h1
      norm_num at h1
    · exact h
  have hQ2 : IsPGroup 2 ((suRad (unitaryInvolution F 2 f) k).map ψ) := suRad_isPGroup.map ψ
  have hQX := ggRCST_map_le_ggRCSX_of_isPGroup ψ (suRad_le_centralizer (k := k)) suRad_isPGroup
  have hXQ := ggRCST_ggRCSX_le_normalizer hker (hZ_su _) ggInvSU_mul_self
    (centralizer_le_normalizer_suRad (σ := unitaryInvolution F 2 f) (k := k))
  have hL₀X := ggRCST_range_le_ggRCSX ψ iotaHom range_iotaHom_le_centralizer
    (top_le_closure_SU hF hk)
  have hX := ggRCSX_le_sup hf ψ hker
  have hkerι := ker_comp_iotaHom_le ψ hker
  by_cases hq : (3 ≤ k ∧ (k, 2 ^ f) ≠ (3, 2)) ∨ (k = 2 ∧ 4 ≤ 2 ^ f)
  · exact ggRootCentDerivedAt_of_quasisimple hp hp2 hQX hQ2 hXQ hL₀X
      (ggRCST_isQuasisimple_range _ (isQuasisimple_su hF hq) hkerι)
      ((CFSG.Quasithin.perfectCore_le _).trans hX) (fun y hy _ => hX hy)
  have hq2 : 2 ^ f = 2 := by
    have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    by_contra hne
    have h4 : 4 ≤ 2 ^ f := by
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by
        by_contra hf2
        push Not at hf2
        have : f = 1 := by omega
        exact hne (by rw [this, pow_one]))
      simpa using this
    apply hq
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · exact Or.inr ⟨by omega, h4⟩
    · exact Or.inl ⟨hk3, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  have hk23 : k = 2 ∨ k = 3 := by
    by_contra hk23
    apply hq
    exact Or.inl ⟨by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  rcases hk23 with rfl | rfl
  ·
    obtain ⟨e⟩ := nonempty_su2_equiv_perm hF hq2
    refine ggRootCentDerivedAt_of_sThree _ e hQX hQ2 hXQ hL₀X hX fun B hB => ?_
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hB⟩
    refine ⟨j, ?_⟩
    have h1 : (ψ.comp iotaHom) (B ^ 2 ^ j) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hj
    have hc := hkerι h1
    have hc' : e (B ^ 2 ^ j) = 1 := perm_three_center _ fun g => by
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hc g']
    exact e.injective (by rw [hc', map_one])
  ·
    have hp3 := hU5 rfl hq2
    refine ggRootCentDerivedAt_of_not_dvd hp hp2 hQ2 (hL₀X.trans hXQ) hX fun hpL => ?_
    have h1 : Nat.card (ψ.comp (iotaHom (σ := unitaryInvolution F 2 f) (m := 3))).range ∣
        Nat.card (SU (unitaryInvolution F 2 f) 3) := Subgroup.card_range_dvd _
    have h216 : Nat.card (SU (unitaryInvolution F 2 f) 3) = 2 ^ 3 * 3 ^ 3 := by
      rw [CFSG.LieType.Steinberg.card_SU_three hF, hq2]
      norm_num
    rw [h216] at h1
    rcases (Nat.Prime.dvd_mul hp).mp (hpL.trans h1) with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))

theorem derivedAt_of_longRoot (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (hU5 : k = 3 → 2 ^ f = 2 → p ≠ 3)
    (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2))) {r : G}
    (hr : GGRootInvolution (rootDatum hF (k + 2)) .PSU ψ r) :
    GGRootCentDerivedAt p ψ.range r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong (Or.inl rfl)) hx hx1
  set h := u₀ * a with hh
  set ψ' := ψ.comp (MulAut.conj h).toMonoidHom with hψ'
  have hr' : ψ' (ggInvSU (unitaryInvolution F 2 f) (k + 2) 1) =
      ψ ((MulAut.conj u₀).toMonoidHom x) := by
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha, hh]
    congr 1
    group
  have hrange : ψ'.range = ψ.range := by
    rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hker' : ψ'.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2)) := by
    intro v hv
    have hz : h * v * h⁻¹ ∈ center (SU (unitaryInvolution F 2 f) (k + 2)) := hker hv
    have h1 := (inferInstance :
      (center (SU (unitaryInvolution F 2 f) (k + 2))).Normal).conj_mem _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have := derivedAt_su hF hp hp2 hk hU5 ψ' hker'
  rwa [hrange, hr'] at this

end Derived

end RCSTSU

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

@[expose] def GGUFiveTwoRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : (ggU .PSU 5 1).K →* G),
    ψ.ker ≤ Subgroup.center (ggU .PSU 5 1).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
      ¬ GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G))

theorem ggRootCentDerivedTag_PSU_of_rank (hU5 : GGUFiveTwoRankInput) :
    GGRootCentDerivedTag .PSU := by
  intro G _ _ p n f
  by_cases hf : 1 ≤ f
  · have h5 : ∀ ψ : (ggU .PSU n f).K →* G, n = 5 → f = 1 →
        ψ.ker ≤ Subgroup.center (ggU .PSU n f).K →
          Subgroup.centralizer (ψ.range : Set G) = ⊥ →
            GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) → p ≠ 3 := by
      rintro ψ rfl rfl hker hC h4 rfl
      exact hU5 G ψ hker hC h4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e] at h5 ⊢
    intro ψ hp hp2 _ hrk hker hC h4 r hr
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrk
      omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine RCSTSU.derivedAt_of_longRoot (card_galoisField_two_mul 2 f hf) hp hp2 (by omega)
      (fun hk3 hq => h5 ψ (by omega) ?_ hker hC h4) ψ hker hr
    have h2 : 2 ^ f = 2 ^ 1 := by rw [hq, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h2
  · intro ψ _ _ hadm
    exact absurd hadm.2.1 hf

end Tag

end CFSG.StandardType
