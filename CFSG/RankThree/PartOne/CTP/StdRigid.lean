module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization
public import CFSG.RankThree.PartOne.CTP.StdSub

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.Classical (subfieldGL)
open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Transport

variable {e : ℕ} {K K' : Type} [Field K] [Field K'] (hK : UnitaryFieldData 2 e K)
  (hK' : UnitaryFieldData 2 e K') (κ : K ≃+* K')

@[expose] def mapGL (n : ℕ) : GL (Fin n) K ≃* GL (Fin n) K' :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) κ).toMulEquiv

theorem coe_mapGL {n : ℕ} (g : GL (Fin n) K) :
    ((mapGL κ n g : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
      (g : Matrix (Fin n) (Fin n) K).map κ := rfl

include hK hK' in
theorem bar_comm_ringEquiv (x : K) : κ (hK.bar x) = hK'.bar (κ x) := by
  rw [hK.bar_apply, hK'.bar_apply, map_pow]

include hK hK' in
theorem mapGL_mem_unitarySU_iff {n : ℕ} {g : GL (Fin n) K} :
    mapGL κ n g ∈ unitarySU 2 e K' n ↔ g ∈ unitarySU 2 e K n := by
  rw [mem_unitarySU_iff hK', mem_unitarySU_iff hK, coe_mapGL]
  have h1 : ((g : Matrix (Fin n) (Fin n) K).map κ).det = κ (g : Matrix (Fin n) (Fin n) K).det := by
    exact (RingHom.map_det (κ : K →+* K') _).symm
  have h2 : (((g : Matrix (Fin n) (Fin n) K).map κ).map hK'.bar)ᵀ *
      (g : Matrix (Fin n) (Fin n) K).map κ =
      (((g : Matrix (Fin n) (Fin n) K).map hK.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K)).map κ := by
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map]
    congr 2
    ext i j
    simp [bar_comm_ringEquiv hK hK' κ]
  rw [h1, h2]
  constructor
  · rintro ⟨hd, hu⟩
    refine ⟨κ.injective (by rw [hd, map_one]), ?_⟩
    refine Matrix.map_injective κ.injective ?_
    show (((g : Matrix (Fin n) (Fin n) K).map hK.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K)).map κ =
      (1 : Matrix (Fin n) (Fin n) K).map κ
    rw [hu, Matrix.map_one _ (map_zero κ) (map_one κ)]
  · rintro ⟨hd, hu⟩
    refine ⟨by rw [hd, map_one], ?_⟩
    rw [hu, Matrix.map_one _ (map_zero κ) (map_one κ)]

theorem mapGL_diagU {n : ℕ} (d : Fin n → Kˣ) :
    mapGL κ n (diagU d) = diagU (fun i => Units.map κ.toMonoidHom (d i)) := by
  apply Units.ext
  rw [coe_mapGL, diagU_val, diagU_val, Matrix.diagonal_map (map_zero _)]
  rfl

theorem mapGL_mem_torusSU {p n : ℕ} {g : GL (Fin n) K} (hg : g ∈ torusSU p n K) :
    mapGL κ n g ∈ torusSU p n K' := by
  obtain ⟨d, h1, h2, rfl⟩ := mem_torusSU_iff.mp hg
  refine mem_torusSU_iff.mpr ⟨fun i => Units.map κ.toMonoidHom (d i), fun i => ?_, ?_,
    (mapGL_diagU κ d).symm⟩
  · rw [← map_pow, h1 i, map_one]
  · rw [← map_prod, h2, map_one]

include hK hK' in
theorem mapGL_mem_blk {n : ℕ} {a b : Fin n} (hab : a ≠ b) {g : GL (Fin n) K}
    (hg : g ∈ blk hK hab) : mapGL κ n g ∈ blk hK' hab := by
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hab).mp hg
  refine (mem_blk_iff hab).mpr ⟨mapGL κ 2 X, ?_, ?_⟩
  · have hX' : X ∈ unitarySU 2 e K 2 := by
      rw [unitarySU_eq_gramSU hK 2]
      exact hX
    have := (mapGL_mem_unitarySU_iff hK hK' κ).mpr hX'
    rw [unitarySU_eq_gramSU hK' 2] at this
    exact this
  · rw [coe_mapGL, hgX, coe_mapGL]
    exact coordEmbed_map_ringHom (κ : K →+* K') a b _

end Transport

section Rigid

variable {e : ℕ} {K : Type} [Field K]

theorem glAut_eq_mapGL (σ : K ≃+* K) {n : ℕ} (g : GL (Fin n) K) :
    glAut σ g = mapGL σ n g := by
  apply Units.ext
  rw [coe_glAut, coe_mapGL]

theorem mapGL_symm_mapGL {K K' : Type} [Field K] [Field K'] (κ : K ≃+* K') {n : ℕ}
    (g : GL (Fin n) K) : mapGL κ.symm n (mapGL κ n g) = g := by
  apply Units.ext
  rw [coe_mapGL, coe_mapGL, Matrix.map_map]
  ext i j
  simp

@[expose] noncomputable def mapSU {K K' : Type} [Field K] [Field K'] {e : ℕ}
    (hK : UnitaryFieldData 2 e K) (hK' : UnitaryFieldData 2 e K') (κ : K ≃+* K') (n : ℕ) :
    ↥(unitarySU 2 e K n) ≃* ↥(unitarySU 2 e K' n) where
  toFun g := ⟨mapGL κ n g, (mapGL_mem_unitarySU_iff hK hK' κ).mpr g.2⟩
  invFun g := ⟨mapGL κ.symm n g, (mapGL_mem_unitarySU_iff hK' hK κ.symm).mpr g.2⟩
  left_inv g := Subtype.ext (mapGL_symm_mapGL κ (g : GL (Fin n) K))
  right_inv g := Subtype.ext (by
    have := mapGL_symm_mapGL κ.symm (n := n) (g : GL (Fin n) K')
    simpa using this)
  map_mul' g g' := Subtype.ext (map_mul (mapGL κ n) _ _)

end Rigid

section Rigid2

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  (unitary_three_full_semilinear_automorphism_realization)

variable {e : ℕ} {Kq K₀ : Type} [Field Kq] [Field K₀]

theorem glAut_mem_blk (h : UnitaryFieldData 2 e K₀) (σ : K₀ ≃+* K₀) {n : ℕ} {a b : Fin n}
    (hab : a ≠ b) {g : GL (Fin n) K₀} (hg : g ∈ blk h hab) : glAut σ g ∈ blk h hab := by
  rw [glAut_eq_mapGL]
  exact mapGL_mem_blk h h σ hab hg

theorem glAut_mem_torusSU (σ : K₀ ≃+* K₀) {p n : ℕ} {g : GL (Fin n) K₀}
    (hg : g ∈ torusSU p n K₀) : glAut σ g ∈ torusSU p n K₀ := by
  rw [glAut_eq_mapGL]
  exact mapGL_mem_torusSU σ hg

theorem rigid_triangle [Finite Kq] [Finite K₀] (hq : UnitaryFieldData 2 e Kq)
    (h₀ : UnitaryFieldData 2 e K₀) (he : 2 ≤ e) (hgcd : Nat.gcd 3 (2 ^ e + 1) = 1)
    (α : ↥(unitarySU 2 e Kq 3) ≃* ↥(unitarySU 2 e K₀ 3)) :
    ∃ A : GL (Fin 3) K₀,
      ((A : Matrix (Fin 3) (Fin 3) K₀).map h₀.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K₀) = 1 ∧
      (∀ (a b : Fin 3) (hab : a ≠ b) (g : ↥(unitarySU 2 e Kq 3)),
        (g : GL (Fin 3) Kq) ∈ blk hq hab ↔
          ((α g : ↥(unitarySU 2 e K₀ 3)) : GL (Fin 3) K₀) ∈
            (blk h₀ hab).map (MulAut.conj A).toMonoidHom) ∧
      (∀ g : ↥(unitarySU 2 e Kq 3), (g : GL (Fin 3) Kq) ∈ torusSU 5 3 Kq ↔
        ((α g : ↥(unitarySU 2 e K₀ 3)) : GL (Fin 3) K₀) ∈
          (torusSU 5 3 K₀).map (MulAut.conj A).toMonoidHom) := by
  have := Fintype.ofFinite Kq
  have := Fintype.ofFinite K₀
  have hcard : Fintype.card Kq = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hq.card_eq_sq, h₀.card_eq_sq]
  let κ : Kq ≃+* K₀ := FiniteField.ringEquivOfCardEq hcard
  let m := mapSU hq h₀ κ 3
  let α₁ : ↥(unitarySU 2 e K₀ 3) ≃* ↥(unitarySU 2 e K₀ 3) := m.symm.trans α
  have hZ : unitaryScalars h₀ 3 = ⊥ := by
    rw [← Subgroup.card_eq_one, card_unitaryScalars h₀ (by norm_num : 1 ≤ 3)]
    exact hgcd
  have hinj : Function.Injective (unitaryProj h₀ 3) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, hZ]
  let pj : ↥(unitarySU 2 e K₀ 3) ≃* unitaryPSU h₀ 3 :=
    MulEquiv.ofBijective (unitaryProj h₀ 3) ⟨hinj, unitaryProj_surjective h₀ 3⟩
  let β : MulAut (unitaryPSU h₀ 3) := pj.symm.trans (α₁.trans pj)
  have hq2 : 2 < 2 ^ e := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨σ, A, hA, hreal⟩ := unitary_three_full_semilinear_automorphism_realization h₀ hq2 β
  have key : ∀ g : ↥(unitarySU 2 e K₀ 3),
      ((α₁ g : ↥(unitarySU 2 e K₀ 3)) : GL (Fin 3) K₀) = A * glAut σ (g : GL (Fin 3) K₀) * A⁻¹ := by
    intro g
    obtain ⟨hg, hβ⟩ := hreal g
    have h1 : β (unitaryProj h₀ 3 g) = unitaryProj h₀ 3 (α₁ g) := by
      show pj (α₁ (pj.symm (pj g))) = pj (α₁ g)
      rw [MulEquiv.symm_apply_apply]
    rw [h1] at hβ
    exact congrArg (fun x : ↥(unitarySU 2 e K₀ 3) => (x : GL (Fin 3) K₀)) (hinj hβ)
  have keyα : ∀ g : ↥(unitarySU 2 e Kq 3),
      ((α g : ↥(unitarySU 2 e K₀ 3)) : GL (Fin 3) K₀) =
        A * glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)) * A⁻¹ := by
    intro g
    have := key (m g)
    have e1 : α₁ (m g) = α g := by
      show α (m.symm (m g)) = α g
      rw [MulEquiv.symm_apply_apply]
    rw [e1] at this
    exact this
  refine ⟨A, hA, fun a b hab g => ?_, fun g => ?_⟩
  · constructor
    · intro hg
      refine ⟨glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)),
        glAut_mem_blk h₀ σ hab (mapGL_mem_blk hq h₀ κ hab hg), ?_⟩
      rw [keyα g]
      rfl
    · rintro ⟨y, hy, hyg⟩
      rw [keyα g] at hyg
      have h2 : glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)) = y := by
        have := hyg
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        have h3 : A * y * A⁻¹ = A * glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)) * A⁻¹ := this
        have := mul_right_cancel h3
        exact (mul_left_cancel this).symm
      have h4 : mapGL κ 3 (g : GL (Fin 3) Kq) ∈ blk h₀ hab := by
        have := glAut_mem_blk h₀ σ⁻¹ hab hy
        rw [← h2] at this
        simpa [← MulAut.mul_apply, ← map_mul] using this
      have h5 := mapGL_mem_blk h₀ hq κ.symm hab h4
      rwa [mapGL_symm_mapGL] at h5
  · constructor
    · intro hg
      refine ⟨glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)),
        glAut_mem_torusSU σ (mapGL_mem_torusSU κ hg), ?_⟩
      rw [keyα g]
      rfl
    · rintro ⟨y, hy, hyg⟩
      rw [keyα g] at hyg
      have h2 : glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)) = y := by
        have := hyg
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        have h3 : A * y * A⁻¹ = A * glAut σ (mapGL κ 3 (g : GL (Fin 3) Kq)) * A⁻¹ := this
        have := mul_right_cancel h3
        exact (mul_left_cancel this).symm
      have h4 : mapGL κ 3 (g : GL (Fin 3) Kq) ∈ torusSU 5 3 K₀ := by
        have := glAut_mem_torusSU σ⁻¹ hy
        rw [← h2] at this
        simpa [← MulAut.mul_apply, ← map_mul] using this
      have h5 := mapGL_mem_torusSU κ.symm h4
      rwa [mapGL_symm_mapGL] at h5

end Rigid2

end CFSG.RankThree.PartOne.CTP
