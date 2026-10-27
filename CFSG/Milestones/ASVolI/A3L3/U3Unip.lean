module

public import CFSG.Milestones.ASVolI.A3L3.U3Facts

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K]

@[expose] def burnsideA315y_u3R (i : K) : Matrix (Fin 3) (HypIndex 1 1) K :=
  Matrix.of fun k a => Sum.elim (fun _ => ![1, i, 0] k)
    (Sum.elim (fun _ => ![0, 0, 1] k) (fun _ => ![2⁻¹, -(i * 2⁻¹), 0] k)) a

theorem burnsideA315y_u3R_isHyp (hU : UnitaryFieldData p 1 K) (two_ne : (2 : K) ≠ 0) {i : K}
    (hi : hU.bar i * i = -1) : IsHypTransport (r := 1) (ε := 1) hU (burnsideA315y_u3R i) := by
  have h2 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne
  have hb2 : hU.bar 2 = 2 := map_ofNat hU.bar 2
  show ((burnsideA315y_u3R i).map hU.bar)ᵀ * burnsideA315y_u3R i = hypGram 1 1 K
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
    simp [burnsideA315y_u3R, hb2] <;>
    first
    | ring1
    | linear_combination hi
    | linear_combination (-(2 : K)⁻¹) * hi + h2
    | linear_combination ((2 : K)⁻¹ * (2 : K)⁻¹) * hi

@[expose] def burnsideA315y_u3δ (u w : K) : HypIndex 1 1 → K :=
  Sum.elim (fun _ => u) (Sum.elim (fun _ => w) (fun _ => u))

theorem burnsideA315y_u3_diag_mul_R (i : K) {D : Matrix (Fin 3) (Fin 3) K} (h01 : D 0 1 = 0)
    (h10 : D 1 0 = 0) (h11 : D 1 1 = D 0 0) (h02 : D 0 2 = 0) (h12 : D 1 2 = 0)
    (h20 : D 2 0 = 0) (h21 : D 2 1 = 0) :
    D * burnsideA315y_u3R i = burnsideA315y_u3R i * diagonal (burnsideA315y_u3δ (D 0 0) (D 2 2)) := by
  ext k a
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases k <;> rcases a with a | a | a <;>
    simp [burnsideA315y_u3R, burnsideA315y_u3δ, h01, h10, h11, h02, h12, h20, h21] <;> ring

theorem burnsideA315y_u3_diag_conj {X : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hX : X.BlockTriangular fullPos ∧ ∀ a, X a a = 1) {δ₁ δ₂ : HypIndex 1 1 → K}
    (hδ : ∀ a, δ₁ a * δ₂ a = 1) :
    (diagonal δ₁ * X * diagonal δ₂).BlockTriangular fullPos ∧
      ∀ a, (diagonal δ₁ * X * diagonal δ₂) a a = 1 := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hX.1 hab, mul_zero, zero_mul]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hX.2 a, mul_one]
    exact hδ a

theorem burnsideA315y_mulAut_conj {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem burnsideA315y_u3_exists_norm_neg_one (hU : UnitaryFieldData p 1 K) :
    ∃ i : K, hU.bar i * i = -1 := by
  have hm1 : (-1 : K) ∈ hU.fixedField := hU.fixedField.neg_mem hU.fixedField.one_mem
  obtain ⟨i, hi⟩ := hU.normHom_surjective ⟨-1, hm1⟩
  refine ⟨i, ?_⟩
  have h := congrArg Subtype.val hi
  rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at h
  rw [mul_comm]
  exact h

section Model

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc

theorem burnsideA315y_u3_conj_mem {i : K} (hR : IsHypTransport (r := 1) (ε := 1) hU
    (burnsideA315y_u3R i)) {d : ↥(MU).Γ} (hd : d ∈ (MU).D₀) {X : ↥(hypSU hU 1 1)}
    (hX : X ∈ hypUnitriangular hU 1 1) :
    (hypTransport hU hR).symm (suConj hU d (hypTransport hU hR X)) ∈
      hypUnitriangular hU 1 1 := by
  set R := burnsideA315y_u3R i with hRdef
  set Rinv : Matrix (HypIndex 1 1) (Fin 3) K := transportInv (r := 1) (ε := 1) hU R with hRinv
  have hRR : Rinv * R = 1 := transportInv_mul hR
  have hRR' : R * Rinv = 1 := mul_transportInv hR
  set Dm := (((d : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hDm
  set Dm' := (((d⁻¹ : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hDm'
  set Xm := ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hXm
  have hmat : ((((hypTransport hU hR).symm (suConj hU d (hypTransport hU hR X)) :
      ↥(hypSU hU 1 1)) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      (Rinv * Dm * R) * Xm * (Rinv * Dm' * R) := by
    have h1 : ((((hypTransport hU hR).symm (suConj hU d (hypTransport hU hR X)) :
        ↥(hypSU hU 1 1)) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
        Rinv * (Dm * (R * Xm * Rinv) * Dm') * R := rfl
    rw [h1]
    simp only [Matrix.mul_assoc]
  obtain ⟨a01, a10, a11, a02, a12, a20, a21⟩ := (MU).D₀_form hd
  obtain ⟨b01, b10, b11, b02, b12, b20, b21⟩ := (MU).D₀_form ((MU).D₀.inv_mem hd)
  have hD1 : Rinv * Dm * R = diagonal (burnsideA315y_u3δ (Dm 0 0) (Dm 2 2)) := by
    rw [Matrix.mul_assoc, burnsideA315y_u3_diag_mul_R i a01 a10 a11 a02 a12 a20 a21,
      ← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have hD2 : Rinv * Dm' * R = diagonal (burnsideA315y_u3δ (Dm' 0 0) (Dm' 2 2)) := by
    rw [Matrix.mul_assoc, burnsideA315y_u3_diag_mul_R i b01 b10 b11 b02 b12 b20 b21,
      ← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have hDD : Dm * Dm' = 1 := by
    rw [hDm, hDm', Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hprod : (Rinv * Dm * R) * (Rinv * Dm' * R) = 1 := by
    calc (Rinv * Dm * R) * (Rinv * Dm' * R) = Rinv * Dm * (R * Rinv) * Dm' * R := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRR', Matrix.mul_one, Matrix.mul_assoc Rinv, hDD, Matrix.mul_one, hRR]
  rw [hD1, hD2, diagonal_mul_diagonal] at hprod
  have hδ : ∀ a, burnsideA315y_u3δ (Dm 0 0) (Dm 2 2) a *
      burnsideA315y_u3δ (Dm' 0 0) (Dm' 2 2) a = 1 := by
    intro a
    have := congrFun (congrFun hprod a) a
    simpa using this
  rw [mem_hypUnitriangular, hmat, hD1, hD2]
  exact burnsideA315y_u3_diag_conj (mem_hypUnitriangular.mp hX) hδ

theorem burnsideA315y_u3_hU [Fact p.Prime] :
    ∃ U : Subgroup (MulAut (unitaryPSU hU 3)),
      CFSG.Quasithin.A315.IsSylowOf p U
        (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)).range ∧
      (MU).D₀.map (MU).c ≤ Subgroup.normalizer (U : Set (MulAut (unitaryPSU hU 3))) := by
  obtain ⟨i, hi⟩ := burnsideA315y_u3_exists_norm_neg_one hU
  have hR : IsHypTransport (r := 1) (ε := 1) hU (burnsideA315y_u3R i) :=
    burnsideA315y_u3R_isHyp hU two_ne hi
  let f : hypPSU hU 1 1 →* MulAut (unitaryPSU hU 3) :=
    (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)).comp
      (hypProjTransport hU hR).toMonoidHom
  have hf : ∀ X : ↥(hypSU hU 1 1),
      f (hypProj hU 1 1 X) = MulAut.conj (unitaryProj hU 3 (hypTransport hU hR X)) := by
    intro X
    show MulAut.conj (hypProjTransport hU hR (hypProj hU 1 1 X)) = _
    rw [hypProjTransport_hypProj]
  obtain ⟨-, -, -, -, ⟨Pb, hPb⟩, -, -⟩ := unitary_order_and_Sylow hU (r := 1) (ε := 1) le_rfl le_rfl
  have hPbp : IsPGroup p ↥(hypProjUnitriangular hU 1 1) := hPb ▸ Pb.isPGroup'
  have hPbi : ¬ p ∣ (hypProjUnitriangular hU 1 1).index := hPb ▸ Pb.not_dvd_index
  have hrange : (⊤ : Subgroup (hypPSU hU 1 1)).map f =
      (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)).range := by
    ext φ
    constructor
    · rintro ⟨q, -, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨q, rfl⟩
      refine ⟨(hypProjTransport hU hR).symm q, Subgroup.mem_top _, ?_⟩
      show MulAut.conj (hypProjTransport hU hR ((hypProjTransport hU hR).symm q)) = _
      rw [MulEquiv.apply_symm_apply]
  refine ⟨(hypProjUnitriangular hU 1 1).map f, ⟨?_, hPbp.map f, ?_⟩, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨_, rfl⟩
  · have h1 := burnsideA315y_relIndex_map_dvd f (le_top : hypProjUnitriangular hU 1 1 ≤ ⊤)
    rw [hrange, Subgroup.relIndex_top_right] at h1
    exact fun h => hPbi (h.trans h1)
  · have key : ∀ d ∈ (MU).D₀, ∀ φ ∈ (hypProjUnitriangular hU 1 1).map f,
        (MU).c d * φ * ((MU).c d)⁻¹ ∈ (hypProjUnitriangular hU 1 1).map f := by
      rintro d hd _ ⟨q, hq, rfl⟩
      obtain ⟨X, hX, rfl⟩ := hq
      set X' := (hypTransport hU hR).symm (suConj hU d (hypTransport hU hR X)) with hX'def
      have hX' : X' ∈ hypUnitriangular hU 1 1 :=
        burnsideA315y_u3_conj_mem hU two_ne hdet hx hy hc hR hd hX
      refine ⟨hypProj hU 1 1 X', ⟨X', hX', rfl⟩, ?_⟩
      rw [hf, hf, burnsideA315y_mulAut_conj, hX'def, MulEquiv.apply_symm_apply]
      rfl
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    constructor
    · exact key d hd φ
    · intro h
      have h2 := key d⁻¹ ((MU).D₀.inv_mem hd) _ h
      rwa [map_inv, inv_inv, show ((MU).c d)⁻¹ * ((MU).c d * φ * ((MU).c d)⁻¹) * (MU).c d = φ by
        group] at h2

end Model

end CFSG.ASVolI
