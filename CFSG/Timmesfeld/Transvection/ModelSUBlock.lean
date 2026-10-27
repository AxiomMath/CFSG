module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeLevi
import CFSG.Timmesfeld.Transvection.AssembleModelSU
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.Timmesfeld.Transvection.ModelSUTransitive

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

private theorem midExt_eq_zero_of_not_mem_range {z : Fin m → F} {i : Fin (m + 2)}
    (hi : i ∉ Set.range (mid (m := m))) : midExt z i = 0 := by
  rw [midExt, dite_eq_right]
  exact fun h => hi (mem_range_mid.2 h)

theorem uForm_midExt (z w : Fin m → F) :
    uForm σ (midExt z : Fin (m + 2) → F) (midExt w) = uForm σ z w := by
  rw [uForm_eq, uForm_eq]
  refine (Fintype.sum_of_injective mid mid_injective (fun j => σ (z j) * w (Fin.rev j))
    (fun i => σ (midExt z i) * midExt w (Fin.rev i)) ?_ ?_).symm
  · intro i hi
    show σ (midExt z i) * midExt w (Fin.rev i) = 0
    rw [midExt_eq_zero_of_not_mem_range hi, map_zero, zero_mul]
  · intro j
    show σ (z j) * w (Fin.rev j) = σ (midExt z (mid j)) * midExt w (Fin.rev (mid j))
    rw [midExt_mid, rev_mid, midExt_mid]

theorem midExt_smul (c : F) (z : Fin m → F) :
    (midExt (c • z) : Fin (m + 2) → F) = c • midExt z := by
  funext i
  rw [Pi.smul_apply]
  by_cases h : 0 < (i : ℕ) ∧ (i : ℕ) < m + 1
  · rw [midExt, dite_eq_left h, midExt, dite_eq_left h]
    simp
  · rw [midExt, dite_eq_right h, midExt, dite_eq_right h]
    simp

theorem mem_perpPair_ends {u : Fin (m + 2) → F} :
    u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) ↔
      u (Fin.last (m + 1)) = 0 ∧ u 0 = 0 := by
  rw [mem_perpPair, uForm_single_left (0 : Fin (m + 2)) u,
    uForm_single_left (Fin.last (m + 1)) u, Fin.rev_zero, Fin.rev_last]

theorem uForm_single_zero_last :
    uForm σ (Pi.single (0 : Fin (m + 2)) 1) (Pi.single (Fin.last (m + 1)) 1) = 1 := by
  rw [uForm_single_left, Fin.rev_zero, Pi.single_eq_same]

theorem iotaMat_uTrans (z : Fin m → F) (c : F) :
    iotaMat (uTrans σ z c) = uTrans σ (midExt z : Fin (m + 2) → F) c := by
  refine isBlkOn_ext (iotaMat_isBlkOn _) ?_ ?_
  · intro x y hxy
    simp only [uTrans, uNil, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, uRow_apply,
      smul_eq_mul]
    have h0 : midExt z x * σ (midExt z (Fin.rev y)) = 0 := by
      rcases hxy with hx | hy
      · rw [midExt_eq_zero_of_not_mem_range hx, zero_mul]
      · rw [midExt_eq_zero_of_not_mem_range
          (fun h => hy ((rev_mem_range_mid_iff (m := m)).1 h)), map_zero, mul_zero]
    rw [h0, mul_zero, add_zero]
  · rw [submatrix_iotaMat]
    ext i j
    simp only [Matrix.submatrix_apply, uTrans, uNil, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, uRow_apply, smul_eq_mul, midExt_mid, rev_mid, Matrix.one_apply,
      mid_injective.eq_iff]

theorem suMat_iotaHom (g : SU σ m) :
    suMat σ (m + 2) (iotaHom g) = iotaMat (suMat σ m g) :=
  mat_iotaHom g

theorem isUTransGroup_map_iotaHom {z : Fin m → F} {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ z T) :
    IsUTransGroup σ (midExt z : Fin (m + 2) → F) (T.map iotaHom) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨c, hc, hc'⟩ := (hT.1 t).1 ht
      exact ⟨c, hc, by rw [suMat_iotaHom, hc', iotaMat_uTrans]⟩
    · rintro ⟨c, hc, hx⟩
      obtain ⟨t, htx⟩ := hT.2 c hc
      exact ⟨t, (hT.1 t).2 ⟨c, hc, htx⟩, suMat_injective σ (by
        rw [hx, suMat_iotaHom, htx, iotaMat_uTrans])⟩
  · obtain ⟨t, htx⟩ := hT.2 c hc
    exact ⟨iotaHom t, by rw [suMat_iotaHom, htx, iotaMat_uTrans]⟩

theorem exists_suMat_eq_of_isometry {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (hdet : M.det = 1)
    (hiso : conjTr σ M * antidiag n * M = antidiag n) : ∃ g : SU σ n, suMat σ n g = M :=
  ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    mem_SU.2 ⟨hdet, hiso⟩⟩, rfl⟩

theorem exists_suMat_mulVec_eq_pair [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin (m + 2) → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) :
    ∃ (x : SU σ (m + 2)) (l : F), l ≠ 0 ∧ suMat σ (m + 2) x *ᵥ Pi.single 0 1 = l • a ∧
      suMat σ (m + 2) x *ᵥ Pi.single (Fin.last (m + 1)) 1 = (σ l)⁻¹ • d := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have ha0 : a ≠ 0 := fun h => by
    rw [h] at had
    simp [uForm_eq] at had
  obtain ⟨g, l, hl, hg, -⟩ := exists_suMat_mulVec_eq_smul_of_perp hσ htr one_ne_zero h1
    (j := 0) (w := Pi.single (0 : Fin (m + 2)) 1) (w' := a)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (single_one_ne_zero _) ha0
    (uForm_single_self (zero_ne_last (m := m))) haa
  set z : Fin (m + 2) → F := (σ l)⁻¹ • d with hz
  have hzz : uForm σ z z = 0 := by
    rw [hz, uForm_smul_left, uForm_smul_right, hdd, mul_zero, mul_zero]
  have h1' : uForm σ (Pi.single 0 1) (suMat σ (m + 2) g⁻¹ *ᵥ z) = 1 := by
    have h := uForm_mulVec σ g (Pi.single (0 : Fin (m + 2)) 1)
      (suMat σ (m + 2) g⁻¹ *ᵥ z)
    rw [suMat_mulVec_suMat_inv_mulVec] at h
    rw [← h, hg, hz, uForm_smul_left, uForm_smul_right, had, mul_one]
    exact mul_inv_cancel₀ ((map_ne_zero σ).2 hl)
  have hz' : uForm σ (suMat σ (m + 2) g⁻¹ *ᵥ z) (suMat σ (m + 2) g⁻¹ *ᵥ z) = 0 := by
    rw [uForm_mulVec, hzz]
  obtain ⟨u, hu, hue⟩ := exists_mem_uRad_mulVec_eq hσ (a := Pi.single (0 : Fin (m + 2)) 1)
    (v := Pi.single (Fin.last (m + 1)) 1) (v' := suMat σ (m + 2) g⁻¹ *ᵥ z)
    (uForm_single_self (zero_ne_last (m := m)))
    (uForm_single_self (by rw [Fin.rev_last]; exact (zero_ne_last (m := m)).symm)) hz'
    uForm_single_zero_last h1'
  refine ⟨g * u, l, hl, ?_, ?_⟩
  · rw [map_mul, ← mulVec_mulVec, hu.1, hg]
  · rw [map_mul, ← mulVec_mulVec, hue, suMat_mulVec_suMat_inv_mulVec, hz]

theorem exists_eq_conjSub_rootGroup [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hm : 2 ≤ m) {z : Fin m → F} (hz : z ≠ 0)
    (hzz : uForm σ z z = 0) {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ z T) :
    ∃ y : SU σ m, T = conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) y := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  let e : Fin m → F := Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1
  have he : e ≠ 0 := single_one_ne_zero _
  have hie : uForm σ e e = 0 := uForm_single_self (lowIdx_ne_rev _ _)
  have hR : IsUTransGroup σ e (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) :=
    isUTransGroup_rootGroup_unitaryLongRoot hσ hm
  obtain ⟨g, l, hl, hg, -⟩ := exists_suMat_mulVec_eq_smul_of_perp hσ htr one_ne_zero h1
    (j := 0) (w := e) (w' := z) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => absurd hi (Nat.not_lt_zero _)) he hz hie hzz
  refine ⟨g, ?_⟩
  have hTg : IsUTransGroup σ z (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) g) :=
    IsUTransGroup.of_smul hσ hl (by rw [← hg]; exact hR.conjSub g)
  exact (hTg.eq hT).symm

end CFSG.Timmesfeld.Transvection.ModelRank
