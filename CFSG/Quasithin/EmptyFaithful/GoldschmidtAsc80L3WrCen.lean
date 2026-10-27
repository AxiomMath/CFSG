module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3WrCom
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Par

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem val_inv_eq_neg {i : (ZMod p)ˣ} (hi : (i : ZMod p) ^ 2 = -1) :
    ((i⁻¹ : (ZMod p)ˣ) : ZMod p) = -(i : ZMod p) := by
  have h1 : (i : ZMod p) * ((i⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  linear_combination ((i⁻¹ : (ZMod p)ˣ) : ZMod p) * hi - (i : ZMod p) * h1

theorem pow_four_eq_one {i : (ZMod p)ˣ} (hi : (i : ZMod p) ^ 2 = -1) : i ^ 4 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    calc (i : ZMod p) ^ 4 = ((i : ZMod p) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hi]; norm_num)

theorem mem_diagT_of_commute_xO (hp2 : p ≠ 2) {i : (ZMod p)ˣ} (hi : (i : ZMod p) ^ 2 = -1)
    {g : SL(3, ZMod p)} (h : piL p g * piL p (xO i) = piL p (xO i) * piL p g) :
    g ∈ diagT p := by
  obtain ⟨q, hqdef⟩ : ∃ q : SL(3, ZMod p), q = g * xO i * g⁻¹ * (xO i)⁻¹ := ⟨_, rfl⟩
  have h1 : piL p q = 1 := by
    rw [hqdef]
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hk : q ∈ Subgroup.center SL(3, ZMod p) := by
    rw [← ker_piL]
    exact h1
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have hr3' : r ^ 3 = 1 := by simpa using hr3
  have hq : q * xO i * g = g * xO i := by
    rw [hqdef]
    group
  have hm := congrArg (fun x : SL(3, ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) hq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hr, coe_xO, val_inv_eq_neg hi] at hm
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ :=
    offdiag_zero_of_scalar_commute (two_ne_zero_zmod hp2) hi hr3' hm
  exact ⟨h01, h02, h10, h12, h20, h21⟩

@[expose] def w13 (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) :=
  ⟨!![0, 0, 1; 0, -1, 0; 1, 0, 0], by norm_num [Matrix.det_fin_three]⟩

theorem w13_mul_self : w13 p * w13 p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [w13, Matrix.mul_apply, Fin.sum_univ_three]

theorem w13_inv : (w13 p)⁻¹ = w13 p := inv_eq_of_mul_eq_one_right w13_mul_self

theorem w13_conj_mem {d : SL(3, ZMod p)} (hd : d ∈ diagT p) : w13 p * d * w13 p ∈ diagT p := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
     simp only [Matrix.mul_apply, Fin.sum_univ_three]
     simp [w13, d1, d2, d3, d4, d5, d6])

theorem w13_mem_normalizer : w13 p ∈ Subgroup.normalizer (diagT p : Set SL(3, ZMod p)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [w13_inv]
  refine ⟨fun hh => w13_conj_mem hh, fun hh => ?_⟩
  have hc := w13_conj_mem hh
  have e : w13 p * (w13 p * h * w13 p) * w13 p = h := by
    calc w13 p * (w13 p * h * w13 p) * w13 p = (w13 p * w13 p) * h * (w13 p * w13 p) := by group
      _ = h := by rw [w13_mul_self]; simp
  rwa [e] at hc

theorem w13_not_mem_leviBlock : w13 p ∉ leviBlock p := fun h => by
  have := (mem_leviBlock_iff.mp h).1
  simp [w13] at this

theorem piL_w13_mem_normalizer :
    piL p (w13 p) ∈ Subgroup.normalizer (diagC p : Set (PSL3 p)) :=
  Subgroup.le_normalizer_map (piL p) ⟨w13 p, w13_mem_normalizer, rfl⟩

theorem piL_w13_not_mem_leviC : piL p (w13 p) ∉ leviC p := fun h => by
  have hc : w13 p ∈ (leviC p).comap (piL p) := h
  rw [comap_leviC] at hc
  exact w13_not_mem_leviBlock hc

end CFSG.Quasithin.E2P.Asc80
