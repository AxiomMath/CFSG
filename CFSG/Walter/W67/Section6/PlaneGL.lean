module

public import CFSG.Walter.W67.Section6.GL2
public import CFSG.Walter.Cited.HuppertPlane

public section

namespace CFSG.Walter.W67.Sec6.GL2

open Huppert

variable {r : ℕ} [hr : Fact r.Prime] {V : Type*} [Group V] [Finite V]

section Coords

variable (hV : Plane r V) {e f : V} (he : e ≠ 1) (hf : f ∉ Subgroup.zpowers e)
include hV he hf

omit [Finite V] in
theorem coords_unique {x y x' y' : ZMod r}
    (h : e ^ x.val * f ^ y.val = e ^ x'.val * f ^ y'.val) : x = x' ∧ y = y' := by
  have h1 : e ^ (x - x').val * f ^ (y - y').val = 1 := by
    rw [sub_eq_add_neg, sub_eq_add_neg, hV.pow_val_add, hV.pow_val_add, hV.pow_val_neg,
      hV.pow_val_neg]
    calc e ^ x.val * (e ^ x'.val)⁻¹ * (f ^ y.val * (f ^ y'.val)⁻¹)
        = (e ^ x.val * f ^ y.val) * (e ^ x'.val * f ^ y'.val)⁻¹ := by
          rw [mul_inv_rev, hV.comm (f ^ y'.val)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hV.comm (e ^ x'.val)⁻¹]
      _ = 1 := by rw [h, mul_inv_cancel]
  obtain ⟨hi, hj⟩ := hV.dvd_of_mul_eq_one he hf h1
  have key : ∀ a b : ZMod r, r ∣ (a - b).val → a = b := by
    intro a b hab
    have : (a - b).val = 0 := by
      have hlt := ZMod.val_lt (a - b)
      obtain ⟨c, hc⟩ := hab
      rcases c with _ | c
      · simpa using hc
      · nlinarith
    rw [ZMod.val_eq_zero, sub_eq_zero] at this
    exact this
  exact ⟨key x x' hi, key y y' hj⟩

noncomputable def cx (v : V) : ZMod r := (hV.exists_coords he hf v).choose

noncomputable def cy (v : V) : ZMod r := (hV.exists_coords he hf v).choose_spec.choose

theorem coords_spec (v : V) : v = e ^ (cx hV he hf v).val * f ^ (cy hV he hf v).val :=
  (hV.exists_coords he hf v).choose_spec.choose_spec

theorem coords_eq {v : V} {x y : ZMod r} (h : v = e ^ x.val * f ^ y.val) :
    cx hV he hf v = x ∧ cy hV he hf v = y :=
  coords_unique hV he hf ((coords_spec hV he hf v).symm.trans h)

omit [Finite V] he hf in
theorem pow_nat_eq (v : V) (n : ℕ) : v ^ n = v ^ ((n : ZMod r)).val :=
  (hV.pow_val_natCast v n).symm

omit [Finite V] he hf in
theorem apply_coords (σ : MulAut V) {a b c d : ZMod r} (hσe : σ e = e ^ a.val * f ^ c.val)
    (hσf : σ f = e ^ b.val * f ^ d.val) (x y : ZMod r) :
    σ (e ^ x.val * f ^ y.val) = e ^ (a * x + b * y).val * f ^ (c * x + d * y).val := by
  rw [map_mul, map_pow, map_pow, hσe, hσf, hV.mul_pow', hV.mul_pow', ← pow_mul, ← pow_mul,
    ← pow_mul, ← pow_mul]
  have e1 : e ^ (a.val * x.val) * f ^ (c.val * x.val) * (e ^ (b.val * y.val) * f ^ (d.val * y.val))
      = e ^ (a.val * x.val + b.val * y.val) * f ^ (c.val * x.val + d.val * y.val) := by
    rw [pow_add, pow_add]
    calc e ^ (a.val * x.val) * f ^ (c.val * x.val) * (e ^ (b.val * y.val) * f ^ (d.val * y.val))
        = e ^ (a.val * x.val) * (f ^ (c.val * x.val) * e ^ (b.val * y.val)) *
            f ^ (d.val * y.val) := by group
      _ = e ^ (a.val * x.val) * (e ^ (b.val * y.val) * f ^ (c.val * x.val)) *
            f ^ (d.val * y.val) := by rw [hV.comm (f ^ _)]
      _ = _ := by group
  rw [e1, pow_nat_eq hV e, pow_nat_eq hV f]
  congr 3 <;> push_cast [ZMod.natCast_val, ZMod.cast_id', id] <;> ring

@[expose] noncomputable def toMat (σ : MulAut V) : Matrix (Fin 2) (Fin 2) (ZMod r) :=
  !![cx hV he hf (σ e), cx hV he hf (σ f); cy hV he hf (σ e), cy hV he hf (σ f)]

theorem toMat_one : toMat hV he hf 1 = 1 := by
  have h1 := coords_eq hV he hf (v := e) (x := 1) (y := 0)
    (by rw [Plane.pow_val_one, ZMod.val_zero, pow_zero, mul_one])
  have h2 := coords_eq hV he hf (v := f) (x := 0) (y := 1)
    (by rw [Plane.pow_val_one, ZMod.val_zero, pow_zero, one_mul])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, MulAut.one_apply, h1.1, h1.2, h2.1, h2.2]

theorem toMat_mul (σ τ : MulAut V) :
    toMat hV he hf (σ * τ) = toMat hV he hf σ * toMat hV he hf τ := by
  have hσe := coords_spec hV he hf (σ e)
  have hσf := coords_spec hV he hf (σ f)
  have hτe := coords_spec hV he hf (τ e)
  have hτf := coords_spec hV he hf (τ f)
  have h1 := coords_eq hV he hf (v := σ (τ e)) (by
    rw [hτe]
    exact apply_coords hV σ hσe hσf _ _)
  have h2 := coords_eq hV he hf (v := σ (τ f)) (by
    rw [hτf]
    exact apply_coords hV σ hσe hσf _ _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, Matrix.mul_apply, Fin.sum_univ_two, h1.1, h1.2, h2.1, h2.2]

@[expose] noncomputable def toGL : MulAut V →* GL (Fin 2) (ZMod r) :=
  MonoidHom.toHomUnits
    { toFun := toMat hV he hf
      map_one' := toMat_one hV he hf
      map_mul' := toMat_mul hV he hf }

theorem ent_toGL (σ : MulAut V) (i j : Fin 2) :
    ent (toGL hV he hf σ) i j = toMat hV he hf σ i j := rfl

theorem ent_toGL_of {σ : MulAut V} {a b c d : ZMod r} (hσe : σ e = e ^ a.val * f ^ c.val)
    (hσf : σ f = e ^ b.val * f ^ d.val) :
    ent (toGL hV he hf σ) 0 0 = a ∧ ent (toGL hV he hf σ) 0 1 = b ∧
      ent (toGL hV he hf σ) 1 0 = c ∧ ent (toGL hV he hf σ) 1 1 = d := by
  have h1 := coords_eq hV he hf hσe
  have h2 := coords_eq hV he hf hσf
  simp only [ent_toGL, toMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

theorem toGL_injective : Function.Injective (toGL hV he hf) := by
  intro σ τ h
  have hσe := coords_spec hV he hf (σ e)
  have hσf := coords_spec hV he hf (σ f)
  have hτe := coords_spec hV he hf (τ e)
  have hτf := coords_spec hV he hf (τ f)
  have hm : ∀ i j, toMat hV he hf σ i j = toMat hV he hf τ i j := fun i j => by
    rw [← ent_toGL, ← ent_toGL, h]
  have h00 := hm 0 0
  have h01 := hm 0 1
  have h10 := hm 1 0
  have h11 := hm 1 1
  simp only [toMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  apply hV.mulAut_ext he hf
  · rw [hσe, hτe, h00, h10]
  · rw [hσf, hτf, h01, h11]

omit [Finite V] hV he hf in
theorem eq_e : e = e ^ (1 : ZMod r).val * f ^ (0 : ZMod r).val := by
  rw [Plane.pow_val_one, ZMod.val_zero, pow_zero, mul_one]

omit [Finite V] hV he hf in
theorem eq_f_pow (k : ZMod r) : f ^ k.val = e ^ (0 : ZMod r).val * f ^ k.val := by
  rw [ZMod.val_zero, pow_zero, one_mul]

omit [Finite V] he hf in
theorem eq_f_inv : f⁻¹ = e ^ (0 : ZMod r).val * f ^ ((r - 1 : ℕ) : ZMod r).val := by
  rw [ZMod.val_zero, pow_zero, one_mul, ← pow_nat_eq hV]
  have hr1 : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hr1, hV.pow f]

end Coords

theorem cast_sub_one_add_one : ((r - 1 : ℕ) : ZMod r) + 1 = 0 := by
  have hr1 : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have : ((r - 1 : ℕ) : ZMod r) + 1 = ((r - 1 + 1 : ℕ) : ZMod r) := by push_cast; ring
  rw [this, Nat.sub_add_cancel hr1, ZMod.natCast_self]

theorem comm_of_plane (hV : Plane r V) {e f : V} (he : e ≠ 1) (hf : f ∉ Subgroup.zpowers e)
    (hr2 : r ≠ 2) {N : Type*} [Group N] [Finite N] (ρ : N →* MulAut V)
    (hcop : Nat.Coprime r (Nat.card ρ.range)) (h2 : (Nat.card ρ.range).factorization 2 ≤ 1)
    {t δ : N} (hte : ρ t e = e) (htf : ρ t f = f⁻¹) (hδe : ρ δ e = e) {k : ZMod r}
    (hδf : ρ δ f = f ^ k.val) (hk : k ≠ 1) (hδo : Odd (orderOf δ)) :
    ∀ n : N, ρ n * ρ t = ρ t * ρ n ∧ ρ n e ∈ Subgroup.zpowers e := by
  set A := ρ.range.map (toGL hV he hf) with hAdef
  have hAcard : Nat.card A = Nat.card ρ.range :=
    Subgroup.card_map_of_injective (toGL_injective hV he hf)
  have hmem : ∀ n : N, toGL hV he hf (ρ n) ∈ A := fun n => ⟨ρ n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ht00, ht01, ht10, ht11⟩ := ent_toGL_of hV he hf (σ := ρ t)
    (hte.trans eq_e) (htf.trans (eq_f_inv hV))
  obtain ⟨hδ00, hδ01, hδ10, hδ11⟩ := ent_toGL_of hV he hf (σ := ρ δ)
    (hδe.trans eq_e) (hδf.trans (eq_f_pow k))
  have hδo' : Odd (orderOf (toGL hV he hf (ρ δ))) := by
    have := orderOf_map_dvd ((toGL hV he hf).comp ρ) δ
    exact hδo.of_dvd_nat this
  have hdiag := diag_of_coprime hr2 (A := A) (by rw [hAcard]; exact hcop) (by rw [hAcard]; exact h2)
    (hmem t) (hmem δ) ht00 ht01 ht10 (by rw [ht11]; exact cast_sub_one_add_one) hδ00 hδ01 hδ10
    hδ11 hk hδo'
  intro n
  obtain ⟨hn01, hn10⟩ := hdiag _ (hmem n)
  refine ⟨?_, ?_⟩
  · apply toGL_injective hV he hf
    rw [map_mul, map_mul]
    apply ext' <;> simp only [ent_mul, hn01, hn10, ht01, ht10] <;> ring
  · have hc := coords_spec hV he hf (ρ n e)
    have h10 : cy hV he hf (ρ n e) = 0 := by
      have := hn10
      rw [ent_toGL] at this
      simpa [toMat] using this
    rw [hc, h10, ZMod.val_zero, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers e) _

end CFSG.Walter.W67.Sec6.GL2
