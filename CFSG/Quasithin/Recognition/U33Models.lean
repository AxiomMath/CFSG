module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.Quasithin

open scoped MatrixGroups
open Matrix
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

private theorem neg_one_ne_one_galoisField (p n : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (-1 : GaloisField p n) ≠ 1 := by
  apply Ring.neg_one_ne_one_of_char_ne_two
  rw [ringChar.eq (GaloisField p n) p]
  exact hp

theorem psl3_exists_involution_centralizer_dvd (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hk : 0 < k) :
    ∃ y : PSL(3, GaloisField p k), y * y = 1 ∧ y ≠ 1 ∧
      p ^ k ∣ Nat.card (Subgroup.centralizer ({y} : Set PSL(3, GaloisField p k))) := by
  classical
  have h02 : (0 : Fin 3) ≠ 1 := by decide
  have hne : (-1 : GaloisField p k) ≠ 1 := neg_one_ne_one_galoisField p k hp
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix.SpecialLinearGroup (Fin 3) (GaloisField p k),
      (Y : Matrix (Fin 3) (Fin 3) (GaloisField p k)) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] :=
    ⟨⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩, rfl⟩
  have hYY : Y * Y = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hY, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hYcomm : ∀ b : GaloisField p k, Y * Matrix.SpecialLinearGroup.transvection h02 b =
      Matrix.SpecialLinearGroup.transvection h02 b * Y := by
    intro b
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hY,
      Matrix.SpecialLinearGroup.transvection_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
  have hYc : Y ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField p k)) := by
    intro h
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have h00 := congr($hr 0 0)
    have h22 := congr($hr 2 2)
    rw [hY] at h00 h22
    simp at h00 h22
    exact hne (h00.symm.trans h22)
  let tv : Multiplicative (GaloisField p k) →*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField p k) :=
    MonoidHom.mk' (fun b => Matrix.SpecialLinearGroup.transvection h02 (Multiplicative.toAdd b))
      (fun a b => by rw [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add])
  let t : Multiplicative (GaloisField p k) →* PSL(3, GaloisField p k) :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField p k)))).comp tv
  have htinj : Function.Injective t := by
    intro a b hab
    have hab' : (QuotientGroup.mk (tv a) : PSL(3, GaloisField p k)) = QuotientGroup.mk (tv b) := hab
    rw [QuotientGroup.eq] at hab'
    have : (tv a)⁻¹ * tv b = Matrix.SpecialLinearGroup.transvection h02
        (-(Multiplicative.toAdd a) + Multiplicative.toAdd b) := by
      show (Matrix.SpecialLinearGroup.transvection h02 (Multiplicative.toAdd a))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h02 (Multiplicative.toAdd b) = _
      rw [Matrix.SpecialLinearGroup.transvection_inv, ← Matrix.SpecialLinearGroup.transvection_add]
    rw [this, Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hab'
    have : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      have := hab'
      rw [neg_add_eq_zero] at this
      exact this
    exact this
  have htcomm : ∀ b, (QuotientGroup.mk Y : PSL(3, GaloisField p k)) * t b =
      t b * QuotientGroup.mk Y := by
    intro b
    show (QuotientGroup.mk Y : PSL(3, GaloisField p k)) *
        QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection h02 (Multiplicative.toAdd b)) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection h02 (Multiplicative.toAdd b)) *
        QuotientGroup.mk Y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hYcomm]
  refine ⟨QuotientGroup.mk Y, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, hYY, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]
    exact hYc
  · have hle : t.range ≤
        Subgroup.centralizer ({(QuotientGroup.mk Y : PSL(3, GaloisField p k))} : Set _) := by
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact htcomm b
    have hcard : Nat.card t.range = p ^ k := by
      rw [← Nat.card_congr (MonoidHom.ofInjective htinj).toEquiv]
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (GaloisField p k) ≃ _)]
      exact GaloisField.card p k hk.ne'
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle

theorem psu3_exists_involution_centralizer_dvd (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hk : 0 < k) :
    ∃ y : CFSG.Open.PSU3 p k, y * y = 1 ∧ y ≠ 1 ∧
      p ^ k ∣ Nat.card (Subgroup.centralizer ({y} : Set (CFSG.Open.PSU3 p k))) := by
  classical
  have hF : Nat.card (GaloisField p (2 * k)) = (p ^ k) ^ 2 := by
    rw [GaloisField.card p (2 * k) (by omega), pow_mul' p 2 k]
  have hq0 : p ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hodd : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have h0 : (0 : GaloisField p (2 * k)) ^ p ^ k = 0 := zero_pow hq0
  have hm1 : (-1 : GaloisField p (2 * k)) ^ p ^ k = -1 := hodd.neg_one_pow
  have hne : (-1 : GaloisField p (2 * k)) ≠ 1 := by
    apply Ring.neg_one_ne_one_of_char_ne_two
    rw [ringChar.eq (GaloisField p (2 * k)) p]
    exact hp
  obtain ⟨U, hU⟩ : ∃ U : GaloisField p (2 * k) → GL (Fin 3) (GaloisField p (2 * k)),
      ∀ b, (U b : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) = !![1, 0, b; 0, 1, 0; 0, 0, 1] :=
    ⟨fun b => ⟨!![1, 0, b; 0, 1, 0; 0, 0, 1], !![1, 0, -b; 0, 1, 0; 0, 0, 1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩,
      fun b => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : GL (Fin 3) (GaloisField p (2 * k)),
      (Y : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] :=
    ⟨⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩,
      rfl⟩
  have hUmul : ∀ a b, U (a + b) = U a * U b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hU, hU, hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hU0 : U 0 = 1 := by
    apply Units.ext
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hYY : Y * Y = 1 := by
    apply Units.ext
    rw [Units.val_mul, hY]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hYU : ∀ b, Y * U b = U b * Y := by
    intro b
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hY, hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hmemU : ∀ b : GaloisField p (2 * k), b + b ^ p ^ k = 0 →
      (ProjGenLinGroup.mk (U b) : ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) ∈
        CFSG.Open.PSU3 p k := by
    intro b hb
    refine Subgroup.mem_map.mpr ⟨U b, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
    · rw [hU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h0]
      linear_combination hb
    · apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hU]
      simp [Matrix.det_fin_three]
  have hmemY : (ProjGenLinGroup.mk Y : ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) ∈
      CFSG.Open.PSU3 p k := by
    refine Subgroup.mem_map.mpr ⟨Y, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
    · rw [hY]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h0, hm1]
    · apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hY]
      simp [Matrix.det_fin_three]
  let σ := unitaryInvolution (GaloisField p (2 * k)) p k
  have hσ : ∀ c, σ c = c ^ p ^ k := fun c => unitaryInvolution_apply _ p k c
  let uHom : Multiplicative (traceZero σ) →* GL (Fin 3) (GaloisField p (2 * k)) :=
    MonoidHom.mk' (fun c => U (c.toAdd : GaloisField p (2 * k))) (fun a b => by
      rw [toAdd_mul, AddSubgroup.coe_add, hUmul])
  have htmem : ∀ c : Multiplicative (traceZero σ),
      (ProjGenLinGroup.mk (uHom c) : ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) ∈
        CFSG.Open.PSU3 p k := fun c => by
    refine hmemU _ ?_
    have := c.toAdd.2
    rw [mem_traceZero, hσ] at this
    exact this
  let t : Multiplicative (traceZero σ) →* CFSG.Open.PSU3 p k :=
    (ProjGenLinGroup.mk.comp uHom).codRestrict _ htmem
  let y : CFSG.Open.PSU3 p k := ⟨ProjGenLinGroup.mk Y, hmemY⟩
  have htcomm : ∀ c, y * t c = t c * y := by
    intro c
    apply Subtype.ext
    show ProjGenLinGroup.mk Y * ProjGenLinGroup.mk (U (c.toAdd : GaloisField p (2 * k))) =
      ProjGenLinGroup.mk (U (c.toAdd : GaloisField p (2 * k))) * ProjGenLinGroup.mk Y
    rw [← map_mul, ← map_mul, hYU]
  have htinj : Function.Injective t := by
    intro a b hab
    have h1 : (ProjGenLinGroup.mk (U (a.toAdd : GaloisField p (2 * k))) :
        ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) =
        ProjGenLinGroup.mk (U (b.toAdd : GaloisField p (2 * k))) := congrArg Subtype.val hab
    rw [ProjGenLinGroup.mk_eq_mk_iff] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 := congrArg (fun g : GL (Fin 3) (GaloisField p (2 * k)) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k)))) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hU] at h2
    have h00 := congrFun (congrFun h2 0) 0
    have h02 := congrFun (congrFun h2 0) 2
    simp [Matrix.mul_apply, Matrix.diagonal_apply] at h00 h02
    have hu1 : u = 1 := h00
    subst hu1
    have : a.toAdd = b.toAdd := Subtype.ext (by simpa using h02)
    exact Multiplicative.toAdd.injective this
  have hy1 : y * y = 1 := by
    apply Subtype.ext
    show ProjGenLinGroup.mk Y * ProjGenLinGroup.mk Y = 1
    rw [← map_mul, hYY, map_one]
  have hyne : y ≠ 1 := by
    intro h
    have h1 : (ProjGenLinGroup.mk Y : ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) = 1 :=
      congrArg Subtype.val h
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 := congrArg (fun g : GL (Fin 3) (GaloisField p (2 * k)) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k)))) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar, hY] at h2
    have h00 := congrFun (congrFun h2 0) 0
    have h11 := congrFun (congrFun h2 1) 1
    simp at h00 h11
    exact hne (by simpa using congrArg Units.val (h00.symm.trans h11))
  refine ⟨y, hy1, hyne, ?_⟩
  have hle : t.range ≤ Subgroup.centralizer ({y} : Set (CFSG.Open.PSU3 p k)) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact htcomm c
  have hcard : Nat.card t.range = p ^ k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective htinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (traceZero σ) ≃ _)]
    exact card_traceZero hF
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end CFSG.Quasithin
