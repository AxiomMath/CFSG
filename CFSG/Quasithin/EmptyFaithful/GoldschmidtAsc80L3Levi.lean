module

public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

@[expose] noncomputable def leviHom (p : ℕ) [Fact p.Prime] :
    GL (Fin 2) (ZMod p) →* SL(3, ZMod p) where
  toFun := lineLevi
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineLevi]
  map_mul' A B := by
    apply Subtype.ext
    show ((lineLevi (A * B) : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((lineLevi A * lineLevi B : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lineLevi, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_mul]
    ring

@[expose] noncomputable def leviBlock (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) :=
  (leviHom p).range

variable {p : ℕ} [Fact p.Prime]

theorem coe_leviHom (A : GL (Fin 2) (ZMod p)) :
    ((leviHom p A : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      !![(A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1, 0;
        0, 0, ((A : Matrix (Fin 2) (Fin 2) (ZMod p)).det)⁻¹] := rfl

theorem leviHom_injective : Function.Injective (leviHom p) := fun A B h => by
  have h' : (⟨lineLevi A, lineLevi_mem A⟩ : ↥(linePar p)) = ⟨lineLevi B, lineLevi_mem B⟩ :=
    Subtype.ext h
  calc A = lineBlk p ⟨lineLevi A, lineLevi_mem A⟩ := (lineBlk_lineLevi A).symm
    _ = lineBlk p ⟨lineLevi B, lineLevi_mem B⟩ := congrArg _ h'
    _ = B := lineBlk_lineLevi B

theorem leviBlock_le_linePar : leviBlock p ≤ linePar p := by
  rintro _ ⟨A, rfl⟩
  exact lineLevi_mem A

theorem mem_leviBlock_iff {g : SL(3, ZMod p)} :
    g ∈ leviBlock p ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0 := by
  constructor
  · rintro ⟨A, rfl⟩
    simp [leviHom, lineLevi]
  · rintro ⟨h02, h12, h20, h21⟩
    have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := g.2
    rw [det_eq_ulBlock_mul h02 h12] at hdet
    have hne : (ulBlock (g : Matrix (Fin 3) (Fin 3) (ZMod p))).det ≠ 0 := fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
    refine ⟨Matrix.GeneralLinearGroup.mk'' (ulBlock (g : Matrix (Fin 3) (Fin 3) (ZMod p)))
      (isUnit_iff_ne_zero.mpr hne), ?_⟩
    apply Subtype.ext
    have h22 : ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2) =
        ((ulBlock (g : Matrix (Fin 3) (Fin 3) (ZMod p))).det)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_leviHom, ulBlock, h02, h12, h20, h21, h22]

@[expose] def planePar (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    simp [Matrix.mul_apply, Fin.sum_univ_three, ha0, ha1, hb0, hb1]
  inv_mem' := by
    rintro a ⟨ha0, ha1⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, ha0, ha1]

theorem mem_planePar_iff {g : SL(3, ZMod p)} :
    g ∈ planePar p ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0 := Iff.rfl

theorem leviBlock_le_planePar : leviBlock p ≤ planePar p := fun _ hg =>
  ⟨(mem_leviBlock_iff.mp hg).2.2.1, (mem_leviBlock_iff.mp hg).2.2.2⟩

theorem slTau_slTau (g : SL(3, ZMod p)) : slTau p (slTau p g) = g :=
  (slTau p).left_inv g

theorem planePar_eq_map : planePar p = (linePar p).map (slTau p).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨slTau p g, ?_, slTau_slTau g⟩
    have hg' : g⁻¹ ∈ planePar p := (planePar p).inv_mem hg
    show slTau p g ∈ linePar p
    rw [mem_linePar_iff]
    simpa [slTau_apply, Matrix.SpecialLinearGroup.coe_transpose] using
      And.intro hg'.1 hg'.2
  · rintro ⟨h, hh, rfl⟩
    have hh' : h⁻¹ ∈ linePar p := (linePar p).inv_mem hh
    rw [mem_planePar_iff]
    simpa [slTau_apply, Matrix.SpecialLinearGroup.coe_transpose] using
      And.intro hh'.1 hh'.2

theorem slTau_mem_leviBlock {g : SL(3, ZMod p)} (hg : g ∈ leviBlock p) :
    slTau p g ∈ leviBlock p := by
  have hg' := mem_leviBlock_iff.mp ((leviBlock p).inv_mem hg)
  rw [mem_leviBlock_iff]
  simpa [slTau_apply, Matrix.SpecialLinearGroup.coe_transpose] using
    And.intro hg'.2.2.1 (And.intro hg'.2.2.2 (And.intro hg'.1 hg'.2.1))

theorem map_slTau_leviBlock : (leviBlock p).map (slTau p).toMonoidHom = leviBlock p := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact slTau_mem_leviBlock hg
  · intro g hg
    exact ⟨slTau p g, slTau_mem_leviBlock hg, slTau_slTau g⟩

theorem exists_uMat_mul_leviHom {g : SL(3, ZMod p)} (hg : g ∈ linePar p) :
    ∃ s : Fin 2 → ZMod p, g = uMat s * leviHom p (lineBlk p ⟨g, hg⟩) := by
  set A := lineBlk p ⟨g, hg⟩ with hA
  have hL : leviHom p A ∈ linePar p := leviBlock_le_linePar ⟨A, rfl⟩
  have hmem : g * (leviHom p A)⁻¹ ∈ linePar p := (linePar p).mul_mem hg ((linePar p).inv_mem hL)
  have hone : lineBlk p ⟨g * (leviHom p A)⁻¹, hmem⟩ = 1 := by
    have h1 : (⟨g * (leviHom p A)⁻¹, hmem⟩ : ↥(linePar p)) = ⟨g, hg⟩ * ⟨leviHom p A, hL⟩⁻¹ := rfl
    rw [h1, map_mul, map_inv]
    have h2 : lineBlk p ⟨leviHom p A, hL⟩ = A := lineBlk_lineLevi A
    rw [h2, ← hA, mul_inv_cancel]
  obtain ⟨s, hs⟩ := (lineBlk_eq_one_iff ⟨g * (leviHom p A)⁻¹, hmem⟩).mp hone
  exact ⟨s, by
    have : g * (leviHom p A)⁻¹ = uMat s := hs
    rw [← this]
    group⟩

theorem eq_leviBlock_or_eq_linePar {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y)
    (hY : Y ≤ linePar p) : Y = leviBlock p ∨ Y = linePar p := by
  by_cases hall : Y ≤ leviBlock p
  · exact Or.inl (le_antisymm hall hB)
  right
  refine le_antisymm hY ?_
  obtain ⟨y, hyY, hyB⟩ := Set.not_subset.mp hall
  obtain ⟨s, hs⟩ := exists_uMat_mul_leviHom (hY hyY)
  obtain ⟨L, hLdef⟩ : ∃ L, L = leviHom p (lineBlk p ⟨y, hY hyY⟩) := ⟨_, rfl⟩
  rw [← hLdef] at hs
  have hL : L ∈ Y := hLdef ▸ hB ⟨_, rfl⟩
  have hsY : uMat s ∈ Y := by
    have : uMat s = y * L⁻¹ := by
      rw [hs]
      group
    rw [this]
    exact Y.mul_mem hyY (Y.inv_mem hL)
  have hs0 : s ≠ 0 := fun h => hyB (by
    rw [hs, h, uMat_zero, one_mul, hLdef]
    exact ⟨_, rfl⟩)
  have ht : ∀ t : Fin 2 → ZMod p, uMat t ∈ Y := by
    intro t
    by_cases ht0 : t = 0
    · rw [ht0, uMat_zero]
      exact Y.one_mem
    obtain ⟨A, hA⟩ := exists_sl2_vecMul hs0 ht0
    set k : SL(3, ZMod p) := leviHom p (Matrix.SpecialLinearGroup.toGL A) with hk
    have hkY : k ∈ Y := hB ⟨_, rfl⟩
    have hk0 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 := by simp [hk, coe_leviHom]
    have hk1 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 := by simp [hk, coe_leviHom]
    have hk2 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1 := by
      have := A.2
      simp [hk, coe_leviHom, this]
    have hkA : ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hk, coe_leviHom, ulBlock]
    have := Y.mul_mem (Y.mul_mem (Y.inv_mem hkY) hsY) hkY
    rwa [conj_uMat hk0 hk1 hk2, hkA, hA] at this
  intro g hg
  obtain ⟨u, hu⟩ := exists_uMat_mul_leviHom hg
  rw [hu]
  exact Y.mul_mem (ht u) (hB ⟨_, rfl⟩)

theorem eq_leviBlock_or_eq_planePar {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y)
    (hY : Y ≤ planePar p) : Y = leviBlock p ∨ Y = planePar p := by
  have hB' : leviBlock p ≤ Y.map (slTau p).toMonoidHom := by
    rw [← map_slTau_leviBlock]
    exact Subgroup.map_mono hB
  have hY' : Y.map (slTau p).toMonoidHom ≤ linePar p := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hY hy
    show slTau p y ∈ linePar p
    rw [mem_linePar_iff]
    have := (planePar p).inv_mem hy'
    simpa [slTau_apply, Matrix.SpecialLinearGroup.coe_transpose] using
      And.intro this.1 this.2
  have hback : ∀ Z : Subgroup SL(3, ZMod p), (Z.map (slTau p).toMonoidHom).map
      (slTau p).toMonoidHom = Z := fun Z => by
    rw [Subgroup.map_map]
    have : (slTau p).toMonoidHom.comp (slTau p).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext slTau_slTau
    rw [this, Subgroup.map_id]
  rcases eq_leviBlock_or_eq_linePar hB' hY' with h | h
  · left
    rw [← hback Y, h, map_slTau_leviBlock]
  · right
    rw [← hback Y, h, planePar_eq_map]

end CFSG.Quasithin.E2P.Asc80
