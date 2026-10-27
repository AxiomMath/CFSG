module

public import CFSG.Quasithin.Background.C124YLL2Root

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

include C in
theorem Z_le_liftFix {B : Subgroup (MulAut W)} (hB : B ≤ Xs) : Z ≤ liftFix U Z B := by
  intro z hz
  refine mem_liftFix.2 ⟨C.coord.Z_le hz, fun b hb => ?_⟩
  have := Z.mul_mem ((C.hZ b (hB hb) z).1 hz) (Z.inv_mem hz)
  exact this

include C in
theorem card_Q : Nat.card (Multiplicative (Fin 2 → F)) = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, C.hF4, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

theorem Kroot_le_Xs : C.Kroot ≤ Xs := C.Kroot_le.trans C.hLX

theorem thetaX_mem_Kroot (b : F) : ((C.thetaX (S2.uSL b) : ↥Xs) : MulAut W) ∈ C.Kroot :=
  C.mem_Kroot.2 ⟨b, rfl⟩

theorem mem_fixImg_Kroot (q : Multiplicative (Fin 2 → F)) :
    q ∈ fixImg U Z C.c C.Kroot ↔ Multiplicative.toAdd q 1 = 0 := by
  rw [mem_fixImg_iff_ind C.coord Xs C.hU C.hZ C.Kroot_le_Xs]
  constructor
  · intro h
    have h1 := h (C.thetaX (S2.uSL 1)) (C.thetaX_mem_Kroot 1)
    rw [C.ind_theta] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp only [slAct, toAdd_ofAdd, S2.uSL_mulVec] at h2
    simpa using h2
  · intro h x hx
    obtain ⟨b, hb⟩ := C.mem_Kroot.1 hx
    have hx' : x = C.thetaX (S2.uSL b) := Subtype.ext hb
    rw [hx', C.ind_theta]
    apply Multiplicative.toAdd.injective
    simp only [slAct, toAdd_ofAdd, S2.uSL_mulVec]
    ext i
    fin_cases i <;> simp [h]

theorem card_fixImg_Kroot : Nat.card ↥(fixImg U Z C.c C.Kroot) = 4 := by
  rw [← C.hF4]
  refine Nat.card_congr ⟨fun q => Multiplicative.toAdd (q : Multiplicative (Fin 2 → F)) 0,
    fun a => ⟨Multiplicative.ofAdd ![a, 0], by rw [C.mem_fixImg_Kroot]; simp⟩, ?_, ?_⟩
  · intro q
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have := (C.mem_fixImg_Kroot q).1 q.2
    ext i
    fin_cases i <;> simp [this]
  · intro a
    simp

theorem woff_Kroot : WOff U Z C.Kroot := by
  rw [WOff]
  refine ⟨?_, C.Kroot_elem, ?_⟩
  · intro h
    have := C.card_Kroot
    rw [h, Subgroup.card_bot] at this
    omega
  · rw [C.coord.card_U, C.coord.card_liftFix (C.Z_le_liftFix C.Kroot_le_Xs), C.card_Q,
      C.card_fixImg_Kroot, C.card_Kroot]
    omega

theorem tight_Kroot : Nat.card U = Nat.card C.Kroot * Nat.card (liftFix U Z C.Kroot) := by
  rw [C.coord.card_U, C.coord.card_liftFix (C.Z_le_liftFix C.Kroot_le_Xs), C.card_Q,
    C.card_fixImg_Kroot, C.card_Kroot]
  ring

theorem moves_Kroot : ∃ u ∈ liftFix U Z C.Kroot, ∃ y ∈ Ls, y u * u⁻¹ ∉ Z := by
  have hq : Multiplicative.ofAdd (![1, 0] : Fin 2 → F) ∈ fixImg U Z C.c C.Kroot := by
    rw [C.mem_fixImg_Kroot]
    simp
  obtain ⟨u, hu, hu'⟩ := mem_fixImg.1 hq
  refine ⟨u, mem_liftFix.2 ⟨u.2, hu'⟩, ((C.θ S2.wSL : ↥Ls) : MulAut W), (C.θ S2.wSL).2, ?_⟩
  intro hmem
  have h1 := (C.coord.ker (resU Xs C.hU (C.thetaX S2.wSL) u * u⁻¹)).2 hmem
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 : C.c (resU Xs C.hU (C.thetaX S2.wSL) u) = slAct S2.wSL (C.c u) := C.equiv _ u _
  rw [h2, hu] at h1
  have h3 := congrFun (congrArg Multiplicative.toAdd h1) 0
  simp only [slAct, toAdd_ofAdd, S2.wSL_mulVec] at h3
  simp at h3

theorem eq_Kroot_of_woff {B : Subgroup (MulAut W)} (hB : B ≤ C.Kroot) (hw : WOff U Z B) :
    B = C.Kroot := by
  have hBX : B ≤ Xs := hB.trans C.Kroot_le_Xs
  obtain ⟨hne, -, hcard⟩ := (C.coord.woff_iff (C.Z_le_liftFix hBX)).1 hw
  obtain ⟨g, hgB, hg1⟩ : ∃ g ∈ B, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  obtain ⟨b, rfl⟩ := C.mem_Kroot.1 (hB hgB)
  have hb : b ≠ 0 := by
    rintro rfl
    apply hg1
    rw [S2.uSL_zero, map_one]
    rfl
  have hle : fixImg U Z C.c B ≤ fixImg U Z C.c C.Kroot := by
    intro q hq
    rw [C.mem_fixImg_Kroot]
    have h1 := (mem_fixImg_iff_ind C.coord Xs C.hU C.hZ hBX q).1 hq (C.thetaX (S2.uSL b)) hgB
    rw [C.ind_theta] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp only [slAct, toAdd_ofAdd, S2.uSL_mulVec] at h2
    have h3 : b * (Multiplicative.toAdd q) 1 = 0 := by simpa using h2
    exact (mul_eq_zero.1 h3).resolve_left hb
  have h4 : Nat.card (fixImg U Z C.c B) ≤ 4 :=
    (Subgroup.card_le_of_le hle).trans C.card_fixImg_Kroot.le
  have h5 : 16 ≤ Nat.card B * 4 := by
    calc 16 = Nat.card (Multiplicative (Fin 2 → F)) := C.card_Q.symm
      _ ≤ Nat.card B * Nat.card (fixImg U Z C.c B) := hcard
      _ ≤ Nat.card B * 4 := Nat.mul_le_mul_left _ h4
  exact Subgroup.eq_of_le_of_card_ge hB (by rw [C.card_Kroot]; omega)

end L2Ctx

end CFSG.Quasithin.C124.YL
