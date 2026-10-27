module

public import CFSG.Quasithin.Background.C124YLL2OddC
public import CFSG.Quasithin.Background.C124YLL2OddB

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

theorem not_woff_odd {B : Subgroup (MulAut W)} (hBX : B ≤ Xs) (hw : WOff U Z B)
    (hBL : ¬ B ≤ Ls) (hB0 : B ⊓ Ls ≤ C.Kroot) : False := by
  have hwq := (C.coord.woff_iff (C.Z_le_liftFix hBX)).1 hw
  obtain ⟨hne, hab, -⟩ := hw
  obtain ⟨t, htB, htL⟩ : ∃ t ∈ B, t ∉ Ls := by
    by_contra h
    push Not at h
    exact hBL fun x hx => h x hx
  let tX : ↥Xs := ⟨t, hBX htB⟩
  have ht2 : tX ^ 2 ^ 1 = 1 := Subtype.ext (by simpa using hab.2 t htB)
  obtain ⟨τ, h0, h1, hadd, hmul, hτ, hnid⟩ := C.odd_semilin ht2 htL
  obtain ⟨ω, -, -, hωω, h2, henum⟩ := S2.F4_data C.hF4
  have hτω : τ ω ≠ ω := by
    rcases S2.tau_cases h2 hωω henum τ h0 h1 hadd hmul with h | h
    · exact absurd h hnid
    · rw [h.1]
      intro h'
      exact one_ne_zero (by linear_combination h')
  have hfix4 : Nat.card ↥(fixImg U Z C.c B) ≤ 4 := by
    have := C.card_fixImg_sq_le hBX htB hτω (hτ ω) ⊤ (fun _ _ => trivial) (fun _ _ => trivial)
    rw [S2.card_top_pi, C.hF4] at this
    nlinarith
  have hB4 : 4 ≤ Nat.card B := by
    have h := hwq.2.2
    rw [C.card_Q] at h
    nlinarith
  have hB2 := C.card_le_two_mul hBX hab htB htL
  have hB0card : Nat.card ↥(B ⊓ Ls) ≤ 4 :=
    (Subgroup.card_le_of_le hB0).trans C.card_Kroot.le
  have hB0ne : B ⊓ Ls ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB2
    omega
  obtain ⟨b0, hb0B, hb01⟩ : ∃ b0 ∈ B ⊓ Ls, b0 ≠ 1 := by
    by_contra h
    push Not at h
    exact hB0ne (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨β, hβ⟩ := C.mem_Kroot.1 (hB0 hb0B)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hb01
    rw [hβ, S2.uSL_zero, map_one]
    rfl
  have hline : ∀ q ∈ fixImg U Z C.c B, Multiplicative.toAdd q ∈ S2.lineAdd F := by
    intro q hq
    have hmemB : ((C.thetaX (S2.uSL β) : ↥Xs) : MulAut W) ∈ B := by
      rw [show ((C.thetaX (S2.uSL β) : ↥Xs) : MulAut W) = b0 from hβ.symm]
      exact hb0B.1
    have := C.fix_of_mem_fixImg hBX hmemB hq
    rw [C.gOf_theta, S2.uSL_mulVec] at this
    have h3 := congrFun this 0
    have h4 : β * (Multiplicative.toAdd q) 1 = 0 := by simpa using h3
    exact S2.mem_lineAdd.2 ((mul_eq_zero.1 h4).resolve_left hβ0)
  have hfix2 : Nat.card ↥(fixImg U Z C.c B) ≤ 2 := by
    have := C.card_fixImg_sq_le hBX htB hτω (hτ ω) (S2.lineAdd F)
      (fun y hy => S2.mem_lineAdd.2 (by simp [S2.mem_lineAdd.1 hy])) hline
    rw [S2.card_lineAdd, C.hF4] at this
    nlinarith
  have hB8 : 8 ≤ Nat.card B := by
    have h := hwq.2.2
    rw [C.card_Q] at h
    nlinarith
  have hB0eq : B ⊓ Ls = C.Kroot :=
    Subgroup.eq_of_le_of_card_ge hB0 (by rw [C.card_Kroot]; omega)
  have hKB : C.Kroot ≤ B := hB0eq ▸ inf_le_left
  have hcom : ∀ b : F, ∀ q, C.gOf tX ((S2.uSL b : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      (S2.uSL b : Matrix (Fin 2) (Fin 2) F) *ᵥ C.gOf tX q := by
    intro b q
    have hy : ((C.thetaX (S2.uSL b) : ↥Xs) : MulAut W) ∈ C.Kroot := C.thetaX_mem_Kroot b
    have hc : tX * C.thetaX (S2.uSL b) = C.thetaX (S2.uSL b) * tX :=
      Subtype.ext (hab.1 t htB _ (hKB hy))
    rw [← C.gOf_theta, ← C.gOf_theta, ← C.gOf_mul, ← C.gOf_mul, hc]
  exact S2.no_semilin_commute τ h1 hτω (C.gOf tX) hτ
    (fun x y hxy => by
      have := congrArg (C.gOf (tX⁻¹)) hxy
      rwa [(C.normSL tX).left, (C.normSL tX).left] at this)
    (hcom 1) (hcom ω)

theorem isElemAbelian2_mono {A B : Subgroup (MulAut W)} (h : A ≤ B) (hB : IsElemAbelian2 B) :
    IsElemAbelian2 A :=
  ⟨fun a ha b hb => hB.1 a (h ha) b (h hb), fun a ha => hB.2 a (h ha)⟩

include C in
theorem woff_le_Ls {B : Subgroup (MulAut W)} (hBX : B ≤ Xs) (hw : WOff U Z B) : B ≤ Ls := by
  by_contra hBL
  have hB0p : IsPGroup 2 ↥(B ⊓ Ls) :=
    isPGroup_of_isElemAbelian2 (isElemAbelian2_mono inf_le_left hw.2.1)
  obtain ⟨l, hl, hle⟩ := exists_conj_le_of_isSylowTwoOf C.Kroot_sylow inf_le_right hB0p
  have hlX : l ∈ Xs := C.hLX hl
  have hB2X : B1.conjAut l B ≤ Xs := B1.conjAut_le hlX hBX
  have hw2 : WOff U Z (B1.conjAut l B) := hw.conj l (C.hU l hlX) (C.hZ l hlX)
  have hB2L : ¬ B1.conjAut l B ≤ Ls := by
    intro h
    apply hBL
    have := B1.conjAut_le (inv_mem hl) h
    rwa [B1.conjAut_inv_conjAut] at this
  have hB2K : B1.conjAut l B ⊓ Ls ≤ C.Kroot := by
    intro y hy
    have h1 : l⁻¹ * y * l ∈ B := B1.mem_conjAut.1 hy.1
    have h2 : l⁻¹ * y * l ∈ Ls := Ls.mul_mem (Ls.mul_mem (Ls.inv_mem hl) hy.2) hl
    exact hle (mem_cjSub.2 ⟨h1, h2⟩)
  exact C.not_woff_odd hB2X hw2 hB2L hB2K

end L2Ctx

end CFSG.Quasithin.C124.YL
