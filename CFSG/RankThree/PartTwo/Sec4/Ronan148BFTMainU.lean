module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTSplitU
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTTorusFrameU

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F] {hU : UnitaryFieldData 2 f F}

theorem commute_scalar_mul_iff {N X : GL (Fin 3) F} (κ : Fˣ) :
    N * (GeneralLinearGroup.scalar (Fin 3) κ * X) = (GeneralLinearGroup.scalar (Fin 3) κ * X) * N ↔
      N * X = X * N := by
  have hsc := (commute_scalar κ N).eq
  constructor
  · intro h
    have h' : GeneralLinearGroup.scalar (Fin 3) κ * (N * X) =
        GeneralLinearGroup.scalar (Fin 3) κ * (X * N) := by
      rw [← mul_assoc, ← hsc, mul_assoc, h, mul_assoc]
    exact mul_left_cancel h'
  · intro h
    rw [← mul_assoc, hsc, mul_assoc, h, mul_assoc]

theorem commute_conj_iff {N X Y : GL (Fin 3) F} :
    (Y⁻¹ * N * Y) * X = X * (Y⁻¹ * N * Y) ↔ N * (Y * X * Y⁻¹) = (Y * X * Y⁻¹) * N := by
  constructor
  · intro h
    calc N * (Y * X * Y⁻¹) = Y * ((Y⁻¹ * N * Y) * X) * Y⁻¹ := by group
      _ = Y * (X * (Y⁻¹ * N * Y)) * Y⁻¹ := by rw [h]
      _ = (Y * X * Y⁻¹) * N := by group
  · intro h
    calc (Y⁻¹ * N * Y) * X = Y⁻¹ * (N * (Y * X * Y⁻¹)) * Y := by group
      _ = Y⁻¹ * ((Y * X * Y⁻¹) * N) * Y := by rw [h]
      _ = X * (Y⁻¹ * N * Y) := by group

theorem nonsplit_case (hf : Odd f) (ρ : F ≃+* F) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x)
    (hρω : ∀ x : F, x ^ 3 = 1 → ρ x = x) {m : ℕ} (hm : Nat.Coprime m 3) {lam : Fˣ}
    (hlm : lam ^ m = 1) (hlN : hU.norm (lam : F) = 1) (hρl : ρ lam ≠ lam)
    {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {E : Subgroup (unitaryPSU hU 3)}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEs : ∀ x ∈ E, psuField hU ρ x = x)
    {zh : unitarySU 2 f F 3} (hzE : unitaryProj hU 3 zh ∈ E)
    {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU)
    (hbE : psuConj hU ⟨W, hW⟩ (dPSU hτ hU hf) ∈ E)
    {Mz : unitarySU 2 f F 3} (hWz : W * (Mz : GL (Fin 3) F) * W⁻¹ = zh) {w₀ w₁ w₂ : Fˣ}
    (hMz : (Mz : GL (Fin 3) F) = cycThree ^ 2 * diagUnits w₀ w₁ w₂)
    (hNW : ¬ ((W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)) * diagTau hτ =
      diagTau hτ * (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)))) :
    ∃ A : Subgroup (unitaryPSU hU 3), ¬ 3 ∣ Nat.card A ∧
      (∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) ∧ (∀ x ∈ A, psuField hU ρ x ∈ A) ∧
      (∀ x ∈ A, x * unitaryProj hU 3 zh = unitaryProj hU 3 zh * x → x = 1) ∧
      ∃ u ∈ A, u ≠ 1 ∧ psuField hU ρ (unitaryProj hU 3 zh * u * (unitaryProj hU 3 zh)⁻¹) = u := by
  set Γ := psuConj hU ⟨W, hW⟩ with hΓ
  set b := Γ (dPSU hτ hU hf) with hb
  have hρτ : ρ τ = τ := hρω τ hτ
  have hzW : unitaryProj hU 3 zh = Γ (unitaryProj hU 3 Mz) := by
    rw [hΓ, psuConj_unitaryProj']
    congr 1
    exact Subtype.ext hWz.symm
  have hNmem : W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W) ∈ unitaryIsom3 hU := mul_mem (inv_mem hW)
    (glAut_mem_unitaryIsom3 ρ (mul_mem (unitarySU_le_unitaryIsom3 zh.2) hW))
  set θ : unitaryPSU hU 3 → unitaryPSU hU 3 :=
    fun w => psuField hU ρ (unitaryProj hU 3 zh * w * (unitaryProj hU 3 zh)⁻¹) with hθdef
  have hθ : ∀ w, θ (Γ w) = Γ (psuConj hU ⟨_, hNmem⟩ (psuField hU ρ w)) := fun w =>
    twist_frame (hU := hU) ρ hW zh w
  have hθb : θ b = b := by
    change psuField hU ρ (unitaryProj hU 3 zh * b * (unitaryProj hU 3 zh)⁻¹) = b
    rw [hEc _ hzE b hbE, mul_inv_cancel_right, hEs b hbE]
  have hfd : psuField hU ρ (dPSU hτ hU hf) = dPSU hτ hU hf := by
    rw [dPSU, psuField_mk]
    congr 1
    exact Subtype.ext (glAut_diagTau ρ hτ hρτ)
  have hcd : psuConj hU ⟨_, hNmem⟩ (dPSU hτ hU hf) = dPSU hτ hU hf := by
    have h1 := hθ (dPSU hτ hU hf)
    rw [← hb, hθb, hfd] at h1
    exact Γ.injective h1.symm
  have hMd : unitaryProj hU 3 (⟨_, conj_mem_unitarySU hNmem
      (diagTau_mem_unitarySU hU hf hτ)⟩ : unitarySU 2 f F 3) =
      unitaryProj hU 3 ⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩ := by
    exact (psuConj_unitaryProj' hNmem ⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩).symm.trans hcd
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) hMd.symm
  change (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)) * diagTau hτ *
    (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W))⁻¹ = _ * diagTau hτ at hζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hNW
    rw [map_one, one_mul] at hζ
    calc (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)) * diagTau hτ
        = (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)) * diagTau hτ *
            (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W))⁻¹ *
              (W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W)) := by group
      _ = _ := by rw [hζ]
  obtain ⟨u, huA, hu1, hθu⟩ := exists_fixed_frameTorus hτ hτ1 ρ hρ3 hm hlm hlN hρl hW hNmem θ
    hθ hζ hζ1
  refine ⟨frameTorus hU hW m, not_three_dvd_card_frameTorus hW hm, ?_, ?_, ?_, u, huA, hu1, hθu⟩
  · intro e he x hx
    exact conj_mem_frameTorus_of_commute hτ hτ1 hf hW (hEc e he b hbE) hx
  · intro x hx
    exact aut_mem_frameTorus hτ hτ1 hf ρ hρτ hW (inv_mul_glAut_mem ρ hW) (psuField hU ρ)
      (psuField_frame ρ hW) (hEs b hbE) hx
  · intro x hx hxz
    rw [hzW] at hxz
    exact eq_one_of_commute_frameTorus hW hm (Or.inr rfl) hMz hx hxz

theorem conj_scalar_mul' (Y X : GL (Fin 3) F) (κ : Fˣ) :
    Y * (GeneralLinearGroup.scalar (Fin 3) κ * X) * Y⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) κ * (Y * X * Y⁻¹) := by
  rw [← mul_assoc Y, (commute_scalar κ Y).eq]
  group

section Conj

variable {τ : F} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0)

include hs in
theorem fourierGL_inv_conj_diagTau :
    (fourierGL h3 hs)⁻¹ * diagTau hτ * fourierGL h3 hs =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * cycThree := by
  have e := fourierGL_mul_cycThree hτ hτ0 h3 hs
  have hsc := (commute_scalar (Units.mk0 τ hτ0 ^ 2)⁻¹ (fourierGL h3 hs)⁻¹).eq
  have e2 : diagTau hτ * fourierGL h3 hs =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * (fourierGL h3 hs * cycThree) := by
    rw [e, map_inv]
    group
  calc (fourierGL h3 hs)⁻¹ * diagTau hτ * fourierGL h3 hs
      = (fourierGL h3 hs)⁻¹ * (diagTau hτ * fourierGL h3 hs) := by group
    _ = ((fourierGL h3 hs)⁻¹ * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹) *
          (fourierGL h3 hs * cycThree) := by rw [e2]; group
    _ = _ := by rw [hsc]; group

include hs in
theorem fourierGL_conj_diagTau :
    fourierGL h3 hs * diagTau hτ * (fourierGL h3 hs)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree⁻¹ := by
  rw [fourierGL_mul_diagTau hτ hτ0 h3 hs]
  group

theorem phaseGL_conj_cycThree :
    phaseGL hτ * cycThree * (phaseGL hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (diagTau hτ * cycThree) := by
  rw [phaseGL_mul_cycThree hτ hτ0]
  group

theorem scalar_mul_cycThree_inv :
    GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cycThree : GL (Fin 3) F)⁻¹ =
      cycThree ^ 2 * diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) := by
  have hc3 := cycThree_pow_three (K := F)
  have hci : (cycThree : GL (Fin 3) F)⁻¹ = cycThree ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', hc3]
  have hsd : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) =
      diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagUnits]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hci, ← hsd, (commute_scalar (Units.mk0 τ hτ0) (cycThree ^ 2 : GL (Fin 3) F)).eq]

end Conj

theorem exists_twist_torus_model (hf : Odd f) (ρ : F ≃+* F) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x)
    (hρω : ∀ x : F, x ^ 3 = 1 → ρ x = x) {m : ℕ} (hm : Nat.Coprime m 3) {lam : Fˣ}
    (hlm : lam ^ m = 1) (hlN : hU.norm (lam : F) = 1) (hρl : ρ lam ≠ lam)
    {E R : Subgroup (unitaryPSU hU 3)} {z : unitaryPSU hU 3}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEs : ∀ x ∈ E, psuField hU ρ x = x) (hz : z ∈ E) (hz1 : z ≠ 1)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set (unitaryPSU hU 3))))
    (hRz : ∀ r ∈ R, r * z = z * r) (hR3 : ¬ 3 ∣ Nat.card R)
    (hRs : ∀ r ∈ R, psuField hU ρ r = r) (hRE : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R)
    (hER : ∃ e ∈ E, ∃ r ∈ R, e * r ≠ r * e) :
    ∃ A : Subgroup (unitaryPSU hU 3), ¬ 3 ∣ Nat.card A ∧
      (∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ ∈ A) ∧ (∀ a ∈ A, psuField hU ρ a ∈ A) ∧
      (∀ a ∈ A, a * z = z * a → a = 1) ∧
      ∃ u ∈ A, u ≠ 1 ∧ psuField hU ρ (z * u * z⁻¹) = u := by
  have hK : PiField false 2 f F := ⟨Nat.prime_two, hU.one_le, hU.card_eq_sq⟩
  have hq : ModThree false (2 ^ f) := two_pow_mod_three_of_odd_ftU hf
  obtain ⟨τ, hτ, hτ1, zh, g₀, rfl, hg₀, hg₀z⟩ := exists_frame_of_odd hf (hE3 z hz) hz1 hodd
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h3 := three_ne_zero_of_unitary hU
  have hs := one_add_tau_add_sq hτ hτ1
  have hρτ : ρ τ = τ := hρω τ hτ
  have hR3' : ∀ r ∈ R, Nat.Coprime 3 (orderOf r) := fun r hr =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
      hR3 (h.trans (Subgroup.orderOf_dvd_natCard R hr))
  have hR1 : ∃ r ∈ R, r ≠ 1 := by
    obtain ⟨e, -, r, hr, her⟩ := hER
    exact ⟨r, hr, fun h => her (by rw [h, mul_one, one_mul])⟩
  obtain ⟨x, hx, xh, hxh, hxz⟩ : ∃ x ∈ E, ∃ xh : unitarySU 2 f F 3, unitaryProj hU 3 xh = x ∧
      ¬ (xh : GL (Fin 3) F) * zh = zh * xh := by
    by_contra hno
    push Not at hno
    obtain ⟨e, he, r, hr, her⟩ := hER
    apply her
    obtain ⟨eh, rfl⟩ := unitaryProj_surjective hU 3 e
    obtain ⟨rh, rfl, hrhm⟩ := exists_lift_pow_eq_one (hR3' _ hr)
    have hrz := congrArg Subtype.val (commute_of_unitaryProj_commute (hR3' _ hr) hrhm (hRz _ hr))
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at hrz
    have hez := hno _ he eh rfl
    have hdiag : ∀ M : GL (Fin 3) F, M * zh = zh * M →
        (g₀⁻¹ * M * g₀) * diagTau hτ = diagTau hτ * (g₀⁻¹ * M * g₀) := by
      intro M hM
      rw [← hg₀z]
      calc g₀⁻¹ * M * g₀ * (g₀⁻¹ * (zh : GL (Fin 3) F) * g₀) = g₀⁻¹ * (M * zh) * g₀ := by group
        _ = g₀⁻¹ * ((zh : GL (Fin 3) F) * M) * g₀ := by rw [hM]
        _ = g₀⁻¹ * (zh : GL (Fin 3) F) * g₀ * (g₀⁻¹ * M * g₀) := by group
    obtain ⟨a₁, b₁, c₁, h₁⟩ := Ronan148V.eq_diagUnits_of_commute_diagTau hτ hτ1 (hdiag _ hez)
    obtain ⟨a₂, b₂, c₂, h₂⟩ := Ronan148V.eq_diagUnits_of_commute_diagTau hτ hτ1 (hdiag _ hrz)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have hcomm : (g₀⁻¹ * (eh : GL (Fin 3) F) * g₀) * (g₀⁻¹ * rh * g₀) =
        (g₀⁻¹ * (rh : GL (Fin 3) F) * g₀) * (g₀⁻¹ * eh * g₀) := by
      rw [h₁, h₂, diagUnits_comm]
    calc (eh : GL (Fin 3) F) * rh = g₀ * ((g₀⁻¹ * (eh : GL (Fin 3) F) * g₀) *
          (g₀⁻¹ * rh * g₀)) * g₀⁻¹ := by group
      _ = g₀ * ((g₀⁻¹ * (rh : GL (Fin 3) F) * g₀) * (g₀⁻¹ * eh * g₀)) * g₀⁻¹ := by rw [hcomm]
      _ = (rh : GL (Fin 3) F) * eh := by group
  obtain ⟨μ, hμ⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) (A := zh) (B := xh * zh * xh⁻¹)
    (by rw [map_mul, map_mul, map_inv, hxh, hEc x hx _ hz, mul_inv_cancel_right])
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hμ
  have hμ3 : μ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hμ
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (commute_scalar u A).eq
  have hzx : (zh : GL (Fin 3) F) * xh * (zh : GL (Fin 3) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * xh := by
    have e1 : (xh : GL (Fin 3) F) * zh = GeneralLinearGroup.scalar (Fin 3) μ * zh * xh := by
      rw [← hμ]; group
    calc (zh : GL (Fin 3) F) * xh * (zh : GL (Fin 3) F)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * zh * xh) *
          (zh : GL (Fin 3) F)⁻¹ := by rw [map_inv]; group
      _ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (xh * zh) * (zh : GL (Fin 3) F)⁻¹ := by rw [e1]
      _ = _ := by group
  have hμ1 : (μ⁻¹ : Fˣ) ≠ 1 := by
    intro h
    apply hxz
    rw [inv_eq_one] at h
    rw [h, map_one, one_mul] at hμ
    calc (xh : GL (Fin 3) F) * zh = xh * zh * (xh : GL (Fin 3) F)⁻¹ * xh := by group
      _ = zh * xh := by rw [hμ]
  have hμ3' : ((μ⁻¹ : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hμ3, inv_one, Units.val_one]
  obtain ⟨y₂, hy₂E, ζ, hζτ, hζ⟩ : ∃ y₂ : unitarySU 2 f F 3, unitaryProj hU 3 y₂ ∈ E ∧
      ∃ ζ : Fˣ, (ζ : F) = τ ∧
        (zh : GL (Fin 3) F) * y₂ * (zh : GL (Fin 3) F)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) ζ * y₂ := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hμ3' with h | h | h
    · exact absurd (Units.ext h) hμ1
    · exact ⟨xh, hxh ▸ hx, μ⁻¹, h, hzx⟩
    · refine ⟨xh⁻¹, by rw [map_inv, hxh]; exact inv_mem hx, μ, ?_, ?_⟩
      · have : (μ : F) = ((μ⁻¹ : Fˣ) : F)⁻¹ := by rw [Units.val_inv_eq_inv_val, inv_inv]
        rw [this, h]
        calc (τ ^ 2)⁻¹ = (τ ^ 2)⁻¹ * τ ^ 3 := by rw [hτ, mul_one]
          _ = τ := by field_simp
      · rw [Subgroup.coe_inv]
        calc (zh : GL (Fin 3) F) * (xh : GL (Fin 3) F)⁻¹ * (zh : GL (Fin 3) F)⁻¹ =
            ((zh : GL (Fin 3) F) * xh * (zh : GL (Fin 3) F)⁻¹)⁻¹ := by group
          _ = (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * xh)⁻¹ := by rw [hzx]
          _ = _ := by rw [_root_.mul_inv_rev, map_inv, inv_inv, hsc]
  obtain ⟨g, hgH, hgy, hgz⟩ := exists_heis_normal_form hK hq hτ hτ1 (y₁ := zh) (y₂ := y₂)
    (g₁ := g₀) (z₁ := 1) y₂.2 ((mem_glPi_false hU).mpr hg₀) (one_mem _)
    (by rw [mul_one]; exact hg₀z) hζτ hζ
  rw [mul_one] at hgz
  have hg : g ∈ unitaryIsom3 hU := (mem_glPi_false hU).mp hgH
  have hΦ := fourierGL_mem_unitarySU hU hf hτ h3 hs
  have hΦU := unitarySU_le_unitaryIsom3 (h := hU) hΦ
  have hT := phaseGL_mem_unitaryIsom3 hU hf hτ
  have hd := diagTau_mem_unitarySU hU hf hτ
  have hρΦ : glAut ρ (fourierGL h3 hs) = fourierGL h3 hs := glAut_fourierGL ρ h3 hs hρτ
  have hρT : glAut ρ (phaseGL hτ) = phaseGL hτ := glAut_phaseGL ρ hτ hρτ
  set Φ := fourierGL h3 hs with hΦdef
  set T := phaseGL hτ with hTdef
  set N := g⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * g) with hNdef
  have hzhg : (zh : GL (Fin 3) F) = g * diagTau hτ * g⁻¹ := by rw [← hgz]; group
  have hy₂g : (y₂ : GL (Fin 3) F) = g * cycThree * g⁻¹ := by rw [← hgy]; group
  set Mz : unitarySU 2 f F 3 := ⟨Φ * diagTau hτ * Φ⁻¹, conj_mem_unitarySU hΦU hd⟩ with hMzdef
  have hMz : (Mz : GL (Fin 3) F) = cycThree ^ 2 *
      diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) (Units.mk0 τ hτ0) := by
    change Φ * diagTau hτ * Φ⁻¹ = _
    rw [hΦdef, fourierGL_conj_diagTau hτ hτ0 h3 hs, scalar_mul_cycThree_inv hτ0]
  have hΦd := fourierGL_inv_conj_diagTau hτ hτ0 h3 hs
  rw [← hΦdef] at hΦd
  by_cases h2 : N * cycThree = cycThree * N
  · by_cases h1 : N * diagTau hτ = diagTau hτ * N
    ·
      obtain ⟨a, ha⟩ := eq_scalar_of_commute_diagTau_cycThree hτ hτ1 h1 h2
      exact split_case hf ρ hρω hτ hτ1 hg hgz hgy hEc hEs hz hy₂E hRz hR3 hRs hRE hR1 ha
    ·
      have hW : g * T * Φ⁻¹ ∈ unitaryIsom3 hU := mul_mem (mul_mem hg hT) (inv_mem hΦU)
      refine nonsplit_case hf ρ hρ3 hρω hm hlm hlN hρl hτ hτ1 hEc hEs hz hW ?_ (Mz := Mz) ?_ hMz ?_
      ·
        have hb : psuConj hU ⟨_, hW⟩ (dPSU hτ hU hf) = unitaryProj hU 3 (zh * y₂) := by
          rw [dPSU, ← unitaryProj_eq_mk, psuConj_unitaryProj']
          refine unitaryProj_eq_of_coe_eq_scalar_mul
            (κ := (Units.mk0 τ hτ0 ^ 2)⁻¹ * Units.mk0 τ hτ0) ?_
          change g * T * Φ⁻¹ * diagTau hτ * (g * T * Φ⁻¹)⁻¹ = _ * ((zh : GL (Fin 3) F) * y₂)
          have hTc := phaseGL_conj_cycThree hτ hτ0
          rw [← hTdef] at hTc
          rw [hzhg, hy₂g]
          calc g * T * Φ⁻¹ * diagTau hτ * (g * T * Φ⁻¹)⁻¹ =
              g * (T * (Φ⁻¹ * diagTau hτ * Φ) * T⁻¹) * g⁻¹ := by group
            _ = g * (T * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * cycThree) *
                T⁻¹) * g⁻¹ := by rw [hΦd]
            _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ *
                (g * (T * cycThree * T⁻¹) * g⁻¹) := by
              rw [conj_scalar_mul', conj_scalar_mul']
            _ = _ := by
              rw [hTc, conj_scalar_mul', map_mul]
              group
        rw [hb, map_mul]
        exact mul_mem hz hy₂E
      · change g * T * Φ⁻¹ * (Φ * diagTau hτ * Φ⁻¹) * (g * T * Φ⁻¹)⁻¹ = zh
        rw [hzhg]
        have hTd := phaseGL_mul_diagTau hτ
        rw [← hTdef] at hTd
        calc g * T * Φ⁻¹ * (Φ * diagTau hτ * Φ⁻¹) * (g * T * Φ⁻¹)⁻¹ =
            g * (T * diagTau hτ) * T⁻¹ * g⁻¹ := by group
          _ = g * diagTau hτ * g⁻¹ := by rw [hTd]; group
      ·
        intro hcomm
        apply h1
        have hNW : (g * T * Φ⁻¹)⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * (g * T * Φ⁻¹)) =
            (T * Φ⁻¹)⁻¹ * N * (T * Φ⁻¹) := by
          rw [hNdef, show (zh : GL (Fin 3) F) * (g * T * Φ⁻¹) = ((zh : GL (Fin 3) F) * g) *
            (T * Φ⁻¹) by group]
          simp only [map_mul, map_inv, hρT, hρΦ]
          group
        rw [hNW, commute_conj_iff] at hcomm
        have hYd : T * Φ⁻¹ * diagTau hτ * (T * Φ⁻¹)⁻¹ =
            GeneralLinearGroup.scalar (Fin 3) ((Units.mk0 τ hτ0 ^ 2)⁻¹ * Units.mk0 τ hτ0) *
              (diagTau hτ * cycThree) := by
          have hTc := phaseGL_conj_cycThree hτ hτ0
          rw [← hTdef] at hTc
          calc T * Φ⁻¹ * diagTau hτ * (T * Φ⁻¹)⁻¹ = T * (Φ⁻¹ * diagTau hτ * Φ) * T⁻¹ := by
                group
            _ = T * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * cycThree) *
                T⁻¹ := by rw [hΦd]
            _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ *
                (T * cycThree * T⁻¹) := by rw [conj_scalar_mul']
            _ = _ := by rw [hTc, map_mul]; group
        rw [hYd, commute_scalar_mul_iff] at hcomm
        calc N * diagTau hτ = N * (diagTau hτ * cycThree) * cycThree⁻¹ := by group
          _ = diagTau hτ * cycThree * N * cycThree⁻¹ := by rw [hcomm]
          _ = diagTau hτ * (cycThree * N) * cycThree⁻¹ := by group
          _ = diagTau hτ * (N * cycThree) * cycThree⁻¹ := by rw [h2]
          _ = diagTau hτ * N := by group
  ·
    have hW : g * Φ⁻¹ ∈ unitaryIsom3 hU := mul_mem hg (inv_mem hΦU)
    refine nonsplit_case hf ρ hρ3 hρω hm hlm hlN hρl hτ hτ1 hEc hEs hz hW ?_ (Mz := Mz) ?_ hMz ?_
    · have hb : psuConj hU ⟨_, hW⟩ (dPSU hτ hU hf) = unitaryProj hU 3 y₂ := by
        rw [dPSU, ← unitaryProj_eq_mk, psuConj_unitaryProj']
        refine unitaryProj_eq_of_coe_eq_scalar_mul (κ := (Units.mk0 τ hτ0 ^ 2)⁻¹) ?_
        change g * Φ⁻¹ * diagTau hτ * (g * Φ⁻¹)⁻¹ = _ * (y₂ : GL (Fin 3) F)
        rw [hy₂g]
        calc g * Φ⁻¹ * diagTau hτ * (g * Φ⁻¹)⁻¹ = g * (Φ⁻¹ * diagTau hτ * Φ) * g⁻¹ := by group
          _ = g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * cycThree) * g⁻¹ := by
              rw [hΦd]
          _ = _ := by rw [conj_scalar_mul']
      rw [hb]
      exact hy₂E
    · change g * Φ⁻¹ * (Φ * diagTau hτ * Φ⁻¹) * (g * Φ⁻¹)⁻¹ = zh
      rw [hzhg]
      group
    · intro hcomm
      apply h2
      have hNW : (g * Φ⁻¹)⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * (g * Φ⁻¹)) = (Φ⁻¹)⁻¹ * N * Φ⁻¹ := by
        rw [hNdef, show (zh : GL (Fin 3) F) * (g * Φ⁻¹) = ((zh : GL (Fin 3) F) * g) * Φ⁻¹ by group]
        simp only [map_mul, map_inv, hρΦ]
        group
      rw [hNW, commute_conj_iff, inv_inv, hΦd, commute_scalar_mul_iff] at hcomm
      exact hcomm

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
