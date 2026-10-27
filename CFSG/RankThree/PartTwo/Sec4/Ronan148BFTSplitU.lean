module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTFrameU

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F] {hU : UnitaryFieldData 2 f F}

theorem unitaryProj_eq_of_coe_eq_scalar_mul {M M' : unitarySU 2 f F 3} {κ : Fˣ}
    (h : (M' : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) κ * M) :
    unitaryProj hU 3 M' = unitaryProj hU 3 M := by
  have h1 : unitaryProj hU 3 (M' * M⁻¹) = 1 := by
    apply Ronan148V.unitaryProj_eq_one_of_scalar hU
    refine ⟨κ, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h, mul_inv_cancel_right]
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem psuConj_scalar {a : Fˣ} (ha : GeneralLinearGroup.scalar (Fin 3) a ∈ unitaryIsom3 hU)
    (x : unitaryPSU hU 3) : psuConj hU ⟨_, ha⟩ x = x := by
  induction x using QuotientGroup.induction_on with
  | H M =>
    rw [psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suConj]
    change GeneralLinearGroup.scalar (Fin 3) a * (M : GL (Fin 3) F) *
      (GeneralLinearGroup.scalar (Fin 3) a)⁻¹ = M
    rw [← (commute_scalar a (M : GL (Fin 3) F)).eq, mul_inv_cancel_right]

theorem psuConj_unitaryProj' {A : GL (Fin 3) F} (hA : A ∈ unitaryIsom3 hU)
    (M : unitarySU 2 f F 3) :
    psuConj hU ⟨A, hA⟩ (unitaryProj hU 3 M) =
      unitaryProj hU 3 ⟨A * M * A⁻¹, conj_mem_unitarySU hA M.2⟩ := by
  rw [unitaryProj_eq_mk, psuConj_mk]
  rfl

theorem psuField_unitaryProj (ρ : F ≃+* F) (M : unitarySU 2 f F 3) :
    psuField hU ρ (unitaryProj hU 3 M) =
      unitaryProj hU 3 ⟨glAut ρ M, glAut_mem_unitarySU hU ρ M.2⟩ := by
  rw [unitaryProj_eq_mk, psuField_mk]
  rfl

theorem eq_scalar_of_commute_diagTau_cycThree {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) F} (h1 : M * diagTau hτ = diagTau hτ * M) (h2 : M * cycThree = cycThree * M) :
    ∃ a : Fˣ, M = GeneralLinearGroup.scalar (Fin 3) a := by
  obtain ⟨a, b, e, rfl⟩ := Ronan148V.eq_diagUnits_of_commute_diagTau hτ hτ1 h1
  have h3 : diagUnits b e a = diagUnits a b e := by
    rw [← cycThree_inv_conj_diagUnits, mul_assoc, h2]
    group
  have hent := fun i => congrFun (congrFun (congrArg (fun g : GL (Fin 3) F =>
    (g : Matrix (Fin 3) (Fin 3) F)) h3) i) i
  have e0 := hent 0
  have e1 := hent 1
  simp only [coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at e0 e1
  refine ⟨a, Units.ext ?_⟩
  rw [coe_diagUnits, GeneralLinearGroup.coe_scalar, scalar_apply]
  congr 1
  funext i
  fin_cases i <;> simp [e0, e1]

theorem three_ne_zero_of_unitary (hU : UnitaryFieldData 2 f F) : (3 : F) ≠ 0 := by
  have : CharP F 2 := hU.charP
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  intro h
  apply one_ne_zero (α := F)
  linear_combination h - h2

theorem eq_one_of_commute_heis {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) F}
    {zh y₂ : unitarySU 2 f F 3} (hgz : g⁻¹ * (zh : GL (Fin 3) F) * g = diagTau hτ)
    (hgy : g⁻¹ * (y₂ : GL (Fin 3) F) * g = cycThree) {r : unitaryPSU hU 3}
    (hr3 : Nat.Coprime 3 (orderOf r)) (hrz : r * unitaryProj hU 3 zh = unitaryProj hU 3 zh * r)
    (hry : r * unitaryProj hU 3 y₂ = unitaryProj hU 3 y₂ * r) : r = 1 := by
  obtain ⟨rh, hrh, hrhm⟩ := exists_lift_pow_eq_one hr3
  rw [← hrh] at hrz hry
  have h1 := commute_of_unitaryProj_commute hr3 hrhm hrz
  have h2 := commute_of_unitaryProj_commute hr3 hrhm hry
  have hd : (g⁻¹ * (rh : GL (Fin 3) F) * g) * diagTau hτ =
      diagTau hτ * (g⁻¹ * (rh : GL (Fin 3) F) * g) := by
    rw [← hgz]
    have := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
    calc g⁻¹ * (rh : GL (Fin 3) F) * g * (g⁻¹ * (zh : GL (Fin 3) F) * g) =
        g⁻¹ * ((rh : GL (Fin 3) F) * zh) * g := by
          group
      _ = g⁻¹ * ((zh : GL (Fin 3) F) * rh) * g := by rw [this]
      _ = g⁻¹ * (zh : GL (Fin 3) F) * g * (g⁻¹ * (rh : GL (Fin 3) F) * g) := by group
  have hc : (g⁻¹ * (rh : GL (Fin 3) F) * g) * cycThree =
      cycThree * (g⁻¹ * (rh : GL (Fin 3) F) * g) := by
    rw [← hgy]
    have := congrArg Subtype.val h2
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
    calc g⁻¹ * (rh : GL (Fin 3) F) * g * (g⁻¹ * (y₂ : GL (Fin 3) F) * g) =
        g⁻¹ * ((rh : GL (Fin 3) F) * y₂) * g := by
          group
      _ = g⁻¹ * ((y₂ : GL (Fin 3) F) * rh) * g := by rw [this]
      _ = g⁻¹ * (y₂ : GL (Fin 3) F) * g * (g⁻¹ * (rh : GL (Fin 3) F) * g) := by group
  obtain ⟨a, ha⟩ := eq_scalar_of_commute_diagTau_cycThree hτ hτ1 hd hc
  rw [← hrh]
  apply Ronan148V.unitaryProj_eq_one_of_scalar hU
  refine ⟨a, ?_⟩
  calc GeneralLinearGroup.scalar (Fin 3) a = g * GeneralLinearGroup.scalar (Fin 3) a * g⁻¹ := by
        rw [(commute_scalar a g).eq.symm.symm]; group
    _ = (rh : GL (Fin 3) F) := by rw [← ha]; group

theorem split_case (hf : Odd f) (ρ : F ≃+* F) (hρω : ∀ x : F, x ^ 3 = 1 → ρ x = x)
    {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {g : GL (Fin 3) F} (hg : g ∈ unitaryIsom3 hU) {zh y₂ : unitarySU 2 f F 3}
    (hgz : g⁻¹ * (zh : GL (Fin 3) F) * g = diagTau hτ)
    (hgy : g⁻¹ * (y₂ : GL (Fin 3) F) * g = cycThree)
    {E R : Subgroup (unitaryPSU hU 3)}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEs : ∀ x ∈ E, psuField hU ρ x = x)
    (hzE : unitaryProj hU 3 zh ∈ E) (hxE : unitaryProj hU 3 y₂ ∈ E)
    (hRz : ∀ r ∈ R, r * unitaryProj hU 3 zh = unitaryProj hU 3 zh * r) (hR3 : ¬ 3 ∣ Nat.card R)
    (hRs : ∀ r ∈ R, psuField hU ρ r = r) (hRE : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R)
    (hR1 : ∃ r ∈ R, r ≠ 1) {a : Fˣ}
    (hN : g⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * g) = GeneralLinearGroup.scalar (Fin 3) a) :
    ∃ A : Subgroup (unitaryPSU hU 3), ¬ 3 ∣ Nat.card A ∧
      (∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) ∧ (∀ x ∈ A, psuField hU ρ x ∈ A) ∧
      (∀ x ∈ A, x * unitaryProj hU 3 zh = unitaryProj hU 3 zh * x → x = 1) ∧
      ∃ u ∈ A, u ≠ 1 ∧ psuField hU ρ (unitaryProj hU 3 zh * u * (unitaryProj hU 3 zh)⁻¹) = u := by
  have h3 := three_ne_zero_of_unitary hU
  have hs := one_add_tau_add_sq hτ hτ1
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hρτ : ρ τ = τ := hρω τ hτ
  set Φ := fourierGL h3 hs with hΦdef
  have hΦ : Φ ∈ unitarySU 2 f F 3 := fourierGL_mem_unitarySU hU hf hτ h3 hs
  have hd : diagTau hτ ∈ unitarySU 2 f F 3 := diagTau_mem_unitarySU hU hf hτ
  have hc : (cycThree : GL (Fin 3) F) ∈ unitarySU 2 f F 3 := cycThree_mem_unitarySU hU
  set Φs : unitarySU 2 f F 3 := ⟨Φ, hΦ⟩ with hΦs
  set ds : unitarySU 2 f F 3 := ⟨diagTau hτ, hd⟩ with hds
  set cs : unitarySU 2 f F 3 := ⟨cycThree, hc⟩ with hcs
  set Γ := psuConj hU ⟨g, hg⟩ with hΓ
  set z := unitaryProj hU 3 zh with hz
  set x₂ := unitaryProj hU 3 y₂ with hx₂
  set y : unitaryPSU hU 3 := Γ (unitaryProj hU 3 Φs) with hy
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (commute_scalar u A).eq
  have hzΓ : z = Γ (unitaryProj hU 3 ds) := by
    rw [hz, hΓ, psuConj_unitaryProj']
    congr 1
    apply Subtype.ext
    change (zh : GL (Fin 3) F) = g * diagTau hτ * g⁻¹
    rw [← hgz]
    group
  have hxΓ : x₂ = Γ (unitaryProj hU 3 cs) := by
    rw [hx₂, hΓ, psuConj_unitaryProj']
    congr 1
    apply Subtype.ext
    change (y₂ : GL (Fin 3) F) = g * cycThree * g⁻¹
    rw [← hgy]
    group
  have hR1' : unitaryProj hU 3 (Φs⁻¹ * ds * Φs) = unitaryProj hU 3 cs := by
    refine unitaryProj_eq_of_coe_eq_scalar_mul (κ := (Units.mk0 τ hτ0 ^ 2)⁻¹) ?_
    have e := fourierGL_mul_cycThree hτ hτ0 h3 hs
    rw [← hΦdef] at e
    change Φ⁻¹ * diagTau hτ * Φ = _ * cycThree
    have e2 : diagTau hτ * Φ =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * (Φ * cycThree) := by
      rw [e, map_inv]
      group
    calc Φ⁻¹ * diagTau hτ * Φ = Φ⁻¹ * (diagTau hτ * Φ) := by group
      _ = Φ⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ * (Φ * cycThree)) := by
          rw [e2]
      _ = (Φ⁻¹ * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹) * (Φ * cycThree) := by
          group
      _ = _ := by rw [hsc]; group
  have hR2' : unitaryProj hU 3 (Φs⁻¹ * cs * Φs) = unitaryProj hU 3 ds⁻¹ := by
    refine unitaryProj_eq_of_coe_eq_scalar_mul (κ := Units.mk0 τ hτ0) ?_
    have e := fourierGL_mul_diagTau hτ hτ0 h3 hs
    rw [← hΦdef] at e
    change Φ⁻¹ * cycThree * Φ = _ * (diagTau hτ)⁻¹
    have e2 : cycThree * Φ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) *
        (Φ * (diagTau hτ)⁻¹) := by
      have e3 : cycThree⁻¹ * Φ = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0))⁻¹ *
          (Φ * diagTau hτ) := by rw [e]; group
      calc cycThree * Φ = cycThree * (Φ * diagTau hτ) * (diagTau hτ)⁻¹ := by group
        _ = cycThree * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) *
            (cycThree⁻¹ * Φ)) * (diagTau hτ)⁻¹ := by rw [e3]; group
        _ = (cycThree * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0)) *
            (cycThree⁻¹ * Φ) * (diagTau hτ)⁻¹ := by group
        _ = _ := by rw [hsc]; group
    calc Φ⁻¹ * cycThree * Φ = Φ⁻¹ * (cycThree * Φ) := by group
      _ = Φ⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) *
          (Φ * (diagTau hτ)⁻¹)) := by rw [e2]
      _ = (Φ⁻¹ * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0)) *
          (Φ * (diagTau hτ)⁻¹) := by group
      _ = _ := by rw [hsc]; group
  have hyz : y⁻¹ * z * y = x₂ := by
    rw [hzΓ, hxΓ, hy, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hR1']
  have hyx : y⁻¹ * x₂ * y = z⁻¹ := by
    rw [hzΓ, hxΓ, hy, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hR2',
      map_inv, map_inv]
  have hNmem : g⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * g) ∈ unitaryIsom3 hU := mul_mem (inv_mem hg)
    (glAut_mem_unitaryIsom3 ρ (mul_mem (unitarySU_le_unitaryIsom3 zh.2) hg))
  have hfΦ : psuField hU ρ (unitaryProj hU 3 Φs) = unitaryProj hU 3 Φs := by
    rw [psuField_unitaryProj]
    congr 1
    exact Subtype.ext (glAut_fourierGL ρ h3 hs hρτ)
  have hθy : psuField hU ρ (z * y * z⁻¹) = y := by
    have h1 := twist_frame (hU := hU) ρ hg zh (unitaryProj hU 3 Φs)
    rw [← unitaryProj_eq_mk] at h1
    rw [hy, h1, hfΦ]
    have hNs : (⟨_, hNmem⟩ : unitaryIsom3 hU) = ⟨GeneralLinearGroup.scalar (Fin 3) a,
        hN ▸ hNmem⟩ := Subtype.ext hN
    rw [hNs, psuConj_scalar]
  have hρg : g⁻¹ * glAut ρ g = GeneralLinearGroup.scalar (Fin 3) a * (diagTau hτ)⁻¹ := by
    have hzg : (zh : GL (Fin 3) F) * g = g * diagTau hτ := by rw [← hgz]; group
    have e1 : glAut ρ ((zh : GL (Fin 3) F) * g) = glAut ρ g * diagTau hτ := by
      rw [hzg, map_mul, glAut_diagTau ρ hτ hρτ]
    rw [e1, ← mul_assoc] at hN
    calc g⁻¹ * glAut ρ g = (g⁻¹ * glAut ρ g * diagTau hτ) * (diagTau hτ)⁻¹ := by group
      _ = _ := by rw [hN]
  have hsy : psuField hU ρ y = z⁻¹ * y * z := by
    have hMmem := inv_mul_glAut_mem (hU := hU) ρ hg
    rw [hy, psuField_frame ρ hg, hfΦ, psuConj_unitaryProj', hzΓ, ← map_inv, ← map_mul,
      ← map_mul]
    congr 1
    refine unitaryProj_eq_of_coe_eq_scalar_mul (κ := 1) ?_
    change (g⁻¹ * glAut ρ g) * Φ * (g⁻¹ * glAut ρ g)⁻¹ = _ * ((diagTau hτ)⁻¹ * Φ * diagTau hτ)
    rw [hρg, map_one, one_mul]
    have hcomm : ∀ X : GL (Fin 3) F, GeneralLinearGroup.scalar (Fin 3) a * X *
        (GeneralLinearGroup.scalar (Fin 3) a)⁻¹ = X := fun X => by
      rw [← hsc a X, mul_inv_cancel_right]
    calc GeneralLinearGroup.scalar (Fin 3) a * (diagTau hτ)⁻¹ * Φ *
          (GeneralLinearGroup.scalar (Fin 3) a * (diagTau hτ)⁻¹)⁻¹
        = GeneralLinearGroup.scalar (Fin 3) a * ((diagTau hτ)⁻¹ * Φ * diagTau hτ) *
            (GeneralLinearGroup.scalar (Fin 3) a)⁻¹ := by group
      _ = _ := hcomm _
  have hyE : ∀ e ∈ E, y⁻¹ * e * y ∈ E := by
    intro e he
    obtain ⟨Me, hMe⟩ := unitaryProj_surjective hU 3 (Γ⁻¹ e)
    have heΓ : e = Γ (unitaryProj hU 3 Me) := by rw [hMe, MulAut.apply_inv_self]
    have hcz : unitaryProj hU 3 (Me * ds * Me⁻¹) = unitaryProj hU 3 ds := by
      apply Γ.injective
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← heΓ, ← hzΓ,
        hEc e he z hzE, mul_inv_cancel_right]
    have hcx : unitaryProj hU 3 (Me * cs * Me⁻¹) = unitaryProj hU 3 cs := by
      apply Γ.injective
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← heΓ, ← hxΓ,
        hEc e he x₂ hxE, mul_inv_cancel_right]
    obtain ⟨ζ₁, hζ₁⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) hcz.symm
    obtain ⟨ζ₂, hζ₂⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) hcx.symm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hζ₁ hζ₂
    obtain ⟨k, j, μ, hμ⟩ := exists_eq_scalar_mul_cycThree_pow_diagTau hτ hτ1 hζ₁ hζ₂
    have hMe' : unitaryProj hU 3 Me = unitaryProj hU 3 cs ^ k * unitaryProj hU 3 ds ^ j := by
      rw [← map_pow, ← map_pow, ← map_mul]
      refine unitaryProj_eq_of_coe_eq_scalar_mul (κ := μ) ?_
      rw [hμ]
      rfl
    have hconj : y⁻¹ * e * y = (z⁻¹) ^ k * x₂ ^ j := by
      have h1 : y⁻¹ * e * y = MulAut.conj y⁻¹ e := by rw [MulAut.conj_apply, inv_inv]
      have h2 : MulAut.conj y⁻¹ z = x₂ := by rw [MulAut.conj_apply, inv_inv, hyz]
      have h3' : MulAut.conj y⁻¹ x₂ = z⁻¹ := by rw [MulAut.conj_apply, inv_inv, hyx]
      rw [h1, heΓ, hMe', map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, ← hxΓ, ← hzΓ,
        h2, h3']
    rw [hconj]
    exact mul_mem (pow_mem (inv_mem hzE) k) (pow_mem hxE j)
  set A : Subgroup (unitaryPSU hU 3) := R.map (MulAut.conj y).toMonoidHom with hA
  have hmemA : ∀ x, x ∈ A ↔ y⁻¹ * x * y ∈ R := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      change y⁻¹ * (y * r * y⁻¹) * y ∈ R
      rwa [show y⁻¹ * (y * r * y⁻¹) * y = r by group]
    · intro h
      exact ⟨_, h, by change y * (y⁻¹ * x * y) * y⁻¹ = x; group⟩
  have hEA : ∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A := by
    intro e he x hx
    rw [hmemA] at hx ⊢
    have := hRE _ (hyE e he) _ hx
    rwa [show y⁻¹ * e * y * (y⁻¹ * x * y) * (y⁻¹ * e * y)⁻¹ = y⁻¹ * (e * x * e⁻¹) * y by group]
      at this
  refine ⟨A, ?_, hEA, ?_, ?_, ?_⟩
  · rw [hA, Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hR3
  ·
    intro x hx
    rw [hmemA] at hx
    have hx' : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    set r := y⁻¹ * x * y with hr
    have hrz := hRz r hx
    have hfx : psuField hU ρ x = z⁻¹ * x * z := by
      rw [hx', map_mul, map_mul, map_inv, hsy, hRs r hx]
      calc z⁻¹ * y * z * r * (z⁻¹ * y * z)⁻¹ = z⁻¹ * y * (z * r * z⁻¹) * y⁻¹ * z := by group
        _ = z⁻¹ * (y * r * y⁻¹) * z := by rw [← hrz, mul_inv_cancel_right]; group
    rw [hfx]
    have := hEA z⁻¹ (inv_mem hzE) x (by rw [hmemA]; exact hx)
    rwa [inv_inv] at this
  ·
    intro x hx hxz
    rw [hmemA] at hx
    set r := y⁻¹ * x * y with hr
    have hr3 : Nat.Coprime 3 (orderOf r) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3' => hR3 ?_
      exact h3'.trans (Subgroup.orderOf_dvd_natCard R hx)
    have hrx : r * x₂ = x₂ * r := by
      rw [← hyz]
      calc y⁻¹ * x * y * (y⁻¹ * z * y) = y⁻¹ * (x * z) * y := by group
        _ = y⁻¹ * (z * x) * y := by rw [hxz]
        _ = y⁻¹ * z * y * (y⁻¹ * x * y) := by group
    have hr1 := eq_one_of_commute_heis hτ hτ1 hgz hgy hr3 (hRz r hx) hrx
    calc x = y * r * y⁻¹ := by rw [hr]; group
      _ = 1 := by rw [hr1]; group
  ·
    obtain ⟨r, hr, hr1⟩ := hR1
    refine ⟨y * r * y⁻¹, ⟨r, hr, rfl⟩, fun h => hr1 ?_, ?_⟩
    · calc r = y⁻¹ * (y * r * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · have hrz := hRz r hr
      calc psuField hU ρ (z * (y * r * y⁻¹) * z⁻¹)
          = psuField hU ρ ((z * y * z⁻¹) * (z * r * z⁻¹) * (z * y * z⁻¹)⁻¹) := by congr 1; group
        _ = psuField hU ρ (z * y * z⁻¹) * psuField hU ρ (z * r * z⁻¹) *
            (psuField hU ρ (z * y * z⁻¹))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = y * r * y⁻¹ := by rw [hθy, ← hrz, mul_inv_cancel_right, hRs r hr]

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
