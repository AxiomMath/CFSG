module

public import CFSG.Quasithin.Background.SmithD39TwoSocle
public import CFSG.Quasithin.Background.SmithD39TwoMod

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

section Translate

theorem isInv_smul_of_comm {H : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥H Y) {x : Γ}
    (hx : ∀ h ∈ H, x * h = h * x) : XMod.IsInv ↥H (x • Y) := by
  intro h q hq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq ⊢
  have hx' : x⁻¹ * (h : Γ) = (h : Γ) * x⁻¹ := by
    have := hx h h.2
    calc x⁻¹ * (h : Γ) = x⁻¹ * ((h : Γ) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * (h : Γ)) * x⁻¹ := by rw [this]
      _ = (h : Γ) * x⁻¹ := by group
  change x⁻¹ • (h : Γ) • q ∈ Y
  rw [smul_smul, hx', mul_smul]
  exact hY h _ hq

theorem isIrr_smul_of_comm {H : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsIrr ↥H Y) {x : Γ}
    (hx : ∀ h ∈ H, x * h = h * x) : XMod.IsIrr ↥H (x • Y) := by
  have hx' : ∀ h ∈ H, x⁻¹ * h = h * x⁻¹ := by
    intro h hh
    have := hx h hh
    calc x⁻¹ * h = x⁻¹ * (h * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * h) * x⁻¹ := by rw [this]
      _ = h * x⁻¹ := by group
  refine ⟨isInv_smul_of_comm hY.1 hx, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : Y = ⊥ := by
      have := congrArg (fun J => x⁻¹ • J) h0
      simpa [smul_smul, Subgroup.smul_bot] using this
    exact hY.2.1.ne' h1
  · intro J hJ _ hJY
    have hJ' : XMod.IsInv ↥H (x⁻¹ • J) := isInv_smul_of_comm hJ hx'
    have hle : x⁻¹ • J ≤ Y := by
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := x⁻¹)).2 hJY
      simpa [inv_smul_smul] using this
    have hJeq : J = x • (x⁻¹ • J) := by rw [smul_inv_smul]
    rcases hY.2.2 (x⁻¹ • J) hJ' bot_le hle with h1 | h1
    · left
      rw [hJeq, h1, Subgroup.smul_bot]
    · right
      rw [hJeq, h1]

theorem inf_eq_bot_or_eq {A : Type*} [Group A] [MulDistribMulAction A Q] {Y Y' : Subgroup Q}
    (hY : XMod.IsIrr A Y) (hY' : XMod.IsIrr A Y') : Y ⊓ Y' = ⊥ ∨ Y = Y' := by
  rcases hY.2.2 (Y ⊓ Y') (hY.1.inf hY'.1) bot_le inf_le_left with h | h
  · exact Or.inl h
  · right
    have hle : Y ≤ Y' := h ▸ inf_le_right
    rcases hY'.2.2 Y hY.1 bot_le hle with h' | h'
    · exact absurd h' hY.2.1.ne'
    · exact h'

theorem iso_of_le_isoComp {A : Type*} [Group A] [MulDistribMulAction A Q] [Finite Q]
    {I J : Subgroup Q} (hJ : XMod.IsIrr A J) (hJI : J ≤ isoComp A I) : XMod.Iso A J I := by
  obtain ⟨⟨J', hJ', hJ'I⟩, hiso⟩ := exists_iso_of_le_iSup
    (S := fun J : {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I} => (J : Subgroup Q))
    (fun J => J.2.1) hJ hJI
  exact hiso.trans hJ'I

theorem card_eq_of_iso {A : Type*} [Group A] [MulDistribMulAction A Q] {Y Y' : Subgroup Q}
    (h : XMod.Iso A Y Y') : Nat.card ↥Y = Nat.card ↥Y' := by
  obtain ⟨φ, -⟩ := h
  exact Nat.card_congr φ.toEquiv

theorem nB_eq_of_iso [Finite Q] {H P : Subgroup Γ} (hPH : P ≤ H) {Y Y' : Subgroup Q}
    (hY : XMod.IsInv ↥H Y) (h : XMod.Iso ↥H Y Y') : nB P Y = nB P Y' := by
  have h' : XMod.Iso ↥H Y' Y := XMod.Iso.symm hY h
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  have hfix : ∀ {Z Z' : Subgroup Q} (χ : ↥Z →* ↥Z')
      (_ : ∀ (a : ↥H) (l l' : ↥Z), a • (l : Q) = (l' : Q) →
        a • ((χ l : ↥Z') : Q) = ((χ l' : ↥Z') : Q)) (y : ↥Z),
      (y : Q) ∈ XMod.fixed ↥P (⊤ : Subgroup Q) →
        ((χ y : ↥Z') : Q) ∈ XMod.fixed ↥P (⊤ : Subgroup Q) := by
    intro Z Z' χ hχ y hy
    refine ⟨trivial, fun p => ?_⟩
    exact hχ ⟨p, hPH p.2⟩ y y (hy.2 p)
  have hinj : ∀ {Z Z' : Subgroup Q} (χ : ↥Z →* ↥Z') (_ : Function.Injective χ)
      (_ : ∀ (y : ↥Z), (y : Q) ∈ XMod.fixed ↥P (⊤ : Subgroup Q) →
        ((χ y : ↥Z') : Q) ∈ XMod.fixed ↥P (⊤ : Subgroup Q)),
      Nat.card ↥(Z ⊓ XMod.fixed ↥P (⊤ : Subgroup Q)) ≤
        Nat.card ↥(Z' ⊓ XMod.fixed ↥P (⊤ : Subgroup Q)) := by
    intro Z Z' χ hχ hfx
    refine Nat.card_le_card_of_injective
      (fun y => ⟨(χ ⟨y.1, y.2.1⟩ : Q), (χ _).2, hfx ⟨y.1, y.2.1⟩ y.2.2⟩) ?_
    intro y y' hyy
    have h0 : ((χ ⟨y.1, y.2.1⟩ : ↥Z') : Q) = ((χ ⟨y'.1, y'.2.1⟩ : ↥Z') : Q) :=
      congrArg (fun z : ↥(Z' ⊓ XMod.fixed ↥P (⊤ : Subgroup Q)) => (z : Q)) hyy
    have h1 : χ ⟨y.1, y.2.1⟩ = χ ⟨y'.1, y'.2.1⟩ := Subtype.ext h0
    exact Subtype.ext (congrArg (fun z : ↥Z => (z : Q)) (hχ h1))
  have h1 := hinj φ.toMonoidHom φ.injective (hfix φ.toMonoidHom hφ)
  have h2 := hinj ψ.toMonoidHom ψ.injective (hfix ψ.toMonoidHom hψ)
  unfold nB rk
  rw [card_eq_of_iso ⟨φ, hφ⟩, le_antisymm h1 h2]

@[expose] def actLin {H : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsInv ↥H Y) {x : Γ}
    (hx : ∀ h ∈ H, h * x = x * h) (hxY : ∀ y ∈ Y, x • y ∈ Y) :
    Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY) where
  toFun p := ⟨Additive.ofMul (x • Additive.toMul p.1), hxY _ p.2⟩
  map_add' p p' := Subtype.ext (by
    show Additive.ofMul (x • Additive.toMul (p.1 + p'.1)) =
      Additive.ofMul (x • Additive.toMul p.1) + Additive.ofMul (x • Additive.toMul p'.1)
    rw [toMul_add, smul_mul', ofMul_mul])
  map_smul' r p := Subtype.ext (by
    show Additive.ofMul (x • Additive.toMul (r.1 p.1)) =
      r.1 (Additive.ofMul (x • Additive.toMul p.1))
    rw [opRing_apply_ofMul_smul hx r.2, ofMul_toMul])

theorem comm_of_isIrr [Finite Q] {H : Subgroup Γ} {Y : Subgroup Q} (hY : XMod.IsIrr ↥H Y)
    {x x' : Γ} (hx : ∀ h ∈ H, h * x = x * h) (hx' : ∀ h ∈ H, h * x' = x' * h)
    (hxY : ∀ y ∈ Y, x • y ∈ Y) (hx'Y : ∀ y ∈ Y, x' • y ∈ Y) :
    ∀ y ∈ Y, x • x' • y = x' • x • y := by
  classical
  have : IsSimpleModule ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1) := (XMod.isIrr_iff hY.1).1 hY
  have : Finite (Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1)) :=
    Finite.of_injective (fun f : Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1) =>
      (f : ↥(XMod.toSubmod hY.1) → ↥(XMod.toSubmod hY.1))) DFunLike.coe_injective
  let _iD : DivisionRing (Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1)) :=
    Module.End.instDivisionRing
  have hc := (Finite.isDomain_to_isField
    (Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1))).mul_comm
    (actLin hY.1 hx hxY) (actLin hY.1 hx' hx'Y)
  intro y hy
  have h1 := congrArg (fun f : Module.End ↥(XMod.opRing ↥H Q) ↥(XMod.toSubmod hY.1) =>
    Additive.toMul (f ⟨Additive.ofMul y, hy⟩).1) hc
  exact h1

end Translate

section Copies

variable [Finite Q] {L H : Subgroup Γ} {R : Subgroup Q}

omit [Finite Q] in
theorem iSup_smul_eq (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l) (hRL : XMod.IsInv ↥L R)
    (hirr : ∀ J : Subgroup Q, J ≤ R → XMod.IsInv ↥L J → XMod.IsInv ↥H J → J = ⊥ ∨ J = R)
    {Y : Subgroup Q} (hY : XMod.IsIrr ↥H Y) (hYR : Y ≤ R) :
    (⨆ l : ↥L, (l : Γ) • Y) = R := by
  have hle : (⨆ l : ↥L, (l : Γ) • Y) ≤ R := by
    refine iSup_le fun l => ?_
    intro q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    have h4 := hRL l _ (hYR hq)
    change (l : Γ) • ((l : Γ)⁻¹ • q) ∈ R at h4
    rwa [smul_inv_smul] at h4
  have hLinv : XMod.IsInv ↥L (⨆ l : ↥L, (l : Γ) • Y) := by
    intro l q hq
    refine Subgroup.iSup_induction (fun l : ↥L => (l : Γ) • Y)
      (C := fun x => (l : Γ) • x ∈ ⨆ l : ↥L, (l : Γ) • Y) hq (fun l' x hx => ?_) ?_ ?_
    · refine Subgroup.mem_iSup_of_mem (l * l') ?_
      rw [Subgroup.coe_mul, mul_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
    · rw [smul_one]; exact one_mem _
    · intro x y hx hy
      rw [smul_mul']
      exact mul_mem hx hy
  have hHinv : XMod.IsInv ↥H (⨆ l : ↥L, (l : Γ) • Y) :=
    XMod.isInv_iSup fun l => isInv_smul_of_comm hY.1 fun h hh => hLH l l.2 h hh
  rcases hirr _ hle hLinv hHinv with h | h
  · exfalso
    have h1 : Y ≤ ⨆ l : ↥L, (l : Γ) • Y := by
      have := le_iSup (fun l : ↥L => (l : Γ) • Y) 1
      simpa using this
    rw [h] at h1
    exact hY.2.1.ne' (le_bot_iff.1 h1)
  · exact h

theorem exists_two_copies (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l) (hLperf : ⁅L, L⁆ = L)
    (hRL : XMod.IsInv ↥L R) (hRH : XMod.IsInv ↥H R)
    (hirr : ∀ J : Subgroup Q, J ≤ R → XMod.IsInv ↥L J → XMod.IsInv ↥H J → J = ⊥ ∨ J = R)
    (hcomm : XMod.commOf ↥L R = R) (hR : R ≠ ⊥) :
    ∃ Y₁ Y₂ : Subgroup Q, Y₁ ≤ R ∧ Y₂ ≤ R ∧ XMod.IsIrr ↥H Y₁ ∧ XMod.IsIrr ↥H Y₂ ∧
      Y₁ ⊓ Y₂ = ⊥ ∧ XMod.Iso ↥H Y₂ Y₁ ∧ R ≤ isoComp ↥H Y₁ ∧
      (⨆ l : ↥L, (l : Γ) • Y₁) = R := by
  obtain ⟨Y₁, hY₁R, hY₁⟩ := exists_isIrr_le hRH hR
  have hsum := iSup_smul_eq hLH hRL hirr hY₁ hY₁R
  have hlY : ∀ l : ↥L, XMod.IsIrr ↥H ((l : Γ) • Y₁) := fun l =>
    isIrr_smul_of_comm hY₁ fun h hh => hLH l l.2 h hh
  have hliso : ∀ l : ↥L, XMod.Iso ↥H ((l : Γ) • Y₁) Y₁ := fun l =>
    iso_smul_of_comm hY₁.1 fun h hh => hLH l l.2 h hh
  have hRiso : R ≤ isoComp ↥H Y₁ := by
    rw [← hsum]
    exact iSup_le fun l => le_isoComp (hlY l) (hliso l)
  have hlR : ∀ l : ↥L, (l : Γ) • Y₁ ≤ R := fun l => hsum ▸ le_iSup (fun l : ↥L => (l : Γ) • Y₁) l
  obtain ⟨l, hl⟩ : ∃ l : ↥L, (l : Γ) • Y₁ ≠ Y₁ := by
    by_contra hall
    push Not at hall
    have hRY : R = Y₁ := by
      rw [← hsum]
      exact le_antisymm (iSup_le fun l => (hall l).le) (by
        have := le_iSup (fun l : ↥L => (l : Γ) • Y₁) 1
        simpa using this)
    have hLY : ∀ l ∈ L, ∀ y ∈ Y₁, l • y ∈ Y₁ := fun l hl y hy => by
      rw [← hRY] at hy ⊢
      exact hRL ⟨l, hl⟩ y hy
    have hcommL : ∀ l ∈ L, ∀ l' ∈ L, ∀ y ∈ Y₁, l • l' • y = l' • l • y := by
      intro l hl l' hl'
      exact comm_of_isIrr hY₁ (fun h hh => (hLH l hl h hh).symm)
        (fun h hh => (hLH l' hl' h hh).symm) (hLY l hl) (hLY l' hl')
    have hfix : L ≤ fixingSubgroup Γ (Y₁ : Set Q) := by
      rw [← hLperf, Subgroup.commutator_le]
      intro l hl l' hl'
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h1 : l'⁻¹ • y ∈ Y₁ := hLY _ (L.inv_mem hl') y hy
      have h2 : l⁻¹ • l'⁻¹ • y ∈ Y₁ := hLY _ (L.inv_mem hl) _ h1
      rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, hcommL l hl l' hl' _ h2,
        smul_inv_smul, smul_inv_smul]
    apply hR
    rw [← hcomm, XMod.commOf_eq_bot_iff, hRY]
    intro y hy
    exact ⟨trivial, fun l => (mem_fixingSubgroup_iff Γ).1 (hfix l.2) y hy⟩
  refine ⟨Y₁, (l : Γ) • Y₁, hY₁R, hlR l, hY₁, hlY l, ?_, hliso l, hRiso, hsum⟩
  rcases inf_eq_bot_or_eq hY₁ (hlY l) with h | h
  · exact h
  · exact absurd h.symm hl

private def commPre (g : Γ) (J R : Subgroup Q) : Subgroup Q where
  carrier := {r | r ∈ R ∧ g • r * r⁻¹ ∈ J}
  mul_mem' := by
    rintro r r' ⟨hr, hrJ⟩ ⟨hr', hr'J⟩
    refine ⟨R.mul_mem hr hr', ?_⟩
    have h1 : g • (r * r') * (r * r')⁻¹ = (g • r * r⁻¹) * (g • r' * r'⁻¹) := by
      rw [smul_mul', mul_inv]
      ac_rfl
    rw [h1]
    exact J.mul_mem hrJ hr'J
  one_mem' := ⟨R.one_mem, by rw [smul_one, inv_one, mul_one]; exact J.one_mem⟩
  inv_mem' := by
    rintro r ⟨hr, hrJ⟩
    refine ⟨R.inv_mem hr, ?_⟩
    have h1 : g • r⁻¹ * r⁻¹⁻¹ = (g • r * r⁻¹)⁻¹ := by rw [smul_inv', mul_inv, inv_inv]
    rw [h1]
    exact J.inv_mem hrJ

theorem exists_three_copies (hQ : ∀ q : Q, q ^ 2 = 1) (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l)
    (hLperf : ⁅L, L⁆ = L) (hRL : XMod.IsInv ↥L R) (hRH : XMod.IsInv ↥H R)
    (hirr : ∀ J : Subgroup Q, J ≤ R → XMod.IsInv ↥L J → XMod.IsInv ↥H J → J = ⊥ ∨ J = R)
    (hcomm : XMod.commOf ↥L R = R) (hR : R ≠ ⊥) {g : Γ} (hgL : g ∈ L) {n : ℕ}
    (hgn : g ^ 2 ^ n = 1) (hg2 : ∃ r ∈ R, g ^ 2 • r ≠ r) :
    ∃ Y₁ : Subgroup Q, Y₁ ≤ R ∧ XMod.IsIrr ↥H Y₁ ∧ R ≤ isoComp ↥H Y₁ ∧
      (∃ Y₂ Y₃ : Subgroup Q, Y₂ ≤ R ∧ Y₃ ≤ R ∧ XMod.IsIrr ↥H Y₂ ∧ XMod.IsIrr ↥H Y₃ ∧
        Y₁ ⊓ Y₂ = ⊥ ∧ (Y₁ ⊔ Y₂) ⊓ Y₃ = ⊥ ∧ XMod.Iso ↥H Y₂ Y₁ ∧ XMod.Iso ↥H Y₃ Y₁) ∧
      (∀ P : Subgroup Γ, P ≤ H → 3 * nB P Y₁ ≤ nB P R) ∧
      (∀ p ∈ H, (∀ y ∈ Y₁, p • y = y) → ∀ r ∈ R, p • r = r) := by
  obtain ⟨Y₁, Y₂, hY₁R, hY₂R, hY₁, hY₂, h12, hiso2, hRiso, hsum⟩ :=
    exists_two_copies hLH hLperf hRL hRH hirr hcomm hR
  have hv : 0 < rk ↥Y₁ := by
    rcases Nat.eq_zero_or_pos (rk ↥Y₁) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hY₁.2.1.ne'
    · exact h
  have hrk2 : rk ↥Y₂ = rk ↥Y₁ := by unfold rk; rw [card_eq_of_iso hiso2]
  obtain ⟨m, hm⟩ := exists_rk_eq_mul hQ hY₁ hRH hRiso
  have hrk12 : rk ↥(Y₁ ⊔ Y₂) = 2 * rk ↥Y₁ := by
    have := rk_sup_add_rk_inf Y₁ Y₂
    rw [h12, rk_bot, hrk2] at this
    omega
  have h12R : Y₁ ⊔ Y₂ ≤ R := sup_le hY₁R hY₂R
  have hm2 : 2 ≤ m := by
    have h1 : rk ↥(Y₁ ⊔ Y₂) ≤ rk ↥R := rk_mono h12R
    rw [hrk12, hm] at h1
    exact le_of_mul_le_mul_right h1 hv
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have hm2' : m = 2 := by omega
    set Bg : Subgroup Γ := Subgroup.zpowers g with hBg
    have hBgL : Bg ≤ L := Subgroup.zpowers_le.2 hgL
    have hBp : IsPGroup 2 ↥Bg := by
      intro b
      refine ⟨n, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
      rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hgn, one_zpow]
      rfl
    have hBgR : ∀ b ∈ Bg, ∀ y ∈ R, b • y ∈ R := fun b hb y hy => hRL ⟨b, hBgL hb⟩ y hy
    have hBgH : ∀ h ∈ H, ∀ b ∈ Bg, h * b = b * h := fun h hh b hb => (hLH b (hBgL hb) h hh).symm
    obtain ⟨y, hyR, hy1, hyB⟩ := exists_mem_not_mem_of_lt hQ hBp (T := ⊥) (Y := R)
      (bot_lt_iff_ne_bot.2 hR) (fun b _ t ht => by
        rw [Subgroup.mem_bot] at ht ⊢; rw [ht, smul_one]) hBgR
    set F := R ⊓ XMod.fixed ↥Bg (⊤ : Subgroup Q) with hF
    have hFinv : XMod.IsInv ↥H F := isInv_inf_fixed hBgH hRH
    have hyF : y ∈ F := by
      refine ⟨hyR, trivial, fun b => ?_⟩
      have h1 := hyB b b.2
      rw [Subgroup.mem_bot] at h1
      exact mul_inv_eq_one.1 h1
    have hFne : F ≠ ⊥ := fun h => hy1 (by rw [← h]; exact hyF)
    obtain ⟨J, hJF, hJ⟩ := exists_isIrr_le hFinv hFne
    have hJR : J ≤ R := hJF.trans inf_le_left
    have hJiso : XMod.Iso ↥H J Y₁ := iso_of_le_isoComp hJ (hJR.trans hRiso)
    have hrkJ : rk ↥J = rk ↥Y₁ := by unfold rk; rw [card_eq_of_iso hJiso]
    have hJg : ∀ j ∈ J, g • j = j := fun j hj => (hJF hj).2.2 ⟨g, Subgroup.mem_zpowers g⟩
    have hJlt : J < R := by
      refine lt_of_le_of_ne hJR fun h => ?_
      have h1 : rk ↥J = rk ↥R := by rw [h]
      rw [hrkJ, hm, hm2'] at h1
      omega
    have hJB : ∀ b ∈ Bg, ∀ t ∈ J, b • t ∈ J := by
      intro b hb t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have h1 : ∀ j : ℕ, g ^ j • t = t := by
        intro j
        induction j with
        | zero => rw [pow_zero, one_smul]
        | succ j ih => rw [pow_succ', mul_smul, ih, hJg t ht]
      have h2 : g ^ k • t = t := by
        rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
        · rw [zpow_natCast, h1]
        · rw [zpow_neg, zpow_natCast, inv_smul_eq_iff, h1]
      rw [h2]
      exact ht
    obtain ⟨y', hy'R, hy'J, hy'B⟩ := exists_mem_not_mem_of_lt hQ hBp hJlt hJB hBgR
    set T := commPre g J R with hT
    have hTH : XMod.IsInv ↥H T := by
      intro h r hr
      refine ⟨hRH h r hr.1, ?_⟩
      have h1 : g • ((h : Γ) • r) * ((h : Γ) • r)⁻¹ = (h : Γ) • (g • r * r⁻¹) := by
        rw [smul_mul', smul_inv', smul_smul, smul_smul, hLH g hgL h h.2]
      change g • ((h : Γ) • r) * ((h : Γ) • r)⁻¹ ∈ J
      rw [h1]
      exact hJ.1 h _ hr.2
    have hJT : J ≤ T := fun j hj => ⟨hJR hj, by rw [hJg j hj, mul_inv_cancel]; exact J.one_mem⟩
    have hy'T : y' ∈ T := ⟨hy'R, hy'B g (Subgroup.mem_zpowers g)⟩
    have hTR : T ≤ R := fun r hr => hr.1
    obtain ⟨t, ht⟩ := exists_rk_eq_mul hQ hY₁ hTH (hTR.trans hRiso)
    have hTeq : T = R := by
      have h1 : rk ↥J < rk ↥T := by
        by_contra hle
        exact hy'J ((eq_of_le_of_rk_le hQ hJT (by omega)) ▸ hy'T)
      have h2 : rk ↥T ≤ rk ↥R := rk_mono hTR
      rw [hrkJ, ht] at h1
      rw [ht, hm, hm2'] at h2
      have h3 : 1 < t := by
        by_contra h4
        push Not at h4
        have := Nat.mul_le_mul_right (rk ↥Y₁) h4
        omega
      have h5 : t ≤ 2 := le_of_mul_le_mul_right h2 hv
      exact eq_of_le_of_rk_le hQ hTR (by rw [ht, hm]; nlinarith)
    obtain ⟨r, hrR, hr⟩ := hg2
    apply hr
    have hrT : r ∈ T := hTeq ▸ hrR
    set w := g • r * r⁻¹ with hw
    have hwJ : w ∈ J := hrT.2
    have hgw : g • w = w := hJg w hwJ
    have hgr : g • r = w * r := by rw [hw, inv_mul_cancel_right]
    rw [pow_two, mul_smul, hgr, smul_mul', hgw, hgr, ← mul_assoc, ← pow_two, hQ, one_mul]
  have h12lt : Y₁ ⊔ Y₂ < R := by
    refine lt_of_le_of_ne h12R fun h => ?_
    have h1 : rk ↥(Y₁ ⊔ Y₂) = rk ↥R := by rw [h]
    rw [hrk12, hm] at h1
    have := Nat.mul_le_mul_right (rk ↥Y₁) hm3
    omega
  obtain ⟨l, hl⟩ : ∃ l : ↥L, ¬ (l : Γ) • Y₁ ≤ Y₁ ⊔ Y₂ := by
    by_contra hall
    push Not at hall
    apply h12lt.ne
    exact le_antisymm h12R (hsum ▸ iSup_le hall)
  have hY₃ : XMod.IsIrr ↥H ((l : Γ) • Y₁) := isIrr_smul_of_comm hY₁ fun h hh => hLH l l.2 h hh
  have hiso3 : XMod.Iso ↥H ((l : Γ) • Y₁) Y₁ := iso_smul_of_comm hY₁.1 fun h hh => hLH l l.2 h hh
  have hY₃R : (l : Γ) • Y₁ ≤ R := hsum ▸ le_iSup (fun l : ↥L => (l : Γ) • Y₁) l
  have h123 : (Y₁ ⊔ Y₂) ⊓ (l : Γ) • Y₁ = ⊥ := by
    rcases hY₃.2.2 _ ((hY₁.1.sup hY₂.1).inf hY₃.1) bot_le inf_le_right with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) hl
  refine ⟨Y₁, hY₁R, hY₁, hRiso, ⟨Y₂, (l : Γ) • Y₁, hY₂R, hY₃R, hY₂, hY₃, h12, h123, hiso2,
    hiso3⟩, fun P hPH => ?_, fun p hp hpY r hr => ?_⟩
  · have hinv : ∀ {Y : Subgroup Q}, XMod.IsInv ↥H Y → ∀ b ∈ P, ∀ y ∈ Y, b • y ∈ Y :=
      fun hY b hb y hy => hY ⟨b, hPH hb⟩ y hy
    have e1 := nB_sup_of_inf_eq_bot P (hinv hY₁.1) (hinv hY₂.1) h12
    have e2 := nB_sup_of_inf_eq_bot P (hinv (hY₁.1.sup hY₂.1)) (hinv hY₃.1) h123
    have e3 := nB_eq_of_iso hPH hY₂.1 hiso2
    have e4 := nB_eq_of_iso hPH hY₃.1 hiso3
    have hle := nB_mono P (sup_le h12R hY₃R)
    omega
  · have hle : R ≤ XMod.fixed ↥(Subgroup.zpowers p) (⊤ : Subgroup Q) := by
      rw [← hsum]
      refine iSup_le fun l' => ?_
      intro q hq
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
      refine mem_fixed_zpowers_iff.2 ?_
      have h1 := hpY _ hq
      have hcomm' : p * (l' : Γ) = (l' : Γ) * p := (hLH l' l'.2 p hp).symm
      calc p • q = p • ((l' : Γ) • ((l' : Γ)⁻¹ • q)) := by rw [smul_inv_smul]
        _ = (l' : Γ) • (p • ((l' : Γ)⁻¹ • q)) := by rw [smul_smul, hcomm', mul_smul]
        _ = q := by rw [h1, smul_inv_smul]
    exact mem_fixed_zpowers_iff.1 (hle hr)

end Copies

end CFSG.Quasithin.SmithD39Two
