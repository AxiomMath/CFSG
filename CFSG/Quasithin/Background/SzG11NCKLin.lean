module

public import CFSG.Quasithin.Background.SzG11NCGalois
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem klin_card_le_four
    (E : Type) [Field E] [Finite E] [Module E V] (hE : Nat.card E = 4)
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} (hyp : G101Hyp B Γ v₁ W X X₀)
    (hlin : ∀ x ∈ X, ∀ (κ : E) (v : V), x (κ • v) = κ • x v) : Nat.card X ≤ 4 := by
  classical
  have : Nontrivial V := ⟨⟨v₁, 0, hyp.point⟩⟩
  have h2E : (2 : E) = 0 := by
    apply smul_left_inj_of_ne_zero hyp.point
    rw [two_smul, zmod_two_add_self, zero_smul]
  obtain ⟨ω, hω0, hω1, hωsq, hcases⟩ := E4_cases hE h2E
  let ωLin : V →ₗ[ZMod 2] V :=
    (AddMonoidHom.mk' (fun v : V => ω • v) (fun a b => smul_add ω a b)).toZModLinearMap 2
  have ωLin_apply : ∀ v, ωLin v = ω • v := fun v => rfl
  let Φ : V →ₗ[ZMod 2] ZMod 2 × ZMod 2 := (B v₁).prod ((B v₁).comp ωLin)
  let Y : Submodule (ZMod 2) V := LinearMap.ker Φ
  have hYmem : ∀ v, v ∈ Y ↔ B v₁ v = 0 ∧ B v₁ (ω • v) = 0 := by
    intro v
    show Φ v = 0 ↔ _
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
  have hYω : ∀ y ∈ Y, ω • y ∈ Y := by
    intro y hy
    obtain ⟨h1, h2⟩ := (hYmem y).1 hy
    refine (hYmem _).2 ⟨h2, ?_⟩
    rw [← mul_smul, ← sq, hωsq, add_smul, one_smul, map_add, h2, h1, add_zero]
  have hYE : ∀ y ∈ Y, ∀ κ : E, κ • y ∈ Y := by
    intro y hy κ
    rcases hcases κ with rfl | rfl | rfl | rfl
    · rw [zero_smul]; exact Y.zero_mem
    · rw [one_smul]; exact hy
    · exact hYω y hy
    · rw [add_smul, one_smul]; exact Y.add_mem (hYω y hy) hy
  have hstar : ∀ u ∈ W, u ≠ 0 → u ≠ v₁ → ∀ κ : E, κ ≠ 0 → κ ≠ 1 → κ • u ∉ W := by
    intro u hu hu0 hu1 κ hκ0 hκ1 hκu
    have hnot : (⟨u, hu⟩ : W) ∉ Submodule.span (ZMod 2) {(⟨v₁, hyp.mem_W⟩ : W)} := by
      intro h
      rw [Submodule.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      have hc' := congrArg Subtype.val hc
      rcases zmod_two_cases c with rfl | rfl
      · apply hu0
        simpa using hc'.symm
      · apply hu1
        simpa using hc'.symm
    obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hf0 : f ⟨v₁, hyp.mem_W⟩ = 0 := by
      have : f ⟨v₁, hyp.mem_W⟩ ∈ (Submodule.span (ZMod 2) {(⟨v₁, hyp.mem_W⟩ : W)}).map f :=
        ⟨_, Submodule.subset_span rfl, rfl⟩
      rw [hf2, Submodule.mem_bot] at this
      exact this
    have hfu : f ⟨u, hu⟩ = 1 := by
      rcases zmod_two_cases (f ⟨u, hu⟩) with h | h
      · exact absurd h hf1
      · exact h
    obtain ⟨x, hxX, hx⟩ := hyp.transvection_full f hf0
    have e1 := hx ⟨u, hu⟩
    have e2 := hx ⟨κ • u, hκu⟩
    simp only at e1 e2
    rw [hfu, one_smul] at e1
    have e3 : x (κ • u) = κ • x u := hlin x hxX κ u
    rw [e2, e1, smul_add] at e3
    have e4 : (f ⟨κ • u, hκu⟩) • v₁ = κ • v₁ := add_left_cancel e3
    have e5 : κ • v₁ = 0 ∨ κ • v₁ = v₁ := by
      rcases zmod_two_cases (f ⟨κ • u, hκu⟩) with h | h
      · left; rw [← e4, h, zero_smul]
      · right; rw [← e4, h, one_smul]
    rcases eq_zero_or_one_of_smul_eq hyp.point e5 with h | h
    · exact hκ0 h
    · exact hκ1 h
  have hxY : ∀ x ∈ X, ∀ y ∈ Y, x y = y := by
    intro x hx y hy
    have hsW : ∀ y' ∈ Y, x y' - y' ∈ W := fun y' hy' =>
      hyp.commutator_le x hx y' ((hYmem y').1 hy').1
    by_contra hne
    have hs0 : x y - y ≠ 0 := sub_ne_zero.2 hne
    have hsκ : ∀ κ : E, κ • (x y - y) ∈ W := by
      intro κ
      have : κ • (x y - y) = x (κ • y) - κ • y := by rw [smul_sub, hlin x hx κ y]
      rw [this]
      exact hsW _ (hYE y hy κ)
    by_cases hsv : x y - y = v₁
    · have h1 : ω • v₁ ∈ W := hsv ▸ hsκ ω
      have h2 : ω • (ω • v₁) ∈ W := by
        rw [← mul_smul, ← sq, hωsq, add_smul, one_smul]
        exact W.add_mem h1 hyp.mem_W
      have hne0 : ω • v₁ ≠ 0 := smul_ne_zero hω0 hyp.point
      have hne1 : ω • v₁ ≠ v₁ := by
        intro h
        exact hω1 (smul_left_inj_of_ne_zero hyp.point (h.trans (one_smul E v₁).symm))
      exact hstar (ω • v₁) h1 hne0 hne1 ω hω0 hω1 h2
    · exact hstar (x y - y) (hsW y hy) hs0 hsv ω hω0 hω1 (hsκ ω)
  have hVcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have hYcard : Nat.card Y = 2 ^ Module.finrank (ZMod 2) Y := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y)
    rwa [Nat.card_zmod] at this
  have hVY : Nat.card V ≤ 4 * Nat.card Y := by
    let Φ' : V →+ ZMod 2 × ZMod 2 :=
      AddMonoidHom.prod ((B v₁).toAddMonoidHom) (((B v₁).comp ωLin).toAddMonoidHom)
    have hker : ∀ v, v ∈ Φ'.ker ↔ v ∈ Y := by
      intro v
      rw [hYmem, AddMonoidHom.mem_ker]
      constructor
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨h1, h2⟩
        exact Prod.ext h1 h2
    have hc1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ'.ker
    have hc2 : Nat.card Φ'.ker = Nat.card Y :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => hker v))
    have hc3 : Nat.card (V ⧸ Φ'.ker) ≤ 4 := by
      have := Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Φ')
      rwa [Nat.card_prod, Nat.card_zmod] at this
    rw [hc1, hc2]
    exact Nat.mul_le_mul_right _ hc3
  have hr : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) Y + 2 := by
    rw [hVcard, hYcard] at hVY
    have h4 : 4 * 2 ^ Module.finrank (ZMod 2) Y = 2 ^ (Module.finrank (ZMod 2) Y + 2) := by ring
    rw [h4] at hVY
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hVY
  have hYp : Nat.card (B.orthogonal Y) ≤ 4 := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate' Y
    have h2 : Nat.card (B.orthogonal Y) = 2 ^ Module.finrank (ZMod 2) (B.orthogonal Y) := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B.orthogonal Y)
      rwa [Nat.card_zmod] at this
    rw [h2, h1]
    have hYle : Module.finrank (ZMod 2) Y ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le Y
    calc 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) Y) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hxYp : ∀ x ∈ X, ∀ v, x v - v ∈ B.orthogonal Y := by
    intro x hx v
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show B y (x v - v) = 0
    have h1 : B (x y) (x v) = B y v := hyp.isometry x (hyp.X_le hx) y v
    rw [hxY x hx y hy] at h1
    rw [map_sub, h1]
    exact sub_eq_zero.2 rfl
  by_cases hYtop : ∀ v, v ∈ Y
  · have hXtriv : ∀ x ∈ X, x = 1 := fun x hx => LinearEquiv.ext fun v => hxY x hx v (hYtop v)
    have hbot : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hXtriv
    rw [hbot, Subgroup.card_bot]
    norm_num
  · push Not at hYtop
    obtain ⟨z, hz⟩ := hYtop
    let Θ : ↥Y × E → V := fun p => (p.1 : V) + p.2 • z
    have hΘinj : Function.Injective Θ := by
      rintro ⟨y, κ⟩ ⟨y', κ'⟩ h
      simp only [Θ] at h
      by_cases hκ : κ = κ'
      · subst hκ
        have : (y : V) = y' := add_right_cancel h
        exact Prod.ext (Subtype.ext this) rfl
      · exfalso
        have h1 : (κ - κ') • z ∈ Y := by
          have : (κ - κ') • z = (y' : V) - y := by
            rw [sub_smul]
            calc κ • z - κ' • z = ((y : V) + κ • z) - y - κ' • z := by abel
              _ = ((y' : V) + κ' • z) - y - κ' • z := by rw [h]
              _ = (y' : V) - y := by abel
          rw [this]
          exact Y.sub_mem y'.2 y.2
        apply hz
        have := hYE _ h1 (κ - κ')⁻¹
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hκ), one_smul] at this
    have hΘbij : Function.Bijective Θ := by
      refine hΘinj.bijective_of_nat_card_le ?_
      rw [Nat.card_prod, hE, mul_comm]
      exact hVY
    have hdec : ∀ v : V, ∃ y : ↥Y, ∃ κ : E, v = (y : V) + κ • z := fun v => by
      obtain ⟨⟨y, κ⟩, h⟩ := hΘbij.2 v
      exact ⟨y, κ, h.symm⟩
    let δ : X → B.orthogonal Y := fun x => ⟨(x : GLV V) z - z, hxYp x x.2 z⟩
    have hδ : Function.Injective δ := by
      intro x x' h
      have h1 : (x : GLV V) z = (x' : GLV V) z := by
        have := congrArg Subtype.val h
        simpa [δ] using this
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      obtain ⟨y, κ, rfl⟩ := hdec v
      rw [map_add, map_add, hlin x x.2 κ z, hlin x' x'.2 κ z, h1, hxY x x.2 y y.2,
        hxY x' x'.2 y y.2]
    calc Nat.card X ≤ Nat.card (B.orthogonal Y) := Nat.card_le_card_of_injective δ hδ
      _ ≤ 4 := hYp

theorem klin_dim_le_six
    (E : Type) [Field E] [Finite E] [Module E V] (hE : Nat.card E = 4)
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} (hyp : G101Hyp B Γ v₁ W X X₀)
    (hlin : ∀ x ∈ X, ∀ (κ : E) (v : V), x (κ • v) = κ • x v) :
    Module.finrank (ZMod 2) V ≤ 6 := by
  have h4 := klin_card_le_four E hE hyp hlin
  have h1 := hyp.dim_le_two_mul
  have h2 : X₀.relIndex X ≤ 4 :=
    le_trans (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card X₀ X)) h4
  have h3 : Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 4 := Nat.log_mono_right h2
  have h5 : Nat.log 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow Nat.one_lt_two]
  omega

end CFSG.Quasithin.SzG11NC
