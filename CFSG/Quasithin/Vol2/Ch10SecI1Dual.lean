module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

noncomputable section

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

section Restrict

variable {Γ V : Type*} [Group Γ] [CommGroup V]

@[expose] def restrictAut (r : Γ →* MulAut V) (U : Subgroup V) (hU : ∀ γ, ∀ u ∈ U, r γ u ∈ U) :
    Γ →* MulAut U where
  toFun γ :=
    { toFun := fun u => ⟨r γ u, hU γ u u.2⟩
      invFun := fun u => ⟨r γ⁻¹ u, hU γ⁻¹ u u.2⟩
      left_inv := fun u => Subtype.ext (by
        change r γ⁻¹ (r γ (u : V)) = u
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun u => Subtype.ext (by
        change r γ (r γ⁻¹ (u : V)) = u
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun u v => Subtype.ext (map_mul (r γ) (u : V) (v : V)) }
  map_one' := MulEquiv.ext fun u => Subtype.ext (by
    change r 1 (u : V) = u
    rw [map_one, MulAut.one_apply])
  map_mul' γ δ := MulEquiv.ext fun u => Subtype.ext (by
    change r (γ * δ) (u : V) = r γ (r δ (u : V))
    rw [map_mul, MulAut.mul_apply])

theorem restrictAut_apply (r : Γ →* MulAut V) (U : Subgroup V) (hU : ∀ γ, ∀ u ∈ U, r γ u ∈ U)
    (γ : Γ) (u : U) : ((restrictAut r U hU γ u : U) : V) = r γ u :=
  rfl

end Restrict

section Rep

variable {Γ V : Type*} [Group Γ] [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] def repOf (r : Γ →* MulAut V) : Representation (ZMod 2) Γ (Additive V) where
  toFun γ := (MulEquiv.toAdditive (r γ)).toAddMonoidHom.toZModLinearMap 2
  map_one' := LinearMap.ext fun w => by
    change Additive.ofMul (r 1 (Additive.toMul w)) = w
    rw [map_one, MulAut.one_apply]
    rfl
  map_mul' γ δ := LinearMap.ext fun w => by
    change Additive.ofMul (r (γ * δ) (Additive.toMul w)) =
      Additive.ofMul (r γ (Additive.toMul (Additive.ofMul (r δ (Additive.toMul w)))))
    rw [map_mul, MulAut.mul_apply]
    rfl

theorem repOf_apply (r : Γ →* MulAut V) (γ : Γ) (w : Additive V) :
    repOf r γ w = Additive.ofMul (r γ (Additive.toMul w)) :=
  rfl

end Rep

section Comm

variable {W : Type*} [CommGroup W]

theorem comm_mem_commV {X : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ X) (w : W) :
    g w * w⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨g, hg, w, rfl⟩

theorem map_mem_commV {X : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ X) {v : W}
    (hv : v ∈ commV X) : g v ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem hg hv

theorem cocycle_id (a b w : W) : b * w⁻¹ = (a * w⁻¹) * (b * a⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem comm_mul_id (a₁ a₂ w₁ w₂ : W) :
    a₁ * a₂ * (w₁ * w₂)⁻¹ = (a₁ * w₁⁻¹) * (a₂ * w₂⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Comm

variable {W : Type} [CommGroup W] [Finite W]

theorem index_le_of_realizes (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)}
    (hfix : fixV Gm = ⊥) {V : Subgroup W} (hcV : commV Gm ≤ V) {D : FFModel} [Finite D.Gam]
    (hR : D.Realizes Gm V ⊥) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) D.Gam M), D.IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    V.index ≤ 2 ^ d := by
  obtain ⟨π, hπs, -, hks, hU, -, hsec, hker, β, hβs, hβk, hβi⟩ := hR
  let r : D.Gam →* MulAut W := Gm.subtype.comp π
  have hrV : ∀ γ, ∀ v ∈ V, r γ v ∈ V := fun γ v hv => hU (π γ) v hv
  let rV := restrictAut r V hrV
  have h2 : ∀ x : Additive ↥V, 2 • x = 0 := fun x => by
    have : (Additive.toMul x) ^ 2 = 1 := Subtype.ext (hW2 _)
    rw [← ofMul_toMul x, ← ofMul_pow, this, ofMul_one]
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule h2
  let ρ := repOf rV
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have := (hβk u).mp (MonoidHom.mem_ker.mp hu)
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  let β' : Additive ↥V ≃+ Additive (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    MulEquiv.toAdditive (MulEquiv.ofBijective β ⟨hβinj, hβs⟩)
  have hModel : D.IsModel ρ := by
    refine ⟨MulEquiv.refl _, β', hks, hsec, hker, fun γ w m hm hw => ?_⟩
    have hw' : β (Additive.toMul w) = QuotientGroup.mk m := congrArg Additive.toMul hw
    exact congrArg Additive.ofMul (hβi γ (Additive.toMul w) m _ hm hw')
  have hcardH1 : Nat.card (H1 ρ) ≤ 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) (hH1 ρ hModel)
  let c : W → (D.Gam → Additive ↥V) := fun w γ =>
    Additive.ofMul ⟨r γ w * w⁻¹, hcV (comm_mem_commV (π γ).2 w)⟩
  have hcw : ∀ w γ, ((Additive.toMul (c w γ) : ↥V) : W) = r γ w * w⁻¹ := fun _ _ => rfl
  have hc : ∀ w, c w ∈ Z1 ρ := by
    intro w γ δ
    apply Additive.toMul.injective
    apply Subtype.ext
    change r (γ * δ) w * w⁻¹ = (r γ w * w⁻¹) * r γ (r δ w * w⁻¹)
    rw [map_mul r γ δ, MulAut.mul_apply, map_mul (r γ), map_inv (r γ)]
    exact cocycle_id (r γ w) (r γ (r δ w)) w
  let Φ : W →* Multiplicative ↥(Z1 ρ) :=
    { toFun := fun w => Multiplicative.ofAdd ⟨c w, hc w⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext γ
        apply Additive.toMul.injective
        apply Subtype.ext
        change r γ 1 * 1⁻¹ = 1
        rw [map_one, inv_one, mul_one]
      map_mul' := fun w₁ w₂ => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext γ
        apply Additive.toMul.injective
        apply Subtype.ext
        change r γ (w₁ * w₂) * (w₁ * w₂)⁻¹ = (r γ w₁ * w₁⁻¹) * (r γ w₂ * w₂⁻¹)
        rw [map_mul (r γ)]
        exact comm_mul_id _ _ _ _ }
  let Ψ : W →* Multiplicative (H1 ρ) :=
    (AddMonoidHom.toMultiplicative ((B1 ρ).comap (Z1 ρ).subtype).mkQ.toAddMonoidHom).comp Φ
  have hkerΨ : Ψ.ker = V := by
    ext w
    rw [MonoidHom.mem_ker]
    constructor
    · intro hw
      have h0 : ((B1 ρ).comap (Z1 ρ).subtype).mkQ ⟨c w, hc w⟩ = 0 :=
        congrArg Multiplicative.toAdd hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨a, ha⟩ := LinearMap.mem_range.mp h0
      have hfixw : w * ((Additive.toMul a : ↥V) : W)⁻¹ ∈ fixV Gm := by
        intro g hg
        obtain ⟨γ, hγ⟩ := hπs ⟨g, hg⟩
        have hγ' : r γ = g := congrArg Subtype.val hγ
        have h1 : ρ γ a - a = c w γ := congrFun ha γ
        have h2 : ((Additive.toMul (ρ γ a - a) : ↥V) : W) = r γ w * w⁻¹ := by
          rw [h1]
          exact hcw w γ
        rw [toMul_sub, Subgroup.coe_div] at h2
        have h2' : r γ ((Additive.toMul a : ↥V) : W) / ((Additive.toMul a : ↥V) : W) =
            r γ w * w⁻¹ := h2
        have e : r γ w = r γ ((Additive.toMul a : ↥V) : W) / ((Additive.toMul a : ↥V) : W) * w :=
          by rw [h2', inv_mul_cancel_right]
        rw [← hγ', map_mul (r γ), map_inv (r γ), e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_div]
        abel
      rw [hfix, Subgroup.mem_bot, mul_inv_eq_one] at hfixw
      rw [hfixw]
      exact (Additive.toMul a).2
    · intro hw
      apply Multiplicative.toAdd.injective
      change ((B1 ρ).comap (Z1 ρ).subtype).mkQ ⟨c w, hc w⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨Additive.ofMul ⟨w, hw⟩, ?_⟩
      funext γ
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((Additive.toMul (ρ γ (Additive.ofMul ⟨w, hw⟩) - Additive.ofMul ⟨w, hw⟩) : ↥V) : W) =
        r γ w * w⁻¹
      rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
      rfl
  have hidx : V.index = Nat.card Ψ.range := by
    have := Subgroup.index_ker Ψ
    rwa [hkerΨ] at this
  rw [hidx]
  have : Finite (H1 ρ) := Module.finite_of_finite (ZMod 2)
  have : Finite (Multiplicative (H1 ρ)) := Finite.of_equiv (H1 ρ) Multiplicative.ofAdd
  calc Nat.card Ψ.range ≤ Nat.card (Multiplicative (H1 ρ)) := Subgroup.card_le_card_group _
    _ = Nat.card (H1 ρ) := rfl
    _ ≤ 2 ^ d := hcardH1

theorem dualCover_le (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} (hfix : fixV Gm = ⊥)
    {D : FFModel} [Finite D.Gam] (hR : D.Realizes Gm (commV Gm) ⊥) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) D.Gam M), D.IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    (commV Gm).index ≤ 2 ^ d :=
  index_le_of_realizes hW2 hfix le_rfl hR hH1

end CFSG.Quasithin.ASInputs.C10KH
