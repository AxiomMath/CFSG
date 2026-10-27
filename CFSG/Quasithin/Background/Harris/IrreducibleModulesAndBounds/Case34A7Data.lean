module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Class
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family

namespace Case34A7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_equiv_of_center_bot {L : Subgroup (GLV V)} (hZ : Subgroup.center ↥L = ⊥)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) :
    ∃ f : ↥L ≃* S, ∀ l : ↥L, f l = e (QuotientGroup.mk l) := by
  let ρ : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hρsurj : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : Function.Injective ρ := by
    intro x y hxy
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y := e.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.1 h1)
  exact ⟨MulEquiv.ofBijective ρ ⟨hinj, hρsurj⟩, fun l => rfl⟩

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem four_le_finrank {L : Subgroup (GLV V)}
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) :
    4 ≤ Module.finrank (ZMod 2) V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := orderOf_two_le_finrank_of_dvd_card_quotient e (p := 5) (by norm_num) (by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide)
  rwa [orderOf_two_zmod_five] at h

@[expose] def PermCoreData {L : Subgroup (GLV V)} (f : ↥L ≃* ↥(alternatingGroup (Fin 7)))
    (β : ↥(permCore 7) →ₗ[ZMod 2] V) : Prop :=
  Function.Bijective β ∧ ∀ (γ : ↥L) (u u' : ↥(permCore 7)),
    (u' : Fin 7 → ZMod 2) =
      permAct ((f γ : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2) →
    β u' = (γ : GLV V) (β u)

theorem card_permCore_seven : Nat.card ↥(permCore 7) = 2 ^ 6 := by
  have h : Nat.card ↥(permCore 7) = Nat.card {x : Fin 7 → ZMod 2 // ∑ i, x i = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  rw [h, Nat.card_eq_fintype_card]
  decide +kernel

theorem data {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) :
    ∃ f : ↥L ≃* ↥(alternatingGroup (Fin 7)), 4 ≤ Module.finrank (ZMod 2) V ∧
      Module.finrank (ZMod 2) V ≤ 8 ∧ m ≤ 3 ∧
      (Module.finrank (ZMod 2) V = 4 ∨ (Module.finrank (ZMod 2) V = 6 ∧
        ∃ β : ↥(permCore 7) →ₗ[ZMod 2] V, PermCoreData f β)) := by
  classical
  have hZ := center_eq_bot h e
  obtain ⟨f, -⟩ := exists_equiv_of_center_bot hZ e
  have hm := m_le_three h e
  have h4 := four_le_finrank e
  have hb := h.bound
  have hd8 : Module.finrank (ZMod 2) V ≤ 8 := by omega
  refine ⟨f, h4, hd8, hm, ?_⟩
  have hcard : Nat.card (Multiplicative V) ≤ 2 ^ 12 := by
    rw [natCard_multiplicative]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  let ι : ↥(toMulSub L) ≃* ↥(alternatingGroup (Fin 7)) := (toMulSubEquiv L).symm.trans f
  have hirr := isIrrOn_toMulSub h.H_irr
  have hL : toMulSub L ≠ ⊥ :=
    ne_bot_of_isQuasisimple (isQuasisimple_toMulSub h.L_comp.2.2)
  have hfix := fixV_eq_bot_of_irr hirr hL
  letI : Module (ZMod 2) (Additive (Multiplicative V)) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      have h3 : Additive.toMul (2 • x) = 1 := by
        rw [toMul_nsmul]
        exact multiplicative_sq_eq_one _
      exact toMul_eq_one.1 h3
  have hirr' : ∀ J : Subgroup (Multiplicative V), (∀ l ∈ toMulSub L, ∀ v ∈ J, l v ∈ J) →
      J = ⊥ ∨ J = ⊤ := hirr.2
  rcases CFSG.Quasithin.B45Alt7.classifyFour ι hirr' hfix hcard with ⟨β₀, hβ₀⟩ | h16
  · right
    let B : ↥(permCore 7) ≃+ V :=
      { toFun := fun u => Multiplicative.toAdd
          (β₀.symm ⟨Multiplicative.ofAdd (u : Fin 7 → ZMod 2), u.2⟩)
        invFun := fun v => ⟨Multiplicative.toAdd
          ((β₀ (Multiplicative.ofAdd v) : ↥(G6.coreMod 7)) : G6.PermMod 7),
            (β₀ (Multiplicative.ofAdd v)).2⟩
        left_inv := fun u => by
          apply Subtype.ext
          simp
        right_inv := fun v => by
          simp
        map_add' := fun u u' => by
          have : (⟨Multiplicative.ofAdd ((u + u' : ↥(permCore 7)) : Fin 7 → ZMod 2),
              (u + u' : ↥(permCore 7)).2⟩ : ↥(G6.coreMod 7)) =
              ⟨Multiplicative.ofAdd (u : Fin 7 → ZMod 2), u.2⟩ *
                ⟨Multiplicative.ofAdd (u' : Fin 7 → ZMod 2), u'.2⟩ := Subtype.ext rfl
          show Multiplicative.toAdd (β₀.symm _) = _
          rw [this, map_mul, toAdd_mul] }
    let β : ↥(permCore 7) →ₗ[ZMod 2] V :=
      { toFun := B
        map_add' := B.map_add
        map_smul' := fun c u => by
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · simp
          · simp }
    have hβ : ∀ u, β u = Multiplicative.toAdd
        (β₀.symm ⟨Multiplicative.ofAdd (u : Fin 7 → ZMod 2), u.2⟩) := fun u => rfl
    have hbij : Function.Bijective β := B.bijective
    have hd : Module.finrank (ZMod 2) V = 6 := by
      have h1 : Nat.card V = Nat.card ↥(permCore 7) := Nat.card_congr (Equiv.ofBijective β hbij).symm
      have h2 := natCard_multiplicative (V := V)
      rw [card_permCore_seven] at h1
      have h3 : Nat.card (Multiplicative V) = Nat.card V := rfl
      rw [h3, h1] at h2
      exact (Nat.pow_right_injective (le_refl 2) h2).symm
    refine ⟨hd, β, hbij, fun γ u u' hu' => ?_⟩
    have hiota : ((ι.symm (f γ) : ↥(toMulSub L)) : MulAut (Multiplicative V)) =
        linEquivMulAut (γ : GLV V) := by
      simp [ι]
    set s : Multiplicative V := β₀.symm ⟨Multiplicative.ofAdd (u : Fin 7 → ZMod 2), u.2⟩ with hs
    have h1 := hβ₀ (f γ) s
    have hβs : (β₀ s : G6.PermMod 7) = Multiplicative.ofAdd (u : Fin 7 → ZMod 2) := by
      rw [hs, MulEquiv.apply_symm_apply]
    have h2 : β₀.symm ⟨Multiplicative.ofAdd (u' : Fin 7 → ZMod 2), u'.2⟩ =
        linEquivMulAut (γ : GLV V) s := by
      apply β₀.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      show Multiplicative.ofAdd (u' : Fin 7 → ZMod 2) = _
      have h3 : (β₀ ((ι.symm (f γ) : MulAut (Multiplicative V)) s) : G6.PermMod 7) = _ := h1
      rw [hiota] at h3
      rw [h3, hβs, hu']
      rfl
    show Multiplicative.toAdd (β₀.symm ⟨Multiplicative.ofAdd (u' : Fin 7 → ZMod 2), u'.2⟩) =
      (γ : GLV V) (Multiplicative.toAdd s)
    rw [h2]
    rfl
  · left
    rw [natCard_multiplicative] at h16
    exact (Nat.pow_right_injective (le_refl 2)) h16

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
