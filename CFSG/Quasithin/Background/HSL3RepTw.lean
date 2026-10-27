module

public import CFSG.Quasithin.Background.HSL3Rep
public import CFSG.Quasithin.Background.HSL3S77Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H.SL3Rep

open Module Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped IsMulCommutative

theorem tauT_tauT (g : SpecialLinearGroup (Fin 3) (ZMod 2)) : tauT (tauT g) = g := by
  apply Subtype.ext
  rw [coe_tauT, ← map_inv, coe_tauT, inv_inv, Matrix.transpose_transpose]

section Fix

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]

@[expose] def fixSpace (f : Module.End (ZMod 2) E) : Submodule (ZMod 2) E :=
  LinearMap.ker (f - 1)

omit [Finite E] in
theorem mem_fixSpace {f : Module.End (ZMod 2) E} {v : E} : v ∈ fixSpace f ↔ f v = v := by
  rw [fixSpace, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

omit [Finite E] in
theorem card_fix_eq (f : Module.End (ZMod 2) E) :
    Nat.card {v : E // f v = v} = Nat.card (fixSpace f) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixSpace.symm)

theorem card_sub (X : Submodule (ZMod 2) E) : Nat.card X = 2 ^ finrank (ZMod 2) X :=
  natCard_eq_two_pow X

theorem card_mul_card_le (F X : Submodule (ZMod 2) E) :
    Nat.card F * Nat.card X ≤ Nat.card ↥(F ⊓ X) * Nat.card E := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F X
  have h2 := Submodule.finrank_le (F ⊔ X)
  rw [card_sub, card_sub, card_sub, natCard_eq_two_pow E, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_sup_of_inf_eq_bot {X Y : Submodule (ZMod 2) E} (h : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [h, finrank_bot, add_zero] at h1
  rw [card_sub, card_sub, card_sub, ← pow_add, h1]

theorem card_sup_le (X Y : Submodule (ZMod 2) E) :
    Nat.card ↥(X ⊔ Y) ≤ Nat.card X * Nat.card Y := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank X Y
  rw [card_sub, card_sub, card_sub, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h1

theorem card_le_of_le {X Y : Submodule (ZMod 2) E} (h : X ≤ Y) : Nat.card X ≤ Nat.card Y := by
  rw [card_sub, card_sub]
  exact Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_mono h)

theorem card_fix_sup_le {f : Module.End (ZMod 2) E} {U U' : Submodule (ZMod 2) E}
    (hU : ∀ u ∈ U, f u ∈ U) (hU' : ∀ u ∈ U', f u ∈ U') (hUU' : U ⊓ U' = ⊥) :
    Nat.card ↥(fixSpace f ⊓ (U ⊔ U')) ≤
      Nat.card ↥(fixSpace f ⊓ U) * Nat.card ↥(fixSpace f ⊓ U') := by
  refine le_trans (card_le_of_le ?_) (card_sup_le _ _)
  rintro v ⟨hvF, hv⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have hvF' : f a + f b = a + b := by rw [← map_add]; exact mem_fixSpace.1 hvF
  have h2 : f a - a = b - f b := by
    rw [sub_eq_sub_iff_add_eq_add, hvF', add_comm]
  have h3 : f a - a ∈ U ⊓ U' := ⟨U.sub_mem (hU a ha) ha, h2 ▸ U'.sub_mem hb (hU' b hb)⟩
  rw [hUU', Submodule.mem_bot] at h3
  have hfa : f a = a := sub_eq_zero.1 h3
  have hfb : f b = b := by
    rw [hfa] at hvF'
    exact add_left_cancel hvF'
  exact Submodule.add_mem_sup ⟨mem_fixSpace.2 hfa, ha⟩ ⟨mem_fixSpace.2 hfb, hb⟩

end Fix

section Min

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] {Γ : Type*} [Monoid Γ]

theorem exists_min_subrep [Nontrivial E] (ρ : Representation (ZMod 2) Γ E) :
    ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ ∀ X : Subrepresentation ρ, X ≤ U → X = ⊥ ∨ X = U := by
  classical
  have : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun X : Subrepresentation ρ => (X : Set E)) SetLike.coe_injective
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact (bot_ne_top_of_ne_zero ρ hv).symm
  obtain ⟨U, hU, hmin⟩ := wellFounded_lt.has_min {X : Subrepresentation ρ | X ≠ ⊥} ⟨⊤, htop⟩
  refine ⟨U, hU, fun X hXU => ?_⟩
  by_cases hX : X = ⊥
  · exact Or.inl hX
  · right
    by_contra hne
    exact hmin X hX (lt_of_le_of_ne hXU hne)

omit [Finite E] in
theorem isIrreducible_of_min {ρ : Representation (ZMod 2) Γ E} {U : Subrepresentation ρ}
    (hU : U ≠ ⊥) (hmin : ∀ X : Subrepresentation ρ, X ≤ U → X = ⊥ ∨ X = U) :
    U.toRepresentation.IsIrreducible := by
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U.toSubmodule) (fun h =>
    hU (Subrepresentation.toSubmodule_injective h))
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top_of_ne_zero _ (m := (⟨v, hvU⟩ : U.toSubmodule))
    fun h => hv0 (congrArg Subtype.val h)⟩, eq_bot_or_eq_top := fun R => ?_ }
  let X : Subrepresentation ρ :=
    ⟨R.toSubmodule.map U.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨U.toRepresentation g y, R.apply_mem_toSubmodule g hy, rfl⟩⟩
  have hXU : X ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rcases hmin X hXU with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have hyX : (y : E) ∈ X := ⟨y, hy, rfl⟩
    rw [h] at hyX
    have hy0 : (y : E) = 0 := (Submodule.mem_bot (ZMod 2)).1 hyX
    exact (Submodule.mem_bot (ZMod 2)).2 (Subtype.ext hy0)
  · right
    rw [eq_top_iff]
    intro y _
    have hyX : (y : E) ∈ X := by
      rw [h]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := hyX
    obtain rfl : y' = y := Subtype.ext hyy'
    exact hy'

end Min

section Faithful

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] noncomputable def repHom
    (ρ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E) :
    SpecialLinearGroup (Fin 3) (ZMod 2) →* (E ≃ₗ[ZMod 2] E) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).toMonoidHom.comp
    (ρ.asGroupHom.comp iota.toMonoidHom)

theorem repHom_injective
    (ρ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E)
    (hnt : ∃ g v, ρ g v ≠ v) : Function.Injective (repHom ρ) := by
  have hS : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 le_rfl
  rw [injective_iff_map_eq_one]
  rcases hS.eq_bot_or_eq_top_of_normal (repHom ρ).ker with h | h
  · intro a ha
    rw [← MonoidHom.mem_ker, h] at ha
    exact ha
  · exfalso
    obtain ⟨g, v, hgv⟩ := hnt
    obtain ⟨g', rfl⟩ := iota.surjective g
    have h1 : g' ∈ (repHom ρ).ker := h ▸ Subgroup.mem_top g'
    rw [MonoidHom.mem_ker] at h1
    apply hgv
    have h2 := congrArg (fun f : E ≃ₗ[ZMod 2] E => f v) h1
    exact h2

end Faithful

theorem sixteen_mul_card_fix_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    [Nontrivial E]
    (ρ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E)
    (hfree : ∀ v : E, (∀ g, ρ g v = v) → v = 0) (g₁ : SpecialLinearGroup (Fin 3) (ZMod 2))
    (τ : E ≃ₗ[ZMod 2] E)
    (hτ : ∀ g v, τ (ρ (iota g) v) = ρ (iota (tauT (g₁ * g * g₁⁻¹))) (τ v)) :
    16 * Nat.card {v : E // ρ (iota S77.th0) v = v} ≤ Nat.card E := by
  classical
  set f := ρ (iota S77.th0) with hf
  rw [card_fix_eq f]
  set F := fixSpace f with hF
  obtain ⟨U, hU0, hUmin⟩ := exists_min_subrep ρ
  have hirr := isIrreducible_of_min hU0 hUmin
  have hnt : ∃ g v, U.toRepresentation g v ≠ v := by
    obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U.toSubmodule) (fun h =>
      hU0 (Subrepresentation.toSubmodule_injective h))
    by_contra h
    push Not at h
    exact hv0 (hfree v fun g => congrArg Subtype.val (h g ⟨v, hvU⟩))
  have hinj := repHom_injective U.toRepresentation hnt
  have hfU : ∀ u ∈ U.toSubmodule, f u ∈ U.toSubmodule := fun u hu =>
    U.apply_mem_toSubmodule _ hu
  have hFU : Nat.card {v : U.toSubmodule // U.toRepresentation (iota S77.th0) v = v} =
      Nat.card ↥(F ⊓ U.toSubmodule) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1, mem_fixSpace.2 (congrArg Subtype.val v.2), v.1.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.2⟩, Subtype.ext (mem_fixSpace.1 v.2.1)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hpos : 0 < Nat.card ↥U.toSubmodule := Nat.card_pos
  rcases card_eq_eight_or U.toRepresentation hirr hnt with h8 | h16
  ·
    set U'₀ : Submodule (ZMod 2) E := U.toSubmodule.map (τ : E →ₗ[ZMod 2] E) with hU'₀
    have hU'inv : ∀ (h : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ⦃v : E⦄, v ∈ U'₀ →
        ρ h v ∈ U'₀ := by
      intro h v hv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨g, rfl⟩ := iota.surjective h
      have e1 := hτ (g₁⁻¹ * tauT g * g₁) u
      rw [show g₁ * (g₁⁻¹ * tauT g * g₁) * g₁⁻¹ = tauT g by group, tauT_tauT] at e1
      rw [LinearEquiv.coe_coe, ← e1]
      exact ⟨_, U.apply_mem_toSubmodule _ hu, rfl⟩
    let U' : Subrepresentation ρ := ⟨U'₀, hU'inv⟩
    have hU'8 : Nat.card U'₀ = 8 := by
      rw [← h8]
      exact (Nat.card_congr (τ.submoduleMap U.toSubmodule).toEquiv).symm
    have hinf : U.toSubmodule ⊓ U'₀ = ⊥ := by
      rcases hUmin (U ⊓ U') inf_le_left with h | h
      · exact congrArg Subrepresentation.toSubmodule h
      · exfalso
        have hle : U.toSubmodule ≤ U'₀ :=
          inf_eq_left.1 (congrArg Subrepresentation.toSubmodule h)
        have heq : U'₀ = U.toSubmodule := by
          refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
          have h1 := card_sub U.toSubmodule
          have h2 := card_sub U'₀
          rw [h8] at h1
          rw [hU'8] at h2
          exact Nat.pow_right_injective le_rfl (h1.symm.trans h2)
        let τU : U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule :=
          τ.ofSubmodules U.toSubmodule U.toSubmodule heq
        have hkey : ∀ g, τU * repHom U.toRepresentation g =
            repHom U.toRepresentation (tauT (g₁ * g * g₁⁻¹)) * τU := fun g =>
          LinearEquiv.ext fun v => Subtype.ext (hτ g v)
        exact false_of_twist h8 _ hinj g₁ τU fun g => by rw [hkey g, mul_inv_cancel_right]
    have hfU' : ∀ u ∈ U'₀, f u ∈ U'₀ := fun u hu => hU'inv _ hu
    have hFU2 : Nat.card ↥(F ⊓ U.toSubmodule) ≤ 2 := by
      rw [← hFU]
      refine le_of_eq (card_fix_eq_two h8 (repHom U.toRepresentation S77.th0) ?_ ?_)
      · rw [← map_pow, S77.th0_pow_three, map_one]
      · intro h
        exact S77.th0_ne_one (hinj (h.trans (map_one _).symm))
    set g' := g₁⁻¹ * tauT S77.th0 * g₁ with hg'
    have hσ : tauT (g₁ * g' * g₁⁻¹) = S77.th0 := by
      rw [hg', show g₁ * (g₁⁻¹ * tauT S77.th0 * g₁) * g₁⁻¹ = tauT S77.th0 by group, tauT_tauT]
    have hFU'2 : Nat.card ↥(F ⊓ U'₀) ≤ 2 := by
      have h3 : g' ^ 3 = 1 := by
        have h4 : g' = MulAut.conj g₁⁻¹ (tauT S77.th0) := by rw [hg', MulAut.conj_apply, inv_inv]
        rw [h4, ← map_pow, ← map_pow, S77.th0_pow_three, map_one, map_one]
      have h1 : g' ≠ 1 := by
        intro h
        apply S77.th0_ne_one
        rw [← hσ, h, mul_one, mul_inv_cancel, map_one]
      refine le_trans (Nat.card_le_card_of_injective
        (fun v : ↥(F ⊓ U'₀) => (⟨⟨τ.symm v, ?_⟩, ?_⟩ :
          {u : U.toSubmodule // repHom U.toRepresentation g' u = u})) ?_)
        (le_of_eq (card_fix_eq_two h8 (repHom U.toRepresentation g') (by
          rw [← map_pow, h3, map_one]) fun h => h1 (hinj (h.trans (map_one _).symm))))
      · obtain ⟨u, hu, hvu⟩ := v.2.2
        rw [← hvu, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact hu
      · apply Subtype.ext
        apply τ.injective
        show τ (ρ (iota g') (τ.symm v)) = τ (τ.symm v)
        rw [hτ, hσ, LinearEquiv.apply_symm_apply, ← hf]
        exact mem_fixSpace.1 v.2.1
      · intro v w hvw
        have h2 := congrArg (fun x : {u : U.toSubmodule // repHom U.toRepresentation g' u = u} =>
          ((x.1 : U.toSubmodule) : E)) hvw
        exact Subtype.ext (τ.symm.injective h2)
    have hX : Nat.card ↥(U.toSubmodule ⊔ U'₀) = 64 := by
      rw [card_sup_of_inf_eq_bot hinf, h8, hU'8]
    have hFX : Nat.card ↥(F ⊓ (U.toSubmodule ⊔ U'₀)) ≤ 4 :=
      (card_fix_sup_le hfU hfU' hinf).trans (Nat.mul_le_mul hFU2 hFU'2)
    have h := card_mul_card_le F (U.toSubmodule ⊔ U'₀)
    rw [hX] at h
    have h' := Nat.mul_le_mul_right (Nat.card E) hFX
    omega
  ·
    rw [hFU] at h16
    have h := card_mul_card_le F U.toSubmodule
    have h1 : Nat.card U.toSubmodule * (16 * Nat.card F) ≤
        Nat.card U.toSubmodule * Nat.card E :=
      calc Nat.card U.toSubmodule * (16 * Nat.card F)
          = 16 * (Nat.card F * Nat.card U.toSubmodule) := by ring
        _ ≤ 16 * (Nat.card ↥(F ⊓ U.toSubmodule) * Nat.card E) := Nat.mul_le_mul_left _ h
        _ = (16 * Nat.card ↥(F ⊓ U.toSubmodule)) * Nat.card E := by ring
        _ ≤ Nat.card U.toSubmodule * Nat.card E := Nat.mul_le_mul_right _ h16
    exact Nat.le_of_mul_le_mul_left h1 hpos

theorem sixteen_mul_card_fix_le_of_mulAut {W : Type*} [Group W] [Finite W] [Nontrivial W]
    [IsElementaryAbelian 2 W] (φ : SpecialLinearGroup (Fin 3) (ZMod 2) →* MulAut W)
    (hfree : ∀ w : W, (∀ g, φ g w = w) → w = 1) (g₁ : SpecialLinearGroup (Fin 3) (ZMod 2))
    (τ : MulAut W) (hτ : ∀ g w, τ (φ g w) = φ (tauT (g₁ * g * g₁⁻¹)) (τ w)) :
    16 * Nat.card {w : W // φ S77.th0 w = w} ≤ Nat.card W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) W :=
    MulDistribMulAction.compHom W (φ.comp iota.symm.toMonoidHom)
  set ρ := CFSG.Theory.Representation.ofElementaryAbelianAction
    (A := (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (G := W) (p := 2) with hρdef
  have hρ : ∀ g w, ρ (iota g) (Additive.ofMul w) = Additive.ofMul (φ g w) := by
    intro g w
    rw [hρdef, CFSG.Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    show Additive.ofMul (φ (iota.symm (iota g)) w) = _
    rw [MulEquiv.symm_apply_apply]
  let τA : Additive W ≃+ Additive W := MulEquiv.toAdditive τ
  let τ' : Additive W ≃ₗ[ZMod 2] Additive W :=
    τA.toLinearEquiv (fun c x => by simpa using (ZMod.map_smul τA.toAddMonoidHom c x))
  have hτ' : ∀ w, τ' (Additive.ofMul w) = Additive.ofMul (τ w) := fun _ => rfl
  have key := sixteen_mul_card_fix_le ρ (fun v hv => by
      have h2 : Additive.toMul v = 1 := hfree _ fun g => by
        have h3 := hv (iota g)
        rw [← ofMul_toMul v, hρ] at h3
        exact Additive.ofMul.injective h3
      rw [← ofMul_toMul v, h2]
      rfl)
    g₁ τ' (fun g v => by
      rw [← ofMul_toMul v, hρ, hτ', hτ', hρ, hτ])
  have e1 : Nat.card {v : Additive W // ρ (iota S77.th0) v = v} =
      Nat.card {w : W // φ S77.th0 w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => ?_)
    rw [← ofMul_toMul v, hρ]
    exact ⟨fun h => Additive.ofMul.injective h, fun h => congrArg Additive.ofMul h⟩
  rw [e1] at key
  exact key

end CFSG.Quasithin.H.SL3Rep
