module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem c23a_bridgep_mkTil_bot_injective (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y h
  have h1 : x.val * (y.val)⁻¹ ∈ (⊥ : Subgroup G) :=
    (mkTil_eq_iff (⊥ : Subgroup G) V hV x y).1 h
  exact IntMod.val_injective (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h1))

private theorem c23a_bridgep_card_preTil (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (E : Subgroup (Vtil (⊥ : Subgroup G) V hV)) :
    Nat.card (preTil (⊥ : Subgroup G) V hV E) = Nat.card E := by
  have hπ : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
    c23a_bridgep_mkTil_bot_injective V hV
  have hval : Function.Injective (valHom V hV) := fun _ _ h => IntMod.val_injective h
  let e : IntMod V hV ≃* Vtil (⊥ : Subgroup G) V hV :=
    MulEquiv.ofBijective (mkTil (⊥ : Subgroup G) V hV)
      ⟨hπ, mkTil_surjective (⊥ : Subgroup G) V hV⟩
  have hcomap : E.comap (mkTil (⊥ : Subgroup G) V hV) = E.map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm' e E
  rw [preTil, Subgroup.card_map_of_injective (f := valHom V hV) hval, hcomap,
    Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]

private theorem c23a_bridgep_map_eq_of_forall_mem {A : Type*} [Group A] [Finite A]
    (φ : MulAut A) {E E' : Subgroup A} (h : ∀ e ∈ E, φ e ∈ E')
    (hcard : Nat.card E' ≤ Nat.card E) :
    E.map φ.toMonoidHom = E' ∧ E'.map φ⁻¹.toMonoidHom = E := by
  have hle : E.map φ.toMonoidHom ≤ E' := by
    rintro x ⟨e, he, rfl⟩
    exact h e he
  have hcardE : Nat.card (E.map φ.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := φ.toMonoidHom) φ.injective
  have hE' : E.map φ.toMonoidHom = E' :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE]; exact hcard)
  have hle' : E'.map φ⁻¹.toMonoidHom ≤ E := by
    rintro x ⟨y, hy, rfl⟩
    rw [← hE'] at hy
    obtain ⟨e, he, rfl⟩ := hy
    simpa using he
  have hcardE' : Nat.card (E'.map φ⁻¹.toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective (K := E') (f := φ⁻¹.toMonoidHom) (φ⁻¹).injective
  refine ⟨hE', Subgroup.eq_of_le_of_card_ge hle' ?_⟩
  rw [hcardE', ← hE', hcardE]

theorem c23a_bridge_sup {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {E₁ E₂ : Subgroup (Vtil (⊥ : Subgroup G) V hV)} (h : E₁ ⊔ E₂ = ⊤) :
    preTil (⊥ : Subgroup G) V hV E₁ ⊔ preTil (⊥ : Subgroup G) V hV E₂ = V := by
  refine le_antisymm (sup_le (preTil_le _ _ _ _) (preTil_le _ _ _ _)) ?_
  intro v hv
  have hx : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨v, hv⟩) ∈ E₁ ⊔ E₂ := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup (s := E₁) (t := E₂)).1 hx
  obtain ⟨a', rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV a
  obtain ⟨b', rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV b
  have hxab : a' * b' = IntMod.mk hV ⟨v, hv⟩ := by
    apply c23a_bridgep_mkTil_bot_injective V hV
    rw [map_mul]
    exact hab
  have hvab : a'.val * b'.val = v := congrArg IntMod.val hxab
  rw [← hvab]
  exact Subgroup.mul_mem_sup ((mem_preTil _ _ _ _).2 ⟨a', rfl, ha⟩)
    ((mem_preTil _ _ _ _).2 ⟨b', rfl, hb⟩)

theorem c23a_bridge_mSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (E : Subgroup (Vtil (⊥ : Subgroup G) V hV)) :
    mSub (preTil (⊥ : Subgroup G) V hV E) = rk ↥E := by
  unfold mSub rk
  rw [c23a_bridgep_card_preTil V hV E]

theorem c23a_bridge_perm {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G))
    {E₁ E₂ : Subgroup (Vtil (⊥ : Subgroup G) V hV)}
    (h : ∀ φ ∈ barSub (⊥ : Subgroup G) V hV M,
      ((∀ e ∈ E₁, φ e ∈ E₁) ∧ (∀ e ∈ E₂, φ e ∈ E₂)) ∨
        ((∀ e ∈ E₁, φ e ∈ E₂) ∧ (∀ e ∈ E₂, φ e ∈ E₁))) :
    ∀ m ∈ M,
      (conjSubgroup (preTil (⊥ : Subgroup G) V hV E₁) m = preTil (⊥ : Subgroup G) V hV E₁ ∧
        conjSubgroup (preTil (⊥ : Subgroup G) V hV E₂) m = preTil (⊥ : Subgroup G) V hV E₂) ∨
      (conjSubgroup (preTil (⊥ : Subgroup G) V hV E₁) m = preTil (⊥ : Subgroup G) V hV E₂ ∧
        conjSubgroup (preTil (⊥ : Subgroup G) V hV E₂) m = preTil (⊥ : Subgroup G) V hV E₁) := by
  intro m hm
  have hM₀ : M ≤ normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hms : m ∈ stabTil (⊥ : Subgroup G) V := (le_stabTil hM hM₀) hm
  let φ : MulAut (Vtil (⊥ : Subgroup G) V hV) := actTil (⊥ : Subgroup G) V hV ⟨m, hms⟩
  have hφ : φ ∈ barSub (⊥ : Subgroup G) V hV M :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV hm hms
  have hpre₁ : conjSubgroup (preTil (⊥ : Subgroup G) V hV E₁) m =
      preTil (⊥ : Subgroup G) V hV (E₁.map φ⁻¹.toMonoidHom) :=
    (s15_Infra_preTil_map_actTil (⊥ : Subgroup G) V hV hms E₁).symm
  have hpre₂ : conjSubgroup (preTil (⊥ : Subgroup G) V hV E₂) m =
      preTil (⊥ : Subgroup G) V hV (E₂.map φ⁻¹.toMonoidHom) :=
    (s15_Infra_preTil_map_actTil (⊥ : Subgroup G) V hV hms E₂).symm
  rcases h φ hφ with ⟨hA₁, hA₂⟩ | ⟨hB₁, hB₂⟩
  · have h1 := c23a_bridgep_map_eq_of_forall_mem φ hA₁ (le_refl (Nat.card E₁))
    have h2 := c23a_bridgep_map_eq_of_forall_mem φ hA₂ (le_refl (Nat.card E₂))
    exact Or.inl ⟨by rw [hpre₁, h1.2], by rw [hpre₂, h2.2]⟩
  · have hle₁₂ : E₁.map φ.toMonoidHom ≤ E₂ := by
      rintro x ⟨e, he, rfl⟩
      exact hB₁ e he
    have hle₂₁ : E₂.map φ.toMonoidHom ≤ E₁ := by
      rintro x ⟨e, he, rfl⟩
      exact hB₂ e he
    have hc₁₂ : Nat.card E₁ ≤ Nat.card E₂ := by
      rw [← Subgroup.card_map_of_injective (K := E₁) (f := φ.toMonoidHom) φ.injective]
      exact Subgroup.card_le_of_le hle₁₂
    have hc₂₁ : Nat.card E₂ ≤ Nat.card E₁ := by
      rw [← Subgroup.card_map_of_injective (K := E₂) (f := φ.toMonoidHom) φ.injective]
      exact Subgroup.card_le_of_le hle₂₁
    have h1 := c23a_bridgep_map_eq_of_forall_mem φ hB₁ hc₂₁
    have h2 := c23a_bridgep_map_eq_of_forall_mem φ hB₂ hc₁₂
    exact Or.inr ⟨by rw [hpre₁, h2.2], by rw [hpre₂, h1.2]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
