module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Heis
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisFacts
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyPerm

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge

section Pinned

variable {τ : Tag}

theorem pinned_comm_of_not_isRoot
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hposα : 0 < height α)
    (hposβ : 0 < height β) (h : ¬ IsRoot τ (α + β)) {R : Type} [CommRing R] (c d : R) :
    pinnedX τ R α c * pinnedX τ R β d = pinnedX τ R β d * pinnedX τ R α c := by
  by_cases hab : α = β
  · subst hab
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hne' : α ≠ -β := fun h' => by
      have := congrArg height h'
      rw [height_neg'] at this
      omega
    exact (simply_laced_root_commutator_unit τ (simplyLaced_of hτ) hα hβ hab hne').2 h R
      _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem exists_pinned_comm_of_isRoot
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hposα : 0 < height α)
    (hposβ : 0 < height β) (hab : α ≠ β) (h : IsRoot τ (α + β)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (R : Type) [CommRing R] (c d : R),
      ⁅pinnedX τ R α c, pinnedX τ R β d⁆ = pinnedX τ R (α + β) ((ε : R) * c * d) := by
  have hne' : α ≠ -β := fun h' => by
    have := congrArg height h'
    rw [height_neg'] at this
    omega
  obtain ⟨hε, hf⟩ := (simply_laced_root_commutator_unit τ (simplyLaced_of hτ) hα hβ hab hne').1 h
  exact ⟨_, hε, fun R _ c d => hf R c d⟩

end Pinned

variable {τ : Tag} {K : Type} [Field K]

noncomputable abbrev subfieldJ
    (τ : Tag) (σ : K ≃+* K) : Subgroup ↥(adjointGroup τ K) :=
  (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)

@[expose] noncomputable def pinnedJ
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : fixSubfield σ) :
    ↥(subfieldJ τ σ) :=
  ⟨⟨pinnedX τ K α (c : K), pinnedX_mem_adjointGroup α _⟩,
    Subgroup.mem_subgroupOf.2 (pinnedX_mem_fixedFieldImage α c.2)⟩

theorem coe_pinnedJ
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : fixSubfield σ) :
    (((pinnedJ σ α c : ↥(subfieldJ τ σ)) : ↥(adjointGroup τ K)) : ModGL τ K) =
      pinnedX τ K α (c : K) := rfl

theorem pinnedJ_ext
    {σ : K ≃+* K} {x y : ↥(subfieldJ τ σ)}
    (h : (((x : ↥(adjointGroup τ K)) : ModGL τ K)) = (((y : ↥(adjointGroup τ K)) : ModGL τ K))) :
    x = y :=
  Subtype.ext (Subtype.ext h)

theorem pinnedJ_add
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c d : fixSubfield σ) :
    pinnedJ σ α (c + d) = pinnedJ σ α c * pinnedJ σ α d :=
  pinnedJ_ext (pinnedX_add τ K α (c : K) (d : K))

theorem pinnedJ_zero
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) : pinnedJ σ α 0 = 1 :=
  pinnedJ_ext (pinnedX_zero τ K α)

theorem pinnedJ_neg
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : fixSubfield σ) :
    (pinnedJ σ α c)⁻¹ = pinnedJ σ α (-c) :=
  pinnedJ_ext (pinnedX_neg τ K α (c : K))

theorem pinnedJ_injective
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) :
    Function.Injective (pinnedJ (τ := τ) σ α) := fun _ _ h =>
  Subtype.ext (pinnedX_injective τ K α (congrArg (fun x : ↥(subfieldJ τ σ) =>
    (((x : ↥(adjointGroup τ K)) : ModGL τ K))) h))

theorem pinnedJ_comm
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hposα : 0 < height α)
    (hposβ : 0 < height β) (h : ¬ IsRoot τ (α + β)) (c d : fixSubfield σ) :
    pinnedJ σ α c * pinnedJ σ β d = pinnedJ σ β d * pinnedJ σ α c :=
  pinnedJ_ext (pinned_comm_of_not_isRoot hτ hα hβ hposα hposβ h (c : K) (d : K))

theorem exists_comm_ss
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (σ : K ≃+* K) (β : Fin τ.rank → ℤ) (hβ : β ∈ heisS τ) :
    ∃ ε : fixSubfield σ, ε ≠ 0 ∧ ∀ c d : fixSubfield σ,
      ⁅(pinnedJ σ (heisα0 τ - β) c)⁻¹, pinnedJ σ β d⁆ = pinnedJ σ (heisα0 τ) (ε * c * d) := by
  have hβpos := hF.pos_of_mem β hβ
  have hlt := hF.two_height_lt β hβ
  have hγpos : 0 < height (heisα0 τ - β) := by
    rw [height_sub']
    omega
  have hne : heisα0 τ - β ≠ β := fun h => hF.sub_not_mem β hβ (by rw [h]; exact hβ)
  have hsum : heisα0 τ - β + β = heisα0 τ := sub_add_cancel _ _
  obtain ⟨ε', hε', hf⟩ := exists_pinned_comm_of_isRoot hτ (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) hγpos hβpos hne (by rw [hsum]; exact hF.isRoot_α0)
  refine ⟨-(ε' : fixSubfield σ), ?_, fun c d => ?_⟩
  · rcases hε' with rfl | rfl <;> simp
  · rw [pinnedJ_neg]
    refine pinnedJ_ext ?_
    have := hf K (-(c : K)) (d : K)
    simp only [hsum] at this
    show ⁅pinnedX τ K (heisα0 τ - β) (((-c : fixSubfield σ) : K)), pinnedX τ K β (d : K)⁆ = _
    rw [show ((-c : fixSubfield σ) : K) = -(c : K) from rfl, this]
    congr 1
    push_cast
    ring

theorem heis_gamma_pos {hF : HeisFacts τ} {β : Fin τ.rank → ℤ} (hβ : β ∈ heisS τ) :
    0 < height (heisα0 τ - β) := by
  have hlt := hF.two_height_lt β hβ
  have hpos := hF.pos_of_mem β hβ
  rw [height_sub']
  omega

@[expose] noncomputable def heisSystem
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (hα0 : 0 < height (heisα0 τ)) (σ : K ≃+* K) :
    HeisSystem ↥(subfieldJ τ σ) (fixSubfield σ) ↥(heisS τ) where
  xa s c := pinnedJ σ s.1 c
  xb s c := pinnedJ σ (heisα0 τ - s.1) c
  z c := pinnedJ σ (heisα0 τ) c
  ε s := Classical.choose (exists_comm_ss τ hτ hF σ s.1 s.2)
  xa_add s c d := pinnedJ_add σ s.1 c d
  xb_add s c d := pinnedJ_add σ _ c d
  z_add c d := pinnedJ_add σ _ c d
  z_injective := pinnedJ_injective σ _
  ε_ne s := (Classical.choose_spec (exists_comm_ss τ hτ hF σ s.1 s.2)).1
  xa_comm s t c d := pinnedJ_comm hτ σ (hF.isRoot_of_mem _ s.2) (hF.isRoot_of_mem _ t.2)
    (hF.pos_of_mem _ s.2) (hF.pos_of_mem _ t.2) (hF.not_isRoot_SS _ s.2 _ t.2) c d
  xb_comm s t c d := pinnedJ_comm hτ σ (hF.isRoot_sub _ s.2) (hF.isRoot_sub _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (heis_gamma_pos (hF := hF) t.2)
    (hF.not_isRoot_TT _ s.2 _ t.2) c d
  z_comm_a c s d := pinnedJ_comm hτ σ hF.isRoot_α0 (hF.isRoot_of_mem _ s.2) hα0
    (hF.pos_of_mem _ s.2) (hF.not_isRoot_α0_S _ s.2) c d
  z_comm_b c s d := pinnedJ_comm hτ σ hF.isRoot_α0 (hF.isRoot_sub _ s.2) hα0
    (heis_gamma_pos (hF := hF) s.2) (hF.not_isRoot_α0_T _ s.2) c d
  xab_comm s t hst c d := pinnedJ_comm hτ σ (hF.isRoot_sub _ s.2) (hF.isRoot_of_mem _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (hF.pos_of_mem _ t.2)
    (by
      rw [add_comm]
      exact hF.not_isRoot_ST _ t.2 _ s.2 (fun h => hst (Subtype.ext h.symm))) c d
  comm_ss s c d := (Classical.choose_spec (exists_comm_ss τ hτ hF σ s.1 s.2)).2 c d

theorem charP_fixSubfield (σ : K ≃+* K) (r : ℕ) [CharP K r] : CharP (fixSubfield σ) r :=
  (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective r).mpr ‹CharP K r›

theorem nonLocalized_E
    [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (hS : (heisS τ).Nonempty) (hcard : τ.rank + τ.rootCount < 2 ^ (heisS τ).card)
    (σ : K ≃+* K) (hsimple : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ))) :
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
  classical
  obtain ⟨r, hrK⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  let F := AlgebraicClosure K
  have hFr : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
  have hkr : CharP (fixSubfield σ) r := charP_fixSubfield σ r
  obtain ⟨β0, hβ0⟩ := hS
  have hα0 : 0 < height (heisα0 τ) := by
    have h1 := hF.two_height_lt β0 hβ0
    have h2 := hF.pos_of_mem β0 hβ0
    omega
  let ρ : ↥(adjointGroup τ K) →* Module.End F (Label τ → F) :=
    (adjRep τ K F).comp (adjointGroup τ K).subtype
  have hρ : Function.Injective ρ := (adjRep_injective τ K F).comp Subtype.val_injective
  refine nonLocalized_fixedFieldImage_of_closing σ r hsimple ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hVfaith
  have : Fact s.Prime := ⟨hs⟩
  have hVc : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have : Finite V := Subtype.finite
  have hlow := (heisSystem hτ hF hα0 σ).heis_lower_bound (φ := (subfieldJ τ σ).subtype) V hr hs
    (Ne.symm hsr) hVexp (fun g v hv => hVnorm g g.2 v hv)
    (fun g hg => Subtype.ext (hVfaith g g.2 hg))
  have hinv : (Nat.card V : F) ≠ 0 := cast_card_ne_zero_of_exponent hr hs hsr hVexp
  have hup := card_le_pow_finrank ρ hρ V hVc hinv hs.pos hVexp
  rw [finrank_label_pi τ F, card_label_eq τ] at hup
  have h2 := (Nat.pow_le_pow_iff_right hs.one_lt).1 (hlow.trans hup)
  have hk2 : 2 ≤ Nat.card (fixSubfield σ) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hSc : Nat.card ↥(heisS τ) = (heisS τ).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h3 : 2 ^ (heisS τ).card ≤ Nat.card (fixSubfield σ) ^ Nat.card ↥(heisS τ) := by
    rw [hSc]
    exact Nat.pow_le_pow_left hk2 _
  omega

end CFSG.SignalizerFunctorTheorem.NonLocalExc
