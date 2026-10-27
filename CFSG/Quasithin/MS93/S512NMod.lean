module

public import CFSG.Quasithin.MS93.S512NQ
public import CFSG.Quasithin.MS93.S38EFFHyp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

section Embed

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem ofA_mem_stab_baseA (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ stab (puAmalgam hTM) (baseA _) := by
  rw [puAmalgam.stab_baseA]
  exact ⟨m, Subgroup.mem_subgroupOf.2 m.2, rfl⟩

@[expose] noncomputable def eM : ↥M →* ↥(stab (puAmalgam hTM) (baseA _)) :=
  (puAmalgam hTM).ofA.codRestrict _ (ofA_mem_stab_baseA hTM)

theorem coe_eM (m : ↥M) : (eM hTM m : (puAmalgam hTM).Universal) = (puAmalgam hTM).ofA m := rfl

theorem eM_surjective : Function.Surjective (eM hTM) := by
  rintro ⟨y, hy⟩
  rw [puAmalgam.stab_baseA] at hy
  obtain ⟨m, -, rfl⟩ := hy
  exact ⟨m, rfl⟩

theorem eM_injective : Function.Injective (eM hTM) := fun _ _ h =>
  (puAmalgam hTM).ofA_injective (congrArg Subtype.val h)

end Embed

section Invariant

variable {Γ : Type*} [Group Γ] {S : Type} [CommGroup S]

@[expose] def IsInv (ρ : Γ →* MulAut S) (S₀ : Subgroup S) : Prop := ∀ g : Γ, ∀ s ∈ S₀, ρ g s ∈ S₀

@[expose] noncomputable def restrict (ρ : Γ →* MulAut S) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) :
    Γ →* MulAut ↥S₀ where
  toFun g :=
    { toFun := fun s => ⟨ρ g s, hS₀ g s s.2⟩
      invFun := fun s => ⟨ρ g⁻¹ s, hS₀ g⁻¹ s s.2⟩
      left_inv := fun s => Subtype.ext (by
        change ρ g⁻¹ (ρ g s) = s
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun s => Subtype.ext (by
        change ρ g (ρ g⁻¹ s) = s
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun s t => Subtype.ext (by simp) }
  map_one' := by
    ext s
    simp
  map_mul' g g' := by
    ext s
    simp

theorem coe_restrict_apply (ρ : Γ →* MulAut S) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (g : Γ)
    (s : ↥S₀) : ((restrict ρ hS₀ g s : ↥S₀) : S) = ρ g s := rfl

theorem exists_minimal_invariant [Finite S] (ρ : Γ →* MulAut S) (hS : Nontrivial S) :
    ∃ S₀ : Subgroup S, S₀ ≠ ⊥ ∧ IsInv ρ S₀ ∧
      ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀ := by
  set P : Set (Subgroup S) := {S₁ | S₁ ≠ ⊥ ∧ IsInv ρ S₁} with hP
  have hne : P.Nonempty := ⟨⊤, top_ne_bot, fun g s _ => Subgroup.mem_top _⟩
  obtain ⟨S₀, ⟨hS₀, hS₀i⟩, hmin⟩ :=
    (InvImage.wf (fun S₁ : Subgroup S => Nat.card S₁) Nat.lt_wfRel.wf).has_min P hne
  refine ⟨S₀, hS₀, hS₀i, fun S₁ hS₁ hS₁i hle => ?_⟩
  by_contra hne'
  apply hmin S₁ ⟨hS₁, hS₁i⟩
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne')

end Invariant

section Irr

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {S : Type} [CommGroup S] {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}

theorem isIrrRep_comp {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    (hsq : ∀ s : S, s ^ 2 = 1)
    (hQ : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) → restrict ρ hS₀ g = 1)
    (hL : ∀ s : S, (∀ l : ↥(stab (puAmalgam h.le) (baseA _)),
      (l : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) → ρ l s = s) → s = 1) :
    S38E.IsIrrRep L ((restrict ρ hS₀).comp (eM h.le)) where
  sq v := Subtype.ext (by simpa using hsq (v : S))
  pCore m hm := by
    have hmQ : (eM h.le m : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) := by
      rw [S5B.qv_baseA_eq h, coe_eM]
      exact (ofA_mem_imM_iff h.le m).2 hm
    rw [MonoidHom.comp_apply]
    exact hQ (eM h.le m) hmQ
  irr W hW := by
    set S₁ : Subgroup S := W.map S₀.subtype with hS₁
    have hS₁i : IsInv ρ S₁ := by
      rintro g _ ⟨w, hw, rfl⟩
      obtain ⟨m, rfl⟩ := eM_surjective h.le g
      exact ⟨_, hW m w hw, rfl⟩
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      have hS₁0 : S₁ ≠ ⊥ := by
        intro h0
        apply hW0
        rw [eq_bot_iff]
        intro w hw
        have : (w : S) ∈ S₁ := ⟨w, hw, rfl⟩
        rw [h0, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (Subtype.ext this)
      have he := hmin S₁ hS₁0 hS₁i (Subgroup.map_subtype_le W)
      rw [eq_top_iff]
      intro w _
      have hw : (w : S) ∈ S₁ := by rw [he]; exact w.2
      obtain ⟨w', hw', hww'⟩ := hw
      rwa [Subtype.ext hww'] at hw'
  ne := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    refine hL s fun l hl => ?_
    rw [S5B.puTrans_L_baseA h] at hl
    obtain ⟨m, hm, hml⟩ := hl
    have h1 := hcon m (Subgroup.mem_subgroupOf.1 hm)
    have h2 := congrArg (fun φ : MulAut ↥S₀ => ((φ ⟨s, hs⟩ : ↥S₀) : S)) h1
    simp only [MonoidHom.comp_apply, coe_restrict_apply, MulAut.one_apply] at h2
    have hl' : eM h.le m = l := Subtype.ext hml
    rwa [hl'] at h2

end Irr

end S512N

end CFSG.Quasithin.MS93
