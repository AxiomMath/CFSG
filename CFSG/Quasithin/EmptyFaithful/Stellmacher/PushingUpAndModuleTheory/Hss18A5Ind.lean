module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Min
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassification

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem nat_alt_irred (Y : Subgroup nat.W)
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, nat.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : ∀ u ∈ Y, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
  · right
    push Not at hbot
    obtain ⟨x, hxY, hx1⟩ := hbot
    rw [eq_top_iff]
    intro y _
    by_cases hy1 : y = 1
    · rw [hy1]; exact Y.one_mem
    · obtain ⟨σ, hσ, hσy⟩ := nat_transitive x y hx1 hy1
      rw [← hσy]
      exact hY σ hσ x hxY

private theorem orth_wt_two_or_four : ∀ y : orth.W, y ≠ 1 → wtO y = 2 ∨ wtO y = 4 := by
  decide +kernel

private theorem orth_gen_four : ∀ y : orth.W, wtO y = 4 →
    ∃ y₁ y₂ : orth.W, wtO y₁ = 2 ∧ wtO y₂ = 2 ∧ y = y₁ * y₂ := by decide +kernel

private theorem orth_gen_two : ∀ y : orth.W, wtO y = 2 →
    ∃ y₁ y₂ : orth.W, wtO y₁ = 4 ∧ wtO y₂ = 4 ∧ y = y₁ * y₂ := by decide +kernel

theorem orth_alt_irred (Y : Subgroup orth.W)
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, orth.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : ∀ u ∈ Y, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
  · right
    push Not at hbot
    obtain ⟨x, hxY, hx1⟩ := hbot
    have horb : ∀ y : orth.W, y ≠ 1 → wtO y = wtO x → y ∈ Y := fun y hy hw => by
      obtain ⟨σ, hσ, hσy⟩ := (orth_orbits x y hx1 hy).mpr hw.symm
      rw [← hσy]
      exact hY σ hσ x hxY
    rw [eq_top_iff]
    intro y _
    by_cases hy1 : y = 1
    · rw [hy1]; exact Y.one_mem
    rcases orth_wt_two_or_four x hx1 with hx | hx <;> rcases orth_wt_two_or_four y hy1 with hy | hy
    · exact horb y hy1 (hy.trans hx.symm)
    · obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := orth_gen_four y hy
      have h1 : y₁ ≠ 1 := fun h => by simp [h] at h₁; revert h₁; decide +kernel
      have h2 : y₂ ≠ 1 := fun h => by simp [h] at h₂; revert h₂; decide +kernel
      exact Y.mul_mem (horb y₁ h1 (h₁.trans hx.symm)) (horb y₂ h2 (h₂.trans hx.symm))
    · obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := orth_gen_two y hy
      have h1 : y₁ ≠ 1 := fun h => by simp [h] at h₁; revert h₁; decide +kernel
      have h2 : y₂ ≠ 1 := fun h => by simp [h] at h₂; revert h₂; decide +kernel
      exact Y.mul_mem (horb y₁ h1 (h₁.trans hx.symm)) (horb y₂ h2 (h₂.trans hx.symm))
    · exact horb y hy1 (hy.trans hx.symm)

section Coind

variable {W : Type} [CommGroup W]

@[expose] def coindSub (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W) :
    Subgroup (Perm (Fin 5) → W) where
  carrier := {f | ∀ (a : Perm (Fin 5)) (ha : a ∈ alternatingGroup (Fin 5)) (τ : Perm (Fin 5)),
    f (a * τ) = ρ ⟨a, ha⟩ (f τ)}
  one_mem' := fun a ha τ => by simp
  mul_mem' := fun {f g} hf hg a ha τ => by
    simp only [Pi.mul_apply, hf a ha τ, hg a ha τ, map_mul]
  inv_mem' := fun {f} hf a ha τ => by
    simp only [Pi.inv_apply, hf a ha τ, map_inv]

variable (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W)

@[expose] def coindShift (σ : Perm (Fin 5)) (f : coindSub ρ) : coindSub ρ :=
  ⟨fun τ => f.1 (τ * σ), fun a ha τ => by simpa [mul_assoc] using f.2 a ha (τ * σ)⟩

@[expose] def coindAut (σ : Perm (Fin 5)) : MulAut (coindSub ρ) where
  toFun := coindShift ρ σ
  invFun := coindShift ρ σ⁻¹
  left_inv := fun f => Subtype.ext (funext fun τ => by simp [coindShift])
  right_inv := fun f => Subtype.ext (funext fun τ => by simp [coindShift])
  map_mul' := fun f g => Subtype.ext (funext fun τ => rfl)

variable [Finite W]

@[expose] def coindModel (hsq : ∀ w : W, w * w = 1) : Model 5 where
  W := coindSub ρ
  grp := Subgroup.toCommGroup _
  fin := inferInstance
  act :=
    { toFun := coindAut ρ
      map_one' := MulEquiv.ext fun f => Subtype.ext (funext fun τ => by
        simp [coindAut, coindShift])
      map_mul' := fun σ τ => MulEquiv.ext fun f => Subtype.ext (funext fun x => by
        simp [coindAut, coindShift, mul_assoc]) }
  sq := fun f => Subtype.ext (funext fun τ => hsq _)

variable (hsq : ∀ w : W, w * w = 1)

theorem coindModel_act_apply (σ : Perm (Fin 5)) (f : (coindModel ρ hsq).W) (τ : Perm (Fin 5)) :
    ((coindModel ρ hsq).act σ f).1 τ = f.1 (τ * σ) := rfl

@[expose] def coindEval : (coindModel ρ hsq).W →* W where
  toFun f := f.1 1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coindEval_apply (f : (coindModel ρ hsq).W) : coindEval ρ hsq f = f.1 1 := rfl

theorem coindEval_act_alt {a : Perm (Fin 5)} (ha : a ∈ alternatingGroup (Fin 5))
    (f : (coindModel ρ hsq).W) :
    coindEval ρ hsq ((coindModel ρ hsq).act a f) = ρ ⟨a, ha⟩ (coindEval ρ hsq f) := by
  rw [coindEval_apply, coindEval_apply, coindModel_act_apply, one_mul]
  have := f.2 a ha 1
  rw [mul_one] at this
  exact this

theorem coindEval_act (σ : Perm (Fin 5)) (f : (coindModel ρ hsq).W) :
    coindEval ρ hsq ((coindModel ρ hsq).act σ f) = f.1 σ := by
  rw [coindEval_apply, coindModel_act_apply, one_mul]

theorem fixW_top_coind (hfree : ∀ w : W, (∀ a (ha : a ∈ alternatingGroup (Fin 5)),
    ρ ⟨a, ha⟩ w = w) → w = 1) : fixW (coindModel ρ hsq) ⊤ = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have h1 : ∀ σ : Perm (Fin 5), f.1 σ = f.1 1 := fun σ => by
    have := congrArg (fun g : (coindModel ρ hsq).W => g.1 1) (hf σ (Subgroup.mem_top σ))
    simpa [coindModel_act_apply] using this
  have h2 : f.1 1 = 1 := by
    refine hfree _ fun a ha => ?_
    have := f.2 a ha 1
    rw [mul_one] at this
    rw [← this, h1 a]
  rw [Subgroup.mem_bot]
  exact Subtype.ext (funext fun σ => by rw [h1, h2]; rfl)

open Classical in
@[expose] noncomputable def coindOfVec (w : W) : (coindModel ρ hsq).W :=
  ⟨fun τ => if h : τ ∈ alternatingGroup (Fin 5) then ρ ⟨τ, h⟩ w else 1, fun a ha τ => by
    by_cases hτ : τ ∈ alternatingGroup (Fin 5)
    · have hat : a * τ ∈ alternatingGroup (Fin 5) := Subgroup.mul_mem _ ha hτ
      simp only [hτ, hat, dite_true]
      exact map_mul ρ ⟨a, ha⟩ ⟨τ, hτ⟩ ▸ rfl
    · have hat : a * τ ∉ alternatingGroup (Fin 5) := fun h' =>
        hτ (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) h')
      simp [hτ, hat]⟩

open Classical in
theorem coindEval_coindOfVec (w : W) : coindEval ρ hsq (coindOfVec ρ hsq w) = w := by
  rw [coindEval_apply]
  show (if h : (1 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) then ρ ⟨1, h⟩ w else 1) = w
  rw [dite_eq_left_of_eq_true (eq_true (Subgroup.one_mem _))]
  exact congrArg (fun φ => φ w) (map_one ρ)

end Coind

theorem injective_of_alt_irred {W : Type} [CommGroup W] {Q P : Model 5} (e : Q.Iso P)
    (hP : ∀ Y : Subgroup P.W, (∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, P.act σ y ∈ Y) →
      Y = ⊥ ∨ Y = ⊤)
    (ι : Q.W →* W) (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W)
    (hι : ∀ a (ha : a ∈ alternatingGroup (Fin 5)) u, ι (Q.act a u) = ρ ⟨a, ha⟩ (ι u))
    (hnz : ∃ u, ι u ≠ 1) : Function.Injective ι := by
  rw [injective_iff_map_eq_one]
  set U : Subgroup P.W := ι.ker.map e.toMulEquiv.toMonoidHom with hU
  have hUinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ U, P.act σ y ∈ U := by
    rintro σ hσ _ ⟨k, hk, rfl⟩
    refine ⟨Q.act σ k, ?_, e.map_act σ k⟩
    have hk' : ι k = 1 := hk
    show ι (Q.act σ k) = 1
    rw [hι σ hσ, hk', map_one]
  intro u hu
  rcases hP U hUinv with h | h
  · have : e.toMulEquiv u ∈ U := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact e.toMulEquiv.injective (by simpa using this)
  · exfalso
    obtain ⟨v, hv⟩ := hnz
    have : e.toMulEquiv v ∈ U := by rw [h]; trivial
    obtain ⟨k, hk, hkv⟩ := this
    have := e.toMulEquiv.injective hkv
    exact hv (this ▸ (hk : ι k = 1))

theorem exists_inj_model {W : Type} [CommGroup W] [Finite W] (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W)
    (hsq : ∀ w : W, w * w = 1)
    (hfree : ∀ w : W, (∀ a (ha : a ∈ alternatingGroup (Fin 5)), ρ ⟨a, ha⟩ w = w) → w = 1)
    {w₀ : W} (hw₀ : w₀ ≠ 1) :
    ∃ Q : Model 5, (Nonempty (Q.Iso orth) ∨ Nonempty (Q.Iso nat)) ∧ fixW Q ⊤ = ⊥ ∧
      ∃ ι : Q.W →* W, Function.Injective ι ∧
        ∀ a (ha : a ∈ alternatingGroup (Fin 5)) u, ι (Q.act a u) = ρ ⟨a, ha⟩ (ι u) := by
  set M := coindModel ρ hsq with hM
  have hfixM : fixW M ⊤ = ⊥ := fixW_top_coind ρ hsq hfree
  have hntM : ∃ w : M.W, w ≠ 1 := ⟨coindOfVec ρ hsq w₀, fun h => hw₀ (by
    rw [← coindEval_coindOfVec ρ hsq w₀, h, map_one])⟩
  obtain ⟨N, hN, hNbot, hirr⟩ := exists_minimal_inv M hntM
  have hfixQ : fixW (M.restrict N hN) ⊤ = ⊥ := by
    rw [fixW_restrict, hfixM]
    exact Subgroup.bot_subgroupOf (H := N)
  have hmoved : ∃ σ w, (M.restrict N hN).act σ w ≠ w := by
    by_contra hall
    push Not at hall
    apply hNbot
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hfix' : u ∈ fixW M ⊤ := by
      intro b _
      exact congrArg Subtype.val (hall b ⟨u, hu⟩)
    rw [hfixM, Subgroup.mem_bot] at hfix'
    exact hfix'
  set ι : (M.restrict N hN).W →* W := (coindEval ρ hsq).comp N.subtype with hι
  have hequiv : ∀ a (ha : a ∈ alternatingGroup (Fin 5)) u,
      ι ((M.restrict N hN).act a u) = ρ ⟨a, ha⟩ (ι u) := fun a ha u =>
    coindEval_act_alt ρ hsq ha u.1
  have hnz : ∃ u, ι u ≠ 1 := by
    obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    have : ∃ σ, f.1.1 σ ≠ 1 := by
      by_contra h
      push Not at h
      exact hf1 (Subtype.ext (Subtype.ext (funext h)))
    obtain ⟨σ, hσ⟩ := this
    refine ⟨(M.restrict N hN).act σ f, ?_⟩
    show coindEval ρ hsq (M.act σ f.1) ≠ 1
    rw [coindEval_act]
    exact hσ
  have hcl := model5_irred_classification _ hirr hmoved
  refine ⟨M.restrict N hN, hcl, hfixQ, ι, ?_, hequiv⟩
  rcases hcl with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact injective_of_alt_irred e orth_alt_irred ι ρ hequiv hnz
  · exact injective_of_alt_irred e nat_alt_irred ι ρ hequiv hnz

end CFSG.Quasithin.F53Mod
