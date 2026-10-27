module

public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.CosetTable

section Ev

variable {G H : Type*} [Group G] [Group H] {m : ℕ}

@[simp] theorem burnsideF48s_ev_nil (h : Fin m → G) : burnsideF48s_ev h [] = 1 := rfl

theorem burnsideF48s_ev_cons (h : Fin m → G) (l : Fin m × Bool) (w : List (Fin m × Bool)) :
    burnsideF48s_ev h (l :: w) = cond l.2 (h l.1) (h l.1)⁻¹ * burnsideF48s_ev h w := rfl

theorem burnsideF48s_ev_append (h : Fin m → G) (u v : List (Fin m × Bool)) :
    burnsideF48s_ev h (u ++ v) = burnsideF48s_ev h u * burnsideF48s_ev h v := by
  simp [burnsideF48s_ev, List.map_append, List.prod_append]

theorem burnsideF48s_ev_map (f : G →* H) (h : Fin m → G) (w : List (Fin m × Bool)) :
    burnsideF48s_ev (fun i => f (h i)) w = f (burnsideF48s_ev h w) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [burnsideF48s_ev_cons, burnsideF48s_ev_cons, ih, map_mul]
    congr 1
    cases l.2 <;> simp

theorem burnsideF48s_ev_replicate (h : Fin m → G) (u : List (Fin m × Bool)) (k : ℕ) :
    burnsideF48s_ev h (List.replicate k u).flatten = burnsideF48s_ev h u ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero]; rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, burnsideF48s_ev_append, ih, pow_succ']

theorem burnsideF48s_ev_mem {K : Subgroup G} (h : Fin m → G) (w : List (Fin m × Bool))
    (hw : ∀ l ∈ w, h l.1 ∈ K) : burnsideF48s_ev h w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [burnsideF48s_ev_cons]
    refine K.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have := hw l List.mem_cons_self
    cases l.2
    · exact K.inv_mem this
    · exact this

theorem burnsideF48s_lift_mk (h : Fin m → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift h (FreeGroup.mk w) = burnsideF48s_ev h w := by
  rw [FreeGroup.lift_mk]
  rfl

theorem burnsideF48s_ev_congr {h h' : Fin m → G} (w : List (Fin m × Bool))
    (hw : ∀ l ∈ w, h l.1 = h' l.1) : burnsideF48s_ev h w = burnsideF48s_ev h' w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [burnsideF48s_ev_cons, burnsideF48s_ev_cons, hw l List.mem_cons_self,
      ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]

end Ev

section Pres

variable {m : ℕ} (ws : List (List (Fin m × Bool))) {G : Type*} [Group G] (h : Fin m → G)

noncomputable def burnsideF48s_presHom (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1) :
    PG m ws →* G :=
  PresentedGroup.toGroup (f := h) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [burnsideF48s_lift_mk]
    exact hrel w hw)

variable {ws h}

theorem burnsideF48s_presHom_of (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1) (i : Fin m) :
    burnsideF48s_presHom ws h hrel (PresentedGroup.of i) = h i := by
  rw [burnsideF48s_presHom, PresentedGroup.toGroup.of]

theorem burnsideF48s_presHom_surjective (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1)
    (hgen : Subgroup.closure (Set.range h) = ⊤) :
    Function.Surjective (burnsideF48s_presHom ws h hrel) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, burnsideF48s_presHom_of hrel i⟩

theorem burnsideF48s_presHom_bijective [Finite G] (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1)
    (hgen : Subgroup.closure (Set.range h) = ⊤) [Finite (PG m ws)]
    (hcard : Nat.card (PG m ws) ≤ Nat.card G) :
    Function.Bijective (burnsideF48s_presHom ws h hrel) :=
  (burnsideF48s_presHom_surjective hrel hgen).bijective_of_nat_card_le hcard

theorem burnsideF48s_card_le_of_pres [Finite (PG m ws)] (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1)
    (hgen : Subgroup.closure (Set.range h) = ⊤) : Nat.card G ≤ Nat.card (PG m ws) :=
  Nat.card_le_card_of_surjective _ (burnsideF48s_presHom_surjective hrel hgen)

theorem burnsideF48s_equiv_of_pres {Y D : Type*} [Group Y] [Group D] [Finite D] {y : Fin m → Y}
    {d : Fin m → D} (hy : ∀ w ∈ ws, burnsideF48s_ev y w = 1)
    (hd : ∀ w ∈ ws, burnsideF48s_ev d w = 1) (hyg : Subgroup.closure (Set.range y) = ⊤)
    (hdg : Subgroup.closure (Set.range d) = ⊤) [Finite (PG m ws)]
    (hcard : Nat.card (PG m ws) ≤ Nat.card D) (hYD : Nat.card D ≤ Nat.card Y) :
    ∃ φ : Y ≃* D, ∀ i, φ (y i) = d i := by
  have hbD := burnsideF48s_presHom_bijective hd hdg hcard
  have hsY := burnsideF48s_presHom_surjective hy hyg
  have hPfin : Finite (PG m ws) := inferInstance
  haveI : Finite Y := by
    exact Finite.of_surjective _ hsY
  have hbY : Function.Bijective (burnsideF48s_presHom ws y hy) :=
    hsY.bijective_of_nat_card_le (hcard.trans hYD)
  let eY := MulEquiv.ofBijective _ hbY
  let eD := MulEquiv.ofBijective _ hbD
  refine ⟨eY.symm.trans eD, fun i => ?_⟩
  have h1 : eY (PresentedGroup.of i) = y i := burnsideF48s_presHom_of hy i
  rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  exact burnsideF48s_presHom_of hd i

end Pres

theorem burnsideF48s_qe_of_equiv {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (φ : Y ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : ↥M₁, ((φ (β.φ1 x) : ↥(M₁ ⊔ M₂)) : E) ∈ M₁)
    (h2 : ∀ x : ↥M₂, ((φ (β.φ2 x) : ↥(M₁ ⊔ M₂)) : E) ∈ M₂) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let F : Y →* E := (M₁ ⊔ M₂).subtype.comp φ.toMonoidHom
  let χ₁ : ↥M₁ →* ↥M₁ := (F.comp β.φ1).codRestrict M₁ h1
  let χ₂ : ↥M₂ →* ↥M₂ := (F.comp β.φ2).codRestrict M₂ h2
  have h12 : ∀ x : ↥(M₁ ⊓ M₂), ((φ (β.φ12 x) : ↥(M₁ ⊔ M₂)) : E) ∈ M₁ ⊓ M₂ := by
    intro x
    refine ⟨?_, ?_⟩
    · rw [← β.comm1 x]; exact h1 _
    · rw [← β.comm2 x]; exact h2 _
  let χ₁₂ : ↥(M₁ ⊓ M₂) →* ↥(M₁ ⊓ M₂) := (F.comp β.φ12).codRestrict (M₁ ⊓ M₂) h12
  have hinj : ∀ {H : Subgroup E} (f : ↥H →* Y), Function.Injective f →
      ∀ (χ : ↥H →* ↥H), (∀ x, ((χ x : ↥H) : E) = ((φ (f x) : ↥(M₁ ⊔ M₂)) : E)) →
        Function.Bijective χ := by
    intro H f hf χ hχ
    have hχi : Function.Injective χ := by
      intro x y hxy
      apply hf
      apply φ.injective
      apply Subtype.ext
      rw [← hχ, ← hχ, hxy]
    exact ⟨hχi, Finite.injective_iff_surjective.1 hχi⟩
  have b1 := hinj (H := M₁) β.φ1 hβ.1 χ₁ fun _ => rfl
  have b2 := hinj (H := M₂) β.φ2 hβ.2.2 χ₂ fun _ => rfl
  have b12 := hinj (H := M₁ ⊓ M₂) β.φ12 hβ.2.1 χ₁₂ fun _ => rfl
  let ψ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂) :=
    { φ1 := MulEquiv.ofBijective χ₁ b1
      φ12 := MulEquiv.ofBijective χ₁₂ b12
      φ2 := MulEquiv.ofBijective χ₂ b2
      comm1 := fun g => by
        apply Subtype.ext
        show ((φ (β.φ12 g) : ↥(M₁ ⊔ M₂)) : E) = ((φ (β.φ1 _) : ↥(M₁ ⊔ M₂)) : E)
        rw [β.comm1]
      comm2 := fun g => by
        apply Subtype.ext
        show ((φ (β.φ12 g) : ↥(M₁ ⊔ M₂)) : E) = ((φ (β.φ2 _) : ↥(M₁ ⊔ M₂)) : E)
        rw [β.comm2] }
  refine ⟨φ, burnsideF48_toAmIso ψ, fun d x => ?_⟩
  cases d
  · exact Subtype.ext rfl
  · exact Subtype.ext rfl
  · exact Subtype.ext rfl

end CFSG.ASVolI
