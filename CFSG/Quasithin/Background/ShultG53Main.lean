module

public import CFSG.Quasithin.Background.ShultG53Ident
public import CFSG.Quasithin.Background.ShultG53Transport2
public import CFSG.Quasithin.Background.ShultG53Form

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv


@[expose] def SixStmt : Prop :=
  ∀ (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier), w ≠ 0 →
    (∀ h : ↥(alternatingGroup (Fin 6)), ρk k h (x0 k) = x0 k → W.ρ h w = w) →
    AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤ →
    Nat.card ↥(AddSubgroup.closure (Set.range
      fun g : {h : ↥(alternatingGroup (Fin 6)) //
        ∀ y : V4, linePred k y → linePred k (ρk k h y)} => W.ρ (g : ↥(alternatingGroup (Fin 6))) w))
      = 4 → W.Iso (Mk k) ∨ W.IsFiveDimCover (Mk k)

structure ModelCover : Prop where
  cover3 : ∀ k : Fin 2, ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 0) →+ C.carrier),
    Function.Surjective π ∧ (∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2) ∧
    (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
      π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n)) ∧ C.IsFiveDimCover (Mk k)
  cover5 : ∀ k : Fin 2, ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 2) →+ C.carrier),
    Function.Surjective π ∧ (∀ n : ↥(Nk k 2), π n = 0 ↔ (n : Fn) ∈ Nk k 4) ∧
    (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 2)),
      π ⟨permAct (Mk k) g n, N2_inv k g n n.2⟩ = C.ρ g (π n)) ∧ C.IsFiveDimCover (Mk (1 - k))
  six : SixStmt

theorem form_transport {V₁ : Md ↥(alternatingGroup (Fin 6))} {k : Fin 2} (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (B : LinearMap.BilinForm (ZMod 2) V₁.carrier) (hB1 : ∀ x, B x x = 0)
    (hB2 : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hB3 : ∀ (g : ↥(alternatingGroup (Fin 6))) x y, B (V₁.ρ g x) (V₁.ρ g y) = B x y) :
    ∀ x y : V4, B (e.symm x) (e.symm y) = B0 x y := by
  have hes : ∀ (g : ↥(alternatingGroup (Fin 6))) (x : V4),
      e.symm (ρk k g x) = V₁.ρ g (e.symm x) := fun g x => by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  refine form_unique k (fun x y => B (e.symm x) (e.symm y)) (fun x x' y => ?_)
    (fun x y y' => ?_) (fun x => hB1 _) (fun g x y => ?_) (fun x hx => ?_)
  · simp only [map_add, LinearMap.add_apply]
  · simp only [map_add]
  · simp only [hes]
    exact hB3 g _ _
  · have h0 : e.symm x = 0 := hB2 _ (fun y' => by
      have := hx (e y')
      simpa using this)
    exact e.symm.injective (h0.trans (map_zero e.symm).symm)

theorem ρ_injective_md (W : Md ↥(alternatingGroup (Fin 6))) (g : ↥(alternatingGroup (Fin 6))) :
    Function.Injective (W.ρ g) := by
  intro a b h
  have := congrArg (W.ρ g⁻¹) h
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem part6_of_data (mc : ModelCover) {V₁ : Md ↥(alternatingGroup (Fin 6))} {k : Fin 2}
    (e₁ : V₁.carrier ≃+ V4)
    (he₁ : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e₁ (V₁.ρ g m) = ρk k g (e₁ m))
    (cA : ↥(alternatingGroup (Fin 6))) (G₁ G₂ : Subgroup (Perm (Fin 6)))
    (hG1 : ∀ g : ↥(alternatingGroup (Fin 6)), g ∈ inG G₁ ↔ ρk k (cA * g * cA⁻¹) (x0 k) = x0 k)
    (hG2 : ∀ g : ↥(alternatingGroup (Fin 6)), g ∈ inG G₂ ↔
      ∀ y : V4, linePred k y → linePred k (ρk k (cA * g * cA⁻¹) y)) : Part6 G₁ G₂ V₁ := by
  rintro W ⟨w, hw0, hfix, hgen, hline⟩
  have hmul : ∀ g : ↥(alternatingGroup (Fin 6)), W.ρ g (W.ρ cA w) = W.ρ (g * cA) w := fun g => by
    rw [map_mul]
    rfl
  have hw'0 : W.ρ cA w ≠ 0 := by
    intro h
    apply hw0
    have := congrArg (W.ρ cA⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this
  have hfix' : ∀ h : ↥(alternatingGroup (Fin 6)), ρk k h (x0 k) = x0 k →
      W.ρ h (W.ρ cA w) = W.ρ cA w := by
    intro h hh
    have hg : cA⁻¹ * h * cA ∈ inG G₁ := (hG1 _).mpr (by
      have : cA * (cA⁻¹ * h * cA) * cA⁻¹ = h := by group
      rw [this]
      exact hh)
    have h1 := hfix _ hg
    calc W.ρ h (W.ρ cA w) = W.ρ cA (W.ρ (cA⁻¹ * h * cA) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2
          group
      _ = W.ρ cA w := by rw [h1]
  have hgen' : AddSubgroup.closure
      (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (W.ρ cA w)) = ⊤ := by
    have hr : Set.range (fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (W.ρ cA w)) =
        Set.range (fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g * cA, (hmul g).symm⟩
      · rintro ⟨g, rfl⟩
        refine ⟨g * cA⁻¹, ?_⟩
        show W.ρ (g * cA⁻¹) (W.ρ cA w) = W.ρ g w
        rw [hmul, mul_assoc, inv_mul_cancel, mul_one]
    rw [hr]
    exact hgen
  have hline' : Nat.card ↥(AddSubgroup.closure (Set.range
      fun g : {h : ↥(alternatingGroup (Fin 6)) //
        ∀ y : V4, linePred k y → linePred k (ρk k h y)} =>
        W.ρ (g : ↥(alternatingGroup (Fin 6))) (W.ρ cA w))) = 4 := by
    let f : W.carrier →+ W.carrier := (W.ρ cA).toAddMonoidHom
    have hr : Set.range (fun g : {h : ↥(alternatingGroup (Fin 6)) //
        ∀ y : V4, linePred k y → linePred k (ρk k h y)} =>
          W.ρ (g : ↥(alternatingGroup (Fin 6))) (W.ρ cA w)) =
        f '' Set.range (fun g : ↥(inG G₂) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w) := by
      ext x
      constructor
      · rintro ⟨⟨h, hh⟩, rfl⟩
        have hg : cA⁻¹ * h * cA ∈ inG G₂ := (hG2 _).mpr (by
          have : cA * (cA⁻¹ * h * cA) * cA⁻¹ = h := by group
          rw [this]
          exact hh)
        refine ⟨_, ⟨⟨_, hg⟩, rfl⟩, ?_⟩
        show W.ρ cA (W.ρ (cA⁻¹ * h * cA) w) = W.ρ h (W.ρ cA w)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
        refine ⟨⟨cA * g * cA⁻¹, (hG2 g).mp hg⟩, ?_⟩
        show W.ρ (cA * g * cA⁻¹) (W.ρ cA w) = W.ρ cA (W.ρ g w)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    rw [hr, ← AddMonoidHom.map_closure]
    have hc : Nat.card ↥((AddSubgroup.closure (Set.range
        fun g : ↥(inG G₂) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)).map f) =
        Nat.card ↥(AddSubgroup.closure (Set.range
          fun g : ↥(inG G₂) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)) :=
      Nat.card_congr (AddSubgroup.equivMapOfInjective _ f (ρ_injective_md W cA)).toEquiv.symm
    rw [hc]
    exact hline
  have h6 := mc.six k W (W.ρ cA w) hw'0 hfix' hgen' hline'
  have hiso : V₁.Iso (Mk k) := ⟨e₁, he₁⟩
  rcases h6 with h | h
  · exact Or.inl (iso_trans' h (iso_symm' hiso))
  · exact Or.inr (isFiveDimCover_of_iso_right' h (iso_symm' hiso))

theorem main_parts (mc : ModelCover) (G₁ G₂ : Subgroup (Perm (Fin 6))) (c : Perm (Fin 6))
    (hc : c ∈ alternatingGroup (Fin 6))
    (hconj : ((∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ cA6)) ∨
      ((∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ cA6)))
    (V₁ V₂ : Md ↥(alternatingGroup (Fin 6)))
    (h₁ : V₁.IsIrred ∧ Nat.card V₁.carrier = 2 ^ 4 ∧ V₁.FixesPoint (inG G₁) ∧
      V₁.FixesLine (inG G₂))
    (h₂ : V₂.IsIrred ∧ Nat.card V₂.carrier = 2 ^ 4 ∧ V₂.FixesPoint (inG G₂) ∧
      V₂.FixesLine (inG G₁))
    (B : LinearMap.BilinForm (ZMod 2) V₁.carrier) (hB1 : ∀ x, B x x = 0)
    (hB2 : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hB3 : ∀ (g : ↥(alternatingGroup (Fin 6))) x y, B (V₁.ρ g x) (V₁.ρ g y) = B x y) :
    Part1 V₁ ∧ Part2 V₁ ∧ Part3 V₁ B ∧ Part4 V₁ B ∧ Part5 V₁ V₂ ∧ Part6 G₁ G₂ V₁ := by
  obtain ⟨k, cA, e₁, e₂, he₁, he₂, hG1, hG2⟩ := identify G₁ G₂ c hc hconj V₁ V₂ h₁ h₂
  have hB := form_transport e₁ he₁ B hB1 hB2 hB3
  exact ⟨part1_of_card V₁ h₁.2.1, part2_of_iso e₁ he₁,
    ⟨part3a_of_iso e₁ he₁ B hB, part3b_of_iso e₁ he₁ (mc.cover3 k)⟩, part4_of_iso e₁ he₁ B hB,
    part5_of_iso e₁ he₁ ⟨e₂, he₂⟩ (mc.cover5 k), part6_of_data mc e₁ he₁ cA G₁ G₂ hG1 hG2⟩

end CFSG.Quasithin.ShultG53
