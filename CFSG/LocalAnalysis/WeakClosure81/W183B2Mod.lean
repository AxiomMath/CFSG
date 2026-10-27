module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Tr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)}

private theorem w183b2_commSpace_commSpace_of_perfect {L : Subgroup (LGL 2 V)}
    [Group.IsPerfect ↥L] {U : Submodule (ZMod 2) V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) :
    commSpace L (commSpace L U) = commSpace L U := by
  set M := commSpace L U with hM
  have hMi : Invariant L M :=
    invariant_commSpace (K := L) (K' := L)
      (fun k' hk' k hk => L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')) hU
  refine le_antisymm (commSpace_le_of_invariant hMi) ?_
  change commSpace L U ≤ commSpace L M
  let S : Subgroup ↥L :=
    { carrier := {g | ∀ u ∈ U, (g : LGL 2 V) u - u ∈ commSpace L M}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {a b} ha hb u hu => by
        have h1 : (a : LGL 2 V) ((b : LGL 2 V) u) - (b : LGL 2 V) u ∈ commSpace L M :=
          ha ((b : LGL 2 V) u) (hU (b : LGL 2 V) b.2 u hu)
        have h2 : (b : LGL 2 V) u - u ∈ commSpace L M := hb u hu
        have h := (commSpace L M).add_mem h1 h2
        rwa [sub_add_sub_cancel] at h
      inv_mem' := fun {a} ha u hu => by
        have h : u - (a : LGL 2 V)⁻¹ u ∈ commSpace L M := by
          have := ha ((a : LGL 2 V)⁻¹ u) (hU ((a : LGL 2 V)⁻¹) (L.inv_mem a.2) u hu)
          simpa using this
        simpa using (commSpace L M).neg_mem h }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ↥L), _root_.commutator_def,
      Subgroup.commutator_le]
    intro g1 _ g2 _ u hu
    obtain ⟨w, hw⟩ : ∃ w, w = ((g1⁻¹ * g2⁻¹ : ↥L) : LGL 2 V) u := ⟨_, rfl⟩
    have hwU : w ∈ U := by
      rw [hw]
      exact hU _ (g1⁻¹ * g2⁻¹).2 u hu
    have hv' : u = (g2 : LGL 2 V) ((g1 : LGL 2 V) w) := by
      rw [hw]
      simp [LinearEquiv.mul_apply, mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv]
    have hc : (g1 : LGL 2 V) ((g2 : LGL 2 V) w) - u =
        ((g1 : LGL 2 V) ((g2 : LGL 2 V) w - w) - ((g2 : LGL 2 V) w - w))
          - ((g2 : LGL 2 V) ((g1 : LGL 2 V) w - w) - ((g1 : LGL 2 V) w - w)) := by
      rw [hv']
      simp only [map_sub]
      abel
    rw [commutatorElement_def]
    have hρc : (((g1 * g2 * g1⁻¹ * g2⁻¹ : ↥L)) : LGL 2 V) u =
        (g1 : LGL 2 V) ((g2 : LGL 2 V) w) := by
      rw [hw]
      simp [LinearEquiv.mul_apply, mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hρc, hc]
    exact (commSpace L M).sub_mem
      (sub_mem_commSpace g1.2 (sub_mem_commSpace g2.2 hwU))
      (sub_mem_commSpace g2.2 (sub_mem_commSpace g1.2 hwU))
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hbL, u, hu, rfl⟩
  have hb : (⟨b, hbL⟩ : ↥L) ∈ S := by rw [hS]; trivial
  exact hb u hu

theorem w183b2_commSpace_commSpace_eq_bot_of_perfect {L₁ L₂ D : Subgroup (LGL 2 V)}
    (p₁ : Group.IsPerfect ↥L₁) (p₂ : Group.IsPerfect ↥L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hD₁ : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁) (hD₂ : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂)
    (H : ∀ R' R : Submodule (ZMod 2) V, R' < R →
      (∀ l ∈ L₁, ∀ u ∈ R', l u ∈ R') → (∀ l ∈ L₂, ∀ u ∈ R', l u ∈ R') →
      (∀ d ∈ D, ∀ u ∈ R', d u ∈ R') →
      (∀ l ∈ L₁, ∀ u ∈ R, l u ∈ R) → (∀ l ∈ L₂, ∀ u ∈ R, l u ∈ R) →
      (∀ d ∈ D, ∀ u ∈ R, d u ∈ R) →
      (∀ W : Submodule (ZMod 2) V, R' ≤ W → W ≤ R →
        (∀ l ∈ L₁, ∀ u ∈ W, l u ∈ W) → (∀ l ∈ L₂, ∀ u ∈ W, l u ∈ W) →
        (∀ d ∈ D, ∀ u ∈ W, d u ∈ W) → W = R' ∨ W = R) →
      commSpace L₁ R ≤ R' ∨ commSpace L₂ R ≤ R') :
    commSpace L₂ (commSpace L₁ ⊤) = ⊥ := by
  set W := commSpace L₁ ⊤ with hWdef
  set R := commSpace L₂ W with hRdef
  have hW₁ : Invariant L₁ W := by
    rw [hWdef]
    exact invariant_commSpace (K := L₁) (K' := L₁)
      (fun k' hk' k hk => L₁.mul_mem (L₁.mul_mem hk' hk) (L₁.inv_mem hk'))
      (fun _ _ _ _ => trivial)
  have hW₂ : Invariant L₂ W := by
    rw [hWdef]
    refine invariant_commSpace (K := L₁) (K' := L₂) ?_ (fun _ _ _ _ => trivial)
    intro k' hk' k hk
    have h : k' * k = k * k' := (hcomm k hk k' hk').symm
    rw [h, show k * k' * k'⁻¹ = k by group]
    exact hk
  have hWD : Invariant D W := by
    rw [hWdef]
    exact invariant_commSpace (K := L₁) (K' := D) hD₁ (fun _ _ _ _ => trivial)
  have hR₂ : Invariant L₂ R := by
    rw [hRdef]
    exact invariant_commSpace (K := L₂) (K' := L₂)
      (fun k' hk' k hk => L₂.mul_mem (L₂.mul_mem hk' hk) (L₂.inv_mem hk')) hW₂
  have hR₁ : Invariant L₁ R := by
    rw [hRdef]
    refine invariant_commSpace (K := L₂) (K' := L₁) ?_ hW₁
    intro a ha b hb
    have h : a * b = b * a := hcomm a ha b hb
    rw [h, show b * a * a⁻¹ = b by group]
    exact hb
  have hRD : Invariant D R := by
    rw [hRdef]
    exact invariant_commSpace (K := L₂) (K' := D) hD₂ hWD
  have hWfix : commSpace L₁ W = W := by
    rw [hWdef]
    haveI := p₁
    exact w183b2_commSpace_commSpace_of_perfect (L := L₁) (U := ⊤) (fun _ _ _ _ => trivial)
  have hRfix : commSpace L₂ R = R := by
    rw [hRdef]
    haveI := p₂
    exact w183b2_commSpace_commSpace_of_perfect (L := L₂) (U := W) hW₂
  by_contra hRne
  haveI : IsNoetherian (ZMod 2) V := inferInstance
  haveI : WellFoundedGT (Submodule (ZMod 2) V) := IsNoetherian.wellFoundedGT
  let S : Set (Submodule (ZMod 2) V) :=
    {R' | R' < R ∧ Invariant L₁ R' ∧ Invariant L₂ R' ∧ Invariant D R'}
  have hSne : S.Nonempty := by
    refine ⟨⊥, bot_lt_iff_ne_bot.mpr hRne, ?_, ?_, ?_⟩
    · intro l hl u hu
      rw [Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
    · intro l hl u hu
      rw [Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
    · intro d hd u hu
      rw [Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
  obtain ⟨R', hR'mem, hR'max⟩ :=
    (wellFounded_gt (α := Submodule (ZMod 2) V)).has_min S hSne
  simp only [S, Set.mem_setOf_eq] at hR'mem
  obtain ⟨hR'lt, hR'₁, hR'₂, hR'D⟩ := hR'mem
  have hirr : ∀ W' : Submodule (ZMod 2) V, R' ≤ W' → W' ≤ R →
      Invariant L₁ W' → Invariant L₂ W' → Invariant D W' → W' = R' ∨ W' = R := by
    intro W' hR'W hWR hi1 hi2 hiD
    rcases eq_or_lt_of_le hR'W with h | h
    · exact Or.inl h.symm
    · right
      by_contra hWRne
      have hWlt : W' < R := lt_of_le_of_ne hWR hWRne
      exact hR'max W' ⟨hWlt, hi1, hi2, hiD⟩ h
  rcases H R' R hR'lt hR'₁ hR'₂ hR'D hR₁ hR₂ hRD hirr with h1 | h2
  · have hRle : R ≤ R' := by
      rw [hRdef, ← hWfix]
      refine commSpace_le_iff.2 fun b hb y hy => ?_
      have key : commSpace L₁ W ≤
          Submodule.comap (((b : V →ₗ[ZMod 2] V)) - LinearMap.id) R' := by
        refine Submodule.span_le.2 ?_
        rintro y ⟨a, ha, w, hw, rfl⟩
        have hbw : b w - w ∈ R := sub_mem_commSpace hb hw
        have h1' : a (b w - w) - (b w - w) ∈ R' := h1 (sub_mem_commSpace ha hbw)
        have hab : a * b = b * a := hcomm a ha b hb
        have hco : a (b w) = b (a w) := by
          have := congrArg (fun e : V ≃ₗ[ZMod 2] V => e w) hab
          simpa [LinearEquiv.mul_apply] using this
        have he : b (a w - w) - (a w - w) = a (b w - w) - (b w - w) := by
          simp only [map_sub]
          rw [hco]
          abel
        show b (a w - w) - (a w - w) ∈ R'
        rw [he]
        exact h1'
      simpa using key hy
    exact absurd hRle (not_le_of_gt hR'lt)
  · have hRle : R ≤ R' := by
      rw [hRfix] at h2
      exact h2
    exact absurd hRle (not_le_of_gt hR'lt)

theorem w183b2_mod_prop_of_quasi {L₁ L₂ D : Subgroup (LGL 2 V)}
    (hq₁ : CFSG.Open.IsQuasisimple ↥L₁) (hq₂ : CFSG.Open.IsQuasisimple ↥L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hD₁ : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁) (hD₂ : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂)
    (hDe : IsElemAbelian 2 D) (hDq : commSpace D (commSub D) = ⊥)
    (hcent : ∀ d ∈ D, (∀ a ∈ L₁, d * a = a * d) → (∀ b ∈ L₂, d * b = b * d) → d = 1)
    (hDn₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hDn₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hrk : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
    (hAbs₁ : AbsIrrOverF4 ↥L₁) (hAbs₂ : AbsIrrOverF4 ↥L₂) :
    commSpace L₂ (commSpace L₁ ⊤) = ⊥ ∧ commSpace L₁ (commSpace L₂ ⊤) = ⊥ := by
  have hp₁ : Group.IsPerfect ↥L₁ := ⟨hq₁.1⟩
  have hp₂ : Group.IsPerfect ↥L₂ := ⟨hq₂.1⟩
  constructor
  · exact w183b2_commSpace_commSpace_eq_bot_of_perfect hp₁ hp₂ hcomm hD₁ hD₂
      (fun R' R hlt hR'₁ hR'₂ hR'D hR₁ hR₂ hRD hirr =>
        w183b2_no_mixed_section_of_quasi hq₁ hq₂ hcomm hD₁ hD₂ hDe hDq hcent hDn₁ hDn₂ hrk
          hAbs₁ hlt hR'₁ hR'₂ hR'D hR₁ hR₂ hRD hirr)
  · exact w183b2_commSpace_commSpace_eq_bot_of_perfect hp₂ hp₁
      (fun a ha b hb => (hcomm b hb a ha).symm) hD₂ hD₁
      (fun R' R hlt hR'₂ hR'₁ hR'D hR₂ hR₁ hRD hirr =>
        w183b2_no_mixed_section_of_quasi hq₂ hq₁
          (fun a ha b hb => (hcomm b hb a ha).symm) hD₂ hD₁ hDe hDq
          (fun d hd h2 h1 => hcent d hd h1 h2) hDn₂ hDn₁ hrk.symm
          hAbs₂ hlt hR'₂ hR'₁ hR'D hR₂ hR₁ hRD hirr)

theorem w183b2_mod_prop {L₁ L₂ D : Subgroup (LGL 2 V)} (h₁ : IsSimpleGroup ↥L₁)
    (n₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (h₂ : IsSimpleGroup ↥L₂)
    (n₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hD₁ : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁) (hD₂ : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂)
    (hDe : IsElemAbelian 2 D) (hDq : commSpace D (commSub D) = ⊥)
    (hcent : ∀ d ∈ D, (∀ a ∈ L₁, d * a = a * d) → (∀ b ∈ L₂, d * b = b * d) → d = 1)
    (hDn₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hDn₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hrk : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
    (hs₁ : IsL3 ↥L₁ 2 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2)
    (hs₂ : IsL3 ↥L₂ 2 ∨ IsAlt ↥L₂ 6 ∨ IsSp4 ↥L₂ 2) (hFD : FinG11Models) :
    commSpace L₂ (commSpace L₁ ⊤) = ⊥ ∧ commSpace L₁ (commSpace L₂ ⊤) = ⊥ := by
  exact w183b2_mod_prop_of_quasi (w183b2_quasi_of_simple_nonab h₁ n₁)
    (w183b2_quasi_of_simple_nonab h₂ n₂) hcomm hD₁ hD₂ hDe hDq hcent hDn₁ hDn₂ hrk
    (w183b2_absIrrOverF4_of_shape hs₁ hFD) (w183b2_absIrrOverF4_of_shape hs₂ hFD)

end CFSG.LocalAnalysis.WeakClosure81

end
