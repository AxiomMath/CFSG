module

public import CFSG.Quasithin.Background.F918P8B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D310Deep : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → V < orbSup T V →
      orbSup T V = ⊤

section Pieces

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem d310_centralizer_le_center (hD : D31 M Mp T L V) (hMp : Mp = L) :
    ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g := by
  subst hMp
  have hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hD.irr.2.1 ⟨x, hx⟩ v hv
  let N : Subgroup ↥Mp :=
    { carrier := {g | ∀ v ∈ V, (g : MulAut W) v = v}
      one_mem' := fun v _ => rfl
      mul_mem' := fun {a b} ha hb v hv => by
        show (a : MulAut W) ((b : MulAut W) v) = v
        rw [hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        have := ha v hv
        show ((a : MulAut W)⁻¹) v = v
        rw [MulAut.inv_apply]
        exact (MulEquiv.symm_apply_eq _).mpr this.symm }
  have hN : N.Normal :=
    ⟨fun n hn g v hv => by
      have h1 : ((g⁻¹ : ↥Mp) : MulAut W) v ∈ V := hinv _ (g⁻¹).2 v hv
      have h2 := hn _ h1
      have h3 : (g : MulAut W) (((g⁻¹ : ↥Mp) : MulAut W) v) = v := by
        rw [← MulAut.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl
      show ((g : MulAut W) * (n : MulAut W) * ((g⁻¹ : ↥Mp) : MulAut W)) v = v
      rw [MulAut.mul_apply, MulAut.mul_apply, h2, h3]⟩
  intro g hg hgV x hx
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hD.quasi N with h | h
  · have hgN : (⟨g, hg⟩ : ↥Mp) ∈ N := hgV
    have hz := h hgN
    rw [Subgroup.mem_center_iff] at hz
    have := hz ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  · exfalso
    have hfix : XMod.fixed ↥Mp V = V := by
      ext v
      rw [XMod.mem_fixed]
      constructor
      · exact fun h => h.1
      · intro hv
        refine ⟨hv, fun a => ?_⟩
        have : a ∈ N := by rw [h]; exact Subgroup.mem_top a
        exact this v hv
    have hlt := hD.irr.2.2.2.1
    rw [hfix] at hlt
    exact lt_irrefl _ hlt

omit [Finite W] in
theorem d310_lt_orbSup (h : ∃ t ∈ T, t ∉ stabSub V) : V < orbSup T V := by
  refine lt_of_le_of_ne (le_orbSup T V) ?_
  intro heq
  obtain ⟨t, htT, htn⟩ := h
  apply htn
  have := le_stabSub_orbSup T V htT
  rwa [← heq] at this

end Pieces

theorem d310_of_deep (h35 : D35) (hdeep : D310Deep) : D310 := by
  intro W _ _ M Mp T L V hD hMp hqM
  have hdeep' := hdeep W M Mp T L V hD hMp hqM
  have hC' := d310_centralizer_le_center hD.hyp hMp
  subst hMp
  by_cases hT : ∀ t ∈ T, t ∈ stabSub V
  · exact Or.inl hT
  · right
    push Not at hT
    have hlt := d310_lt_orbSup hT
    have htop := hdeep' hlt
    obtain ⟨-, ⟨t₀, ht₀, ht₀n⟩, h4, h5⟩ := h35 W M Mp T Mp V hD hlt hC'
    refine ⟨?_, ⟨t₀, ht₀, ht₀n⟩, fun t ht htn => ?_⟩
    · unfold D35Five at h5
      rcases h5 with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have hs := (h4 t ht htn).2
      refine ⟨?_, d310_not_secIsoL hD ht hs⟩
      rw [htop, top_inf_eq] at hs
      exact hs

end CFSG.Quasithin
