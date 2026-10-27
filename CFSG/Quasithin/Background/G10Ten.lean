module

public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G11

@[expose] def G10ComponentStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ X L T : Subgroup (GLV V)),
    IsComponentOf L Γ → X ≤ Γ → (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) → numConjugates Γ L ≤ 2 →
    IsSylowTwoOf T Γ → T ≤ Subgroup.normalizer (X : Set (GLV V)) →
    ⁅normalClosure Γ L, X⁆ = normalClosure Γ L

namespace G108Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem not_isSolvable_L : ¬ Group.IsSolvable ↥L := by
  obtain ⟨l, hl, hl1⟩ := hyp.exists_ne_one_mem_L
  have hperf : Group.IsPerfect ↥L := ⟨hyp.component.2.2.1⟩
  have : Nontrivial ↥L := ⟨⟨⟨l, hl⟩, 1, fun h => hl1 (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥L

theorem not_isSolvable_Γ : ¬ Group.IsSolvable ↥Γ := by
  intro hsolv
  apply hyp.not_isSolvable_L
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hyp.L_le)

theorem eq_bot_of_fixed {J : Submodule (ZMod 2) V}
    (h : ∀ k ∈ normalClosure Γ L, ∀ u ∈ J, k u = u) : J = ⊥ := by
  rw [eq_bot_iff, ← hyp.fixedSpace_H]
  exact fun u hu k hk => h k hk u hu

theorem g10_10 (h4 : G1004Stmt) (hc : G10ComponentStmt) : G1010Concl Γ v₁ X L := by
  intro U hU0 hUinv
  set H := normalClosure Γ L with hH
  obtain ⟨J, hJU, hJ⟩ := exists_isIrr_le hUinv hU0
  have hJH : Invariant H J := hJ.1.mono le_sup_left
  have hHΓ : H ≤ Γ := hyp.H_le
  have hHne : H ≠ ⊥ := by
    obtain ⟨l, hl, hl1⟩ := hyp.exists_ne_one_mem_L
    intro hbot
    apply hl1
    have : l ∈ H := le_normalClosure Γ L hl
    rw [hbot] at this
    exact (Subgroup.mem_bot.1 this)
  have hcomm : commSpace X J ≠ ⊥ := by
    intro hbot
    have hXJ : ∀ x ∈ X, ∀ u ∈ J, x u = u := commSpace_eq_bot_iff.1 hbot
    have hne : fixedSpace X ≠ Submodule.span (ZMod 2) {v₁} := by
      intro heq
      have hJle : J ≤ Submodule.span (ZMod 2) {v₁} := by
        rw [← heq]
        exact fun u hu x hx => hXJ x hx u hu
      have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      have hJv : ∀ u ∈ J, u ≠ 0 → u = v₁ := by
        intro u hu hu0
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hJle hu)
        rcases hc2 c with rfl | rfl
        · rw [zero_smul] at hc
          exact absurd hc.symm hu0
        · rw [one_smul] at hc
          exact hc.symm
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ.ne_bot
      have huv : u = v₁ := hJv u hu hu0
      subst huv
      have : u ∈ fixedSpace H := by
        intro h hh
        have hmem : h u ∈ J := hJH h hh u hu
        by_cases h0 : h u = 0
        · exfalso
          apply hu0
          exact h.injective (h0.trans (map_zero h).symm)
        · exact hJv _ hmem h0
      rw [hyp.fixedSpace_H, Submodule.mem_bot] at this
      exact hyp.point this
    have hconj : numConjugates Γ L ≤ 2 := by
      rcases hyp.three with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨S, hS, hXS, hSn⟩ := hyp.four
    have hT : IsSylowTwoOf S Γ := hyp.toG101Hyp.isSylowTwoOf_of_stabilizer hS
    have hN := hc V Γ X L S hyp.component hyp.X_le hyp.noncomm hconj hT hSn
    apply hJ.ne_bot
    apply hyp.eq_bot_of_fixed
    intro k hk u hu
    have hk' : k ∈ ⁅H, X⁆ := by
      rw [hN]
      exact hk
    have hcent : ⁅H, X⁆ ≤ centralizerOn (⊤ : Subgroup (GLV V)) J := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨h, hh, x, hx, rfl⟩
      refine ⟨Subgroup.mem_top _, fun u hu => ?_⟩
      have hx1 : x⁻¹ u = u := hXJ x⁻¹ (X.inv_mem hx) u hu
      have hh1 : h⁻¹ u ∈ J := hJH h⁻¹ (H.inv_mem hh) u hu
      have hx2 : x (h⁻¹ u) = h⁻¹ u := hXJ x hx _ hh1
      have e : (⁅h, x⁆ : GLV V) u = h (x (h⁻¹ (x⁻¹ u))) := rfl
      rw [e, hx1, hx2]
      simp
    exact (hcent hk').2 u hu
  have hv : v₁ ∈ J := by
    by_contra hv
    by_cases hJtop : J = ⊤
    · exact hv (hJtop ▸ Submodule.mem_top)
    have hc4 := h4 V B Γ v₁ W X X₀ hyp.toG101Hyp H hHΓ (normalClosure_normal Γ L) hHne J
      hJ.ne_bot hJtop hJ (Or.inr ⟨hv, hcomm⟩)
    exact hyp.not_isSolvable_Γ hc4.2.2
  refine ⟨hJU hv, fun hbot => hcomm ?_⟩
  exact eq_bot_iff.2 ((commSpace_mono le_rfl hJU).trans hbot.le)

end G108Hyp

theorem g10_10 (h4 : G1004Stmt) (hc : G10ComponentStmt) : G1010Stmt :=
  fun _ _ _ _ _ _ _ _ _ _ _ hyp => hyp.g10_10 h4 hc

end G11

end CFSG.Quasithin
