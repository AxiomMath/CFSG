module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFix

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFinrank_le_of_fix_le {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x : G} (hx : x ^ p = 1)
    {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hfix : ∀ b : Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers x) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let W : Submodule (ZMod p) (Module.Dual (ZMod p) V) := Submodule.span (ZMod p) (Set.range α)
  have hker : ∀ w ∈ W.dualCoannihilator, ((Additive.toMul (ι.symm w) : Bs) : G) ∈
      Subgroup.zpowers x := by
    intro w hw
    refine hfix _ fun i => ?_
    have hαi : α i w = 0 :=
      (Submodule.mem_dualCoannihilator w).mp hw _ (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := hlin i w
    rw [hαi, zero_smul, sub_zero, ggLin_apply] at h1
    have h2 := congrArg ι.symm h1
    rw [AddEquiv.symm_apply_apply] at h2
    exact Additive.ofMul.injective (by rw [h2]; rfl)
  let e : W.dualCoannihilator → Subgroup.zpowers x := fun w => ⟨_, hker w.1 w.2⟩
  have he : Function.Injective e := by
    intro w w' hww
    have h0 : ((Additive.toMul (ι.symm w.1) : Bs) : G) =
        ((Additive.toMul (ι.symm w'.1) : Bs) : G) :=
      congrArg (fun z : Subgroup.zpowers x => (z : G)) hww
    have h1 : (Additive.toMul (ι.symm w.1) : Bs) = Additive.toMul (ι.symm w'.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  have hcard : Nat.card W.dualCoannihilator ≤ p := by
    refine (Nat.card_le_card_of_injective e he).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hx
  have hkerrank : Module.finrank (ZMod p) W.dualCoannihilator ≤ 1 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W.dualCoannihilator
    have h2 : p ^ Module.finrank (ZMod p) W.dualCoannihilator ≤ p ^ 1 := by
      rw [h1, pow_one]; exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hW : Module.finrank (ZMod p) W ≤ Fintype.card Λ := finrank_range_le_card (R := ZMod p) α
  rw [← Subspace.finrank_add_finrank_dualCoannihilator_eq W]
  omega

theorem ggThree_le_card_of_fix (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hO : GGOpAutTrivial p Bs)
    (hI : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hN : GGNbr p B x D J y K) (hR : GGReflGenerated p (ggAutomizer K Bs))
    (hPm : GGScalarsOrWeyl' p B Bs x D J) {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    3 ≤ Fintype.card Λ := by
  classical
  obtain ⟨hp, hBs, hxB, -, -⟩ := hC.tableB_facts
  have hx : x ^ p = 1 := hBs.2 x hxB
  have hfin := ggFinrank_le_of_fix_le hx ι φ h α hlin fun b hb =>
    hFix G p B Bs x L D J hC hO hI hNT y K hN hR hPm b (by
      rw [hL]
      exact ggFixed_of_mem_closure φ b hb)
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have h4 := pow_four_le_card_of_bmax hp hS.1 hC.1.2.2.2.2.2.1.2.2.2
  have hBBs : B ≤ Bs := hC.2.1.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hcard : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
    rw [FiniteField.pow_finrank_eq_natCard p V]
    exact Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
  have h4' : p ^ 4 ≤ p ^ Module.finrank (ZMod p) V := by
    rw [← hcard]
    exact h4.trans hle
  have h4'' : 4 ≤ Module.finrank (ZMod p) V := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4'
  omega

theorem ggFinrank_eq_of_fix (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hO : GGOpAutTrivial p Bs)
    (hI : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hN : GGNbr p B x D J y K) (hR : GGReflGenerated p (ggAutomizer K Bs))
    (hPm : GGScalarsOrWeyl' p B Bs x D J) {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (ha : V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  classical
  obtain ⟨hp, hBs, hxB, -, -⟩ := hC.tableB_facts
  have hx : x ^ p = 1 := hBs.2 x hxB
  have hfin := ggFinrank_le_of_fix_le hx ι φ h α hlin fun b hb =>
    hFix G p B Bs x L D J hC hO hI hNT y K hN hR hPm b (by
      rw [hL]
      exact ggFixed_of_mem_closure φ b hb)
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hle := hind.fintype_card_le_finrank
  rw [Fintype.card_option] at hle
  omega

theorem ggForkCrossGe5Input_of_f1_split (hFix : GGTBFixInput) (h₁ : GGForkCrossGe5MainInput)
    (h₂ : GGForkCrossGe5ExcInput) : GGForkCrossGe5Input := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ h5 Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  by_cases hf : GGForkF1Fails M
  · exact h₂ G p B Bs x L D J hC hO hI hNT y K hN hR hPm h5 Λ M C V ι φ φa h α ha αa b c hM hCM hF
      hlin hlina hind hL hK hf
  · exact h₁ G p B Bs x L D J hC hO hI hNT y K hN hR hPm h5 Λ M C V ι φ φa h α ha αa b c hM hCM hF
      hlin hlina hind hL hK hf
      (ggThree_le_card_of_fix hFix hC hO hI hNT hN hR hPm ι φ h α hlin hL)

theorem ggForkCrossGe5Main_of_input (h : GGForkCrossGe5Input) : GGForkCrossGe5MainInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ h5 Λ _ _ M C V _ _ ι φ φa h' α ha αa b c
    hM hCM hF hlin hlina hind hL hK _ _
  exact h G p B Bs x L D J hC hO hI hNT y K hN hR hPm h5 Λ M C V ι φ φa h' α ha αa b c hM hCM hF
    hlin hlina hind hL hK

theorem ggForkCrossGe5Exc_of_input (h : GGForkCrossGe5Input) : GGForkCrossGe5ExcInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ h5 Λ _ _ M C V _ _ ι φ φa h' α ha αa b c
    hM hCM hF hlin hlina hind hL hK _
  exact h G p B Bs x L D J hC hO hI hNT y K hN hR hPm h5 Λ M C V ι φ φa h' α ha αa b c hM hCM hF
    hlin hlina hind hL hK

example : GGForkF1Fails CoxeterMatrix.F₄ := Or.inr ⟨Equiv.refl _, fun _ _ => rfl⟩

end CFSG.StandardType
