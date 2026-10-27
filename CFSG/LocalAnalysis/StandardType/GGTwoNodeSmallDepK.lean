module

public import CFSG.LocalAnalysis.StandardType.GGRowKSide
public import CFSG.LocalAnalysis.StandardType.GGSmallDepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeSmallDepK_false (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hyK : y ∉ K) {N : ℕ}
    (hCI : GGSmallDepCaseIAt p N) (hCII : GGSmallDepCaseIIAt p N)
    (hN5 : 5 ≤ N) (hpN : p ∣ N) (hne : Nat.card ↥Bs ≠ p ^ (N - 1))
    (hXd : GGResXDatumA p Bs K (N - 1))
    (hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hKs : GGResTwoNodeSideDatum p Bs K J) (hLs : GGResTwoNodeSideDatum p Bs L J) : False := by
  classical
  obtain ⟨Λ, i1, i2, MK, CK, V, i3, i4, ι, φ, h, α, e, hMK, hWMK, hCK, hlin, hrefl, hpair, ⟨f, hf⟩,
    hclos⟩ := hXd
  letI := i1; letI := i2; letI := i3; letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdep : ¬ LinearIndependent (ZMod p) h :=
    ggXDatumA_dep_K hp2 hH hy hyK hfixK hN5 hpN e hMK hCK hlin hpair hclos
  let F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨y, hy⟩)) :=
    ggXDatumA_frame_K hp2 hH hy hfixK hN5 hpN e hMK hCK hlin hpair hclos hdep
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
  have hfin : Module.finrank (ZMod p) V = N := by
    have hb := ggDepA_finrank_bounds F
    have hne' : Module.finrank (ZMod p) V ≠ N - 1 := by
      intro hfr
      exact hne (by rw [hcardV, hfr])
    omega
  have hJK : ggAutomizer J Bs ≤ ggAutomizer K Bs := ggTwoNodeSide_automizer_le hKs
  obtain ⟨t, ha, αa, htK, htlin, hαaha, hαay, hjoin, hnt, hcard⟩ :=
    ggTwoNodeL_lside_two hFix hOrbK hp2 hH hy hN5 e hlin hclos hJK F hLs
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hlin (e i) v
  have hra : ∀ v, ra v = v - αa v • ha := by
    intro v
    exact htlin v
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    simpa only [r, ra] using hnt
  have hcard' : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    simpa only [r, ra] using hcard
  by_cases hHa : ha ∈ Submodule.span (ZMod p) (Set.range (fun i : Fin (N - 1) => h (e i)))
  · exact hCII V (fun i => h (e i)) (fun i => α (e i)) _
      hp2 hfin F r hr ra ha αa hra hαaha hαay hnt' hcard' hHa
  · exact hCI V (fun i => h (e i)) (fun i => α (e i)) _
      hp2 hfin F r hr ra ha αa hra hαaha hjoin hαay hnt' hcard' hHa

end CFSG.StandardType

end
