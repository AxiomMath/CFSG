module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepTwoK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepFrame
public import CFSG.LocalAnalysis.StandardType.GGRowKSide
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeAtL_false_of_dep (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ}
    (hN : 11 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGResLeviSideDatumLE3 p Bs K J) : False := by
  have hN5 : 5 ≤ N := by omega
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨x, hx⟩)) :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hML hCL hφ hpair hAL hdep
  obtain ⟨t, ha, αa, htK, htlin, hαaha, hαax, hjoin, hnt, hcard⟩ :=
    hK.elim
      (fun hK => ggTwoNodeOdd_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK)
      (fun hK => hK.elim
        (fun hK => ggTwoNodeTwo_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK)
        (fun hK => ggTwoNodeLE3_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK))
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
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
  · exact ggDepAOdd_caseII_false hKG hp2 hN F r hr ra ha αa hra hαaha hαax hnt' hcard' hHa
  · refine ggDepAOdd_caseI_false hKG hp2 hN F r hr ra ha αa hra hαaha ?_ hαax hnt' hcard' hHa
    obtain ⟨c, hc⟩ := hjoin
    exact ⟨c, hc⟩


theorem ggTwoNodeAtK_false_of_dep (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeLarge p J K)
    (hy : y ∈ Bs) {N : ℕ}
    (hN : 11 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hJK : ggAutomizer J Bs ≤ ggAutomizer K Bs)
    (hdep : ¬ LinearIndependent (ZMod p) h)
    (hL : GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGResLeviSideDatumLE3 p Bs L J) : False := by
  have hN5 : 5 ≤ N := by omega
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨y, hy⟩)) :=
    ggXDatumA_frame_K hp2 hH hy (fun b hb => hFixK.2 G p B Bs x L D J y K hH hrow b hb)
      hN5 hpN e hMK hCK hφ hpair hAK hdep
  obtain ⟨t, ha, αa, htK, htlin, hαaha, hαay, hjoin, hnt, hcard⟩ :=
    hL.elim
      (fun hL => ggTwoNodeL_lside hFix hOrbK hp2 hH hy hN5 e hφ hAK hJK F hL)
      (fun hL => hL.elim
        (fun hL => ggTwoNodeL_lside_two hFix hOrbK hp2 hH hy hN5 e hφ hAK hJK F hL)
        (fun hL => ggTwoNodeL_lside_LE3 hFix hOrbK hp2 hH hy hN5 e hφ hAK hJK F hL))
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
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
  · exact ggDepAOdd_caseII_false hKG hp2 hN F r hr ra ha αa hra hαaha hαay hnt' hcard' hHa
  · refine ggDepAOdd_caseI_false hKG hp2 hN F r hr ra ha αa hra hαaha ?_ hαay hnt' hcard' hHa
    obtain ⟨c, hc⟩ := hjoin
    exact ⟨c, hc⟩

end CFSG.StandardType

end
