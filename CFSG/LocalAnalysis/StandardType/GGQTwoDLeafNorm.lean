module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDForkNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_tbwNormAmb_of_dLeaf (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {y : G} {K : Subgroup G} (M : GGQTwoAmbModel p Bs x y L (L ⊔ K))
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i))
    {n : ℕ} (hn : 5 ≤ n) (f : Fin n ≃ {k // k ≠ M.a})
    (hf : ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D n i j) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV}) :
    ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod p), c ≠ 0 ∧
      (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := p) M.model φ (M.coroot i) = c • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφx
  have hφxg : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hH hAJS M.hx hφ hφxg
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [M.parabL_L]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  exact ggQ2_dNormal_of_normalizer M.toLin hn f hf hind _ hTnorm

theorem ggQ2_tbwNormNbrAmb_of_dLeaf (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs y x K (L ⊔ K))
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i))
    {n : ℕ} (hn : 5 ≤ n) (f : Fin n ≃ {k // k ≠ M.a})
    (hf : ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D n i j) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV}) :
    ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod p), c ≠ 0 ∧
      (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := p) M.model φ (M.coroot i) = c • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφy
  have hφyg : φ ⟨y, M.hx⟩ ∈ Subgroup.zpowers (⟨y, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hH hAJS hK1 hnb M.hx hφ hφyg
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [M.parabL_L]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  exact ggQ2_dNormal_of_normalizer M.toLin hn f hf hind _ hTnorm

end CFSG.StandardType

end
