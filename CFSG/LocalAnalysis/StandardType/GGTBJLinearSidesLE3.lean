module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAPermutationDatumLE3
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAParabolicLE3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem exists_adapted_weyl_datum_of_diagonal_linear_block_corank
    {G : Type} [Group G] [Finite G] {p r c : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 3 ≤ r) (hcr : c ≤ r) (hrc : 1 ≤ r - c)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r + 1 - c)
    (hJ : J = (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear S).map
      (X.subtype.comp ψ)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Fin r → MulAut Bs) (h : Fin r → V)
      (α : Fin r → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) ∧
      (∃ e : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (e ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range (φ ∘ Fin.castLE (by omega : r - c ≤ r))) := by
  classical
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNP, hρ, hφ, hlin, hrefl, hpair, ⟨f, hf⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF hr hBs hSC hN hψ hker hdiag
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have hρX : ∀ σ, ρ σ ∈ ggAutomizer X Bs := fun σ =>
    mem_ggAutomizer_iff.mpr ⟨ψ (TypeA.permSL σ⁻¹), (ψ _).2, hNP σ, hρ σ⟩
  have hJS : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ := by
    rw [hJ, ← Subgroup.map_map]
    exact TypeANbrDvd.ggAutomizer_blockSpecialLinear_ambient_eq (Fact.out : p.Prime)
      hp2 hpF hN hBs hSC hψ hker hdiag hNP ρ hρ S
  obtain ⟨φ', h', α', hlin', hrefl', hpair', hf', hclos', hJgen'⟩ :=
    exists_adapted_typeA_datum_of_supported_permutations_corank hrc hcr
      ι ρ hρX φ h α hφ hlin hrefl hpair f hf hclos S hS hJS
  exact ⟨V, hVadd, hVmod, ι, φ', h', α', hlin', hrefl', hpair', hf', hclos', hJgen'⟩

theorem ggResSideDatumLE3_of_diagonal_linear_block
    {G : Type} [Group G] [Finite G] {p r c : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 3 ≤ r) (hc : 1 ≤ c) (hc3 : c ≤ 3)
    (hcr : c + 1 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r + 1 - c)
    (hJ : J = (blockSpecialLinear S).map (X.subtype.comp ψ)) :
    (c = 1 → GGResSideDatum p Bs X J) ∧ (2 ≤ c → GGResLeviSideDatumLE3 p Bs X J) := by
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, hlin, hrefl, hpair, ⟨e, he⟩, hclos, hJgen⟩ :=
    exists_adapted_weyl_datum_of_diagonal_linear_block_corank hp2 hpF hr (by omega) (by omega)
      hBs hSC hN hψ hker hdiag S hS hJ
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  exact ggTBJTypeAParabolicLE3 hp2 hc hc3 (by omega) (by omega) rfl rfl hlin hrefl hpair he hclos
    hJgen

end CFSG.StandardType

end
