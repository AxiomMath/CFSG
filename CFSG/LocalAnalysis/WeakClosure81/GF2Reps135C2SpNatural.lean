module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpNatType
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisDescent
import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6NatType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis
open scoped Matrix TensorProduct

private theorem spNA_addIrreducible_mat (n : ℕ) (K : Type) [Field K] :
    CFSG.LieType.SpecialLinear.IsIrreducibleAdd
      (fun (g : StatedSp n K) (v : Fin n ⊕ Fin n → K) => mat n K g *ᵥ v) := by
  intro A hA
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  obtain h | ⟨v, hv, hv0⟩ := A.bot_or_exists_ne_zero
  · exact (hbot h).elim
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact A.zero_mem
  obtain ⟨g, hg, hgv⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hv0 hw
  have hmem := hA ⟨g, hg⟩ hv
  change (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v ∈ A at hmem
  rwa [hgv] at hmem

theorem exists_addEquiv_spn_natural {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) (StatedSp n K) W) [ρ.IsIrreducible] (k : Type)
    [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) k]
    {y₀ : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule] ρ.asModule}
    {χ : StatedSp n K → k}
    (ht : (spCurtisDatum n K).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y₀ χ 0)
    (φ : K →+* k) (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, by omega⟩ : K)) :
    ∃ β : W ≃+ (Fin n ⊕ Fin n → K), ∀ (g : StatedSp n K) (w : W),
      β (ρ g w) = mat n K g *ᵥ β w := by
  exact exists_addEquiv_of_isCurtisType (D := spCurtisDatum n K) (ρ := ρ) (R := mat n K)
    (spNA_addIrreducible_mat n K) k φ
    (isSimpleRep_sp_matMap (n := n) (by omega) φ) ht
    (isCurtisType_spn_matMap hn hK φ χ hχ)

end CFSG.LocalAnalysis.WeakClosure81
