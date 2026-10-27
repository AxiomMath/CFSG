module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

noncomputable abbrev kgLangT3Inn (n : ℕ) (K : Type) [Field K] :
    Subgroup (MulAut (GGTriD4R n K)) :=
  (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)).range

@[expose] def KGLangT3Strong (n : ℕ) (K : Type) [Field K] : Prop :=
  ∀ A : Subgroup (MulAut (GGTriD4R n K)), IsElemAbelian 3 A →
    ∀ α₀ ∈ A, α₀ ∉ kgLangT3Inn n K →
    ∀ h : GGTriD4R n K, h ≠ 1 → MulAut.conj h ∈ A →
    ∀ J₀ : Subgroup (GGTriD4R n K),
      IsComponentOf J₀ (Subgroup.centralizer ({h} : Set (GGTriD4R n K))) →
    ∀ (E : Type) [Field E] [Finite E]
      (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)),
      (∃ At : Subgroup (GL (Fin 3) E), IsMulCommutative At ∧
        ∀ α ∈ A, ∃ g ∈ At, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : GGTriD4R n K) = α j ∧
          θ₀ (QuotientGroup.mk j') = TableB.linConjAut (Fin 3) E g (θ₀ (QuotientGroup.mk j))) →
      ∃ k : GGTriD4R n K, (∀ α ∈ A, α ∈ kgLangT3Inn n K → α k = k) ∧ k * (α₀ k)⁻¹ = h

end CFSG.StandardType
