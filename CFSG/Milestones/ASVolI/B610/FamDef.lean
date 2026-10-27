module

public import CFSG.Quasithin.Background.B610TwoOff

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

structure burnsideB610_Fam (H T V : Subgroup G) (hV : IsElemAbelian 2 V) (F : Type) [Field F]
    {ι : Type} (S : Finset ι) (X : ι → Subgroup G) (D : ∀ i, NatData (X i) V F) : Prop where
  inj : ∀ i ∈ S, ∀ j ∈ S, X i = X j → i = j
  le : ∀ i ∈ S, X i ≤ H
  cent : ∀ i ∈ S, H ⊓ Subgroup.centralizer (V : Set G) ≤ X i
  comm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j,
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)
  triv : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    X j ≤ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)
  ker : ∀ i ∈ S, ∀ a : ↥(nLV (X i) V), (D i).act a = 1 →
    (a : G) ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)
  conj : ∀ i ∈ S, ∀ h ∈ H, ∃ j ∈ S, cjSub h (X i) = X j
  orbit : ∀ i ∈ S, ∀ j ∈ S, ∃ h ∈ H, cjSub h (X i) = X j
  res : twoResidual H ≤ ⨆ i ∈ S, X i
  fix : ∀ i ∈ S, fixV ((D i).img (twoResidual H)) = ⊥
  gen : ∀ i ∈ S, ∀ P : Subgroup G, P ≤ X i → IsPGroup 2 P →
    Nat.card ((D i).img P) = Nat.card F →
    ∃ k ∈ X i ⊓ twoResidual H, autI hV (X i) ≤ autI hV P ⊔ autI hV (cjSub k P)
  thomp : ∀ i ∈ S, thompsonJ T ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G)

end CFSG.Quasithin.B610T
