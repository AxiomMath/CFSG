module

public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualSplit
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

structure GGTCHyp
    (t : StatedLieTag) {X : Type} [Group X] [Finite X] (n f : ℕ)
    (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ B D J L : Subgroup X) (x : X) : Prop where
  range : ψ.range = G₀
  ker : ψ.ker ≤ Subgroup.center (ggU t n f).K
  adm : StatedLieAdmissible t n 2 f
  rank_two : 2 ≤ (ggU t n f).D.rank
  perfect : commutator ↥G₀ = ⊤
  model : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f
  cent_odd : Odd (Nat.card (Subgroup.centralizer (G₀ : Set X)))
  prime : p.Prime
  ne_two : p ≠ 2
  b_norm : B ≤ Subgroup.normalizer (G₀ : Set X)
  b_diag : ∀ b ∈ B, GGPsiInnerDiag (ggU t n f).D ψ b
  b_elem : IsElemAbelian p B
  b_card : p ^ 4 ≤ Nat.card B
  b_HN : (t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1) → p ^ (n - 3) ≤ Nat.card B
  b_faithful : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥
  b_local : ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set X)
  rank_le : ∀ E T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T → IsElemAbelian p E →
    E ≤ Subgroup.normalizer (T : Set X) → Nat.card E ≤ Nat.card B
  d_le : D ≤ B
  d_card : Nat.card D = p ^ 2
  x_mem : x ∈ D
  x_ne : x ≠ 1
  j_comp : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))
  j_norm : B ≤ Subgroup.normalizer (J : Set X)
  j_cent : B ⊓ Subgroup.centralizer (J : Set X) = D
  l_le : L ≤ G₀
  l_comp : IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})
  j_le_l : J ≤ L
  j_only : ∀ K : Subgroup X, IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set X)) → K = J
  l_norm : B ≤ Subgroup.normalizer (L : Set X)
  l_split : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab)
  l_cyc : ∀ S : Subgroup X, S ≤ Subgroup.centralizer (L : Set X) → IsPGroup p S → IsCyclic S
  nbr : ∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ K : Subgroup X,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≠ J → p ∣ Nat.card J →
      GGInnerDiagOn (Subgroup.zpowers x) K →
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
          LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥))
  nbr_odd : ∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup X,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) → J ≤ K →
      Odd (Nat.card (Subgroup.center ↥K))
  gen : ∀ H : Subgroup X, L ≤ H → (∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup X,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≤ H) → G₀ ≤ H
  e6 : (t = .E6 ∨ t = .twistedE6) → ∃ A : Subgroup X, B ≤ A ∧ IsElemAbelian p A ∧
    A ≤ Subgroup.normalizer (G₀ : Set X) ∧ (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) ∧
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) ∧
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A

@[expose] def GGTCCtx
    (t : StatedLieTag) {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ) (ψ : (ggU t n f).K →* G) :
    Prop :=
  GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ ∧
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J ∧
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) ∧
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) ∧
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))

@[expose] def GGTCAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ B D J L : Subgroup X) (x : X), GGTCHyp t n f ψ p G₀ B D J L x →
      GGSixLSevenFieldExtCase J t f → ¬ GGSixLSevenE6Case p L J t f →
        t = .PSL ∧ Nat.Coprime n (2 ^ f - 1)

end CFSG.StandardType.TableCRes

end
