module

public import CFSG.Quasithin.EmptyFaithful.S14612F0
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a
public import CFSG.Quasithin.EmptyFaithful.S14612GB1
public import CFSG.Quasithin.EmptyFaithful.S14612GB2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Shape

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {H PQ : Subgroup G} {p : ℕ}

theorem IsE9Z4Shape.two_pow_nine_le (h35 : Lemma1435) (h5 : Stage1461Five) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) :
    2 ^ 9 ≤ Nat.card ↥(pCoreOf 2 H) :=
  S.two_pow_nine_le_card_pCoreOf_of_irreducible hred.isHTM
    (shape_irreducible classAutShapeStmt h35 S hred hshape)
    (shape_card_uK_Z classAutShapeStmt h35 S hred hshape)
    (S.not_uK_le_centralizer_pCoreOf h5 hred)

theorem IsE9Z4Shape.equality_case (h35 : Lemma1435) (h5 : Stage1461Five) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (hQ : Nat.card ↥(pCoreOf 2 H) = 2 ^ 9) :
    conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T ∧
      Nat.card ↥(conjClosure (VZ T M) H) = 2 ^ 5 ∧
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
        conjClosure (VZ T M) H ∧
      conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) =
        quasithinOmegaOneCenter T ∧
      Nat.card ↥T = 2 ^ 11 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := S.equality_case_of_irreducible hred.isHTM
    (shape_irreducible classAutShapeStmt h35 S hred hshape)
    (shape_card_uK_Z classAutShapeStmt h35 S hred hshape)
    (S.not_uK_le_centralizer_pCoreOf h5 hred) hQ
  exact ⟨h1, h2, h3, h4, S.card_T_of_card_pCoreOf hred.isHTM hshape.2 hQ⟩

end Shape

@[expose] def NoE9Z4Min : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      Nat.card ↥(pCoreOf 2 H) = 2 ^ 9 →
      conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T →
      Nat.card ↥(conjClosure (VZ T M) H) = 2 ^ 5 →
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
        conjClosure (VZ T M) H →
      conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) =
        quasithinOmegaOneCenter T →
      Nat.card ↥T = 2 ^ 11 → False

structure NoE9Z4Res : Prop where
  min : NoE9Z4Min
  big : NoE9Z4Large

theorem noE9Z4_of_res (h35 : Lemma1435) (h5 : Stage1461Five) (r : NoE9Z4Res) : NoE9Z4 := by
  intro G _ _ T M S H PQ p hred hmax hshape
  have hle := IsE9Z4Shape.two_pow_nine_le h35 h5 S hred hshape
  rcases hle.lt_or_eq with hlt | heq
  · exact r.big G T M S H PQ p hred hmax hshape hlt
  · obtain ⟨h1, h2, h3, h4, h5'⟩ := IsE9Z4Shape.equality_case h35 h5 S hred hshape heq.symm
    exact r.min G T M S H PQ p hred hmax hshape heq.symm h1 h2 h3 h4 h5'

end CFSG.Quasithin
