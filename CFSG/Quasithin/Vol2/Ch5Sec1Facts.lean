module

public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem nonempty_equiv_psl_of_lieModel {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 n) :
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 n (by omega) hK)⟩
  all_goals exact absurd h0 (by norm_num)

theorem isL2Quot_of_lieModel {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 n) : IsL2Quot n X :=
  nonempty_equiv_psl_of_lieModel hn h

theorem isRankOneListed_of_lieModel {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 n) : IsRankOneListed X :=
  Or.inl ⟨n, hn, nonempty_equiv_psl_of_lieModel hn h⟩

theorem l2RankOneSylowFact_of (hF : RankOneListedFacts.{0}) : L2RankOneSylowFact := by
  intro X _ n hn h
  exact hF X (isRankOneListed_of_lieModel (by omega) h)

end CFSG.Quasithin.H13
