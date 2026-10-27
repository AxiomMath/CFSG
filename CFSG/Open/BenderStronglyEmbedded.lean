module

public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input

public section

universe u v w

namespace CFSG.Open.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem bender_psl2_borel (f : ℕ) (hf : 2 ≤ f) :
    fusionBenderBorel PSL(2, GaloisField 2 f) (2 ^ f) 1 :=
  _root_.CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf

end CFSG.Open.Open

namespace CFSG.Open.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem bender_psu3_borel (f : ℕ) (hf : 2 ≤ f) :
    fusionBenderBorel (PSU3 2 f) (2 ^ f) 3 :=
  _root_.CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2 f hf

end CFSG.Open.Open

namespace CFSG.Open.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem bender_strongly_embedded
    (X : Type) [Group X] [Finite X] (H : Subgroup X) (hH : fusionStronglyEmbedded H) :
    (∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
        ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
    ∃ (M N : Subgroup X) (_ : M.Normal) (_ : N.Normal) (_ : (M.subgroupOf N).Normal),
      M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧ fusionIsBenderGroup (N ⧸ M.subgroupOf N) :=
  _root_.CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 X H hH

end CFSG.Open.Open

namespace CFSG.Open.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem bender_suzuki_borel (a : ℕ) (ha : 1 ≤ a) :
    fusionBenderBorel (Sz a) (2 ^ (2 * a + 1)) 2 :=
  _root_.CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 a ha

end CFSG.Open.Open
