module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.LieModelSimple
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P2214S

theorem false_of_isSz_of_isL2 {X : Type} [Group X] {m n : ℕ} (hS : IsSz X n) (hL : IsL2 X m) :
    False :=
  CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS
    (CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)))

theorem isSz_bar2 (D : Data G) (Ch : Choice2011 G) (h17 : S21_17 D Ch) (hJ : J1NotSp4SU3)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hSz : IsSz ↥(mbarImage D.M c.V K) n) (hc2 : (conjSetOf D.M K).ncard = 2) :
    IsSz (Bar2 K) n := by
  haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hnab := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
  have hZb : Subgroup.center ↥(mbarImage D.M c.V K) = ⊥ := uc22p22a_center_eq_bot hnab
  obtain ⟨⟨e⟩, -⟩ := uc22p22a_data D c hKC (uc22p22a_isQuasisimple_of_simple hnab)
  have hZ : Subgroup.center (Bar2 K) = ⊥ := by
    rcases h17 h1930 c.toCtx21 K hKC with heq | ⟨-, m, -, hL | hS⟩ | ⟨-, hj, -⟩
    · have := uc22p2214_ncard_eq_one_of_eq heq
      omega
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL)
        (by decide) hL
      exact uc22p21k_center_eq_bot hKC.2.2
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS
      exact uc22p21k_center_eq_bot hKC.2.2
    · exact (hJ _ hj).1
  exact CFSG.Blueprint.LieModel.of_quotient_center hZ
    ((CFSG.Blueprint.LieModel.quotient_center hZb hSz).of_mulEquiv e.symm)

theorem sz_cong_of_s21_15 (D : Data G) (Ch : Choice2011 G)
    (h2115 : S21_15C D Ch) (h17 : S21_17 D Ch) (hJ : J1NotSp4SU3) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hSz : IsSz ↥(mbarImage D.M c.V K) n) (hc2 : (conjSetOf D.M K).ncard = 2) {p : ℕ}
    (hp : p ∈ D.sig) : (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)] :=
  sz_cong_of_s21_15C h2115 h1930 c.toCtx21 hKC hc2 (isSz_bar2 D Ch h17 hJ h1930 c hKC hSz hc2) hp

theorem not_two_pow_cong_neg_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2n : (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]) : ¬ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by
  intro hn
  have h1 : (2 : ℤ) ^ (2 * n) ≡ 1 [ZMOD (p : ℤ)] := by
    have := hn.pow 2
    rwa [neg_one_sq, ← pow_mul, mul_comm] at this
  have h2 := Int.ModEq.dvd (h2n.symm.trans h1)
  rw [show (1 : ℤ) - -1 = 2 by norm_num] at h2
  have h3 : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

theorem false_of_weak (D : Data G) (Ch : Choice2011 G)
    (h2115 : S21_15C D Ch) (h17 : S21_17 D Ch) (hJ : J1NotSp4SU3) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hSz : IsSz ↥(mbarImage D.M c.V K) n) (hc2 : (conjSetOf D.M K).ncard = 2) {p : ℕ}
    (hp : p ∈ D.sig) (hweak : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : False :=
  not_two_pow_cong_neg_one (D.sig_prime p hp).1 (D.sig_prime p hp).2
    (sz_cong_of_s21_15 D Ch h2115 h17 hJ h1930 c hKC hSz hc2 hp) hweak

end P2214S

end CFSG.LocalAnalysis.UniquenessCase.UC22
