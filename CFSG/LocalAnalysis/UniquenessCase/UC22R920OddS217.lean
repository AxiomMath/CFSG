module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R920OddS2119
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenShapes
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3AMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Pow
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedThree)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217l2_not_isL2Odd_r920odd (D : Data G) (Ch : Choice2011 G) (h212 : S21_12 D Ch)
    (h8107 : F08.R8107 D) (h847 : F08.R847 D) (h920 : R920odd D)
    (hsig : D.sig.Nonempty) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) : ¬ IsL2Odd (Bar2 L) q := by
  intro hLq
  have hLM : L ≤ D.M := hL.1.le
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  let f : MulAut G := MulAut.conj m
  have hMf : D.M.map f.toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hK : L.map f.toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M f hMf hL
  have hLK : L ≠ L.map f.toMonoidHom := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he.symm)
  have hKq : IsL2Odd (Bar2 (L.map f.toMonoidHom)) q :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (UC6S846.bar2Equiv (Subgroup.equivMapOfInjective L f.toMonoidHom f.injective)) hLq
  have hL3 := pRank_three_eq_one_and_thin8_or_isU3 (Or.inr (Or.inr (Or.inr ⟨q, hq, hLq⟩)))
  have hK3 := pRank_three_eq_one_and_thin8_or_isU3 (K := L.map f.toMonoidHom)
    (Or.inr (Or.inr (Or.inr ⟨q, hq, hKq⟩)))
  have h3L : 3 ∣ Nat.card L :=
    CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three (by rw [hL3.1])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hD₃L : zpowers ((x : ↥L) : G) ≤ L := Subgroup.zpowers_le.mpr x.2
  have hD₃3 : Nat.card (zpowers ((x : ↥L) : G)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hD₃U := mem_uniqueSet_of_card_eq_three D h8107 hL hK hLK hL3 hK3 hD₃L hD₃3
  exact Ctx21.false_of_isL2Odd_r920odd D Ch h212 h920 h847 hsig hH c hn3 hL hK hLK hq hq5 hLq
    hD₃L hD₃3 hD₃U

theorem s21_17RPow_of_s21_17RV_r920odd (hG : CFSG.Open.GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (he : 3 < CFSG.Open.evenRank G) (hK3 : StronglyEmbeddedThree)
    (h82 : F08.R82 D) (h8100E : R8100E D) (h5 : S21_5 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hSg : UC6S846.SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h869 : F08.R869NS5 D) (h212 : S21_12 D Ch) (h8107 : F08.R8107 D) (h847 : F08.R847 D)
    (h920 : R920odd D) (hsig : D.sig.Nonempty) (h : S21_17RV D Ch) :
    S21_17RPow D Ch := fun hH c L hL hnN =>
  ⟨s21_17R_one_pow_of_griess hG D Ch h5 hn3 hSg h76 h869 hH c L hL hnN,
    fun _ hn hL2 => uc22s217l2_ncard_le_two D Ch he hK3 h82 h5 hH c (hn3 hH c) hL hn hL2,
    fun hc2 hL2 => uc22s217l2_isPowTwo_of_pair D Ch he hK3 h8100E hH c hL hc2 hL2,
    fun _ hq hq5 =>
      uc22s217l2_not_isL2Odd_r920odd D Ch h212 h8107 h847 h920 hsig hH c (hn3 hH c) hL hnN hq
        hq5,
    h hH c L hL hnN⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
