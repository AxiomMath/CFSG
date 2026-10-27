module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem uc22p2121d_pRank_mulAut_le_of_not_dvd {X : Type*} [Group X] [Finite X] {p a : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥) (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ a)
    (hOut : ¬ p ∣ Nat.card (Outer X)) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ a := by
  have h1 := GL83.I713.pRank_mulAut_le hp hZ
  have h2 := GL83.I713.pRank_top_eq_zero_of_not_dvd hp hOut
  omega

theorem uc22p2121d_pRank_mulAut_le_of_isCyclic {X : Type*} [Group X] [Finite X] {p a : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥) (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ a) (hcyc : IsCyclic (Outer X)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ a + 1 := by
  have h1 := GL83.I713.pRank_mulAut_le hp hZ
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (Outer X)) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isCyclic hp (Subgroup.isCyclic ⊤)
  omega

theorem uc22p2121d_pRank_mulAut_l2 {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsL2 X n) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 ∧
      (¬ p ∣ n → CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1) := by
  obtain ⟨hs, hnonab⟩ := CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel hX
  haveI := hs
  have hZ := GL83.I713.center_eq_bot_of_simple hnonab
  have hm : CFSG.Open.StatedClassicalModel X .PSL 2 2 n := hX.statedClassicalModel (by decide)
  have hX1 := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hm hp hp2
  obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  let e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hcyc : IsCyclic (Outer X) := by
    have : IsCyclic (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
      CFSG.Quasithin.OuterPrimeControl.outer_psl2_isCyclic K
        (Or.inl (by rw [hK]; exact Nat.even_pow.2 ⟨even_two, by omega⟩))
    exact isCyclic_of_surjective (equivalence e').symm.toMonoidHom (equivalence e').symm.surjective
  have hdvd : Nat.card (Outer X) ∣ n * Nat.gcd 2 (2 ^ n - 1) :=
    (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor Nat.prime_two K hK).2 X ⟨e'⟩
  refine ⟨uc22p2121d_pRank_mulAut_le_of_isCyclic hp hZ hX1 hcyc, fun hpn => ?_⟩
  refine uc22p2121d_pRank_mulAut_le_of_not_dvd hp hZ hX1 fun h => ?_
  rcases (Nat.Prime.dvd_mul hp).1 (h.trans hdvd) with h' | h'
  · exact hpn h'
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h'.trans (Nat.gcd_dvd_left 2 _)))

theorem uc22p2121d_not_three_dvd_two_pow_add_one {n : ℕ} (hn : Even n) : ¬ 3 ∣ 2 ^ n + 1 := by
  obtain ⟨r, rfl⟩ := hn
  have h4 : 2 ^ (r + r) = 4 ^ r := by rw [← two_mul, pow_mul]; norm_num
  have h41 : 4 ^ r % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [h4]
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
