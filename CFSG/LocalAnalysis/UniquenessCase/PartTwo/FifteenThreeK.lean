module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s15PerfShape (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ IsLn X n 1) ∨ (∃ n : ℕ, 6 ≤ n ∧ IsSpn X n 1) ∨
  (∃ n : ℕ, 6 ≤ n ∧ IsOmegaPlus X n 1) ∨ (∃ n : ℕ, 6 ≤ n ∧ IsOmegaMinus X n 1) ∨
  (∃ n : ℕ, 5 ≤ n ∧ UC22.IsAlt X n)

theorem s15KNatPerf.shape {V : Type} [CommGroup V] {X : Type} [Group X] {K : Subgroup (MulAut V)}
    {Z : Subgroup V} (h : s15KNatPerf X K Z) : s15PerfShape X := by
  rcases h with ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ |
    ⟨n, hn, hX, -⟩
  · exact Or.inl ⟨n, hn, hX⟩
  · exact Or.inr (Or.inl ⟨n, hn, hX⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, hX⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hX⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn, hX⟩)))

@[expose] def RRank3Omega153 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsOmegaMinus X 6 1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3

@[expose] def RCover3Rank153 : Prop :=
  ∀ (X Y : Type) [Group X] [Finite X] [Group Y] [Finite Y], CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) → Nonempty ((X ⧸ Subgroup.center X) ≃* Y) →
    s15PerfShape Y → 2 < CFSG.Open.pRank 3 (⊤ : Subgroup Y) →
      2 < CFSG.Open.pRank 3 (⊤ : Subgroup X)

theorem s15_Three_odd_center {X : Type} [Group X] [Finite X] (h : CFSG.pCore 2 X = ⊥) :
    Odd (Nat.card (Subgroup.center X)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center X) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center X)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : ((z : Subgroup.center X) : X) ∈ Subgroup.center X := z.2
  have hN : (Subgroup.zpowers ((z : Subgroup.center X) : X)).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hk : ((z : Subgroup.center X) : X) ^ k ∈ Subgroup.center X :=
      Subgroup.zpow_mem _ hzc k
    have h1 := Subgroup.mem_center_iff.1 hk g
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hP : IsPGroup 2 (Subgroup.zpowers ((z : Subgroup.center X) : X)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    rw [Subgroup.orderOf_coe, hz, pow_one]
  have hle : Subgroup.zpowers ((z : Subgroup.center X) : X) ≤ CFSG.pCore 2 X :=
    le_sSup ⟨hN, hP⟩
  rw [h] at hle
  have hz1 : ((z : Subgroup.center X) : X) = 1 :=
    Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem s15_Three_qs_of_open {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hcomm
  have hc : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b =>
    by_contra fun hne => hcomm ⟨a, b, hne⟩
  have hle : commutator X ≤ Subgroup.center X := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) x y
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hc _ _)] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  haveI := hsimple
  obtain ⟨a, ha⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hx : x ∈ commutator X := by
    rw [hperf]
    exact Subgroup.mem_top x
  exact ha ((QuotientGroup.eq_one_iff x).2 (hle hx))

theorem s15_Three_bar2_facts {M K : Subgroup G} (hK : K ∈ calC M) :
    CFSG.Open.IsQuasisimple (Bar2 K) ∧ Odd (Nat.card (Subgroup.center (Bar2 K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hK.2.2, s15_Three_odd_center CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot⟩

theorem s15_Three_hyp81_of_rank {M K : Subgroup G} (hK : K ∈ calC M)
    (h3 : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K))) : F08.Hyp81 M K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hK.1, hK.2.1, ?_, Or.inl (s15_Three_qs_of_open hK.2.2)⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).exists_card_eq
    rw [hn]
    intro h3d
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)
    omega
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) = CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hN
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 K :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 K).symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 K)
  omega

section Covers

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15_Three_strong_alt {hV : IsElemAbelian 2 V} (h880 : F08.R880 D)
    (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2) {K : Subgroup G}
    (hK : s15Covers D V₀ V hV K₀ K)
    (hA : UC22.IsAlt ↥(barSub V₀ V hV K₀) 6 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 7 ∨
      IsLn ↥(barSub V₀ V hV K₀) 4 1 ∨ IsLn ↥(barSub V₀ V hV K₀) 5 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  by_contra hns
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKC, -, -, -, ⟨e⟩⟩ := hK
  obtain ⟨hqs, hodd⟩ := s15_Three_bar2_facts hKC
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hs6, hs7, hs8, hs5⟩ := hSchur (Bar2 K) hqs hodd
  have key : UC22.IsAlt (Bar2 K) 6 ∨ F08.IsA6Z3 (Bar2 K) ∨ UC22.IsAlt (Bar2 K) 7 ∨
      F08.IsA7Z3 (Bar2 K) ∨ UC22.IsAlt (Bar2 K) 8 ∨ IsLn (Bar2 K) 5 1 := by
    rcases hA with h6 | h7 | h4 | h5
    · rcases hs6 ⟨e.trans h6.some⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hs7 ⟨e.trans h7.some⟩ with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · obtain ⟨e8⟩ := (hIso _).1 h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hs8 ⟨e.trans e8⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hs5 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h5))))))
  have hlist : F08.List880 (Bar2 K) := by
    unfold F08.List880
    rcases key with h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
  exact hNotJ2 (Bar2 K) (h880 K hKC hlist hns P hP).1 key

theorem s15_Three_strong_rank {hV : IsElemAbelian 2 V} (h82 : F08.R82 D)
    (hCov : RCover3Rank153) {K : Subgroup G} (hK : s15Covers D V₀ V hV K₀ K)
    (hshape : s15PerfShape ↥(barSub V₀ V hV K₀))
    (h3 : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV K₀))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  obtain ⟨hKC, -, -, -, hiso⟩ := hK
  obtain ⟨hqs, hodd⟩ := s15_Three_bar2_facts hKC
  obtain ⟨e⟩ := hiso
  exact h82 K (s15_Three_hyp81_of_rank hKC (hCov _ _ hqs hodd ⟨e⟩ hshape h3))

theorem s15_Three_strong_omega {hV : IsElemAbelian 2 V} (h82 : F08.R82 D)
    (hCov : RCover3Rank153) (hOm : RRank3Omega153) {K : Subgroup G} (hK : s15Covers D V₀ V hV K₀ K)
    (hΩ : IsOmegaMinus ↥(barSub V₀ V hV K₀) 6 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
  s15_Three_strong_rank h82 hCov hK (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, hΩ⟩))))
    (by rw [hOm _ hΩ]; norm_num)

end Covers

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
