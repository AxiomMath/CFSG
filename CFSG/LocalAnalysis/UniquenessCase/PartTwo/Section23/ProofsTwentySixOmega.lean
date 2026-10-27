module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusQ
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_26OmegaCore (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
    (3 : ℕ) ∉ D.sig → ¬ IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M)) → False

private theorem isCyclic_sylow_three_of_isCyclic_pCore (D : Data G)
    (h : IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M))) :
    ∀ P : Sylow 3 ↥(oTwoThreeOf D.M), IsCyclic ↥P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P
  let Q : Subgroup G := (P : Subgroup ↥(oTwoThreeOf D.M)).map (oTwoThreeOf D.M).subtype
  have hQ0 : CFSG.ABGLocalTools.IsSylowOf 3 Q (oTwoThreeOf D.M) := ⟨P, rfl⟩
  have hQM : Q ≤ D.M := hQ0.le.trans (uc22p21c_barPreimage_le D.M _)
  have hbar := uc22p22u_sylow_barPreimage (M := D.M) (r := 3) Nat.prime_three (by norm_num)
    (CFSG.pCore_isPGroup (p := 3)) hQ0
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let f : ↥Q →* ↥(CFSG.pCore 3 (Bar2 D.M)) :=
    (π.comp (Subgroup.inclusion hQM)).codRestrict (CFSG.pCore 3 (Bar2 D.M)) fun x => by
      rw [← hbar.1]
      exact uc22p21c_mem_barImage.2 ⟨Subgroup.inclusion hQM x, x.2, rfl⟩
  have hinj : Function.Injective f :=
    injective_barImage_mk'_of_disjoint_pCoreOf hQM hbar.2 f fun _ => rfl
  have hQcyc : IsCyclic ↥Q := by
    letI : IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M)) := h
    exact isCyclic_of_injective f hinj
  let e := Subgroup.equivMapOfInjective (P : Subgroup ↥(oTwoThreeOf D.M))
    (oTwoThreeOf D.M).subtype (oTwoThreeOf D.M).subtype_injective
  letI : IsCyclic ↥Q := hQcyc
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

private theorem three_not_mem_sig_of (D : Data G) (Ch : Choice2011 G) (h52 : S23_5_2Omega D Ch)
    (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hOmega : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    (3 : ℕ) ∉ D.sig := by
  classical
  intro h3sig
  obtain ⟨-, hcn⟩ := h52 h1930 c hOmega
  have h3pi : 3 ∈ piSet c.B0 := by
    rw [c.hpi, hcn]
    exact ⟨Nat.prime_three, uc22s13xo_three_dvd_sub_one ⟨_, by ring⟩⟩
  obtain ⟨b3, hb3ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 3 h3pi.2
  have hb3G : orderOf (b3 : G) = 3 := by
    rw [Subgroup.orderOf_coe, hb3ord]
  have hb3ne : (b3 : G) ≠ 1 := by
    intro hb1
    rw [hb1, orderOf_one] at hb3G
    norm_num at hb3G
  let A : Subgroup G := Subgroup.zpowers (b3 : G)
  have hA : A ≤ c.withB0.toCtx23.toCtx21.B := by
    rw [Ctx23L.withB0_B]
    exact Subgroup.zpowers_le.mpr b3.2
  have h212 := s21_2 D Ch h1930 c.withB0.toCtx23.toCtx21 A hA
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hmem : (b3 : G) ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers (b3 : G)
    exact hb3ne (Subgroup.mem_bot.1 hmem)
  have hA3 : IsPGroup 3 ↥A := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    have hcard : Nat.card ↥A = orderOf (b3 : G) := Nat.card_zpowers (b3 : G)
    rw [hcard, hb3G]
    norm_num
  have hAU : A ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded Nat.prime_three
      (hsp 3 (by rw [← h6 h1930 c]; exact h3sig))
      (Subgroup.zpowers_le.mpr (c.hBM b3.2)) hAne hA3
  exact h212 (normalizer_le_of_mem_uniqueSet D.maxLocal hAU)

theorem s23_26Omega_of (D : Data G) (Ch : Choice2011 G) (h52 : S23_5_2Omega D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig → CFSG.Open.pRank r D.M ≤ 3)
    (hcore : S23_26OmegaCore D Ch) :
    S23_26Omega D Ch := by
  classical
  intro h1930 c hOmega P
  have h3not : (3 : ℕ) ∉ D.sig := three_not_mem_sig_of D Ch h52 h6 hsp h1930 c hOmega
  refine ⟨h3not, ?_⟩
  have hcyc : IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M)) := by
    by_contra hnc
    exact hcore h1930 c hOmega h3not hnc
  exact isCyclic_sylow_three_of_isCyclic_pCore D hcyc P

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
