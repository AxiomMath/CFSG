module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)

variable {G : Type} [Group G] [Finite G]

@[expose] def R7_8R3 (D : Data G) : Prop :=
  ∀ (p : ℕ) (H P D₀ : Subgroup G), Sec7Hyp D p H →
    CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ D.M) →
    D₀ = CFSG.RankThree.PartOne.omegaOne p P →
      (∀ x ∈ D₀, x ^ p = 1) ∧ ⁅⁅D₀, D₀⁆, D₀⁆ = ⊥ ∧
        ((H ⊓ D.M = H ⊓ normalizer (P : Set G) ∧
            IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀
              (inSubgroup frattini D₀) ∧
            P = D₀) ∨
          (((Nonempty (LKQuot7 p H ≃* MulAut (CFSG.Theory.Comparator.PSL2Model 3)) ∧ p = 3) ∨
              (IsAutSz (LKQuot7 p H) 5 ∧ p = 5)) ∧
            ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) ∧
              S ≤ normalizer (D₀ : Set G) ∧ IsCyclic S ∧ S ≤ rankThreeLayer (Opp p H)) ∨
          (IsAlt ↥(Opp p H) 10 ∧ p = 5 ∧ PartTwo.S17.IsA5xA5 ↥(Opp p (H ⊓ D.M))))

theorem uc22s13xi_pRank_le_lkQuot7 {p : ℕ} [Fact p.Prime] (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (⊤ : Subgroup (LKQuot7 p H)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  haveI := hE.1
  have hmem : ∀ x : ↥E, QuotientGroup.mk' (CFSG.pPrimeCore p ↥H) (Subgroup.inclusion hEH x) ∈
      ImageModK p H (Opp p H) := by
    intro x
    refine ⟨Subgroup.inclusion hEH x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have hord : ∃ k : ℕ, orderOf (x : G) = p ^ k := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hE.2 x x.2)) with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    exact Subgroup.subset_closure ⟨hEH x.2, hord⟩
  set f : ↥E →* LKQuot7 p H :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hEH)).codRestrict _ hmem
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hEH x ∈ CFSG.pPrimeCore p ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      exact congrArg Subtype.val hx
    set y : ↥(CFSG.pPrimeCore p ↥H) := ⟨Subgroup.inclusion hEH x, h1⟩
    have hy : y ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [y] using hE.2 x x.2
    have h2 : orderOf y = 1 :=
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy)
        CFSG.pPrimeCore_coprime_card).eq_one_of_dvd (orderOf_dvd_natCard y)
    have h3 := congrArg (fun z : ↥(CFSG.pPrimeCore p ↥H) => ((z : ↥H) : G))
      (orderOf_eq_one_iff.mp h2)
    exact Subtype.ext h3
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hcard f hf le_top

theorem uc22s13xi_pRank_le_two {H : Subgroup G}
    (e : LKQuot7 3 H ≃* MulAut (CFSG.Theory.Comparator.PSL2Model 3)) : CFSG.Open.pRank 3 H ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd
      (CFSG.Theory.Comparator.PSL2Model 3) := ⟨3, by decide, by norm_num, ⟨MulEquiv.refl _⟩⟩
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (CFSG.Theory.Comparator.PSL2Model 3))) ≤ 2 :=
    CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => by
      have := (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.table113_T2 _ hL E hE).1
      norm_num
      exact this
  calc CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (LKQuot7 3 H)) :=
        uc22s13xi_pRank_le_lkQuot7 H
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (CFSG.Theory.Comparator.PSL2Model 3))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
    _ ≤ 2 := h1

theorem uc22s13xi_not_alt2 {M H D₀ : Subgroup G} {p : ℕ} (hp : p = 3)
    (hr : 3 ≤ CFSG.Open.pRank 3 H) :
    ¬ (((Nonempty (LKQuot7 p H ≃* MulAut (CFSG.Theory.Comparator.PSL2Model 3)) ∧ p = 3) ∨
        (IsAutSz (LKQuot7 p H) 5 ∧ p = 5)) ∧
      ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ M) ∧
        S ≤ normalizer (D₀ : Set G) ∧ IsCyclic S ∧ S ≤ rankThreeLayer (Opp p H)) := by
  subst hp
  rintro ⟨⟨⟨e⟩, -⟩ | ⟨-, h5⟩, -⟩
  · have := uc22s13xi_pRank_le_two e
    omega
  · omega

theorem uc22s13xi_alt1_of_r7_8R3 {D : Data G} (h78 : R7_8R3 D) {H P D₀ : Subgroup G}
    (hH : Sec7Hyp D 3 H) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ D.M))
    (hD₀ : D₀ = CFSG.RankThree.PartOne.omegaOne 3 P) (hr : 3 ≤ CFSG.Open.pRank 3 H) :
    (∀ x ∈ D₀, x ^ 3 = 1) ∧ ⁅⁅D₀, D₀⁆, D₀⁆ = ⊥ ∧
      (H ⊓ D.M = H ⊓ normalizer (P : Set G) ∧
        IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀) ∧
        P = D₀) := by
  obtain ⟨hexp, hcl, h1 | h2 | ⟨-, h5, -⟩⟩ := h78 3 H P D₀ hH hP hD₀
  · exact ⟨hexp, hcl, h1⟩
  · exact absurd h2 (uc22s13xi_not_alt2 rfl hr)
  · omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
