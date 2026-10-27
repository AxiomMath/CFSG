module

public import CFSG.GroupTheory.CharacteristicNormalizer
public import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96C
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem inf_L_subgroupOf_characteristic_pz2a
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((P ⊓ c.L).subgroupOf P).Characteristic := by
  have hforward : ∀ (ψ : MulAut ↥P) (y : ↥P),
      y ∈ (P ⊓ c.L).subgroupOf P → ψ y ∈ (P ⊓ c.L).subgroupOf P := by
    intro ψ y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hy3G : (y : G) ^ 3 = 1 :=
      c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (y : G) hy
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hy3G
    have hψ3 : ((ψ y : ↥P) : G) ^ 3 = 1 := by
      have h : (ψ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
      simpa using congrArg (fun z : ↥P => (z : G)) h
    exact Subgroup.mem_inf.mpr ⟨(ψ y).2,
      c.forall_pow_three_eq_one_mem_L_of_threeCover
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
        hON hP ((ψ y : ↥P) : G) (ψ y).2 hψ3⟩
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hforward φ y hy
  · intro hx
    exact ⟨φ.symm x, hforward φ.symm x hx, by simp⟩

theorem normalizer_sylow_le_normalizer_zSub
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((zSub P c.L) : Set G) :=
  (CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic inf_le_left
      (inf_L_subgroupOf_characteristic_pz2a c hON hP)).trans
    (CFSG.LocalAnalysis.GLTheoremA.S9.L96.normalizer_le_normalizer_center (P ⊓ c.L))

theorem pRank_three_G_le_three
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := by
  have hNPM : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer
        (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
          Set G) :=
    normalizer_sylow_le_normalizer_zSub c hON hP
  have hNP : Subgroup.normalizer (P : Set G) ≤ D.M := hNPM.trans hNZ
  have hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22q_isSylowOf_top_of_normalizer hP hNP
  exact (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three le_top hPG hP.le).trans
    c.pRank_three_M.le

theorem pRank_Xbar_le_three
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {J : Subgroup G} :
    CFSG.Open.pRank 3 (Xbar c P J) ≤ 3 := by
  let N := CFSG.pPrimeCore 3 ↥(G0 c P J)
  have h1 : CFSG.Open.pRank 3 (Xbar c P J) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥(G0 c P J) ⧸ N)) :=
    CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥(G0 c P J) ⧸ N)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(G0 c P J)) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply CFSG.SectionRank.pRank_quotient_eq
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(G0 c P J)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_three.one_lt
      (G0 c P J).subtype (G0 c P J).subtype_injective
  exact h1.trans (h2.trans_le (h3.trans (pRank_three_G_le_three c hON hP hNZ)))

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
