module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrPRank
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem eq_of_ggLabelIso_triD4_twF4 {lab lab' : LargeEvenLabel}
    (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (h : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  unfold GGLabelIso at h
  rcases ht with rfl | rfl <;> rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem dvd_sub_or_add_of_halfSplit {p : ℕ} (hp : p.Prime) {lab lab' : LargeEvenLabel}
    {c : Prop} (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (hiso : GGLabelIso lab lab')
    (hlab' : LargeEvenInLambda2 lab') (h : LargeEvenHalfSplit p lab' c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  rw [eq_of_ggLabelIso_triD4_twF4 ht hiso] at hlab' h
  rcases largeEvenHalfSplit_dvd hlab' h with h | ⟨-, h | h⟩
  · rw [pow_two, mul_self_tsub_one] at h
    exact (hp.dvd_mul.mp h).symm
  all_goals (subst h; simp at ht)

theorem ggRowSmall_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_Small p Bs K) : False := by
  obtain ⟨hp, hp2, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  obtain ⟨y, hnb⟩ := hK.1
  obtain ⟨lab', hlab', hhas', -, -, -, -, -, hHS⟩ := largeEvenMarking_exists_hasLabel
    (ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds (ggRawInndiagIsoInput_of_rest
      (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)) hcfg.1.1 hnb
      (hcfg.1.2.2.1.2 y K hnb))
  obtain ⟨hX, lab, hlab, hraw⟩ := ggNbr_inndiag_pRank_ge_three hcfg hK hrow
  have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  have hiso := ggLabelRigidInput_holds lab lab' _ hlab hlab' hhas hhas'
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists hraw
  have key : ∀ T : LargeEvenLabel → Prop, T lab → StandardType.LargeEvenMarking ↥K
      (fun lab R _ I _ _ => T lab ∧ ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) := fun T hT =>
    ⟨hX, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _, hE⟩ =>
      ⟨hs, hna, θ, hT, hE⟩) hraw⟩
  obtain ⟨t, r, n⟩ := lab
  dsimp only [ggRowP_Small] at hS
  rcases hS with ⟨rfl, hr⟩ | hBC | rfl | rfl | rfl | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | rfl | rfl | rfl | rfl
  · have h1 : 1 ≤ r := hlab.2.1
    rcases (by omega : r = 1 ∨ r = 2) with hr | hr
    · exact ggInndiag_pRank_le_two_A1 hp hp2 (key _ ⟨rfl, hr⟩)
    · exact ggInndiag_pRank_le_two_A2 hp hp2 (key _ ⟨rfl, hr⟩)
  · exact ggInndiag_pRank_le_two_B2 hp hp2 (key _ hBC)
  · exact ggInndiag_pRank_le_two_B2der hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_G2 hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_G2der hp hp2 (key _ rfl)
  · have h2 : 2 ≤ r := hlab.2.1
    exact ggInndiag_pRank_le_two_twA2 hp hp2 (key _ ⟨rfl, (by omega : r = 2)⟩)
  · exact ggInndiag_pRank_le_two_twD2 hp hp2 (key _ ⟨rfl, hr⟩)
  · exact ggInndiag_pRank_le_two_triD4 hp
      (key _ ⟨rfl, dvd_sub_or_add_of_halfSplit hp (.inl rfl) hiso hlab' hHS⟩)
  · exact ggInndiag_pRank_le_two_twB2 hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_twF4 hp hp2
      (key _ ⟨rfl, dvd_sub_or_add_of_halfSplit hp (.inr rfl) hiso hlab' hHS⟩)
  · exact ggInndiag_pRank_le_two_twF4der hp hp2 (key _ rfl)

end CFSG.StandardType

end
