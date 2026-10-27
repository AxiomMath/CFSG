module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KConj
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSL3
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.Blueprint.Chevalley
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3139
public import Certificates.Certificate3168
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2Inner


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eInvFour_G2_inner (h3 : 3 ∣ Nat.card K - 1)
    {Ē : Subgroup (MulAut ↥(adjointGroup .G2 K))} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9)
    (hrange : Ē ≤ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range) :
    EInvFour ↥(adjointGroup .G2 K) Ē := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hconjinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  obtain ⟨ι, hι, -⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := K)
  set Et : Subgroup ↥(adjointGroup .G2 K) := Ē.comap MulAut.conj with hEt
  have hEtcard : Nat.card Et = 9 := by
    rw [hEt, Item211LieProof.card_comap_conj hZ hrange, hE9]
  have hEtexp : ∀ x ∈ Et, x ^ 3 = 1 := by
    intro x hx
    apply hconjinj
    rw [map_pow, map_one]
    exact hE3.2 _ hx
  have hEtcomm : ∀ x ∈ Et, ∀ y ∈ Et, x * y = y * x := by
    intro x hx y hy
    apply hconjinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE3.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hEtp : IsPGroup 3 Et := fun g => ⟨1, Subtype.ext (by simpa using hEtexp g.1 g.2)⟩
  obtain ⟨y₀, hy₀⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_conj_le_range_of_three_dvd_sub_one h3
    ι hι Et hEtp
  set E' : Subgroup ↥(adjointGroup .G2 K) := Et.map (MulAut.conj y₀).toMonoidHom with hE'
  set ES : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := E'.comap ι with hES
  have hmapES : ES.map ι = E' := Subgroup.map_comap_eq_self hy₀
  have hEScard : 9 ≤ Nat.card ES := by
    have h1 : Nat.card ES = Nat.card (ES.map ι) := (Subgroup.card_map_of_injective hι).symm
    rw [h1, hmapES, hE', Subgroup.card_map_of_injective (MulAut.conj y₀).injective, hEtcard]
  have hmemE' : ∀ x ∈ Et, y₀ * x * y₀⁻¹ ∈ E' := fun x hx => ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hESexp : ∀ s ∈ ES, s ^ 3 = 1 := by
    intro s hs
    apply hι
    rw [map_pow, map_one]
    obtain ⟨x, hx, hxs⟩ : ι s ∈ E' := hs
    have : (MulAut.conj y₀) x ^ 3 = 1 := by
      rw [← map_pow, hEtexp x hx, map_one]
    rw [← hxs]
    simpa using this
  have hEScomm : ∀ s ∈ ES, ∀ t ∈ ES, s * t = t * s := by
    intro s hs t ht
    apply hι
    rw [map_mul, map_mul]
    obtain ⟨x, hx, hxs⟩ : ι s ∈ E' := hs
    obtain ⟨x', hx', hxt⟩ : ι t ∈ E' := ht
    rw [← hxs, ← hxt]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hEtcomm x hx x' hx']
  obtain ⟨WS, hWSab, hWS4, hWSinv, s₀, hs₀, w₀, hw₀, hmoveS⟩ :=
    exists_four_sl3 hω hω1 ES hESexp hEScomm hEScard
  set W : Subgroup ↥(adjointGroup .G2 K) := WS.map ι with hW
  have hWab : IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.map hWSab ι
  have hW4 : Nat.card W = 4 := by rw [hW, Subgroup.card_map_of_injective hι, hWS4]
  have hnorm : ∀ x ∈ Et, ∀ w ∈ W, (y₀ * x * y₀⁻¹) * w * (y₀ * x * y₀⁻¹)⁻¹ ∈ W := by
    intro x hx w hw
    obtain ⟨wS, hwS, rfl⟩ := hw
    have hxE' : y₀ * x * y₀⁻¹ ∈ E' := hmemE' x hx
    rw [← hmapES] at hxE'
    obtain ⟨s, hs, hsx⟩ := hxE'
    rw [← hsx, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hWSinv s hs wS hwS, rfl⟩
  refine eInvFour_of_conj_data hrange y₀ hWab hW4 ?_ ?_
  · intro x hxE
    exact hnorm x hxE
  · obtain ⟨x₀, hx₀, hx₀s⟩ : ι s₀ ∈ E' := hs₀
    refine ⟨x₀, hx₀, ι w₀, ⟨w₀, hw₀, rfl⟩, fun h => hmoveS ?_⟩
    have hconj : y₀ * x₀ * y₀⁻¹ = ι s₀ := by
      have := hx₀s
      simpa [MulAut.conj_apply] using this
    rw [hconj, ← map_inv, ← map_mul, ← map_mul] at h
    exact hι h

end G2Inner

end CFSG.RankThree.PartTwo.Sec21.Hering214
