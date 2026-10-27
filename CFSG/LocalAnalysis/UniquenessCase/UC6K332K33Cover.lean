module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Lists
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.NativeSporadic (Carrier)

private theorem k33Cover_of_isLinThreeCover3 {L : Type} [Group L]
    (hq : CFSG.Open.IsQuasisimple L) (hZ3 : Nat.card (Subgroup.center L) = 3)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsLinThreeCover3 d)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie d).Group) : K33Cover L := by
  obtain ⟨i, hv⟩ := d
  have eL : L ⧸ Subgroup.center L ≃* TauCeti.ValidLieTypeIndex.Group ⟨i, hv⟩ := e
  rcases hd with ⟨q, hi, h3q⟩ | ⟨q, hi, h3q⟩
  · have hi' : i = .A 2 q := hi
    subst hi'
    have hm : LieModel (L ⧸ Subgroup.center L) .PSL 3 q.p q.exponent :=
      (CFSG.Models.lieModel_A 2 q hv eL).toBlueprint (by decide)
    have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    have hpos : 0 < q.p ^ q.exponent := pow_pos q.prime_p.pos _
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q.p, q.exponent, by omega, hq, hZ3, hm⟩)))
  · have hi' : i = .twistedA 2 q := hi
    subst hi'
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    have hm' := CFSG.Models.lieModel_twistedA 2 q hv eL
    rw [hc, hf] at hm'
    have hm : LieModel (L ⧸ Subgroup.center L) .PSU 3 q.p q.exponent :=
      hm'.toBlueprint (by decide)
    have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q.p, q.exponent, by omega, hq, hZ3, hm⟩)))

theorem k33_threeCover_of_three_dvd
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (Carrier .M22 ≃* (TauCeti.CFSGIndex.sporadic .M22).Group))
    (L : Type) [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L))
    (hZp : IsPGroup 3 (Subgroup.center L)) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Cover L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : Subgroup.center L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  have hrk3 : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 := by omega
  obtain ⟨hcyc, hZ3⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.bal3ThreeCenter_of_tables
      hGA hAlt hSpor L hq hcat hne hZp hrk3
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover in
  rcases kFactAlphaListM3Wide_of_tables hGA hSpor L hq hcat hne hZp hcyc hrk3 with
    he6 | he7 | heM | heO | ⟨d, hd, heL⟩
  · exact Or.inl ⟨hq, hZ3, he6⟩
  · exact Or.inr (Or.inl ⟨hq, hZ3, he7⟩)
  · obtain ⟨b⟩ := hM22
    obtain ⟨eM⟩ := heM
    exact Or.inr (Or.inr (Or.inl ⟨hq, hZ3, ⟨eM.trans b.symm⟩⟩))
  · obtain ⟨eO⟩ := heO
    let : Group.IsPerfect L := ⟨hq.1⟩
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    have e' : L ⧸ Subgroup.center L ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan :=
      eO.trans b.symm
    obtain ⟨π, hπ, hker⟩ := CFSG.AGLEmbedding.exists_surjective_ker_eq_center e'
    have hD := CFSG.AGLEmbedding.abelianSylowDatum_ON_three
    have h3 : 3 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
      rw [CFSG.Sporadic.ON.card_ON]
      norm_num
    have h3le := CFSG.AGLEmbedding.KFactProofs.CoverThree.three_le_pRank_cover_of_abelianSylowDatum
      π hπ hker hZ3 hZp hcyc hD h3
    omega
  · obtain ⟨eL⟩ := heL
    exact k33Cover_of_isLinThreeCover3 hq hZ3 d hd eL

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
