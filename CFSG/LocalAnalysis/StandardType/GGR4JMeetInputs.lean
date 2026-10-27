module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRow
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetMarking
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetData
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRank
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetNoL34
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDecomp
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import Certificates.Certificate1002
public import Certificates.Certificate1003

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExtDatum_restrict_some {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α') :
    GGExtDatum ι C (fun i => φ' (some i)) (fun i => h' (some i)) (fun i => α' (some i)) :=
  { mem := fun i => hD.mem (some i)
    lin := fun i w => hD.lin (some i) w
    pair := fun i j => hD.pair (some i) (some j)
    indep := hD.indep.comp some (Option.some_injective _)
    diag := fun j => hD.diag (some j) }

theorem ggR4JMeet_of_inputs
    (hAmb : GGR4AmbientLabel) (hM7a : GGF4OrderThreeLayer)
    (hM7b : GGE6OppOrderThreeLayer) : GGR4JMeet := by
  intro G _ _ p B Bs x L D J hCfg _ hInnAll _ y K _ _ _ hFact hp Λ _ _ C b c V _ _ ι φ' h' α' hD
    hspan hF4 hGenL _
  subst hp
  obtain ⟨e, he, -⟩ := hF4
  have hcardΛ : Fintype.card Λ = 4 := by
    simpa using (Fintype.card_congr e).symm
  have hCard : Nat.card Bs = 3 ^ 5 := ggR4J_card_Bs hD hspan hcardΛ
  have hLab := hAmb G B Bs x L D J hCfg hInnAll.1 hCard Λ C V ι (fun i => φ' (some i))
    (fun i => h' (some i)) (fun i => α' (some i)) (ggExtDatum_restrict_some hD) ⟨e, he⟩ hGenL
  obtain ⟨hperf, hInnL, hZL, f, hf, hrow⟩ :=
    ggR4Meet_marking_of_row ggR4SurvivorRow_holds hLab
  obtain ⟨hJL, z, hz1, hz3, hJlayer, hJcomp, hEz, hEab, hE4⟩ :=
    ggR4Meet_data hCfg hCard hZL hInnL
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInnAll.1
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  rcases hrow with hF4L | ⟨hE6L, h3⟩ | ⟨hT6L, h3⟩
  · exact ggR4Meet_of_rank hJL hE4
      ((hM7a ↥L f hf hF4L z hz1 hz3 _ hJlayer hJcomp).2 _ hEz hEab)
  · rcases hM7b ↥L f hf (Or.inl ⟨hE6L, h3⟩) z hz1 hz3 _ hJlayer hJcomp with
      ⟨-, hr⟩ | ⟨-, hL1, hJ1⟩
    · exact ggR4Meet_of_rank hJL hE4 (hr _ hEz hEab)
    · exact (ggR4Meet_noE6TwoL34 hCfg hBsN hCard hperf hZL hL1 hJ1).elim
  · rcases hM7b ↥L f hf (Or.inr ⟨hT6L, h3⟩) z hz1 hz3 _ hJlayer hJcomp with
      ⟨-, hr⟩ | ⟨-, hL1, hJ1⟩
    · exact ggR4Meet_of_rank hJL hE4 (hr _ hEz hEab)
    · exact (ggR4Meet_noE6TwoL34 hCfg hBsN hCard hperf hZL hL1 hJ1).elim

end CFSG.StandardType

end
