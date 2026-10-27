module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSCrComp
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB NbrInnerRest

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBNbrInner_of_torusLift_K {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : U63TB.GGTorusNbrSCrK p r R I) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hr : p ^ r ≤ Nat.card (ggGamma K hN).range := by
    have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hK θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  have h3 : p ^ 3 ≤ Nat.card (ggGamma K hN).range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  exact ggTableBNbrInner_of_card hcfg hnb hK θ hN hBsI hr h3 hT hYN hYK hYn hYp

end Config

theorem ggTableBNbrInnerInputOn_of_labelsSCrK {S : ℕ → LargeEvenLabel → Prop} {r : ℕ}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p r R ∧ U63TB.GGTorusNbrSCrK p r R I) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hlift, hT⟩
    exact ⟨hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_torusLift_K hcfg hnb hK θ hN hBsI hlift hT hYN hYK hYn hYp⟩
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

section Certs

theorem ggTableBNbrInnerInputOn_e6Div : GGTableBNbrInnerInputOn GGTableBE6DivLabel :=
  ggTableBNbrInnerInputOn_of_labelsSCrK (r := 5) fun p lab _ hlab hS => by
    obtain ⟨htag, rfl, h3⟩ := hS
    exact largeEvenLabelAll_e6Div_nbr (ggE6DivTorusNbrInput_of_model e6ThreeModel_holds) htag hlab
      h3

theorem ggTableBNbrInnerInputOn_twE6Three (hR : GGTwE6ThreeNbrRankInput) :
    GGTableBNbrInnerInputOn GGTableBTwE6ThreeLabel := by
  classical
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hK : commutator K = ⊤ := hP.1
  have hDisj : LargeEvenMarking ↥K (fun lab R _ I F θ =>
      (P lab R I F θ ∧ (GGTableBTwE6ThreeLabel p lab ∧
          ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)) ∨
      (P lab R I F θ ∧ ¬ (GGTableBTwE6ThreeLabel p lab ∧
          ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I))) :=
    largeEvenMarking_mono (fun lab R _ I F θ hPθ => by
      by_cases hH : GGTableBTwE6ThreeLabel p lab ∧
          ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I
      · exact Or.inl ⟨hPθ, hH⟩
      · exact Or.inr ⟨hPθ, hH⟩) hP
  rcases largeEvenMarking_or hDisj with hyes | hno
  · have hInnL : GGInnerDiagOnLab GGTwE6BadLabel p Bs K := by
      refine largeEvenMarking_mono (fun lab R _ I F θ hH => ?_) hyes
      obtain ⟨-, hS, hBI⟩ := hH
      exact ⟨hS, largeEvenSplit_of_twE6BadLabel hS, hN, fun b hb =>
        ⟨_, hBI b⁻¹ (Bs.inv_mem hb), largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))⟩⟩
    obtain ⟨lab, -, -, -, -, -, -, -, hbl, -⟩ := largeEvenMarking_exists_hasLabel hInnL
    have hp3 : p = 3 := hbl.2.1
    subst hp3
    have h5 := hR G 3 B Bs x L D J hcfg rfl y K hnb hInnL hN
      (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)
    have h3 : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range :=
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)).trans h5
    have hyes' := largeEvenMarking_and_labelAll
      (S := fun lab => GGTableBTwE6ThreeLabel 3 lab)
      (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ U63TB.GGTorusNbrSCrK 3 5 R I)
      (fun lab hlab hS => largeEvenLabelAll_twE6Three_nbr
        (ggTwE6ThreeTorusNbrInput_of_model e6ThreeModel_holds) hlab hS)
      (fun lab R _ I F θ hH => hH.2.1) hyes
    refine largeEvenMarking_mono (fun lab R _ I F θ hH => ?_) hyes'
    obtain ⟨⟨hPθ, -, -⟩, -, hT⟩ := hH
    exact ⟨hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_card hcfg hnb hK θ hN hBsI h5 h3 hT hYN hYK hYn hYp⟩
  · refine largeEvenMarking_mono (fun lab R _ I F θ hPθ => ?_) hno
    exact ⟨hPθ.1, fun hS hBI => absurd ⟨hS, hBI⟩ hPθ.2⟩

end Certs

end CFSG.StandardType.E6ThreeModel
