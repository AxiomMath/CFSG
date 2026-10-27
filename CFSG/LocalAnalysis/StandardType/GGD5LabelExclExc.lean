module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelGlue
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3951
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitE6Two
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGPumpTwExcKnownHolds
import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10e_not_exc {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (_hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel (fun _ lab =>
        (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6) ∧ lab.n = 1) 3 Bs L := by
  intro hq
  have hq' : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .E6 ∧ lab.n = 1) ∨
        ((lab.tag = .E7 ∧ lab.n = 1) ∨
          ((lab.tag = .E8 ∧ lab.n = 1) ∨ (lab.tag = .twE6 ∧ lab.n = 1)))) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
      rcases h with ⟨h, hn⟩
      rcases h with h | h | h | h
      · exact Or.inl ⟨h, hn⟩
      · exact Or.inr (Or.inl ⟨h, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hn⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hn⟩))) hq
  rcases GGInnerDiagOnLabel.elim_or hq' with hE6 | h'
  ·
    have hE6supplier : LargeEvenLabelAll ⟨.E6, 0, 1⟩ (fun R _ I _ =>
        GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
            ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
            ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
              (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
              3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
              Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) :=
      ggPumpTwExcKnown_holds 1 (by norm_num) ⟨.E6, 0, 1⟩ (Or.inl ⟨rfl, by norm_num⟩)
    have hE6refl : LargeEvenLabelAll ⟨.E6, 0, 1⟩
        (fun R _ I _ => GGTorusReflGenW 3 4 R I) := by
      intro Q hQ
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
      obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
      have hK2 : Nat.card K = 2 := by simpa using hK
      exact ⟨K, hField, hFinite, hK, hQ',
        ggTorusReflGenW_E6Two_three (K := K) hK2⟩
    have hE6torus : LargeEvenLabelAll ⟨.E6, 0, 1⟩ (fun R _ _ _ => GGTorusLift 3 4 R) :=
      largeEvenLabelAll_torusLift_E6_two ⟨rfl, rfl⟩
    have hE6both : LargeEvenLabelAll ⟨.E6, 0, 1⟩ (fun R _ I _ =>
        (GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
            ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
            ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
              (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
              3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
              Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
        (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R)) :=
      largeEvenLabelAll_and hE6supplier (largeEvenLabelAll_and hE6refl hE6torus)
    have hqE6' : LargeEvenMarking L (fun lab R _ I _ θ =>
        ((lab.tag = .E6 ∧ lab.n = 1) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        ((GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
            ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
            ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
              (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
              3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
              Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
        (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R))) := by
      refine largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .E6 ∧ lab.n = 1)
        (P' := fun R _ I _ =>
          (GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
            ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
              ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
              ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
                3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
                Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
          (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R)) ?_ ?_ hE6
      · intro lab hlab hs
        have hlabE6 : lab = ⟨.E6, 0, 1⟩ := by
          obtain ⟨t, l, n⟩ := lab
          obtain ⟨ht, hn⟩ := hs
          dsimp only at ht hn hlab
          subst ht
          subst hn
          have hl0 : l = 0 := by simpa using hlab.2
          subst hl0
          rfl
        exact hlabE6 ▸ hE6both
      · intro lab R _ I F θ hP
        exact hP.1
    obtain ⟨hL, _, _, hraw⟩ := hqE6'
    obtain ⟨R, hR, I, F, _, _, θ, hP, hE6facts⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨⟨_, _⟩, hBsN, hBs3⟩ := hP
    obtain ⟨hE6P1, hE6P2⟩ := hE6facts
    obtain ⟨_, _, horder⟩ := hE6P1
    obtain ⟨hrefl, hlift⟩ := hE6P2
    have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
    have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
      hS.1.1.2.1.2.2.2
    have hge := card_range_ggGamma_bstar_ge (p := 3) (r := 4) hS.1.1 hL θ hBsN hlift
    have h4 : 3 ^ 4 ≤ Nat.card (ggGamma L hBsN).range := hge.1
    have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := hge.2
    have hTB : GGTorusTBGroup 3 4 R I L (ggQuotHom θ) (ggGamma L hBsN).range :=
      ggTorusTBGroup_of_marking (r := 4) Nat.prime_three hBs hSC hL θ hBsN
        (fun b hb => ggLAut_mem_of_induces L θ hBsN hBs3 hb) h4 h3
    have hInner : Nat.card (ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (ggGamma L hBsN).range) = 1152 :=
      horder L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
        (ggGamma L hBsN).range hTB.2.2.2.1 hTB.2.2.2.2.1 h4 hTB.2.2.2.2.2.2.2
    have hWrefl : ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (ggGamma L hBsN).range ≤
          Subgroup.closure (ggTorusReflSet 3 (ggGamma L hBsN).range) :=
      hrefl L (ggQuotHom θ) (ggGamma L hBsN).range hTB
    have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
      have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
          Bs ⊓ Subgroup.centralizer (L : Set G) := by
        intro z hz
        exact ⟨hz.1.1, hz.2⟩
      have h := Subgroup.card_le_of_le hle
      rwa [GGConfig.card_bstar_inf_centralizer_L hS.1.1] at h
    have hcardEq := card_ggAutomizer_eq_gamma_of_weylReflSet (p := 3) Nat.prime_three
      (by norm_num) (X := L) hBs hSC hS.1.2.2.2.1 hBsN hZ hWrefl
    rw [← hcardEq] at hInner
    rw [lup10c_card_automizer M e hecart he0 hbas] at hInner
    norm_num at hInner
  rcases GGInnerDiagOnLabel.elim_or h' with hE7 | h'
  ·
    have hE7lift : LargeEvenLabelAll ⟨.E7, 0, 1⟩
        (fun R _ _ _ => GGTorusLift 3 6 R) := by
      intro Q hQ
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
      obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
      have hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two le_rfl hK
      exact ⟨K, hField, hFinite, hK, hQ', TableBExcTwo.ggTorusLift_E7Two (K := K)⟩
    have hqE7' : LargeEvenMarking L (fun lab R _ I _ θ =>
        ((lab.tag = .E7 ∧ lab.n = 1) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        GGTorusLift 3 6 R) := by
      refine largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .E7 ∧ lab.n = 1)
        (P' := fun R _ _ _ => GGTorusLift 3 6 R) ?_ ?_ hE7
      · intro lab hlab hs
        have hlabE7 : lab = ⟨.E7, 0, 1⟩ := by
          obtain ⟨t, l, n⟩ := lab
          obtain ⟨ht, hn⟩ := hs
          dsimp only at ht hn hlab
          subst ht
          subst hn
          have hl0 : l = 0 := by simpa using hlab.2
          subst hl0
          rfl
        exact hlabE7 ▸ hE7lift
      · intro lab R _ I F θ hP
        exact hP.1
    obtain ⟨_, _, _, hraw⟩ := hqE7'
    obtain ⟨R, hR, I, F, _, _, θ, _, hlift⟩ := largeEvenRawDatum_exists hraw
    exact lup10c_not_torusLift hS M e hbas (θ := θ) (r := 6) (by norm_num) hlift
  rcases GGInnerDiagOnLabel.elim_or h' with hE8 | htwE6
  ·
    have hE8lift : LargeEvenLabelAll ⟨.E8, 0, 1⟩
        (fun R _ _ _ => GGTorusLift 3 7 R) := by
      intro Q hQ
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
      obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
      have hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two le_rfl hK
      exact ⟨K, hField, hFinite, hK, hQ', TableBExcTwo.ggTorusLift_E8Two (K := K)⟩
    have hqE8' : LargeEvenMarking L (fun lab R _ I _ θ =>
        ((lab.tag = .E8 ∧ lab.n = 1) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        GGTorusLift 3 7 R) := by
      refine largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .E8 ∧ lab.n = 1)
        (P' := fun R _ _ _ => GGTorusLift 3 7 R) ?_ ?_ hE8
      · intro lab hlab hs
        have hlabE8 : lab = ⟨.E8, 0, 1⟩ := by
          obtain ⟨t, l, n⟩ := lab
          obtain ⟨ht, hn⟩ := hs
          dsimp only at ht hn hlab
          subst ht
          subst hn
          have hl0 : l = 0 := by simpa using hlab.2
          subst hl0
          rfl
        exact hlabE8 ▸ hE8lift
      · intro lab R _ I F θ hP
        exact hP.1
    obtain ⟨_, _, _, hraw⟩ := hqE8'
    obtain ⟨R, hR, I, F, _, _, θ, _, hlift⟩ := largeEvenRawDatum_exists hraw
    exact lup10c_not_torusLift hS M e hbas (θ := θ) (r := 7) (by norm_num) hlift
  ·
    have hmark : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
      change LargeEvenMarking L (fun lab R _ I _ θ =>
        GGTableBTwE6ThreeLabel 3 lab ∧ LargeEvenSplit 3 lab ∧
          Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
      refine largeEvenMarking_mono ?_ htwE6
      intro lab R _ I F θ hP
      obtain ⟨⟨htag, hn1⟩, hBsN, hBs3⟩ := hP
      refine ⟨⟨htag, rfl, ?_⟩, ?_, hBsN, hBs3⟩
      · rw [hn1]
        norm_num
      · exact Or.inr (Or.inr (Or.inr ⟨hn1, rfl⟩))
    have h6 := ggL48TwE6_pow_six_le_card ggTwE6ThreeBstarRankInput_holds hS.1.1 hmark
    have h5 := lup10c_card_Bs M e hbas
    rw [h5] at h6
    norm_num at h6


end CFSG.StandardType

end
