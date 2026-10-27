module

public import CFSG.Quasithin.Recognition.SzVBS5Key
public import CFSG.Quasithin.Recognition.SzVBS5Hyp
public import CFSG.Quasithin.Recognition.SzVBOddL24Main
public import CFSG.Quasithin.Recognition.SzVBGeo

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F204

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem r1Setting_plus (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1)) :
    R1SettingLegacyBare K1 L2 (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)) Zs := by
  have e : pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1) = twistFree K1 S := sup_comm _ _
  rw [e]
  exact r1Setting_plus_of_inf h (inf_L2_le_twistFree rankOneListedFacts h hL)

theorem vBeta_plus (h : R1SettingLegacyBare K1 L2 S Zs) :
    vBeta K1 L2 (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)) Zs = vBeta K1 L2 S Zs := by
  have e : pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1) = twistFree K1 S := sup_comm _ _
  rw [e]
  exact vBeta_plus_eq h

theorem plus_le (h : R1SettingLegacyBare K1 L2 S Zs) :
    pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1) ≤
      K1 ⊔ pCoreOf 2 (K1 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1))) := by
  have e : pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1) = twistFree K1 S := sup_comm _ _
  rw [e]
  exact twistFree_le_sup_pCoreOf h.hyp.h1.normalizes h.hyp.h1.pgroup h.hyp.h1.sylow

@[expose] def VBOddL24FarA5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    IsL2Quot 2 (OTwoQuot K1) → S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ →
    7 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) →
    ¬ Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2))

@[expose] def VBEvenL24A5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    IsL2Quot 2 (OTwoQuot K1) → S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ →
    ¬ Even (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2))

theorem f112R1aAbelian_of_A5 (hO : VBOddL24FarA5Statement) (hE : VBEvenL24A5Statement) :
    F112R1aAbelianStatement := by
  intro G _ _ K1 L2 S Zs h hL hab
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  have h' := r1Setting_plus h hL
  have hab' : ⁅vBeta K1 L2 (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)) Zs,
      vBeta K1 L2 (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)) Zs⁆ = ⊥ := by
    rw [vBeta_plus h]
    exact hab
  have hb := three_le_critDist_of_comm hRO h' hab'
  obtain ⟨h3, h5⟩ := not_odd_le_five_L24 hRO h' hL
  rcases Nat.even_or_odd (critDist (K1 ⊔ L2 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)))
      (L2 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1))) (K1 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)))
      (conjClosure Zs L2)) with hev | hodd
  · exact hE G K1 L2 _ Zs h' hL (plus_le h) hab' hev
  · have h7 : 7 ≤ critDist (K1 ⊔ L2 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)))
        (L2 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1))) (K1 ⊔ (pCoreOf 2 (K1 ⊔ S) ⊔ (S ⊓ K1)))
        (conjClosure Zs L2) := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact hO G K1 L2 _ Zs h' hL (plus_le h) hab' h7 hodd

end CFSG.Quasithin.SzVB
