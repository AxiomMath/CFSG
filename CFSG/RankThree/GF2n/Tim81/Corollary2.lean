module

public import CFSG.RankThree.GF2n.Tim81.Defs
public import CFSG.CGT.Timmesfeld75.NodeDerivation
public import CFSG.RankThree.GF2n.Tim78Bridge
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.GF2n.Statements

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.Open CFSG.Open.StatedAPI

theorem tim81UnitaryStatement_of_theorem1_sec8 (h1 : Theorem1Statement) (h8 : Sec8Statement) :
    Tim81UnitaryStatement := by
  intro G _ _ _ hnonab hK hchar M hM B hB hTI h4 hWCQ hNWC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCore 2 G = ⊥ := by
    haveI : (pCore 2 G).Normal := pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 G) with h | h
    · exact h
    · exfalso
      have hP : IsPGroup 2 ↥(⊤ : Subgroup G) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := G)
      have hP' : IsPGroup 2 G :=
        hP.of_surjective (⊤ : Subgroup G).subtype Subgroup.topEquiv.surjective
      haveI : Group.IsNilpotent G := hP'.isNilpotent
      have hcomm : ∀ a b : G, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable G)
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hcomm a b)
  have hF : generalizedFitting M = pCore 2 M :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore M 2).1 (hchar M hM.1)
  have hmaxAb : Maximal (fun U : Subgroup G => U ≤ M ∧
      M ≤ Subgroup.normalizer (U : Set G) ∧ IsMulCommutative U) B :=
    Tim78.maximalAbelian_of_maximalElemAbelian hnonab hM hF hB hTI h4
  have hHyp : Hyp M B := ⟨hO2, hM, hF, hmaxAb, hB.prop.2.2, hTI⟩
  obtain ⟨H, hH⟩ := h8 G hnonab hK hchar M B hHyp h4 hWCQ hNWC
  rcases h1 G M B hHyp h4 hWCQ with hwc | huc | hnone
  · exact (hNWC hwc).elim
  ·
    obtain ⟨f, hf, hcard, _hnorm, m, hm, Φ, hrange, hker, _hconj⟩ := huc
    have hBne : B ≠ ⊥ := by
      intro hbot
      have : Nat.card B = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    have htop : Subgroup.normalClosure (B : Set G) = ⊤ :=
      CFSG.CGT.Timmesfeld75.normalClosure_eq_top_of_simple hBne
    have hsurj : Function.Surjective Φ :=
      MonoidHom.range_eq_top.mp (by rw [hrange, htop])
    let S := Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m
    let e : (S ⧸ Subgroup.center S) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj)
    have hm3 : 3 ≤ m := by omega
    have hneq : (m, 2 ^ f) ≠ (3, 2) := by
      intro hEq
      have hm' : m = 3 := congrArg Prod.fst hEq
      omega
    have hadm : StatedLieAdmissible .PSU m 2 f :=
      ⟨Nat.prime_two, by omega, hm3, hneq⟩
    have hFcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      CFSG.Timmesfeld.Transvection.card_galoisField_two_mul (by omega : 1 ≤ f)
    have hmodel : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU m 2 f :=
      Unitary.statedClassicalModel_center_quotient (F := GaloisField 2 (2 * f))
        (p := 2) (f := f) (n := m) hadm hFcard
    exact ⟨f, hcard, hf, m, hm, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hmodel⟩
  · exact (hnone H hH).elim

end CFSG.RankThree.GF2n.Tim81
