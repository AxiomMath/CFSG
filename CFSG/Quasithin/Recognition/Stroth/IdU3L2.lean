module

public import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
public import CFSG.Quasithin.Recognition.Stroth.LieExtU5
public import CFSG.Quasithin.Recognition.Stroth.U5NotQuasithin
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

theorem idU3L2_of_moufang (hM : Str86Moufang) (hO : Str86Orders)
    (hW : Weiss80UnitaryQuadrangle) : IdU3L2 := by
  intro G _ _ L1 L2 S hF hU3 hBig hL2
  obtain ⟨k, hk, F, hField, hFin, hFc, hSU3⟩ := hU3
  letI : Field F := hField
  haveI : Finite F := hFin
  obtain ⟨hm, -, -, hS⟩ := hO G L1 L2 S k F hF hk hFc hSU3 hBig hL2
  have hWM := hM G L1 L2 S hF ⟨k, hk, F, hField, hFin, hFc, hSU3⟩ hBig hL2
  have hN1 : HasNormalCopy (Subconst (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (StatedProj (StatedSU 3 (2 ^ k) F)) := by
    obtain ⟨N, hN, ⟨f⟩⟩ := f112_exists_normal_iso_psu3_left hF hk hFc hSU3
    exact ⟨N, hN, ⟨f⟩⟩
  have hsimple2 : IsSimpleGroup (oTwoQuot ↥L2) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot (by omega) hm
  have hN2 : HasNormalCopy (Subconst (L2 ⊔ bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S))
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k))) := by
    obtain ⟨N, hN, ⟨f⟩⟩ := f112_exists_normal_iso_oTwoQuot_right hF.toW hsimple2
    obtain ⟨g⟩ := hm
    exact ⟨N, hN, ⟨f.trans g⟩⟩
  obtain ⟨D, hDgrp, hD, hE⟩ :=
    hW G (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) k (2 * k) F hk (by omega) hFc rfl hWM hN1 hN2
      ⟨3 * k, by omega, by
        rw [f112_parabolic_inf_eq_bigB hF.toW]
        exact f112_relIndex_left_u3 hF hk hFc hSU3⟩
      ⟨2 * k, by omega, by
        rw [f112_parabolic_inf_eq_bigB hF.toW]
        exact f112_relIndex_right_l2 hF.toW (by omega) hm⟩
  letI : Group D := hDgrp
  have hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 k) :=
    isAmalgamOfGroup_psu5_of_ext hF hk hFc hSU3 hm hS hD hE
  have hk2 : k = 2 := eq_two_of_isAmalgamOfGroup_psu5 hF (by omega) hA
  subst hk2
  have hcard : Nat.card F = 4 ^ 2 := by simpa using hFc
  refine ⟨⟨F, hField, hFin, hcard, ?_⟩, hm, hA⟩
  rcases hSU3 with hSU | hPSU
  · obtain ⟨e⟩ := hSU
    exact ⟨e⟩
  · obtain ⟨e⟩ := hPSU
    have hcardZ : Nat.card ((StatedScalars (Fin 3) F).subgroupOf
        (StatedSU 3 (2 ^ 2) F)) = 1 := by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hFc (n := 3)
        (by norm_num)).2.2]
      norm_num
    have hbot : (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 4 F) = ⊥ :=
      (Subgroup.card_eq_one (H := (StatedScalars (Fin 3) F).subgroupOf
        (StatedSU 3 4 F))).mp (by simpa using hcardZ)
    have e' : StatedProj (StatedSU 3 4 F) ≃* StatedSU 3 4 F :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact ⟨e.trans e'⟩

end CFSG.Quasithin.Stroth
