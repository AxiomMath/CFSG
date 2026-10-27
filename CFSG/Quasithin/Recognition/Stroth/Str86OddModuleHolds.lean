module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleNatural
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleOrthFalse

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86OddModuleOf_holds :
    Str86OddModuleOf := by
  intro G _ _ L1 L2 S k m F _ _ hF hSB hk hFc hU3 hB2 hL2 hkm hZI hZQ hab
  classical
  have hm : 2 ≤ m := by omega
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  obtain ⟨D, hDS, hDQ, hD⟩ :=
    str86_exists_displacement hF hSB hk hFc hU3 hB2 hL2 hkm hZI hZQ hab
  have hc1 := str86_chief_count_one hF hSB hk hFc hU3 hB2 hL2 hkm hZI hDS hDQ hD
  obtain ⟨hstep, hnc⟩ := str86_commutator_isChiefStep hF hSB hk hFc hU3 hB2 hm hL2 hZI hc1
  have hWZ2 : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤ Z2 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro z hz h hh
    have h1 : h * z⁻¹ * h⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (str86_z2_normal_u3H L1 L2 S hh) z⁻¹).mp
        ((Z2 L1 L2 S).inv_mem hz)
    rw [commutatorElement_def]
    simpa [mul_assoc] using (Z2 L1 L2 S).mul_mem hz h1
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep (q2_le_u3H L1 L2 S)
      (pCoreOf_isPGroup 2 (P2 L1 L2 S))
  obtain ⟨e₀⟩ := str86_isL2Quot_u3H hF.toW hL2
  let e := e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 m))
  obtain ⟨hZW, hWS⟩ := str86_z1_le_commutator hF hSB hk hFc hU3 hB2 hm hL2 hZI
  rcases str86_chief_natural_or_orth hF hSB hk hL2 hkm hstep hnc hWZ2 hE e hDS hDQ hD with
    hnat | ⟨l, hl, hml, horth⟩
  ·
    have hZ1 := str86_card_z1_of_natural hF hSB hm hL2 hstep hE e hnat hWS
    refine ⟨⟨hstep, hE, e, hnat⟩, hZW, hZ1, ?_, ?_⟩
    · exact str86_natural_commutator_zpowers_eq hF hSB hm hL2 hstep rfl hE e hnat hWS hZ1
    · exact str86_natural_inf_conj_eq hF hSB hk hFc hU3 hm hL2 hstep hWZ2 rfl hE e hnat hWS
  ·
    exact (str86_orth_false hF hSB hk hFc hU3 hB2 hL2 hkm hZI hZQ hab hstep hWZ2 rfl hE e hl
      hml horth).elim

end CFSG.Quasithin.Stroth

end
