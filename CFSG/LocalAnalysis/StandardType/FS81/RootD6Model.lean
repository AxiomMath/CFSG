module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.GLTheoremA CFSG.LieType.Chevalley

section Certificates


theorem isEmSevenModel_holds : IsEmSevenModel := by
  intro G _ _ Y hY
  obtain ⟨⟨t, r, n⟩, hP, hlab⟩ := exists_glaLabel hY
  obtain ⟨hmt, -, hn⟩ := hP
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, -, hM⟩ := quasisimple_markedModel_of_isLabel hlab
  have hL : LieModel (↥Y ⧸ Subgroup.center ↥Y) .E7 0 2 1 := by
    have h := lieModel_of_markedModel_E7 ht hM
    rwa [hn] at h
  obtain ⟨F, hF, hFin, hcard, ⟨iso⟩⟩ :=
    (hL.chevalleyExceptionalModel (by decide)).2
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  have hZ : Subgroup.center ↥Y = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hq le_rfl hcard iso
  let e0 : (↥Y ⧸ Subgroup.center ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eAQ : AdjointQuotient Tag.E7 F ≃* ↥(adjointGroup Tag.E7 F) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E7) (K := F))).trans
      QuotientGroup.quotientBot
  let φ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_zmod]
    norm_num)
  exact ⟨(e0.symm.trans (iso.trans (eAQ.trans
    (CFSG.TauCetiBridge.adjointGroupCongr φ)))).symm⟩

end Certificates

end CFSG.StandardType.FrameRoute.FS81
