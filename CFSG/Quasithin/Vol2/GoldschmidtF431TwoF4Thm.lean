module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Local
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Rec
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.GH74.GLS.SP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13 CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift


set_option linter.unusedSectionVars false

theorem f431Rank2At_twistedF4_of_inputs
    (hRec : ∀ f : ℕ, IsSec53Param .twistedF4 0 f → F431Recognition .twistedF4 0 f)
    (hstd : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
      (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a →
      ∃ V L : Subgroup (Gm K a),
        StdTwo (Gm K a) (Ug K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) (zg hK)
          (tg hK) ∧
        StdLoc (Gm K a) (Ug K a) (zg hK) (tg hK) V L ∧
        StdOrient3 (Gm K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) (zg hK) (tg hK)) :
    F431Rank2At .twistedF4 0 :=
  fun G _ _ hG hnab M₁ M₂ f hP hyps =>
    f431_nonL3_of_inputs (hRec f hP) (f431Out_twistedF4 f) (f431Local_twistedF4_of_std f hstd) G
      hG hnab M₁ M₂ hyps

theorem f431Rank2At_twistedF4_of_octagon
    (hR : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ),
      1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
        RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a)) :
    F431Rank2At .twistedF4 0 :=
  f431Rank2At_twistedF4_of_inputs (fun f _ => f431Recognition_f4 f hR)
    fun K _ _ _ a hK ha => ⟨Vg K a, Lg K a, f4_stdTwo ha hK, f4_stdLoc ha hK,
      stdOrient3_twoF4 ha hK⟩

theorem f431Rank2At_twistedF4 : F431Rank2At .twistedF4 0 :=
  f431Rank2At_twistedF4_of_octagon fun _ _ _ _ _ _ hK => octRGD2 hK

end CFSG.Quasithin.H13.F431.TwoF4
