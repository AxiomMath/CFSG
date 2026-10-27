module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegFrame
public import CFSG.LocalAnalysis.StandardType.GGResIICell
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.OrthOrderBound

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.ZS

theorem qTwoGlobSel_join_le_ggAInf
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {Kset : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J Kset) :
    ggAutomizerJoin L Bs Kset ≤ ggAInf 3 B Bs x L D J :=
  GGNbrSet.automizerJoin_le_ggAInf hcfg.2.2.2.1

theorem qTwoGlobSel_factorial_dvd_card_Abar
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {Kset : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J Kset)
    {N : ℕ} (hN1 : 1 ≤ N)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs Kset))
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ) :
    N.factorial ∣ Nat.card Abar := by
  have hle : ggAutomizerJoin L Bs Kset ≤ ggAInf 3 B Bs x L D J :=
    qTwoGlobSel_join_le_ggAInf hcfg
  have hcard_join : Nat.card (ggAutomizerJoin L Bs Kset) = N.factorial :=
    qTwoDegFrame_card_weyl hN1 hA
  have hdv : Nat.card (ggAutomizerJoin L Bs Kset) ∣ Nat.card (ggAInf 3 B Bs x L D J) :=
    Subgroup.card_dvd_of_le hle
  have hcard_ainf : Nat.card (ggAInf 3 B Bs x L D J) = Nat.card Abar :=
    Nat.card_congr ρ.toEquiv
  rwa [hcard_join, hcard_ainf] at hdv

theorem qTwoGlobSel_linWeyl_of_card_eq
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {Kset : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J Kset)
    {N : ℕ} (hN1 : 1 ≤ N) (hN2 : 2 ≤ N)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs Kset))
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hcard : Nat.card Abar = N.factorial) :
    ZS.LinWeyl 3 Abar := by
  have hle : ggAutomizerJoin L Bs Kset ≤ ggAInf 3 B Bs x L D J :=
    qTwoGlobSel_join_le_ggAInf hcfg
  have hcard_join : Nat.card (ggAutomizerJoin L Bs Kset) = N.factorial :=
    qTwoDegFrame_card_weyl hN1 hA
  have hcard_ainf : Nat.card (ggAInf 3 B Bs x L D J) = Nat.card Abar :=
    Nat.card_congr ρ.toEquiv
  have heq : ggAutomizerJoin L Bs Kset = ggAInf 3 B Bs x L D J := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard_ainf, hcard, hcard_join]
  obtain ⟨e, he⟩ := hA
  let e' : (CoxeterMatrix.A (N - 1)).Group ≃* ↥(ggAInf 3 B Bs x L D J) :=
    e.trans (MulEquiv.subgroupCongr heq)
  let f : (CoxeterMatrix.A (N - 1)).Group ≃* ↥Abar := e'.trans ρ
  have hM : GGIsWeylMatrix (CoxeterMatrix.A (N - 1)) :=
    CFSG.StandardType.ggResII_isWeyl_A (by omega)
  refine ⟨Fin (N - 1), CoxeterMatrix.A (N - 1), hM, f, fun i => ?_⟩
  have hrefl : GGIsReflection 3 ((e' ((CoxeterMatrix.A (N - 1)).simple i) :
      ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs) := by
    simpa [e', MulEquiv.subgroupCongr_apply] using he i
  exact (hD.2.2.2.2.2.1 (e' ((CoxeterMatrix.A (N - 1)).simple i))).mp hrefl

end CFSG.StandardType.QTwo

end
