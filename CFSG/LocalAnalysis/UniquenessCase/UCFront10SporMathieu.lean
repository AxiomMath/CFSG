module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Quasithin.H13.NQCatA314M23
public import CFSG.Quasithin.Background.HSporLatMathieu
import CFSG.Quasithin.H13.NQCatT513Hall
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B5FinOut
import CFSG.Quasithin.Background.C1GNA7
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.H13.A7Nat1238YCases
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
import CFSG.Quasithin.Vol2.Ch10SecD33
import CFSG.Quasithin.Vol2.Ch10SecDClA
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA11Main
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
import CFSG.Quasithin.Vol2.Ch11SecBTCStar
import CFSG.Quasithin.Vol2.Ch11SecCFacts
import CFSG.Quasithin.Vol2.Ch11SecCFacts2
import CFSG.Quasithin.Vol2.Ch11SecSMain
import CFSG.Quasithin.Vol2.Ch11SecSShape2
import CFSG.Quasithin.Vol2.Ch11SecSSym2
import CFSG.Quasithin.Vol2.Ch11SecSSym4
import CFSG.Quasithin.Vol2.Ch11SecSSym5
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type
import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
import CFSG.Quasithin.Vol2.KGNatCoord
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Transvection.Statement
import CFSG.Walter.J1
import CFSG.Walter.JRFacts
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

theorem k105SporAt_of_indexThree {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    (h : CFSG.Quasithin.H.NPrimeHall.IndexThree (⊤ : Subgroup Γ))
    (e : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) : K105SporAt s := by
  intro X _ _ hX S H hS hSH _ h3
  obtain ⟨e₀⟩ := hX
  let e₁ : X ≃* Γ := e₀.trans e
  have hT := CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e₁ hS
  have hcH : Nat.card ↥(H.map e₁.toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective e₁.injective
  have hcS : Nat.card ↥(S.map e₁.toMonoidHom) = Nat.card ↥S :=
    Subgroup.card_map_of_injective e₁.injective
  rcases h (S.map e₁.toMonoidHom) (H.map e₁.toMonoidHom) ⟨hT.1, hT.2.1, hT.2.2⟩
    (Subgroup.map_mono hSH) le_top with h1 | h1
  · rw [hcH, hcS] at h1
    exact (Subgroup.eq_of_le_of_card_ge hSH h1.le).ge
  · rw [hcH, hcS] at h1
    exact absurd ((dvd_mul_right 3 _).trans h1) h3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem k105SporAt_M11 : K105SporAt .M11 := by
  classical
  have hck := M11Lat.cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf M11Lat.Ugrp ⊤ :=
    M11Lat.cert.isSylowTwoOf_top (rawIsEnc 11) hck (k := 4) (m := 495) (by decide) (by decide)
      (by omega)
  have hUc : Nat.card ↥M11Lat.Ugrp = 16 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top hU (a := 4) (m := 495)
      (M11Lat.cert.card_m (rawIsEnc 11) hcl hsz) (by decide)
  refine k105SporAt_of_index (s := .M11) hU (fun Z hZ _ m hm => ?_)
    (MulEquiv.subgroupCongr M11Lat.mGens_closure).symm
  obtain ⟨j, hj, hLM, hZL, hcardj⟩ := M11Lat.cert.overgroup_cases_idx (rawIsEnc 11) hck Z hZ
  have hlen : (M11Lat.cert.tGens :: M11Lat.cert.lat).length = 5 := by
    simp [M11Lat.cert, M11Lat.lat]
  rw [hlen] at hj
  rw [hZL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj, hUc] at hm
  have hs : M11Lat.cert.sizes = [16, 720, 48, 7920, 144] := rfl
  rw [hs] at hm
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hm <;> omega

theorem k105SporAt_M12 :
    K105SporAt .M12 :=
  k105SporAt_of_indexThree (s := .M12) (Γ := ↥CFSG.Blueprint.NativeSporadic.M12)
    CFSG.Quasithin.H.MathieuLat.m12_indexThree (MulEquiv.refl _)

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem k105SporAt_M22 : K105SporAt .M22 := by
  classical
  have hck := M22Lat.cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf M22Lat.Ugrp ⊤ :=
    M22Lat.cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have hUc : Nat.card ↥M22Lat.Ugrp = 128 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top hU (a := 7) (m := 3465)
      (M22Lat.cert.card_m (rawIsEnc 22) hcl hsz) (by decide)
  refine k105SporAt_of_index (s := .M22) hU (fun Z hZ _ m hm => ?_)
    (MulEquiv.subgroupCongr M22Lat.mGens_closure).symm
  obtain ⟨j, hj, hLM, hZL, hcardj⟩ := M22Lat.cert.overgroup_cases_idx (rawIsEnc 22) hck Z hZ
  have hlen : (M22Lat.cert.tGens :: M22Lat.cert.lat).length = 6 := by
    simp [M22Lat.cert, M22Lat.lat]
  rw [hlen] at hj
  rw [hZL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj, hUc] at hm
  have hs : M22Lat.cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  rw [hs] at hm
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hm <;> omega

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312M23 CFSG.Quasithin.H.MathieuLat in
theorem k105SporAt_M23 :
    K105SporAt .M23 := by
  refine k105SporAt_of_index (s := .M23) (Γ := ↥CFSG.Blueprint.NativeSporadic.M23) m23_S_sylow
    (fun Z hZ _ m hm => ?_) (MulEquiv.refl _)
  obtain ⟨j, hj, rfl⟩ := m23_complete Z hZ
  have hS : Nat.card ↥m23Ctx.S = 128 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top m23_S_sylow (a := 7) (m := 79695)
      (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num) (by decide)
  rw [CFSG.Quasithin.H13.NQCat.A314D.card_memberOrTop hj, hS] at hm
  interval_cases j <;> simp at hm <;> omega

theorem k105SporAt_M24 :
    K105SporAt .M24 :=
  k105SporAt_of_indexThree (s := .M24) (Γ := ↥CFSG.Blueprint.NativeSporadic.M24)
    CFSG.Quasithin.H.MathieuLat.m24_indexThree (MulEquiv.refl _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
