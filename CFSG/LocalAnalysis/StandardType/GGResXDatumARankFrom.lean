module

public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBTorAFrom_of_all {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (h : GGTBTorAll) : GGTBTorAFrom r₀ :=
  fun p hp hp2 lab hlab htag hr hdvd hM hnot =>
    h.1 p hp hp2 lab hlab htag (by omega) hdvd hM hnot

theorem ggTBTorLiftAFrom_of_rows {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (h : GGTBTorLiftRows) :
    GGTBTorLiftAFrom r₀ :=
  fun p hp hp2 lab hlab htag hr hdvd hM hnot =>
    h p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
      (CoxeterMatrix.A lab.rank) hp hp2 hlab
      (GGTBTorRowAt.aDep htag (by omega) hdvd hM hnot)

private theorem l05nP2F_datum_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGIsWeylMatrix (CoxeterMatrix.A N)) (hMC : GGIntCartan (CoxeterMatrix.A N) C)
    (hTor : GGTorusTorData m N C (CoxeterMatrix.A N) ↥X (ggGamma X hN).range) :
    GGResXDatumA p Bs X N := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ :=
    exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -⟩ :=
    ggHLT_lin hm hpm hBs hS hN w hw V ι (x := 1) (Subgroup.one_mem Bs)
      (Subgroup.one_mem (Subgroup.centralizer (X : Set G)))
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin N, inferInstance, inferInstance, CoxeterMatrix.A N, C, V, hVadd, hVmod, ι,
    (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
    ggHLT_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem ggResXDatumA_core_L_from {r₀ : ℕ} (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀)
    {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs L) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
        GGTWRowPred r₀ p lab ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥L (ggGamma L hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hT p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R) :=
    hLift p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hHas, ?_, ?_⟩
  · exact ⟨hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2.1, hP'.2.2.2.2⟩
  · exact hWtor ↥L (ggQuotHom θ) (ggGamma L hN).range hTB

theorem ggResXDatumA_core_K_from {r₀ : ℕ} (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀)
    {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs K) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
        GGTWRowPred r₀ p lab ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥K (ggGamma K hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hT p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R) :=
    hLift p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hTB := ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hHas, ?_, ?_⟩
  · exact ⟨hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2.1, hP'.2.2.2.2⟩
  · exact hWtor ↥K (ggQuotHom θ) (ggGamma K hN).range hTB

theorem ggResXDatumA_of_tbTor_from_K {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hT : GGTBTorAFrom r₀)
    (hLift : GGTBTorLiftAFrom r₀) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      GGTWRowPred r₀ p lab ∧ GGResXDatumA p Bs K lab.rank := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨lab, hN, hlab, hHas, hP, hTor⟩ := ggResXDatumA_core_K_from hT hLift hH h
  exact ⟨lab, hlab, hHas, hP,
    l05nP2F_datum_of_torData hH.1.1.2.2.2.2.2.1.2.1 (ggHLT_odd_ggTorM hlab) hP.2.2.2.1 hBs hS hN
      (ggHLT_weyl_A (by have := hP.2.1; omega)) (ggIntCartan_A lab.rank) hTor⟩

end CFSG.StandardType

end
