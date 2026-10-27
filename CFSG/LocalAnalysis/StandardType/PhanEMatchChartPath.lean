module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchFrame
public import CFSG.LocalAnalysis.StandardType.PhanEMatchPlist
public import CFSG.LocalAnalysis.StandardType.PhanEMatchSeam
public import CFSG.LocalAnalysis.StandardType.PhanEResS2c
public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormalX

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1) (hpanel : StdPanel hct F (nrep hct w₀))

include hext hw₀ hsq hpanel in
theorem exists_chart_flagCode (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) {c : PhanCode} (hc : c.IsFlagCode)
    (hc22 : c ≠ PhanCode.a3_22x) (L : SLPath M c.rank) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J) {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)}
    {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hcore : ∀ k : Fin c.rank, L.e k ∈ I ↔ c.coreN k = true)
    (hperm : ∀ k : Fin c.rank, L.e k ∈ I →
      ∃ k' : Fin c.rank, k'.val = c.permN k ∧ L.e k' = π (L.e k)) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a)) (flagSys Fld c.rank),
      ChartOf hct F J a Θ (refSet Fld (c.rank + 1) c.cut)
        (flagPsi' Fld f hK (c.rank + 1) c.cut c.plist) := by
  obtain ⟨hIJ, hR, hcoreF, ht₀, hl₀, hψ⟩ := hfr
  obtain ⟨hd, hI, hPu, hPl⟩ := seam_hyps_of_match hct F PC hc L hcore hperm hπ
  obtain ⟨Θ₀, N, hN, hS, hψ'⟩ :=
    exists_seam hct hext F hw₀ hsq L hJ hIJ hR hcoreF ht₀ hl₀ hψ hd hI
      (sg Fld f : Fld →+* Fld) (permSL c.blockPerm) c.polB hPu hPl
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_psiRes hct hext F hw₀ hsq hpanel J a
  let S : Set ↥(residue (cs) (stdδ hct) J a) :=
    {x | (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct)
      (stdFlip F (nrep hct w₀)) J a}
  have hψS : ∀ c ∈ S, ψ c ∈ S := fun c hc => hψ2 c hc
  have hψψ : ∀ c ∈ S, ψ (ψ c) = c := fun c hc => hψ3 c hc
  have hψ'' : ∀ A ∈ blockSL Fld c.rank c.cut, ∀ x ∈ S,
      Θ₀.Φ x = flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (c.rank + 1)) →
        Θ₀.Φ (ψ x) = flagAct N (flagAct
          (SpecialLinearGroup.toGL (kapMat (sg Fld f : Fld →+* Fld) c.polB
            (permSL c.blockPerm) A)) (stdFlag Fld (c.rank + 1))) := by
    intro A hA x hx hAx
    exact hψ' A hA x (ψ x) hAx (hψ1 x)
  obtain ⟨Θ, hΘS, hΘψ⟩ := exists_chart_shape
    ((buildingOver (cs) (stdδ hct) J).restrict (residue (cs) (stdδ hct) J a))
    hK hd S ψ Θ₀ N hN hS hψS hψψ c.polB (permSL c.blockPerm)
    (coe_permSL_blockPerm hc hc22) hψ'' c.plist (PhanCode.plist_spec hc)
  refine ⟨Θ, ?_, ?_⟩
  · exact hΘS
  · intro x x' hx hx'
    have hxS : x ∈ S := hx
    have hx'eq : x' = ψ x := Subtype.ext (by rw [hψ1 x]; exact hx')
    rw [hx'eq]
    exact hΘψ x hxS

include hext hw₀ hsq hpanel in
theorem exists_chart_22x_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (L : SLPath M 3) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J) {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)}
    {t₀ l₀ : K} (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hcore : ∀ k : Fin 3, L.e k ∈ I ↔ PhanCode.a3_22x.coreN k = true)
    (hperm : ∀ k : Fin 3, L.e k ∈ I →
      ∃ k' : Fin 3, k'.val = PhanCode.a3_22x.permN k ∧ L.e k' = π (L.e k)) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a)) (flagSys Fld 3),
      ChartOf hct F J a Θ (refSet Fld 4 [0, 2, 4]) (flagPsiX hK) := by
  obtain ⟨hIJ, hR, hcoreF, ht₀, hl₀, hψ⟩ := hfr
  obtain ⟨hd, hI, hPu, hPl⟩ :=
    seam_hyps_of_match (c := PhanCode.a3_22x) hct F PC
      (by simp [PhanCode.IsFlagCode]) L hcore hperm hπ
  obtain ⟨Θ₀, N, hN, hS, hψ'⟩ :=
    exists_seam hct hext F hw₀ hsq L hJ hIJ hR hcoreF ht₀ hl₀ hψ hd hI
      (sg Fld f : Fld →+* Fld) (permSL PhanCode.a3_22x.blockPerm)
      PhanCode.a3_22x.polB hPu hPl
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_psiRes hct hext F hw₀ hsq hpanel J a
  let S : Set ↥(residue (cs) (stdδ hct) J a) :=
    {x | (x : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct)
      (stdFlip F (nrep hct w₀)) J a}
  have hψS : ∀ c ∈ S, ψ c ∈ S := fun c hc => hψ2 c hc
  have hψψ : ∀ c ∈ S, ψ (ψ c) = c := fun c hc => hψ3 c hc
  have hψ'' : ∀ A ∈ blockSL Fld 3 [0, 2, 4], ∀ x ∈ S,
      Θ₀.Φ x = flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld 4) →
        Θ₀.Φ (ψ x) = flagAct N (flagAct
          (SpecialLinearGroup.toGL (kapMat (sg Fld f : Fld →+* Fld) false
            (permSL PhanCode.a3_22x.blockPerm) A)) (stdFlag Fld 4)) := by
    intro A hA x hx hAx
    exact hψ' A hA x (ψ x) hAx (hψ1 x)
  obtain ⟨Θ, hΘS, hΘψ⟩ := exists_chart_22x
    ((buildingOver (cs) (stdδ hct) J).restrict (residue (cs) (stdδ hct) J a))
    hK S ψ Θ₀ N hN hS hψS hψψ (permSL PhanCode.a3_22x.blockPerm)
    (coe_permSL_blockPerm_22x) hψ''
  refine ⟨Θ, ?_, ?_⟩
  · exact hΘS
  · intro x x' hx hx'
    have hxS : x ∈ S := hx
    have hx'eq : x' = ψ x := Subtype.ext (by rw [hψ1 x]; exact hx')
    rw [hx'eq]
    exact hΘψ x hxS

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
