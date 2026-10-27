module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchFrame
public import CFSG.LocalAnalysis.StandardType.PhanEMatchPlist
public import CFSG.LocalAnalysis.StandardType.PhanEMatchSeam
public import CFSG.LocalAnalysis.StandardType.PhanEMatchShape
public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd
public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd3
public import CFSG.LocalAnalysis.StandardType.PhanEResS2cProd
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

private lemma plh_ne_22x_of_node_or_path2 {c : PhanCode} (hc : c.IsNode ∨ c.IsPath2) :
    c ≠ PhanCode.a3_22x := by
  rintro rfl
  simpa [PhanCode.IsNode, PhanCode.IsPath2] using hc

private lemma plh_chartOf_of_normalForm {ι Ω : Type} {Y : ChamberSystem ι Ω}
    {J : Set (Fin D.rank)} {a : K ⧸ borel D H}
    (Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
      (residue (cs) (stdδ hct) J a)) Y) (R₀' : Set Ω) (ψ' : Ω → Ω)
    (ψ : ↥(residue (cs) (stdδ hct) J a) → ↥(residue (cs) (stdδ hct) J a))
    (hψ1 : ∀ x : ↥(residue (cs) (stdδ hct) J a),
      ((ψ x : ↥(residue (cs) (stdδ hct) J a)) : K ⧸ borel D H) =
        Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a
          (x : K ⧸ borel D H))
    (hS : ∀ c : ↥(residue (cs) (stdδ hct) J a),
      (c : K ⧸ borel D H) ∈
        Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a ↔ Θ.Φ c ∈ R₀')
    (hψ : ∀ c : ↥(residue (cs) (stdδ hct) J a),
      (c : K ⧸ borel D H) ∈
        Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a →
        Θ.Φ (ψ c) = ψ' (Θ.Φ c)) :
    ChartOf hct F J a Θ R₀' ψ' := by
  refine ⟨hS, ?_⟩
  intro x x' hx hx'
  rw [Subtype.ext (hx'.trans (hψ1 x).symm)]
  exact hψ x hx

include hext hw₀ hsq hpanel in
theorem exists_chart_prod_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) {c₁ c₂ : PhanCode}
    (hc₁ : c₁.IsNode ∨ c₁.IsPath2) (hc₂ : c₂.IsNode) (L₁ : SLPath M c₁.rank) (L₂ : SLPath M 1)
    {J₁ J : Set (Fin D.rank)} (hJ₁ : Set.range L₁.e = J₁) (hJ : insert (L₂.e 0) J₁ = J)
    (hz : L₂.e 0 ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i (L₂.e 0) = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hcore₁ : ∀ k : Fin c₁.rank, L₁.e k ∈ I ↔ c₁.coreN k = true)
    (hperm₁ : ∀ k : Fin c₁.rank, L₁.e k ∈ I →
      ∃ k' : Fin c₁.rank, k'.val = c₁.permN k ∧ L₁.e k' = π (L₁.e k))
    (hcore₂ : L₂.e 0 ∈ I ↔ c₂.coreN 0 = true)
    (hperm₂ : L₂.e 0 ∈ I → ∃ k' : Fin 1, k'.val = c₂.permN 0 ∧ L₂.e k' = π (L₂.e 0)) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a)) ((flagSys Fld c₁.rank).prod (flagSys Fld 1)),
      ChartOf hct F J a Θ (refSet Fld (c₁.rank + 1) c₁.cut ×ˢ refSet Fld 2 c₂.cut)
        (Prod.map (flagPsi' Fld f hK (c₁.rank + 1) c₁.cut c₁.plist)
          (flagPsi' Fld f hK 2 c₂.cut c₂.plist)) := by
  have hf₁ : c₁.IsFlagCode := hc₁.elim PhanCode.IsNode.isFlagCode PhanCode.IsPath2.isFlagCode
  have hf₂ : c₂.IsFlagCode := hc₂.isFlagCode
  have hne₁ : c₁ ≠ PhanCode.a3_22x := plh_ne_22x_of_node_or_path2 hc₁
  have hne₂ : c₂ ≠ PhanCode.a3_22x := plh_ne_22x_of_node_or_path2 (Or.inl hc₂)
  let cc₂ := c₂
  let JJ := J
  rcases hc₂ with rfl | rfl
  all_goals
    subst hJ₁
    subst hJ
    obtain ⟨hIJ, hR, hcoreF, ht₀, hl₀, hψfr⟩ := hfr
    obtain ⟨hd₁, hI₁, hPu₁, hPl₁⟩ :=
      seam_hyps_of_match hct F PC hf₁ L₁ hcore₁ hperm₁ hπ
    have hcore₂' : ∀ k : Fin cc₂.rank, L₂.e k ∈ I ↔ cc₂.coreN k = true :=
      Fin.forall_fin_one.mpr hcore₂
    have hperm₂' : ∀ k : Fin cc₂.rank, L₂.e k ∈ I →
        ∃ k' : Fin cc₂.rank, k'.val = cc₂.permN k ∧ L₂.e k' = π (L₂.e k) :=
      Fin.forall_fin_one.mpr hperm₂
    obtain ⟨hd₂, hI₂, hPu₂, hPl₂⟩ :=
      seam_hyps_of_match hct F PC hf₂ L₂ hcore₂' hperm₂' hπ
    obtain ⟨Θ₀, N₁, N₂, hN₁, hN₂, hSseam, hψseam⟩ :=
      exists_seam_prod hct hext F hw₀ hsq L₁ L₂ rfl rfl hz hcomm hIJ hR hcoreF ht₀ hl₀
        hψfr hd₁ hd₂ hI₁ (Fin.forall_fin_one.mp hI₂) (sg Fld f) (permSL c₁.blockPerm)
          (permSL cc₂.blockPerm)
        c₁.polB cc₂.polB hPu₁ hPl₁ hPu₂ hPl₂
    obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_psiRes hct hext F hw₀ hsq hpanel JJ a
    let S : Set ↥(residue (cs) (stdδ hct) JJ a) :=
      {x | (x : K ⧸ borel D H) ∈
        Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) JJ a}
    have hψ'' : ∀ A₁ ∈ blockSL Fld c₁.rank c₁.cut, ∀ A₂ ∈ blockSL Fld 1 cc₂.cut,
        ∀ c ∈ S,
        Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (c₁.rank + 1)),
          flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2)) →
        Θ₀.Φ (ψ c) =
          (flagAct N₁ (flagAct (SpecialLinearGroup.toGL
              (kapMat (sg Fld f) c₁.polB (permSL c₁.blockPerm) A₁))
                (stdFlag Fld (c₁.rank + 1))),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL
              (kapMat (sg Fld f) cc₂.polB (permSL cc₂.blockPerm) A₂)) (stdFlag Fld 2))) := by
      intro A₁ hA₁ A₂ hA₂ c hc hpair
      exact hψseam A₁ hA₁ A₂ hA₂ c (ψ c) hpair (hψ1 c)
    obtain ⟨Θ, hΘS, hΘψ⟩ :=
      exists_chart_prod ((buildingOver (cs) (stdδ hct) JJ).restrict
        (residue (cs) (stdδ hct) JJ a)) hK hd₁ hd₂ S ψ Θ₀ N₁ N₂ hN₁ hN₂ hSseam
        (fun c hc => hψ2 c hc) (fun c hc => hψ3 c hc) c₁.polB cc₂.polB
        (permSL c₁.blockPerm) (permSL cc₂.blockPerm)
        (coe_permSL_blockPerm hf₁ hne₁) (coe_permSL_blockPerm hf₂ hne₂) hψ''
        c₁.plist cc₂.plist (PhanCode.plist_spec hf₁) (PhanCode.plist_spec hf₂)
    exact ⟨Θ, plh_chartOf_of_normalForm hct F Θ
      (refSet Fld (c₁.rank + 1) c₁.cut ×ˢ refSet Fld 2 cc₂.cut)
      (Prod.map (flagPsi' Fld f hK (c₁.rank + 1) c₁.cut c₁.plist)
        (flagPsi' Fld f hK 2 cc₂.cut cc₂.plist)) ψ hψ1
      (fun c => hΘS c) (fun c hc => hΘψ c hc)⟩

include hext hw₀ hsq hpanel in
theorem exists_chart_prod3_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) {c₁ c₂ c₃ : PhanCode}
    (hc₁ : c₁.IsNode) (hc₂ : c₂.IsNode) (hc₃ : c₃.IsNode) (Lx Ly Lz : SLPath M 1)
    {J : Set (Fin D.rank)} (hJ : insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0}) = J)
    (hxy : Lx.e 0 ≠ Ly.e 0) (hxz : Lx.e 0 ≠ Lz.e 0) (hyz : Ly.e 0 ≠ Lz.e 0)
    (hmxy : coxeterMatrix D.isFiniteType (Lx.e 0) (Ly.e 0) = 2)
    (hmxz : coxeterMatrix D.isFiniteType (Lx.e 0) (Lz.e 0) = 2)
    (hmyz : coxeterMatrix D.isFiniteType (Ly.e 0) (Lz.e 0) = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hcorex : Lx.e 0 ∈ I ↔ c₁.coreN 0 = true)
    (hpermx : Lx.e 0 ∈ I → ∃ k' : Fin 1, k'.val = c₁.permN 0 ∧ Lx.e k' = π (Lx.e 0))
    (hcorey : Ly.e 0 ∈ I ↔ c₂.coreN 0 = true)
    (hpermy : Ly.e 0 ∈ I → ∃ k' : Fin 1, k'.val = c₂.permN 0 ∧ Ly.e k' = π (Ly.e 0))
    (hcorez : Lz.e 0 ∈ I ↔ c₃.coreN 0 = true)
    (hpermz : Lz.e 0 ∈ I → ∃ k' : Fin 1, k'.val = c₃.permN 0 ∧ Lz.e k' = π (Lz.e 0)) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a))
        (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)),
      ChartOf hct F J a Θ ((refSet Fld 2 c₁.cut ×ˢ refSet Fld 2 c₂.cut) ×ˢ refSet Fld 2 c₃.cut)
        (Prod.map (Prod.map (flagPsi' Fld f hK 2 c₁.cut c₁.plist)
          (flagPsi' Fld f hK 2 c₂.cut c₂.plist)) (flagPsi' Fld f hK 2 c₃.cut c₃.plist)) := by
  have hf₁ : c₁.IsFlagCode := hc₁.isFlagCode
  have hf₂ : c₂.IsFlagCode := hc₂.isFlagCode
  have hf₃ : c₃.IsFlagCode := hc₃.isFlagCode
  have hne₁ : c₁ ≠ PhanCode.a3_22x := plh_ne_22x_of_node_or_path2 (Or.inl hc₁)
  have hne₂ : c₂ ≠ PhanCode.a3_22x := plh_ne_22x_of_node_or_path2 (Or.inl hc₂)
  have hne₃ : c₃ ≠ PhanCode.a3_22x := plh_ne_22x_of_node_or_path2 (Or.inl hc₃)
  let cc₁ := c₁
  let cc₂ := c₂
  let cc₃ := c₃
  let JJ := J
  rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> rcases hc₃ with rfl | rfl
  all_goals
    subst hJ
    obtain ⟨hIJ, hR, hcoreF, ht₀, hl₀, hψfr⟩ := hfr
    have hcorex' : ∀ k : Fin cc₁.rank, Lx.e k ∈ I ↔ cc₁.coreN k = true :=
      Fin.forall_fin_one.mpr hcorex
    have hpermx' : ∀ k : Fin cc₁.rank, Lx.e k ∈ I →
        ∃ k' : Fin cc₁.rank, k'.val = cc₁.permN k ∧ Lx.e k' = π (Lx.e k) :=
      Fin.forall_fin_one.mpr hpermx
    have hcorey' : ∀ k : Fin cc₂.rank, Ly.e k ∈ I ↔ cc₂.coreN k = true :=
      Fin.forall_fin_one.mpr hcorey
    have hpermy' : ∀ k : Fin cc₂.rank, Ly.e k ∈ I →
        ∃ k' : Fin cc₂.rank, k'.val = cc₂.permN k ∧ Ly.e k' = π (Ly.e k) :=
      Fin.forall_fin_one.mpr hpermy
    have hcorez' : ∀ k : Fin cc₃.rank, Lz.e k ∈ I ↔ cc₃.coreN k = true :=
      Fin.forall_fin_one.mpr hcorez
    have hpermz' : ∀ k : Fin cc₃.rank, Lz.e k ∈ I →
        ∃ k' : Fin cc₃.rank, k'.val = cc₃.permN k ∧ Lz.e k' = π (Lz.e k) :=
      Fin.forall_fin_one.mpr hpermz
    obtain ⟨hdx, hIx', hPux, hPlx⟩ :=
      seam_hyps_of_match hct F PC hf₁ Lx hcorex' hpermx' hπ
    obtain ⟨hdy, hIy', hPuy, hPly⟩ :=
      seam_hyps_of_match hct F PC hf₂ Ly hcorey' hpermy' hπ
    obtain ⟨hdz, hIz', hPuz, hPlz⟩ :=
      seam_hyps_of_match hct F PC hf₃ Lz hcorez' hpermz' hπ
    obtain ⟨Θ₀, Nx, Ny, Nz, hNx, hNy, hNz, hSseam, hψseam⟩ :=
      exists_seam_prod3 hct hext F hw₀ hsq Lx Ly Lz rfl rfl rfl hxy hxz hyz hmxy hmxz hmyz
        hIJ hR hcoreF ht₀ hl₀ hψfr hdx hdy hdz (Fin.forall_fin_one.mp hIx')
          (Fin.forall_fin_one.mp hIy') (Fin.forall_fin_one.mp hIz')
        (sg Fld f) (permSL cc₁.blockPerm) (permSL cc₂.blockPerm) (permSL cc₃.blockPerm)
        cc₁.polB cc₂.polB cc₃.polB
        (fun k hk c => ⟨hPux k hk c, hPlx k hk c⟩)
        (fun k hk c => ⟨hPuy k hk c, hPly k hk c⟩)
        (fun k hk c => ⟨hPuz k hk c, hPlz k hk c⟩)
    obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_psiRes hct hext F hw₀ hsq hpanel JJ a
    let S : Set ↥(residue (cs) (stdδ hct) JJ a) :=
      {x | (x : K ⧸ borel D H) ∈
        Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) JJ a}
    have hψ'' : ∀ Ax ∈ blockSL Fld 1 cc₁.cut, ∀ Ay ∈ blockSL Fld 1 cc₂.cut,
        ∀ Az ∈ blockSL Fld 1 cc₃.cut, ∀ c ∈ S,
        Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2),
          flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) →
        Θ₀.Φ (ψ c) =
          ((flagAct Nx (flagAct (SpecialLinearGroup.toGL
              (kapMat (sg Fld f) cc₁.polB (permSL cc₁.blockPerm) Ax)) (stdFlag Fld 2)),
            flagAct Ny (flagAct (SpecialLinearGroup.toGL
              (kapMat (sg Fld f) cc₂.polB (permSL cc₂.blockPerm) Ay)) (stdFlag Fld 2))),
              flagAct Nz (flagAct (SpecialLinearGroup.toGL
                (kapMat (sg Fld f) cc₃.polB (permSL cc₃.blockPerm) Az)) (stdFlag Fld 2))) := by
      intro Ax hAx Ay hAy Az hAz c hc hpair
      exact hψseam Ax hAx Ay hAy Az hAz c (ψ c) hpair (hψ1 c)
    obtain ⟨Θ, hΘS, hΘψ⟩ :=
      exists_chart_prod3 ((buildingOver (cs) (stdδ hct) JJ).restrict
        (residue (cs) (stdδ hct) JJ a)) hK hdx hdy hdz S ψ Θ₀ Nx Ny Nz hNx hNy hNz hSseam
        (fun c hc => hψ2 c hc) (fun c hc => hψ3 c hc) cc₁.polB cc₂.polB cc₃.polB
        (permSL cc₁.blockPerm) (permSL cc₂.blockPerm) (permSL cc₃.blockPerm)
        (coe_permSL_blockPerm hf₁ hne₁) (coe_permSL_blockPerm hf₂ hne₂)
        (coe_permSL_blockPerm hf₃ hne₃) hψ''
        cc₁.plist cc₂.plist cc₃.plist (PhanCode.plist_spec hf₁) (PhanCode.plist_spec hf₂)
          (PhanCode.plist_spec hf₃)
    exact ⟨Θ, plh_chartOf_of_normalForm hct F Θ
      ((refSet Fld 2 cc₁.cut ×ˢ refSet Fld 2 cc₂.cut) ×ˢ refSet Fld 2 cc₃.cut)
      (Prod.map (Prod.map (flagPsi' Fld f hK 2 cc₁.cut cc₁.plist)
        (flagPsi' Fld f hK 2 cc₂.cut cc₂.plist)) (flagPsi' Fld f hK 2 cc₃.cut cc₃.plist))
      ψ hψ1 (fun c => hΘS c) (fun c hc => hΘψ c hc)⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
