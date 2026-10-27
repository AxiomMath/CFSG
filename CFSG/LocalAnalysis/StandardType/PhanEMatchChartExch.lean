module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchFrame
public import CFSG.LocalAnalysis.StandardType.PhanEMatchPlist
public import CFSG.LocalAnalysis.StandardType.PhanEMatchSeam
public import CFSG.LocalAnalysis.StandardType.PhanEMatchShape
public import CFSG.LocalAnalysis.StandardType.PhanEMatchExch
public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd
public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd3
public import CFSG.LocalAnalysis.StandardType.PhanEResS2cExch
public import CFSG.LocalAnalysis.StandardType.PhanEResS2cA2A1

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt.SLClosed
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2] {f : ℕ}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

theorem blk_one_matrix (B : SpecialLinearGroup (Fin 2) Fld) :
    ((WeakCT.blk Fld 1 B : SpecialLinearGroup (Fin 3) Fld) : Matrix (Fin 3) (Fin 3) Fld) =
      emb21 (B : Matrix (Fin 2) (Fin 2) Fld) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WeakCT.blk, WeakCT.coe_blockSL_three_one, emb21]

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1) (hpanel : StdPanel hct F (nrep hct w₀))

private theorem plh_cutTypes_one_02 : cutTypes 1 [0, 2] = ({0} : Set (Fin 1)) := by
  ext j
  simp only [cutTypes, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [Nat.forall_lt_iff_fin]
  fin_cases j <;> decide

private theorem plh_cutTypes_two_013 : cutTypes 2 [0, 1, 3] = ({1} : Set (Fin 2)) := by
  ext j
  simp only [cutTypes, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [Nat.forall_lt_iff_fin]
  fin_cases j <;> decide

include hext hw₀ hsq hpanel in
theorem exists_chart_exchA1A1_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (L₁ L₂ : SLPath M 1)
    {J₁ J : Set (Fin D.rank)} (hJ₁ : Set.range L₁.e = J₁) (hJ : insert (L₂.e 0) J₁ = J)
    (hz : L₂.e 0 ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i (L₂.e 0) = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hI₁ : L₁.e 0 ∈ I) (hI₂ : L₂.e 0 ∈ I) (hπ₁ : π (L₁.e 0) = L₂.e 0)
    (hπ₂ : π (L₂.e 0) = L₁.e 0) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a)) ((flagSys Fld 1).prod (flagSys Fld 1)),
      ChartOf hct F J a Θ (Set.univ : Set (FlagK Fld 2 × FlagK Fld 2)) (psiA1A1 hK) := by
  subst hJ
  subst hJ₁
  have hd₁ : IsCut (1 + 1) [0, 2] := PhanCode.isCut_cut (c := PhanCode.a1moved) trivial
  have hk₁ : cutTypes 1 [0, 2] = ({0} : Set (Fin 1)) := plh_cutTypes_one_02
  have hI₁' : ∀ k : Fin 1, L₁.e k ∈ I ↔ k ∈ cutTypes 1 [0, 2] := by
    intro k
    rw [hk₁]
    fin_cases k
    exact ⟨fun _ => rfl, fun _ => hI₁⟩
  have hπ₁' : weylAction D.isFiniteType v (Pi.single (F.op (L₁.e (0 : Fin 1))) 1) =
      Pi.single (L₂.e 0) 1 := by
    simpa only [hπ₁] using hπ (L₁.e (0 : Fin 1)) hI₁
  have hπ₂' : weylAction D.isFiniteType v (Pi.single (F.op (L₂.e 0)) 1) =
      Pi.single (L₁.e (0 : Fin 1)) 1 := by
    simpa only [hπ₂] using hπ (L₂.e 0) hI₂
  let β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (1 + 1)) Fld :=
    MonoidHom.id (SpecialLinearGroup (Fin 2) Fld)
  have hβu : ∀ c : Fld, β (tv Fld 0 1 c) =
      tv Fld (0 : Fin 1).castSucc (0 : Fin 1).succ c := fun _ => rfl
  have hβl : ∀ c : Fld, β (tv Fld 1 0 c) =
      tv Fld (0 : Fin 1).succ (0 : Fin 1).castSucc c := fun _ => rfl
  obtain ⟨hXu₁, hXl₁, hXu₂, hXl₂⟩ :=
    hX_of_swap (hct := hct) (F := F) (PC := PC) (L₁ := L₁) (L₂ := L₂)
      (v := v) (k₁ := (0 : Fin 1)) (hπ₁ := hπ₁') (hπ₂ := hπ₂') (β := β)
      (hβu := hβu) (hβl := hβl)
  obtain ⟨Θ₀, N₁, N₂, _hStab₁, hcoreΘ, hψΘ⟩ :=
    Res.exists_seam_exch (hct := hct) (hext := hext) (F := F) (hw₀ := hw₀) (hsq := hsq)
      (L₁ := L₁) (L₂ := L₂) (J₁ := Set.range L₁.e) (z := L₂.e 0)
      (hJ₁ := rfl) (hz₂ := rfl) (hz := hz) (hcomm := hcomm)
      (hIJ := hfr.1) (hR := hfr.2.1) (hcore := hfr.2.2.1)
      (ht₀ := hfr.2.2.2.1) (hl₀ := hfr.2.2.2.2.1) (hψ := hfr.2.2.2.2.2)
      (d₁ := [0, 2]) (hd₁ := hd₁) (k₁ := (0 : Fin 1)) (hk₁ := hk₁)
      (hI₁ := hI₁') (hI₂ := hI₂)
      (β := β) (hβu := hβu) (hβl := hβl) (θ := (sg Fld f : Fld →+* Fld))
      (P₁ := 1) (P₂ := 1) (pol₁ := false) (pol₂ := false)
      (hXu₁ := hXu₁) (hXl₁ := hXl₁) (hXu₂ := hXu₂) (hXl₂ := hXl₂)
  obtain ⟨ψ, hψeq, hψcore, hψinv⟩ :=
    exists_psiRes (hct := hct) (F := F) (hext := hext) (hw₀ := hw₀) (hsq := hsq)
      (hpanel := hpanel) (J := insert (L₂.e 0) (Set.range L₁.e)) (a := a)
  let S : Set ↥(residue (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e)) a) :=
    {x | (x : K ⧸ borel D H) ∈
      Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
        (insert (L₂.e 0) (Set.range L₁.e)) a}
  have hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).1 ∈ refSet Fld 2 [0, 2] := fun c => hcoreΘ c
  have hψS : ∀ c ∈ S, ψ c ∈ S := fun c hc => hψcore c hc
  have hψψ : ∀ c ∈ S, ψ (ψ c) = c := fun c hc => hψinv c hc
  have hψ'' : ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) Fld, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL B₁) (stdFlag Fld 2),
        flagAct (SpecialLinearGroup.toGL B₂) (stdFlag Fld 2)) →
      Θ₀.Φ (ψ c) =
        (flagAct N₁ (flagAct (SpecialLinearGroup.toGL (kapMat (sg Fld f) false 1 B₂))
            (stdFlag Fld 2)),
          flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg Fld f) false 1 B₁))
            (stdFlag Fld 2))) := by
    intro B₁ B₂ c _ hΦ
    exact hψΘ B₁ B₂ c (ψ c) hΦ (hψeq c)
  obtain ⟨Θ, hΘS, hΘψ⟩ :=
    Res.exists_chart_exchA1A1
      ((buildingOver (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e))).restrict
        (residue (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e)) a))
      hK S ψ Θ₀ N₁ N₂ hS hψS hψψ 1 1 rfl rfl hψ''
  refine ⟨Θ, fun x => hΘS x, ?_⟩
  intro x x' hx hx'
  have hx'' : x' = ψ x := Subtype.ext (by rw [hx', ← hψeq x])
  rw [hx'']
  exact hΘψ x hx

include hext hw₀ hsq hpanel in
theorem exists_chart_exchA2A1_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) (L₁ : SLPath M 2) (L₂ : SLPath M 1)
    {J₁ J : Set (Fin D.rank)} (hJ₁ : Set.range L₁.e = J₁) (hJ : insert (L₂.e 0) J₁ = J)
    (hz : L₂.e 0 ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i (L₂.e 0) = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hI₁ : ∀ k : Fin 2, L₁.e k ∈ I ↔ k = 1) (hI₂ : L₂.e 0 ∈ I) (hπ₁ : π (L₁.e 1) = L₂.e 0)
    (hπ₂ : π (L₂.e 0) = L₁.e 1) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a)) ((flagSys Fld 2).prod (flagSys Fld 1)),
      ChartOf hct F J a Θ {x : FlagK Fld 3 × FlagK Fld 2 | x.1 ∈ refSet Fld 3 [0, 1, 3]}
        (psiA2A1 hK) := by
  subst hJ
  subst hJ₁
  have hd₁ : IsCut (2 + 1) [0, 1, 3] := PhanCode.isCut_cut (c := PhanCode.a2panel) trivial
  have hk₁ : cutTypes 2 [0, 1, 3] = ({1} : Set (Fin 2)) := plh_cutTypes_two_013
  have hI₁' : ∀ k : Fin 2, L₁.e k ∈ I ↔ k ∈ cutTypes 2 [0, 1, 3] := by
    intro k
    rw [hk₁]
    simpa only [Set.mem_singleton_iff] using hI₁ k
  have hπ₁' : weylAction D.isFiniteType v (Pi.single (F.op (L₁.e (1 : Fin 2))) 1) =
      Pi.single (L₂.e 0) 1 := by
    simpa only [hπ₁] using hπ (L₁.e (1 : Fin 2)) ((hI₁ (1 : Fin 2)).mpr rfl)
  have hπ₂' : weylAction D.isFiniteType v (Pi.single (F.op (L₂.e 0)) 1) =
      Pi.single (L₁.e (1 : Fin 2)) 1 := by
    simpa only [hπ₂] using hπ (L₂.e 0) hI₂
  let β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (2 + 1)) Fld :=
    WeakCT.blk Fld 1
  have hβu : ∀ c : Fld, β (tv Fld 0 1 c) =
      tv Fld (1 : Fin 2).castSucc (1 : Fin 2).succ c := fun c => blk_one_tv01' c
  have hβl : ∀ c : Fld, β (tv Fld 1 0 c) =
      tv Fld (1 : Fin 2).succ (1 : Fin 2).castSucc c := fun c => blk_one_tv10' c
  obtain ⟨hXu₁, hXl₁, hXu₂, hXl₂⟩ :=
    hX_of_swap (hct := hct) (F := F) (PC := PC) (L₁ := L₁) (L₂ := L₂)
      (v := v) (k₁ := (1 : Fin 2)) (hπ₁ := hπ₁') (hπ₂ := hπ₂') (β := β)
      (hβu := hβu) (hβl := hβl)
  obtain ⟨Θ₀, N₁, N₂, hStab₁, hcoreΘ, hψΘ⟩ :=
    Res.exists_seam_exch (hct := hct) (hext := hext) (F := F) (hw₀ := hw₀) (hsq := hsq)
      (L₁ := L₁) (L₂ := L₂) (J₁ := Set.range L₁.e) (z := L₂.e 0)
      (hJ₁ := rfl) (hz₂ := rfl) (hz := hz) (hcomm := hcomm)
      (hIJ := hfr.1) (hR := hfr.2.1) (hcore := hfr.2.2.1)
      (ht₀ := hfr.2.2.2.1) (hl₀ := hfr.2.2.2.2.1) (hψ := hfr.2.2.2.2.2)
      (d₁ := [0, 1, 3]) (hd₁ := hd₁) (k₁ := (1 : Fin 2)) (hk₁ := hk₁)
      (hI₁ := hI₁') (hI₂ := hI₂)
      (β := β) (hβu := hβu) (hβl := hβl) (θ := (sg Fld f : Fld →+* Fld))
      (P₁ := 1) (P₂ := 1) (pol₁ := false) (pol₂ := false)
      (hXu₁ := hXu₁) (hXl₁ := hXl₁) (hXu₂ := hXu₂) (hXl₂ := hXl₂)
  obtain ⟨ψ, hψeq, hψcore, hψinv⟩ :=
    exists_psiRes (hct := hct) (F := F) (hext := hext) (hw₀ := hw₀) (hsq := hsq)
      (hpanel := hpanel) (J := insert (L₂.e 0) (Set.range L₁.e)) (a := a)
  let S : Set ↥(residue (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e)) a) :=
    {x | (x : K ⧸ borel D H) ∈
      Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
        (insert (L₂.e 0) (Set.range L₁.e)) a}
  have hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).1 ∈ refSet Fld 3 [0, 1, 3] := fun c => hcoreΘ c
  have hψS : ∀ c ∈ S, ψ c ∈ S := fun c hc => hψcore c hc
  have hψψ : ∀ c ∈ S, ψ (ψ c) = c := fun c hc => hψinv c hc
  have hψ'' : ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) Fld, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag Fld 3),
        flagAct (SpecialLinearGroup.toGL B₂) (stdFlag Fld 2)) →
      Θ₀.Φ (ψ c) =
        (flagAct N₁ (flagAct
            (SpecialLinearGroup.toGL (β (kapMat (sg Fld f) false 1 B₂))) (stdFlag Fld 3)),
          flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg Fld f) false 1 B₁))
            (stdFlag Fld 2))) := by
    intro B₁ B₂ c _ hΦ
    exact hψΘ B₁ B₂ c (ψ c) hΦ (hψeq c)
  obtain ⟨Θ, hΘS, hΘψ⟩ :=
    Res.exists_chart_exchA2A1
      ((buildingOver (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e))).restrict
        (residue (cs) (stdδ hct) (insert (L₂.e 0) (Set.range L₁.e)) a))
      hK S ψ Θ₀ N₁ N₂ hStab₁ hS hψS hψψ β blk_one_matrix 1 1 rfl rfl hψ''
  refine ⟨Θ, fun x => hΘS x, ?_⟩
  intro x x' hx hx'
  have hx'' : x' = ψ x := Subtype.ext (by rw [hx', ← hψeq x])
  rw [hx'']
  exact hΘψ x hx

include hext hw₀ hsq hpanel in
theorem exists_chart_exch3_of_frame (hK : Nat.card Fld = (2 ^ f) ^ 2)
    (PC : M.PhiCompat F (sg Fld f : Fld →+* Fld)) {c₃ : PhanCode} (hc₃ : c₃.IsNode)
    (Lx Ly Lz : SLPath M 1) {J : Set (Fin D.rank)}
    (hJ : insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0}) = J)
    (hxy : Lx.e 0 ≠ Ly.e 0) (hxz : Lx.e 0 ≠ Lz.e 0) (hyz : Ly.e 0 ≠ Lz.e 0)
    (hmxy : coxeterMatrix D.isFiniteType (Lx.e 0) (Ly.e 0) = 2)
    (hmxz : coxeterMatrix D.isFiniteType (Lx.e 0) (Lz.e 0) = 2)
    (hmyz : coxeterMatrix D.isFiniteType (Ly.e 0) (Lz.e 0) = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hfr : IsFrame hct F J a g v I t₀ l₀) {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1)
    (hIx : Lx.e 0 ∈ I) (hIy : Ly.e 0 ∈ I) (hπx : π (Lx.e 0) = Ly.e 0) (hπy : π (Ly.e 0) = Lx.e 0)
    (hcorez : Lz.e 0 ∈ I ↔ c₃.coreN 0 = true)
    (hpermz : Lz.e 0 ∈ I → ∃ k' : Fin 1, k'.val = c₃.permN 0 ∧ Lz.e k' = π (Lz.e 0)) :
    ∃ Θ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
        (residue (cs) (stdδ hct) J a))
        (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)),
      ChartOf hct F J a Θ ((Set.univ : Set (FlagK Fld 2 × FlagK Fld 2)) ×ˢ refSet Fld 2 c₃.cut)
        (Prod.map (psiA1A1 hK) (flagPsi' Fld f hK 2 c₃.cut c₃.plist)) := by
  subst hJ
  let c := c₃
  rcases hc₃ with rfl | rfl
  all_goals
    have hf₃ : c.IsFlagCode := trivial
    have hcorez' : ∀ k : Fin c.rank, Lz.e k ∈ I ↔ c.coreN k = true := by
      intro k
      fin_cases k
      exact hcorez
    have hpermz' : ∀ k : Fin c.rank, Lz.e k ∈ I →
        ∃ k' : Fin c.rank, k'.val = c.permN k ∧ Lz.e k' = π (Lz.e k) := by
      intro k
      fin_cases k
      exact hpermz
    obtain ⟨hdz, hIz, hPu, hPl⟩ :=
      seam_hyps_of_match (hct := hct) (F := F) (PC := PC) hf₃ Lz hcorez' hpermz' hπ
    have hκz : NodeKap hct F Lz v c.cut (sg Fld f) (permSL c.blockPerm) c.polB :=
      fun k hk x => ⟨hPu k hk x, hPl k hk x⟩
    have hπx' : weylAction D.isFiniteType v (Pi.single (F.op (Lx.e (0 : Fin 1))) 1) =
        Pi.single (Ly.e 0) 1 := by
      simpa only [hπx] using hπ (Lx.e (0 : Fin 1)) hIx
    have hπy' : weylAction D.isFiniteType v (Pi.single (F.op (Ly.e 0)) 1) =
        Pi.single (Lx.e (0 : Fin 1)) 1 := by
      simpa only [hπy] using hπ (Ly.e 0) hIy
    let β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (1 + 1)) Fld :=
      MonoidHom.id (SpecialLinearGroup (Fin 2) Fld)
    have hβu : ∀ x : Fld, β (tv Fld 0 1 x) =
        tv Fld (0 : Fin 1).castSucc (0 : Fin 1).succ x := fun _ => rfl
    have hβl : ∀ x : Fld, β (tv Fld 1 0 x) =
        tv Fld (0 : Fin 1).succ (0 : Fin 1).castSucc x := fun _ => rfl
    obtain ⟨hXu₁, hXl₁, hXu₂, hXl₂⟩ :=
      hX_of_swap (hct := hct) (F := F) (PC := PC) (L₁ := Lx) (L₂ := Ly)
        (v := v) (k₁ := (0 : Fin 1)) (hπ₁ := hπx') (hπ₂ := hπy') (β := β)
        (hβu := hβu) (hβl := hβl)
    obtain ⟨Θ₀, Nx, Ny, Nz, hStabz, hcoreΘ, hψΘ⟩ :=
      Res.exists_seam_exch3 (hct := hct) (hext := hext) (F := F) (hw₀ := hw₀) (hsq := hsq)
        (Lx := Lx) (Ly := Ly) (Lz := Lz) (x := Lx.e 0) (y := Ly.e 0) (z := Lz.e 0)
        (hx := rfl) (hy := rfl) (hz := rfl) (hxy := hxy) (hxz := hxz) (hyz := hyz)
        (hmxy := hmxy) (hmxz := hmxz) (hmyz := hmyz) (hIJ := hfr.1) (hR := hfr.2.1)
        (hcore := hfr.2.2.1) (ht₀ := hfr.2.2.2.1) (hl₀ := hfr.2.2.2.2.1)
        (hψ := hfr.2.2.2.2.2) (hIx := hIx) (hIy := hIy) (dz := c.cut) (hdz := hdz)
        (hIz := hIz (⟨0, by simp [c, PhanCode.rank]⟩ : Fin c.rank)) (θ := (sg Fld f : Fld →+* Fld))
        (Px := 1) (Py := 1) (Pz := permSL c.blockPerm)
        (polx := false) (poly := false) (polz := c.polB)
        (hXu₁ := hXu₁) (hXl₁ := hXl₁) (hXu₂ := hXu₂) (hXl₂ := hXl₂) (hκz := hκz)
    obtain ⟨ψ, hψeq, hψcore, hψinv⟩ :=
      exists_psiRes (hct := hct) (F := F) (hext := hext) (hw₀ := hw₀) (hsq := hsq)
        (hpanel := hpanel) (J := insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0})) (a := a)
    let S : Set ↥(residue (cs) (stdδ hct)
        (insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0})) a) :=
      {x | (x : K ⧸ borel D H) ∈
        Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0})) a}
    have hS : ∀ x, x ∈ S ↔ (Θ₀.Φ x).2 ∈ refSet Fld 2 c.cut := fun x => hcoreΘ x
    have hψS : ∀ x ∈ S, ψ x ∈ S := fun x hx => hψcore x hx
    have hψψ : ∀ x ∈ S, ψ (ψ x) = x := fun x hx => hψinv x hx
    have hPz : ((permSL c.blockPerm : SpecialLinearGroup (Fin 2) Fld) :
        Matrix (Fin 2) (Fin 2) Fld) =
        if c.polB then (revBlocks Fld 2 c.cut : Matrix (Fin 2) (Fin 2) Fld) else 1 :=
      coe_permSL_blockPerm hf₃ (fun h => by
        have h' : c.rank = PhanCode.a3_22x.rank := congrArg PhanCode.rank h
        rw [show c.rank = 1 from rfl, show PhanCode.a3_22x.rank = 3 from rfl] at h'
        exact (by decide : (1 : ℕ) ≠ 3) h')
    have hψ'' : ∀ Bx By : SpecialLinearGroup (Fin 2) Fld,
        ∀ Az ∈ blockSL Fld 1 c.cut, ∀ x ∈ S,
        Θ₀.Φ x = ((flagAct (SpecialLinearGroup.toGL Bx) (stdFlag Fld 2),
          flagAct (SpecialLinearGroup.toGL By) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) →
        Θ₀.Φ (ψ x) =
          ((flagAct Nx (flagAct (SpecialLinearGroup.toGL (kapMat (sg Fld f) false 1 By))
              (stdFlag Fld 2)),
            flagAct Ny (flagAct (SpecialLinearGroup.toGL (kapMat (sg Fld f) false 1 Bx))
              (stdFlag Fld 2))),
            flagAct Nz (flagAct
              (SpecialLinearGroup.toGL (kapMat (sg Fld f) c.polB (permSL c.blockPerm) Az))
              (stdFlag Fld 2))) := by
      intro Bx By Az hAz x _ hΦ
      exact hψΘ Bx By Az hAz x (ψ x) hΦ (hψeq x)
    obtain ⟨Θ, hΘS, hΘψ⟩ :=
      Res.exists_chart_exch3
        ((buildingOver (cs) (stdδ hct)
            (insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0}))).restrict
          (residue (cs) (stdδ hct) (insert (Lz.e 0) (insert (Ly.e 0) {Lx.e 0})) a))
        hK hdz S ψ Θ₀ Nx Ny Nz hStabz hS hψS hψψ 1 1 rfl rfl c.polB
        (permSL c.blockPerm) hPz hψ'' c.plist (PhanCode.plist_spec hf₃)
    refine ⟨Θ, fun x => hΘS x, ?_⟩
    intro x x' hx hx'
    have hx'' : x' = ψ x := Subtype.ext (by rw [hx', ← hψeq x])
    rw [hx'']
    exact hΘψ x hx

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
