module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Lab

variable {G : Type} [Group G]

@[expose] def GGInnerDiagOnLab (S : ℕ → LargeEvenLabel → Prop) (p : ℕ) (Bs L : Subgroup G) :
    Prop :=
  LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

variable {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}

theorem GGInnerDiagOnLab.innerDiagOn (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOn Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.2.1, hP.2.2.2⟩) h

theorem GGInnerDiagOnLab.mono (hST : ∀ p lab, S p lab → T p lab)
    (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOnLab T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ _ hP.1, hP.2⟩) h

theorem GGInnerDiagOnLab.elim_or (h : GGInnerDiagOnLab (fun p lab => S p lab ∨ T p lab) p Bs L) :
    GGInnerDiagOnLab S p Bs L ∨ GGInnerDiagOnLab T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact Or.inl ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact Or.inr ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

theorem ggInnerDiagOnLab_of_cover [Finite G]
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab) {B : Subgroup G}
    {x : G} (hT : GGThmIHyp p B x L) : GGInnerDiagOnLab S p B L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hT.2.2.2.2.2.2.2.1
  exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.1, hP⟩) hraw⟩

end Lab

@[expose] def GGBstarInnerDiagLInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p B L → GGInnerDiagOnLab S p Bs L

@[expose] def GGLTransvectionCenterInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L →
      ∀ φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs, GGIsTransvection p φ →
        ∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x

@[expose] def GGLNoInvariantLineInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L →
      ∀ E : Subgroup G, E ≤ Bs → x ∈ E → Nat.card E = p ^ 2 →
        ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G)

theorem ggLTransvectionCenterInputOn_of (h : GGLTransvectionCenterInput)
    (S : ℕ → LargeEvenLabel → Prop) : GGLTransvectionCenterInputOn S :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC hL.innerDiagOn

theorem ggLNoInvariantLineInputOn_of (h : GGLNoInvariantLineInput)
    (S : ℕ → LargeEvenLabel → Prop) : GGLNoInvariantLineInputOn S :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC hL.innerDiagOn

section Or

variable {S T : ℕ → LargeEvenLabel → Prop}

theorem GGBstarInnerDiagLInputOn.or (hS : GGBstarInnerDiagLInputOn S)
    (hT : GGBstarInnerDiagLInputOn T) :
    GGBstarInnerDiagLInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hC hL
  rcases hL.elim_or with h | h
  · exact (hS G p B Bs x L D J hC h).mono fun _ _ h' => Or.inl h'
  · exact (hT G p B Bs x L D J hC h).mono fun _ _ h' => Or.inr h'

theorem GGLTransvectionCenterInputOn.or (hS : GGLTransvectionCenterInputOn S)
    (hT : GGLTransvectionCenterInputOn T) :
    GGLTransvectionCenterInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hC hL
  rcases hL.elim_or with h | h
  · exact hS G p B Bs x L D J hC h
  · exact hT G p B Bs x L D J hC h

theorem GGLNoInvariantLineInputOn.or (hS : GGLNoInvariantLineInputOn S)
    (hT : GGLNoInvariantLineInputOn T) :
    GGLNoInvariantLineInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hC hL
  rcases hL.elim_or with h | h
  · exact hS G p B Bs x L D J hC h
  · exact hT G p B Bs x L D J hC h

end Or

section Consumers

variable {S : ℕ → LargeEvenLabel → Prop}

theorem ggNoTransvection_of_on {G : Type} [Group G] [Finite G] (hK : GGKantorReductionInput)
    (hcen : GGLTransvectionCenterInputOn S) (hline : GGLNoInvariantLineInputOn S) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hO : GGOpAutTrivial p Bs) (hL : GGInnerDiagOnLab S p Bs L) : GGNoTransvection p Bs := by
  intro φ hφ htv
  obtain ⟨hT, hBs, hstd⟩ := hC
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hBs.1 hT.2.2.2.2.2.2.1.2.1
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.2.1.1.is_comm.comm a b
  have hexp : ∀ a : ↥Bs, a ^ p = 1 := fun a => Subtype.ext (by simpa using hBs.2.1.2 a a.2)
  rcases exists_transvection_fix_or_plane_mul hK hp hp2 hcomm hexp Bs.normalizerMonoidHom.range
      (noNormalP_of_ggOpAutTrivial hO) ⟨φ, mem_ggInduced_top_iff.mp hφ, htv⟩ ⟨x, hxBs⟩ with
    ⟨ψ, ⟨g, rfl⟩, hψtv, hψx, b, hb⟩ | ⟨E, hEcard, hxE, hEinv⟩
  · have hgx : (g : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (g : G) * x * (g : G)⁻¹ = x := congrArg Subtype.val hψx
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * (g : G) := by group
        _ = x * (g : G) := by rw [h1]
    have hmem : Bs.normalizerMonoidHom g ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs :=
      mem_ggInduced_iff.mpr ⟨g, hgx, rfl⟩
    exact hb (mem_zpowers_mk_of_coe_mem hxBs
      (hcen G p B Bs x L D J ⟨hT, hBs, hstd⟩ hL _ hmem hψtv b))
  · refine hline G p B Bs x L D J ⟨hT, hBs, hstd⟩ hL (E.map Bs.subtype)
      (Subgroup.map_subtype_le E) ⟨⟨x, hxBs⟩, hxE, rfl⟩
      (by rw [Subgroup.card_map_of_injective Bs.subtype_injective, hEcard]) ?_
    refine CFSG.StandardType.le_normalizer_of_map_conj_le fun g hg => ?_
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have hge := hEinv (Bs.normalizerMonoidHom ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩ e he
    exact ⟨_, hge, rfl⟩

theorem ggCor42Input_of_on
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (hK : GGKantorReductionInput) (hLID : GGBstarInnerDiagLInputOn S)
    (hcen : GGLTransvectionCenterInputOn S) (hline : GGLNoInvariantLineInputOn S)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input := by
  intro G _ _ p B Bs x L D J hC hO
  have hL := hLID G p B Bs x L D J hC (ggInnerDiagOnLab_of_cover hcov hC.1)
  have hNT := ggNoTransvection_of_on hK hcen hline hC hO hL
  refine ⟨hL.innerDiagOn, fun y K hK' => ?_⟩
  have hN := hnorm G p B Bs x L D J hC y K hK'
  have h5 := (hC.1.2.2.2.2.2.2.2.2.2.1 y K (isNeighborOf_of_ggNbr hC.2.2 hK')).2
  have hM := hfield G p B Bs x L D J hC y K hK' hN _ (hgraph G p B Bs x L D J hC y K hK' hN _ h5)
  refine largeEvenMarking_mono ?_ hM
  rintro lab R _ I F θ ⟨⟨-, hall⟩, himp⟩
  refine ⟨hN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))⟩⟩
  by_contra hnot
  obtain ⟨φ, hφ, htv⟩ := himp hall ⟨b⁻¹, Bs.inv_mem hb, hnot⟩
  exact hNT φ hφ htv

theorem ggNoTransvectionInput_of_on
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (hK : GGKantorReductionInput) (hLID : GGBstarInnerDiagLInputOn S)
    (hcen : GGLTransvectionCenterInputOn S) (hline : GGLNoInvariantLineInputOn S) :
    GGNoTransvectionInput := by
  intro G _ _ p B Bs x L D J hC hO _
  exact ggNoTransvection_of_on hK hcen hline hC hO
    (hLID G p B Bs x L D J hC (ggInnerDiagOnLab_of_cover hcov hC.1))

end Consumers

end CFSG.StandardType
