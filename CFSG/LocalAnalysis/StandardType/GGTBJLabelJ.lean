module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGTCJDatum
import CFSG.LocalAnalysis.StandardType.GGTCJCoverGen
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
import CFSG.LocalAnalysis.StandardType.GGTCJDivOrth
import CFSG.LocalAnalysis.StandardType.GGTCJDivUni
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCSymp
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FamLin FamUni FamOrth)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tbjLabelJ_J_le_K {G : Type} [Group G] [Finite G] (hI3 : GGNbrSubcomponentInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    J ≤ K :=
  hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb

private theorem tbjLabelJ_isComponentOf {G : Type} [Group G] [Finite G]
    {p : ℕ} {B : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hnb : GGNbr p B x D J y K) (hJK : J ≤ K) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
  isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnb hJK

private theorem tbjLabelJ_marking_actor
    {G : Type} [Group G] {p : ℕ} {Bs K : Subgroup G} {x : G}
    {R : Type} [Group R] (I : Set (MulAut R))
    (θ : (↥K ⧸ Subgroup.center ↥K) ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hind : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hx : x ∈ Bs) (hxp : x ^ p = 1) :
    let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hN hx⟩
    let ψ : ↥K →* R :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    e ^ p = 1 ∧ Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center ↥K ∧
      ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (e l) := by
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hN hx⟩
  let ψ : ↥K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hep : e ^ p = 1 := by
    dsimp only [e]
    rw [← map_pow]
    have h1 : (⟨x, hN hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [h1, map_one]
  have hψsurj : Function.Surjective ψ := by
    dsimp only [ψ]
    exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥K := by
    intro l hl
    have h0 : ψ l = 1 := hl
    dsimp only [ψ] at h0
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hx)
  refine ⟨hep, hψsurj, hψker, φ, hφI, ?_⟩
  intro l
  have hrel : ((e l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹ := by
    dsimp only [e]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have h := hφ l (e l) hrel
  exact h

theorem ggNbrK_label_J_of_tcj_onLabel_of_le (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hK : GGInnerDiagOnLabel S p Bs K) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧
      GGHasLabel lab (K ⧸ Subgroup.center K) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hKperf : commutator ↥K = ⊤ := hK.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hTCJ p hp hp2 lab hlab) hK
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨hS, hBN, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBN hxBs
  have hx1 : x ^ p = 1 := hBel.2 x hx
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  let ψ : ↥K →* R := (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hactor := tbjLabelJ_marking_actor I θ hBN hind hxBs hx1
  dsimp only at hactor
  obtain ⟨hep, hψsurj, hψker, hφe⟩ := hactor
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    tbjLabelJ_isComponentOf hSS hDJ hnb hJK
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥K ψ hψsurj hψker hKperf _ hep hφe (J.subgroupOf K) hJcomp
  refine ⟨lab, labJ, hlab, hS, hhas, hlabJ, hdvd, ?_⟩
  exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
    (Subgroup.map_center_eq _)) hhasJ

theorem ggNbrK_label_J_of_tcj_onLabel (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : GGInnerDiagOnLabel S p Bs K) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧
      GGHasLabel lab (K ⧸ Subgroup.center K) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) :=
  ggNbrK_label_J_of_tcj_onLabel_of_le hTCJ hcfg hnb (tbjLabelJ_J_le_K hI3 hcfg hnb) hK

@[expose] def GGTBJLeftOnLab (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel S p Bs L → GGResXDatum p Bs L →
    ∀ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenInLambda2 labJ → S p lab →
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      lab.n ∣ labJ.n →
        GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨ GGResRowAt ggRowNonLevi p J L

@[expose] def GGTBJNbrOnLab (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel S p Bs K → GGResXDatum p Bs K →
    ∀ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenInLambda2 labJ → S p lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      lab.n ∣ labJ.n →
        GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨ GGResRowAt ggRowNonLevi p J K

theorem GGTBJLeftOnLab.toLeftOn (hTCJ : GGTCJKnown) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBJLeftOnLab S) : GGTBJLeftOn S := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX
  obtain ⟨lab, labJ, hΛ, hS, hhas, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hH.1 hL hH.2.2.2.2.1
  exact h G p B Bs x L D J y K hH hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd

theorem GGTBJNbrOnLab.toNbrOn (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    {S : ℕ → LargeEvenLabel → Prop} (h : GGTBJNbrOnLab S) : GGTBJNbrOn S := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX
  obtain ⟨lab, labJ, hΛ, hS, hhas, hΛJ, hdvd, hhasJ⟩ :=
    ggNbrK_label_J_of_tcj_onLabel hTCJ hI3 hH.1 hH.2.2.2.2.1 hK
  exact h G p B Bs x L D J y K hH hK hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd

end CFSG.StandardType

end
