module

public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAutChain
public import CFSG.LocalAnalysis.WeakClosure81.OuterInvolutionPairs
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Blueprint CFSG.Open
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (OutPCyc outPCyc_of_outPNice)
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Quasithin.Vol2.Ch11.SecU1.U3 (mem_of_isInnerAut)
open CFSG.RankThree.PartOne.OutStructure (Inn OutPNice outPNice_PSU_odd)
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem outer_pair_of_outPCyc {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (hOut : OutPCyc 2 ↥L) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  classical
  haveI : Finite ↥L := Subtype.finite
  have hcyc : ∀ B : Subgroup (MulAut ↥L), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner ↥L))) := by
    intro B hB
    obtain ⟨g, -, hle⟩ := hOut B hB
    have hle' : B.map (QuotientGroup.mk' (inner ↥L)) ≤
        Subgroup.zpowers (QuotientGroup.mk' (inner ↥L) g) := by
      calc
        B.map (QuotientGroup.mk' (inner ↥L))
            ≤ (Subgroup.zpowers g ⊔ Inn ↥L).map (QuotientGroup.mk' (inner ↥L)) :=
              Subgroup.map_mono hle
        _ = (Subgroup.zpowers g).map (QuotientGroup.mk' (inner ↥L)) ⊔
              (Inn ↥L).map (QuotientGroup.mk' (inner ↥L)) := by
              rw [Subgroup.map_sup]
        _ = Subgroup.zpowers (QuotientGroup.mk' (inner ↥L) g) ⊔ ⊥ := by
              rw [MonoidHom.map_zpowers, QuotientGroup.map_mk'_self]
        _ = Subgroup.zpowers (QuotientGroup.mk' (inner ↥L) g) := by
              rw [sup_bot_eq]
    exact Subgroup.isCyclic_of_le hle'
  exact outer_pair_of_isCyclic_out_image hC hcyc

theorem outer_pair_psu3_of_statedModel {L : Subgroup G}
    (hAS : SecE3.AlmostSimple L)
    {p f : ℕ} (hL : StatedClassicalModel ↥L .PSU 3 p f) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  letI : L.Normal := hAS.normal
  haveI : Finite ↥L := Subtype.finite
  have hdiag : ¬ 2 ∣ Nat.gcd 3 (p ^ f + 1) := by
    intro hd
    have h23 : 2 ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 (p ^ f + 1))
    norm_num at h23
  have hNice : OutPNice 2 ↥L := outPNice_PSU_odd Nat.prime_two hL hdiag
  have hOut : OutPCyc 2 ↥L := outPCyc_of_outPNice hNice
  exact outer_pair_of_outPCyc hAS.centralizer_eq hOut

theorem outer_pair_psu3 {L : Subgroup G}
    (hAS : SecE3.AlmostSimple L)
    {p f : ℕ} (hL : LieModel ↥L .PSU 3 p f) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L :=
  outer_pair_psu3_of_statedModel hAS
    (CFSG.GH74.Generic.stated_of_lieModel_PSU hL)

end CFSG.LocalAnalysis.WeakClosure81

end
