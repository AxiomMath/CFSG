module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Six
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
public import CFSG.LocalAnalysis.StandardType.GGInvolutionRankOneRepresentative
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

private theorem p9uLS_fixes_of_le_centralizer {Bs X : Subgroup G} {y : G} (hy : y ∈ Bs)
    (hXy : X ≤ Subgroup.centralizer ({y} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer X Bs) : y ∈ ggHyperplane Bs φ := by
  obtain ⟨g, hgX, -, hact⟩ := mem_ggAutomizer_iff.mp hφ
  have hgy : g * y * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hXy hgX)
    rw [h]; group
  refine ⟨⟨y, hy⟩, ?_, rfl⟩
  change φ ⟨y, hy⟩ = ⟨y, hy⟩
  apply Subtype.ext
  rw [hact]
  exact hgy

theorem qtwoDL1_seed (ha₀ : GGLNoncyclicInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrefl : GGIsReflection p r)
    (h6 : Nat.card ↥(ggRankOneIn L Bs r) = 6) :
    ggRankOne Bs r = ggRankOneIn L Bs r := by
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
  have hr2 : r * r = 1 := by simpa [pow_two] using hrefl.1
  have hxBs : x ∈ Bs := SecFiveL1Odd.le_bstar hcfg hcfg.1.1.2.2.1.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hxH : x ∈ ggHyperplane Bs r := p9uLS_fixes_of_le_centralizer hxBs hLx hrA
  have hMx : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by simpa using hxH)
  have hMN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar hcfg.1.1.1.2.2.2.2.2.2.1
      (ha₀ G p B x L hcfg.1.1.1) (hMx hg)
  have hHBs : ggHyperplane Bs r ≤ Bs := Subgroup.map_subtype_le _
  have hBsC : Bs ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨h, hHBs hh⟩ ⟨b, hb⟩)
  have hCN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.normalizer (ggRankOneIn L Bs r : Set G) := by
    intro g hg
    apply ggMem_normalizer_oTwoPrime
    have hgL : g ∈ Subgroup.normalizer (L : Set G) := hMN hg
    have hgC : g ∈ Subgroup.normalizer
        (Subgroup.centralizer (ggHyperplane Bs r : Set G) : Set G) :=
      Subgroup.le_normalizer hg
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := L)
      (K := Subgroup.centralizer (ggHyperplane Bs r : Set G)) ⟨hgL, hgC⟩
  have hSC : ggRankOneIn L Bs r ≤
      Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    (ggOTwoPrime_le (L ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))).trans inf_le_right
  obtain ⟨n, hnS, -, -, hnact⟩ :=
    exists_two_representative_mem_ggRankOneIn hrA (by simpa [pow_two] using hrefl.1)
  have hBsS : Bs ≤ Subgroup.normalizer (ggRankOneIn L Bs r : Set G) := hBsC.trans hCN
  have hBsHS : Bs ≤ ggHyperplane Bs r ⊔ ggRankOneIn L Bs r :=
    ggBs_le_hyperplane_sup_of_rep hpp hp2 hBs hr2 hBsS hnS hnact
  have hker : Subgroup.centralizer (ggRankOneIn L Bs r : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer (Bs : Set G) := by
    rw [SecFiveL1Solv.commonKernel hHBs hBsHS]
    exact inf_le_right
  have hodd' : Odd (Nat.card ↥(Subgroup.centralizer (ggHyperplane Bs r : Set G) ⊓
      Subgroup.centralizer (ggRankOneIn L Bs r : Set G))) := by
    rw [inf_comm]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker)
  have hS2 : ggRankOneIn L Bs r ≤ ggOTwoPrime (ggRankOneIn L Bs r) :=
    qtwoDL1_le_ggOTwoPrime_ggOTwoPrime _
  have hconc : ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r : Set G)) =
      ggRankOneIn L Bs r :=
    qtwoDL1_ggOTwoPrime_eq_of_card_six hSC hCN h6 hS2 hodd'
  show ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r : Set G)) =
    ggRankOneIn L Bs r
  exact hconc

end CFSG.StandardType.QTwo

end
