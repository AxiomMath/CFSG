module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineDecomp
import CFSG.GroupTheory.ThompsonOffender
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace InS3

private theorem pRank_eq_pRank_group (X : Subgroup G) :
    CFSG.Open.pRank 2 X = CFSG.pRank 2 ↥X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem le_thompsonJ_of_max {X A : Subgroup G} (hAX : A ≤ X)
    (hAel : IsElemAbelian 2 A) (hAcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 X) :
    A ≤ InS3.thompsonJ X := by
  have hcardX : Nat.card (A.subgroupOf X) = 2 ^ CFSG.pRank 2 ↥X := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hAcard,
      pRank_eq_pRank_group]
  have hAelX : CFSG.IsElementaryAbelian 2 (A.subgroupOf X) := by
    haveI : CFSG.IsElementaryAbelian 2 A := hAel.isElementaryAbelian
    exact CFSG.IsElementaryAbelian.subgroupOf (p := 2) hAX
  have hle : A.subgroupOf X ≤ CFSG.elemThompson ↥X 2 :=
    CFSG.Quasithin.BlueprintB2.le_elemThompson ⟨hAelX, hcardX⟩
  have hmap := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hAX] at hmap

theorem thompsonJ_le_of_forall_max {X Y : Subgroup G}
    (h : ∀ A : Subgroup G, A ≤ X → IsElemAbelian 2 A →
      Nat.card A = 2 ^ CFSG.Open.pRank 2 X → A ≤ Y) :
    InS3.thompsonJ X ≤ Y := by
  have hmain : CFSG.elemThompson ↥X 2 ≤ Y.comap X.subtype := by
    refine sSup_le fun B hB => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    exact h (B.map X.subtype) (Subgroup.map_subtype_le B)
      ((CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB.1).map X.subtype)
      (by rw [Subgroup.card_map_of_injective X.subtype_injective, hB.2,
        pRank_eq_pRank_group]) ⟨x, hx, rfl⟩
  have h2 : (CFSG.elemThompson ↥X 2).map X.subtype ≤ Y :=
    Subgroup.map_le_iff_le_comap.mpr hmain
  simpa [InS3.thompsonJ, CFSG.inSubgroup] using h2

theorem thompsonJ_mono_of_pRank_eq {X T : Subgroup G} (hXT : X ≤ T)
    (hrank : CFSG.Open.pRank 2 X = CFSG.Open.pRank 2 T) :
    InS3.thompsonJ X ≤ InS3.thompsonJ T :=
  thompsonJ_le_of_forall_max fun A hAX hAel hAcard =>
    le_thompsonJ_of_max (hAX.trans hXT) hAel (hAcard := by rw [hAcard, hrank])

theorem omegaOneZJ_le_thompsonJ (X : Subgroup G) :
    InS3.omegaOneZJ X ≤ InS3.thompsonJ X := by
  have h := Subgroup.map_mono (f := X.subtype)
    (CFSG.elemThompsonCenterTorsion_le (H := ↥X) (p := 2) Nat.prime_two)
  simpa [InS3.omegaOneZJ, InS3.thompsonJ, CFSG.inSubgroup] using h

end InS3

namespace Ctx23L

private theorem pCoreOf_L_eq_cent (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 c.L = c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
  obtain ⟨hV, hLV, κ, -, -⟩ := exists_coordinates_V D Ch h4 h23 h1930 c
  exact pCoreOf_L_eq D Ch h4 h23 h1930 c hV hLV κ

private theorem sup_eq_sup_centTV (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.L ⊔ D.T = c.L ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) := by
  have hTsub : D.T ≤ c.L ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) := by
    intro t ht
    obtain ⟨l, hl, hcl⟩ := exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ht
    have hmemC : t * l⁻¹ ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) :=
      ⟨D.T.mul_mem ht (D.T.inv_mem hl.1), hcl⟩
    have ht' : t = (t * l⁻¹) * l := by group
    rw [ht']
    have h := Subgroup.mul_mem_sup hmemC hl.2
    rwa [sup_comm] at h
  exact le_antisymm (sup_le le_sup_left hTsub)
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))

private theorem exists_pCoreOf_sup_decomp (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {r : G} (hr : r ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    ∃ l : G, l ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ∧ l ∈ c.L ∧
      ∃ x : G, x ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) ∧ l * x = r := by
  classical
  let S : Subgroup G := c.L ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G))
  have hS_eq : c.L ⊔ D.T = S := sup_eq_sup_centTV D Ch h4 h23 h1930 c
  have hrS : r ∈ S := by
    rw [← hS_eq]
    exact uc22main1_pCoreOf_le _ hr
  have hnormS : S ≤ Subgroup.normalizer (c.L : Set G) :=
    sup_le (Subgroup.le_normalizer (H := c.L)) (inf_le_left.trans c.hL.1.1)
  haveI : (c.L.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : c.L ≤ S)).2 hnormS
  have hsup : c.L.subgroupOf S ⊔
      (D.T ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf S = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := c.L)
      (A' := D.T ⊓ Subgroup.centralizer (c.V : Set G)) (B := S)
      (le_sup_left : c.L ≤ S)
      (le_sup_right : D.T ⊓ Subgroup.centralizer (c.V : Set G) ≤ S)
    rw [Subgroup.subgroupOf_self] at h
    exact h.symm
  have hmem : (⟨r, hrS⟩ : ↥S) ∈ c.L.subgroupOf S ⊔
      (D.T ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf S := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨l, hl, x, hx, hlx⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hlL : (l : G) ∈ c.L := Subgroup.mem_subgroupOf.mp hl
  have hxin : (x : G) ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) :=
    Subgroup.mem_subgroupOf.mp hx
  have hlx' : (l : G) * (x : G) = r := congrArg Subtype.val hlx
  have hxR : (x : G) ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    centTVLeO2LT_of D Ch h4 h23 h1930 c hxin
  have hlR : (l : G) ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
    have h : (l : G) = r * (x : G)⁻¹ := by
      rw [← hlx']
      group
    rw [h]
    exact (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).mul_mem hr
      ((CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).inv_mem hxR)
  exact ⟨l, hlR, hlL, x, hxin, hlx'⟩

private theorem pCoreOf_L_of_mem_pCoreOf (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {l : G} (hlL : l ∈ c.L) (hlR : l ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    l ∈ CFSG.Open.pCoreOf 2 c.L := by
  refine uc22main1_le_pCoreOf (K := c.L)
    (P := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ⊓ c.L) inf_le_right ?_ ?_ ⟨hlR, hlL⟩
  · exact (uc22main1_isPGroup_pCoreOf (c.L ⊔ D.T)).to_le inf_le_left
  · intro k hk y hy
    exact ⟨uc22main1_conj_mem_pCoreOf_self ((le_sup_left : c.L ≤ c.L ⊔ D.T) hk) hy.1,
      c.L.mul_mem (c.L.mul_mem hk hy.2) (c.L.inv_mem hk)⟩

private theorem exists_pCoreOf_L_mul_centTV_of_mem (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {r : G} (hr : r ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    ∃ l : G, l ∈ CFSG.Open.pCoreOf 2 c.L ∧
      ∃ x : G, x ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) ∧ l * x = r := by
  obtain ⟨l, hlR, hlL, x, hxin, hlx⟩ :=
    exists_pCoreOf_sup_decomp D Ch h4 h23 h1930 c hr
  exact ⟨l, pCoreOf_L_of_mem_pCoreOf D Ch c hlL hlR, x, hxin, hlx⟩

private theorem cent_sup_le_pCoreOf (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
  uc22main1_le_pCoreOf (K := c.L ⊔ D.T)
    (P := (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)) inf_le_left
    (isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c)
    (conj_mem_sup_inf_centralizer_V D Ch c)

private theorem pCoreOf_le_cent_sup (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ Subgroup.centralizer (c.V : Set G) := by
  have hO2L := pCoreOf_L_eq_cent D Ch h4 h23 h1930 c
  intro r hr
  obtain ⟨l, hlO2L, x, hxin, hlx⟩ :=
    exists_pCoreOf_L_mul_centTV_of_mem D Ch h4 h23 h1930 c hr
  have hlC : l ∈ Subgroup.centralizer (c.V : Set G) := by
    rw [hO2L] at hlO2L
    exact hlO2L.2
  rw [← hlx]
  exact (Subgroup.centralizer (c.V : Set G)).mul_mem hlC hxin.2

theorem cent_sup_eq_pCoreOf (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) =
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
  le_antisymm (cent_sup_le_pCoreOf D Ch h4 h23 h1930 c)
    (le_inf (uc22main1_pCoreOf_le _) (pCoreOf_le_cent_sup D Ch h4 h23 h1930 c))

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
