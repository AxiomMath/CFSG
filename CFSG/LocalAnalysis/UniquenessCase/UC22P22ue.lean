module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ub
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_isComponent_map_subtype {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal] {C : Subgroup ↥N}
    (hC : IsComponentOf C (⊤ : Subgroup ↥N)) : CFSG.IsComponent (C.map N.subtype) := by
  rw [CFSG.isComponent_iff_open]
  refine ⟨le_top, ?_, ?_⟩
  · have h1 : C.IsSubnormal := IsSubnormal.top_iff.1 hC.2.1
    have h2 : (C.map N.subtype).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_map_subtype h1 (Subgroup.Normal.isSubnormal inferInstance)
    exact IsSubnormal.top_iff.2 h2
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (C.equivMapOfInjective N.subtype N.subtype_injective).symm hC.2.2

theorem uc22p22u_calC_of_le {X M K : Subgroup G} (hK : K ∈ calC M) (hKX : K ≤ X) (hXM : X ≤ M) :
    K ∈ calC X := by
  have h := hK.1.inf X
  rw [inf_eq_left.2 hKX, inf_eq_right.2 hXM] at h
  exact ⟨h, hK.2⟩

theorem uc22p22u_outAbelian_thin (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hthin : F08.Thin8 L) :
    ∀ σ τ : MulAut ↥(barImage D.M L), ∃ y : ↥(barImage D.M L), σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  have hK : CFSG.IsKGroup (Bar2 L) := s13_isKGroup_bar D (s13_le_of_mem_calC hL)
  have hsimple : IsSimpleGroup (Bar2 L) := (s13_list_bar hThin D hL hthin).1
  have hnonab : ∃ x y : Bar2 L, x * y ≠ y * x := s13_nonabelian_bar hL
  have hsyl : ∀ P : Sylow 3 (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L)) := by
    intro P
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine s13_Bridge13_isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) P.isPGroup' ?_
    calc CFSG.pRank 3 ↥(P : Subgroup (Bar2 L))
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(P : Subgroup (Bar2 L))) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top 3 _
      _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
          CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (Subgroup.subtype _)
            (Subgroup.subtype_injective _)
      _ = CFSG.pRank 3 (Bar2 L) := (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Bar2 L)).symm
      _ ≤ 1 := s13_pRank_bar_le_one hthin Nat.prime_three (by norm_num)
  have hout : ∀ σ τ : MulAut (Bar2 L), ∃ y : Bar2 L, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
    intro σ τ
    obtain ⟨y, hy⟩ := hCyc (Bar2 L) hK hsimple hnonab hsyl σ τ
    exact ⟨y, hy.symm⟩
  obtain ⟨e⟩ := s13_bar_equiv hL
  exact s13_outAbelian_of_mulEquiv e hout

@[expose] def C118 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ ≤
    centralizer ((((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))).map
        (barImage D.M (F11.CTilde D.M V₀ V)).subtype) ⊔
      ((CFSG.layer ↥(barImage D.M (F11.CTilde D.M V₀ V))).map
        (barImage D.M (F11.CTilde D.M V₀ V)).subtype) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ⊔
      (CFSG.layer ↥(barImage D.M (F11.CTilde D.M V₀ V))).map (barImage D.M (F11.CTilde D.M V₀ V)).subtype

@[expose] def R118W (D : Data G) : Prop := ∀ V : Subgroup G, F11.Hyp11 D ⊥ V → C118 D ⊥ V

theorem uc22p22u_r118W (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G) (h116 : R116W D)
    (h117 : R117W D) : R118W D := by
  intro V hV
  obtain ⟨hW, -⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have h116V := (h116 V hV).2
  have h117V := h117 V hV
  unfold C117 at h117V
  unfold C118
  generalize hX : F11.CTilde D.M ⊥ V = X at hVc h116V h117V ⊢
  have hXM : X ≤ D.M := by rw [hVc]; exact inf_le_left
  have hO : pCoreOf 2 D.M ≤ X := by
    rw [hVc]
    exact le_inf (uc22p21c_pCoreOf_le D.M) (uc22p22u_pCore_le_cent hW)
  have hn : D.M ≤ normalizer (X : Set G) := by
    rw [hVc]
    exact uc22p22u_normalizes_cent hW.1.1.2.2.1
  haveI hNn : (barImage D.M X).Normal := uc22p22u_barImage_normal hn
  refine uc22p22u_sub_le_cent_layer (barImage D.M X) _ h116V ?_
  intro C hC y hy
  obtain ⟨K, hK, hKbar⟩ := uc22p21c_exists_calC_of_component D.M (uc22p22u_isComponent_map_subtype _ hC)
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hbarle : barImage D.M K ≤ barImage D.M X := hKbar ▸ Subgroup.map_subtype_le C
  have hKX : K ≤ X := by
    intro k hk
    refine uc22p22u_barPreimage_le hO hbarle (uc22p21c_mem_barPreimage.2 ⟨hKM hk, ?_⟩)
    exact uc22p21c_mem_barImage.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩
  obtain ⟨hMK, hthin⟩ := h117V K (uc22p22u_calC_of_le hK hKX hXM)
  haveI hKn : (barImage D.M K).Normal := uc22p22u_barImage_normal hMK
  obtain ⟨c, hcK, hc⟩ := uc22p22u_acts_inner (barImage D.M K) ⊤
    (le_of_eq (Subgroup.normalizer_eq_top_iff.2 hKn).symm)
    (uc22p22u_outAbelian_thin hThin hCyc D hK hthin) y hy
  rw [hKbar] at hcK
  obtain ⟨c', hc', rfl⟩ := hcK
  exact ⟨c', hc', fun x hx => hc x (hKbar ▸ ⟨x, hx, rfl⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
