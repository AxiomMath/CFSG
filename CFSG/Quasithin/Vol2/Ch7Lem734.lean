module

public import CFSG.Quasithin.Vol2.Ch7Lem755
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuV_inf_omegaOneCenter_ne_bot (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    fsuV T I ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have : Group.IsNilpotent T := hT2.isNilpotent
  have hVT := fsuV_le_T hfsu hV hN
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hnormal : ((fsuV T I).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTN
  have hne : (fsuV T I).subgroupOf T ≠ ⊥ := by
    intro h
    apply fsuV_ne_bot hfsu
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyV : (y : G) ∈ fsuV T I := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hyZ : (y : G) ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨y.2, hyC⟩, hV.2 _ hyV⟩
  intro h
  have hmem : (y : G) ∈ fsuV T I ⊓ quasithinOmegaOneCenter T := ⟨hyV, hyZ⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

omit [Finite G] in
theorem inf_eq_inf_normalizer_of_center {V M H : Subgroup G} (hTI : IsTISetUnder V M)
    (hNM : Subgroup.normalizer (V : Set G) ≤ M) (hZV : V ⊓ quasithinOmegaOneCenter T ≠ ⊥)
    (hZH : quasithinOmegaOneCenter T ≤ centerOf H) :
    H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) := by
  refine le_antisymm (fun h hh => ⟨hh.1, ?_⟩) (inf_le_inf_left _ hNM)
  refine mem_normalizer_of_ti hTI inf_le_left hZV hh.2 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' := (hZH hu.2).2
  exact (Subgroup.mem_centralizer_iff.mp hu' h hh.1).symm

theorem hypE336_of_hypE61 {V M : Subgroup G} (hE : E6.HypE61 T M V)
    (hloc : ∀ H : Subgroup G, IsHStar T M H → 1 < E1.nParam H →
      H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) ∧
        H ⊓ M ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (H ⊓ M)) :
    HypE336 T V M :=
  ⟨hE.hyp322, hE.qtke, hE.isUniqueM_normalizer_Q, hloc⟩

theorem wParam_le_nPrime_of_E339 (h339 : ASInputs.AS_E_3_39) (h331 : Stmt3_3_1)
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hE : HypE336 T (fsuV T I) (fsuM T L))
    (hr : (nPrime (autI hV ⊤) : ℕ∞) < rParam (fsuV T I)) :
    (∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        wParam T (fsuV T I) ≤ E1.nParam H ∧ E1.nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞)) ∧
      wParam T (fsuV T I) ≤ (nPrime (autI hV ⊤) : ℕ∞) := by
  have hall : ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
      wParam T (fsuV T I) ≤ E1.nParam H ∧ E1.nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞) :=
    fun H hH => (h339 G T (fsuV T I) (fsuM T L) hV (fsuV_ne_bot hyp.fsu) hE hr H hH).1
  obtain ⟨H, hH⟩ := ((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow).2 L hyp.fsu.maximal hyp.fsu.quasisimple).2.2.1
  exact ⟨hall, ((hall H hH).1).trans (hall H hH).2⟩

omit [Finite G] in
theorem nPrime_lt_sParam {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hr : (nPrime (autI hV ⊤) : ℕ∞) < rParam V) (hm : nPrime (autI hV ⊤) < mParam (autI hV ⊤)) :
    nPrime (autI hV ⊤) < sParam hV := by
  unfold sParam
  have hlt : (nPrime (autI hV ⊤) : ℕ∞) < min (rParam V) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) :=
    lt_min hr (by exact_mod_cast hm)
  have hne : min (rParam V) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (min_le_right _ _)
  rw [← ENat.coe_toNat hne] at hlt
  exact_mod_cast hlt

end CFSG.Quasithin.H13
