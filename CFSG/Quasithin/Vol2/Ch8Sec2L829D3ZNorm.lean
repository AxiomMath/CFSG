module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22F
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327TI
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G]

theorem fsuV_le_reducedAggregate_d3z [Finite G] {T L I : Subgroup G} (hfsu : FSU G T L I) :
    fsuV T I ≤ reducedAggregate (L ⊔ T) := by
  have hN := (CFSG.Quasithin.Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)).2.2.2
  refine conjClosure_le fun t ht z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) z).mp
    (hfsu.irrPlus.1 hz)

theorem isElemAbelian_fsuV_d3z [Finite G] {T L I : Subgroup G} (hfsu : FSU G T L I) :
    IsElemAbelian 2 (fsuV T I) := by
  obtain ⟨hsq, hcomm, -⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)
  have hV := fsuV_le_reducedAggregate_d3z hfsu
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hV a.2) _ (hV b.2))⟩⟩, fun x hx => hsq x (hV hx)⟩

theorem fsuL0_sup_le_normalizer_fsuV_d3z [Finite G] {T L I : Subgroup G} (hfsu : FSU G T L I) :
    fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  refine sup_le ?_ (CFSG.Quasithin.le_normalizer_conjClosure I T)
  exact CFSG.Quasithin.Vol2.Ch11.SecA.le_normalizer_conjClosure_of_le' hfsu.irrPlus.2.2.1
    (CFSG.Quasithin.le_normalizer_conjClosure L T)

theorem fsuV_inf_omegaOneCenter_ne_bot_d3z [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) : fsuV T I ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have hV := isElemAbelian_fsuV_d3z hfsu
  have hN := fsuL0_sup_le_normalizer_fsuV_d3z hfsu
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

theorem mem_normalizer_of_ti_d3z {V M U : Subgroup G} (hTI : IsTISetUnder V M)
    (hUV : U ≤ V) (hU : U ≠ ⊥) {g : G} (hgM : g ∈ M)
    (hgU : g ∈ Subgroup.centralizer (U : Set G)) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  by_contra hgN
  apply hU
  rw [eq_bot_iff, ← hTI g hgM hgN]
  intro u hu
  refine Subgroup.mem_inf.2 ⟨hUV hu, ?_⟩
  have hcomm : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hgU u hu).symm
  refine ⟨u, hUV hu, ?_⟩
  change g⁻¹ * u * g⁻¹⁻¹ = u
  rw [inv_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem zNormVStmt_m22f_holds (h325 : Stmt3_2_5) (h711n : Stmt7_1_1_normal) :
    ZNormVStmt_m22f := by
  intro G _ _ T L I hyp _ _ hc _ hrowM _ x hx
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    h711n G T L I hyp hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrowM))))))
  have hTI : IsTISetUnder (fsuV T I) (fsuM T L) :=
    CFSG.Quasithin.H13.TI325.of_stmt3_2_5_of_le_normalizer h325 hyp.fsu hTL
  have hne := fsuV_inf_omegaOneCenter_ne_bot_d3z hyp.fsu
  have hgU : x ∈ Subgroup.centralizer
      ((fsuV T I ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right) hx.2
  exact mem_normalizer_of_ti_d3z hTI inf_le_left hne hx.1 hgU

end CFSG.Quasithin.H13
