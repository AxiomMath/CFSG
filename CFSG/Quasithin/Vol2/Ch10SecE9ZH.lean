module

public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10SecC8X
public import CFSG.Quasithin.Vol2.Ch10SecE9ZF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

abbrev ZQ (T L I : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))

omit [Finite G] in
theorem isElemAbelian_ZQ (T L I : Subgroup G) : IsElemAbelian 2 (ZQ T L I) :=
  SecC.isElemAbelian_omegaOneCenterOf' _

theorem le_normalizer_ZQ (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) :
    fsuL0 T L ⊔ T ≤ Subgroup.normalizer (ZQ T L I : Set G) :=
  (SecA.le_normalizer_inf_centralizer h37 h38 hyp).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem fsuVM_le_ZQ (hyp : Hyp10 G T L I) : fsuVM T L I ≤ ZQ T L I :=
  SecC.fsuVM_le_omegaOneCenterOf hyp

theorem omegaOne_T1_le_ZQ (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : quasithinOmegaOneCenter (T1 T L) ≤ ZQ T L I := by
  have hVT1 : fsuVM T L I ≤ T1 T L := fun v hv =>
    SecA.inf_centralizer_le_T1 h37 h38 hyp (SecC.fsuVM_le_Q hyp hv)
  have hQT1 : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ T1 T L :=
    SecA.inf_centralizer_le_T1 h37 h38 hyp
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT1, hzc⟩, hz2⟩
  have hzc' : z ∈ Subgroup.centralizer (T1 T L : Set G) := hzc
  have h1 : z ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => Subgroup.mem_centralizer_iff.mp hzc' v (hVT1 hv)
  have h2 : z ∈ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => Subgroup.mem_centralizer_iff.mp hzc' q (hQT1 hq)
  exact Subgroup.subset_closure ⟨⟨⟨hzT1.1, h1⟩, h2⟩, hz2⟩

theorem mem_centralizer_ZQ_iff (h3228 : TmpL6_3_2_2_eight)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) {x : G} (hx : x ∈ fsuL0 T L ⊔ T) :
    x ∈ Subgroup.centralizer (ZQ T L I : Set G) ↔ x ∈ pCoreOf 2 (fsuL0 T L ⊔ T) := by
  constructor
  · intro h
    refine SecA.inf_centralizer_le_pCoreOf_sup h37 h38 hyp ⟨hx, ?_⟩
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (fsuVM_le_ZQ hyp)) h
  · intro h
    rw [← inf_centralizer_eq_pCoreOf_of_case3 h3228 hyp h3] at h
    exact SecC.Q_le_centralizer_omegaOne T (fsuVM T L I) h

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
