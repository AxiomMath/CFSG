module

public import CFSG.Quasithin.Vol2.Ch10SecATorusA
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_ne_one_mem_centralizer {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K ≤ P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hK : K ≠ ⊥) :
    ∃ k ∈ K, k ≠ 1 ∧ k ∈ Subgroup.centralizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have : (K.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mpr hPK
  have hKne : K.subgroupOf P ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have h1 : (⟨k, hKP hk⟩ : ↥P) ∈ K.subgroupOf P := Subgroup.mem_subgroupOf.mpr hk
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨⟨z, hzK, hzZ⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hKne)
  refine ⟨z, Subgroup.mem_subgroupOf.mp hzK, fun h => hz1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨r, hr⟩)

theorem exists_mem_centralizer_of_fsuCVM_eq_bot (hyp : Ch10.Hyp10 G T L I)
    (hC0 : fsuCVM T L I = ⊥) :
    ∃ v ∈ fsuUL T L I, v ∉ fsuCVM T L I ∧
      v ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))
      Subgroup.le_normalizer
  have hP : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) :=
    hyp.fsu.sylow.1.to_le inf_le_left
  have hUP : fsuUL T L I ≤ T ⊓ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_inf ((fsuUL_le_fsuVM T L I).trans (fsuVM_le_T hyp)) Subgroup.le_normalizer
  obtain ⟨v, hvU, hv1, hvC⟩ :=
    exists_ne_one_mem_centralizer hP hUP inf_le_right (commutator_fsuVM_ne_bot hyp.fsu)
  refine ⟨v, hvU, by rw [hC0, Subgroup.mem_bot]; exact hv1, ?_⟩
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_inf_left T hLU)) hvC

theorem isSylowTwoOf_autOn_inf (hyp : Ch10.Hyp10 G T L I) :
    IsSylowTwoOf (autOn (T ⊓ L) (fsuUL T L I)) (autOn L (fsuUL T L I)) := by
  have hloc := hyp.fsu.maximal.1
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))
      Subgroup.le_normalizer
  have hsylTL := isSylowTwoOf_inf hloc
  refine ⟨A4.autOn_mono inf_le_right, isPGroup_autOn hsylTL.2.1, ?_⟩
  rw [autOn_subgroupOf_eq_map (W := fsuUL T L I) (inf_le_right : T ⊓ L ≤ L) hLU]
  exact fun h => hsylTL.2.2 (h.trans (Subgroup.index_map_dvd _ (autOnHomOf_surjective hLU)))

theorem conjAct_mem_autOn_of_mem_fsuL0 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyU : y ∈ Subgroup.normalizer (fsuUL T L I : Set G)) :
    conjAct (fsuUL T L I) ⟨y, hyU⟩ ∈ autOn L (fsuUL T L I) := by
  obtain ⟨l, hlL, hl⟩ := exists_mem_autOn_of_mem_fsuL0 h37 h38 hyp hyL0
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))
      Subgroup.le_normalizer
  have hφl : conjAct (fsuUL T L I) ⟨y, hyU⟩ = conjAct (fsuUL T L I) ⟨l, hLU hlL⟩ := by
    ext u
    rw [coe_conjAct_apply', coe_conjAct_apply']
    exact hl u u.2
  exact mem_autOn_iff'.mpr ⟨_, hlL, hφl.symm⟩

omit [Finite G] in
theorem conjAct_mem_normalizer_autOn {K W : Subgroup G} {y : G}
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    conjAct W ⟨y, hyW⟩ ∈ Subgroup.normalizer (autOn K W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn _ hyK

omit [Finite G] in
theorem odd_orderOf_conjAct {W : Subgroup G} {y : G} (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (hyodd : Odd (orderOf y)) : Odd (orderOf (conjAct W ⟨y, hyW⟩)) := by
  refine Odd.of_dvd_nat hyodd ((orderOf_map_dvd (conjAct W) _).trans ?_)
  rw [← Subgroup.orderOf_coe]

end CFSG.Quasithin.Vol2.Ch10.SecA
