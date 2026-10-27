module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_center_ne_bot' {P U : Subgroup G} (hP : IsPGroup 2 P) (hUP : U ≤ P)
    (hUn : P ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (P ⊓ Subgroup.centralizer (P : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (U.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf P ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (P ⊓ Subgroup.centralizer (P : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem exists_mem_centralizer_ne_one {P U X : Subgroup G} (hP : IsPGroup 2 P) (hUP : U ≤ P)
    (hXP : X ≤ P) (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ u ∈ Subgroup.centralizer (X : Set G) := by
  have hQ : IsPGroup 2 ↥(X ⊔ U) := hP.to_le (sup_le hXP hUP)
  have hn : X ⊔ U ≤ Subgroup.normalizer (U : Set G) := sup_le hXU Subgroup.le_normalizer
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_center_ne_bot' hQ le_sup_right hn hU)
  refine ⟨u, hu.1, fun h => hu1 (Subtype.ext h), ?_⟩
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hu.2.2

omit [Finite G] in
theorem centralizer_conj_le_iff {M : Subgroup G} {m : G} (hm : m ∈ M) (u : G) :
    Subgroup.centralizer ({m * u * m⁻¹} : Set G) ≤ M ↔
      Subgroup.centralizer ({u} : Set G) ≤ M := by
  constructor
  · intro h x hx
    have hx' : m * x * m⁻¹ ∈ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc m * x * m⁻¹ * (m * u * m⁻¹) = m * (x * u) * m⁻¹ := by group
        _ = m * (u * x) * m⁻¹ := by rw [hx]
        _ = m * u * m⁻¹ * (m * x * m⁻¹) := by group
    have := M.mul_mem (M.mul_mem (M.inv_mem hm) (h hx')) hm
    have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rwa [e] at this
  · intro h x hx
    have hx' : m⁻¹ * x * m ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc m⁻¹ * x * m * u = m⁻¹ * (x * (m * u * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * u * m⁻¹) * x) * m := by rw [hx]
        _ = u * (m⁻¹ * x * m) := by group
    have := M.mul_mem (M.mul_mem hm (h hx')) (M.inv_mem hm)
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at this

theorem normalizer_le_of_thompsonJ (h3210 : TmpL6_3_2_10_eight) (hyp : Hyp10 G T L I)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hJS : thompsonJ T ≤ S) : Subgroup.normalizer (S : Set G) ≤ fsuM T L := by
  by_cases hiii : Sub326iii T L I
  · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hiii, rfl⟩) hJ S hS hJS).2
  · have hV : fsuV T I ≤ fsuVM T L I := le_conjClosure _ _
    exact (h3210 G T L I (fsuV T I) hyp.fsu (Or.inr ⟨hiii, rfl⟩)
      (hJ.trans (Subgroup.centralizer_le hV)) S hS hJS).2

theorem fsuCVM_eq_bot_of_thompsonJ (h3210 : TmpL6_3_2_10_nine) (hyp : Hyp10 G T L I)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) : fsuCVM T L I = ⊥ := by
  by_cases hiii : Sub326iii T L I
  · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hiii, rfl⟩) hJ).2
  · have hV : fsuV T I ≤ fsuVM T L I := le_conjClosure _ _
    have hZ := (h3210 G T L I (fsuV T I) hyp.fsu (Or.inr ⟨hiii, rfl⟩)
      (hJ.trans (Subgroup.centralizer_le hV))).1
    by_contra hne
    have hT : IsPGroup 2 T := hyp.fsu.sylow.1
    have hVT := SecA.fsuVM_le_T hyp
    have hTN : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) := fun s hs => by
      have h1 := SecA.le_normalizer_fsuVM T L I hs
      have h2 := SecA.le_normalizer_centralizer (V := fsuL0 T L) (SecA.le_fsuM T L) hs
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro x
      exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩,
        fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩
    obtain ⟨z, hz, hz1, hzc⟩ := exists_mem_centralizer_ne_one hT (inf_le_left.trans hVT) le_rfl
      hTN hne
    have hzZ : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :=
      ⟨Subgroup.subset_closure ⟨⟨hVT hz.1, hzc⟩, (SecA.isElemAbelian_fsuVM hyp).2 z hz.1⟩, hz.2⟩
    rw [hZ, Subgroup.mem_bot] at hzZ
    exact hz1 hzZ

end CFSG.Quasithin.Vol2.Ch10.SecC
