module

public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin

open scoped commutatorElement

section Components

variable {G : Type*} [Group G] [Finite G]

theorem isComponent_subgroupOf_of_mem_cComp_of_isSimpleGroup {M K : Subgroup G}
    (hK : K ∈ cComp M) (hs : IsSimpleGroup ↥K) : CFSG.IsComponent (K.subgroupOf M) := by
  have hKM : K ≤ M := le_of_mem_cComp hK
  have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    exact not_isSolvable_of_mem_cComp hK (Group.isSolvable_of_comm hcomm)
  have hq : CFSG.IsQuasisimple ↥K := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKM).symm hq,
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hK))⟩

theorem cComp_eq_or_commutator_eq_bot_of_isSimpleGroup {M K K' : Subgroup G}
    (hK : K ∈ cComp M) (hK' : K' ∈ cComp M) (hs : IsSimpleGroup ↥K) (hs' : IsSimpleGroup ↥K') :
    K = K' ∨ ⁅K, K'⁆ = ⊥ := by
  have hKM : K ≤ M := le_of_mem_cComp hK
  have hK'M : K' ≤ M := le_of_mem_cComp hK'
  rcases CFSG.LocalCores.distinct_components_commute
      (isComponent_subgroupOf_of_mem_cComp_of_isSimpleGroup hK hs)
      (isComponent_subgroupOf_of_mem_cComp_of_isSimpleGroup hK' hs') with h | h
  · left
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hKM, Subgroup.map_subgroupOf_eq_of_le hK'M] at this
  · right
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKM,
      Subgroup.map_subgroupOf_eq_of_le hK'M, Subgroup.map_bot] at this

end Components

section InspFiveA

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem insp5a_commute (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hL38 : A38Types ↥L) :
    ⁅L, conjAutSub t L⁆ = ⊥ := by
  have hLs : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hL38
  have hLts : IsSimpleGroup ↥(conjAutSub t L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types (a38Types_conjAutSub t hL38)
  rcases cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hD.comp
      (conjAutSub_mem_cComp hD.comp (hD.sylow.1 htT)) hLs hLts with h | h
  · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm) htL
  · exact h

private theorem insp5a_conj_le_normalizer (hD : D31 M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hL38 : A38Types ↥L) :
    conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have h : conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact insp5a_commute hD htT htL hL38
  exact h.trans (Subgroup.centralizer_le_normalizer _)

theorem insp5a_Mp_le_normalizer (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [hMp]
  exact sup_le Subgroup.le_normalizer (insp5a_conj_le_normalizer hD htT htL hL38)

theorem insp5a_conj_cases (hD : D31 M Mp T L V) (htT : t ∈ T)
    (hMp : Mp = L ⊔ conjAutSub t L) (hL38 : A38Types ↥L) :
    ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L := by
  intro s hs
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hKc : conjAutSub s L ∈ cComp M := conjAutSub_mem_cComp hD.comp (hD.sylow.1 hs)
  have hLtc : conjAutSub t L ∈ cComp M := conjAutSub_mem_cComp hD.comp (hD.sylow.1 htT)
  have hLs : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hL38
  have hLts : IsSimpleGroup ↥(conjAutSub t L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types (a38Types_conjAutSub t hL38)
  have hKs : IsSimpleGroup ↥(conjAutSub s L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types (a38Types_conjAutSub s hL38)
  have h1 : ⁅L, conjAutSub s L⁆ = ⊥ :=
    (cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hD.comp hKc hLs hKs).resolve_left
      fun h => hne1 h.symm
  have h2 : ⁅conjAutSub t L, conjAutSub s L⁆ = ⊥ :=
    (cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hLtc hKc hLts hKs).resolve_left
      fun h => hne2 h.symm
  have hKMp : conjAutSub s L ≤ Mp := by
    rw [hD.Mp_eq]
    intro x hx
    rw [mem_conjAutSub_iff] at hx
    have := mem_conjClosure (Z := L) (H := T) hs hx
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at this
  have hMpc : Mp ≤ Subgroup.centralizer (conjAutSub s L : Set (MulAut W)) := by
    rw [hMp]
    exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
  have hab : ⁅conjAutSub s L, conjAutSub s L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKMp.trans hMpc)
  exact ne_bot_of_mem_cComp hKc ((perfect_of_mem_cComp hKc).symm.trans hab)

theorem insp5a_acts_as_L (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hL38 : A38Types ↥L) :
    ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u := by
  intro a ha
  rw [hMp] at ha
  exact exists_mem_of_mem_sup_of_le_centSub (insp5a_conj_le_normalizer hD htT htL hL38)
    (fun y hy u hu => hV0 u hu y hy) a ha

theorem insp5a_V_facts (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hL38 : A38Types ↥L) :
    V ≠ ⊥ ∧ Mp ≤ stabSub V ∧ commSub V L = V := by
  obtain ⟨hinv, hcommMp, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.irr
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  refine ⟨?_, le_stabSub_of_forall_mem hinv, ?_⟩
  · intro h
    rw [h] at hlt
    exact not_lt_bot hlt
  · refine le_antisymm (commSub_le_of_invariant fun x hx w hw => hinv x (hLMp hx) w hw) ?_
    calc V = commSub V Mp := hcommMp.symm
      _ ≤ commSub V L := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨g, hg, v, hv, rfl⟩
        obtain ⟨l, hl, hgl⟩ := insp5a_acts_as_L hD htT htL hMp hV0 hL38 g hg
        rw [hgl v hv]
        exact Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩

theorem insp5a_normalizes (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hcomm : commV L = V)
    (hL38 : A38Types ↥L) :
    (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have _ := hcomm
  obtain ⟨hVne, hstab, hcommV⟩ := insp5a_V_facts hD htT htL hMp hV0 hL38
  have hMpN := insp5a_Mp_le_normalizer hD htT htL hMp hL38
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    hD.Mp_eq ▸ le_normalizer_conjClosure L T
  have hS : ∀ s ∈ T, s ∈ stabSub V → s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro s hsT hsV
    by_contra hsn
    have hLs : conjAutSub s L = conjAutSub t L :=
      (insp5a_conj_cases hD htT hMp hL38 s hsT).resolve_left fun h =>
        hsn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hfix : V ≤ fixV L := by
      intro v hv l hl
      have hsl : s * l * s⁻¹ ∈ conjAutSub t L := by
        rw [← hLs]
        exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
      have h := hV0 (s v) ((hsV v).2 hv) _ hsl
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h
      exact s.injective h
    exact hVne (by rw [← hcommV, commSub_eq_bot_iff.mpr hfix])
  intro y hy
  obtain ⟨hyMT, hyV⟩ := Subgroup.mem_inf.mp hy
  have hy' : y ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hyMT
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hy'
  obtain ⟨m, hm, s, hs, rfl⟩ := hy'
  have hsV : s ∈ stabSub V := by
    have : m⁻¹ * (m * s) ∈ stabSub V :=
      (stabSub V).mul_mem ((stabSub V).inv_mem (hstab hm)) hyV
    simpa using this
  exact (Subgroup.normalizer (L : Set (MulAut W))).mul_mem (hMpN hm) (hS s hs hsV)

end InspFiveA

end CFSG.Quasithin
