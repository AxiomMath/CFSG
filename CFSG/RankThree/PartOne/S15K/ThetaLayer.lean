module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.GroupTheory.SteinbergCECentralThetaQuasisimple
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

theorem eq_or_commutator_eq_bot_of_components {Γ : Type*} [Group Γ] [Finite Γ] {H Q₁ Q₂ : Subgroup Γ} (h₁ : Q₁ ≤ H) (h₂ : Q₂ ≤ H)
    (c₁ : IsComponent (Q₁.subgroupOf H)) (c₂ : IsComponent (Q₂.subgroupOf H)) :
    Q₁ = Q₂ ∨ ⁅Q₁, Q₂⁆ = ⊥ := by
  rcases LocalCores.distinct_components_commute c₁ c₂ with h | h
  · left
    have h' := (Subgroup.subgroupOf_inj (K := H)).1 h
    rwa [inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h'
  · right
    have h2 := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
      Subgroup.map_subgroupOf_eq_of_le h₂, Subgroup.map_bot] at h2

theorem theta_inf_normal_solvable {p : ℕ} (hp : p.Prime) {C H : Subgroup G} (hHC : H ≤ C) :
    ((inSubgroup (aschbacherSolvableCore p) C ⊓ H).subgroupOf H).Normal ∧
      Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) C ⊓ H : Subgroup G) := by
  set θC := inSubgroup (aschbacherSolvableCore p) C with hθC
  refine ⟨?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro h hh
    have hCn : C ≤ Subgroup.normalizer (θC : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (Subgroup.le_normalizer (H := C))
    have h1 : h ∈ Subgroup.normalizer (θC : Set G) := hCn (hHC hh)
    have h2 : h ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective, h1, h2]
  · have hsol := (theta_solvable_and_not_dvd hp C).1
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : θC ⊓ H ≤ θC)) (Subgroup.inclusion_injective _)

theorem eq_component_of_mem_thetaComponentsAt_of_perfect {p : ℕ} (hp : p.Prime) {b : G}
    {H : Subgroup G} (hHC : H ≤ Subgroup.centralizer ({b} : Set G)) {ι : Type*}
    (Q : ι → Subgroup G) (hQH : ∀ i, Q i ≤ H) (hQc : ∀ i, IsComponent ((Q i).subgroupOf H))
    (hperf : ∀ Y : Subgroup G, Y ≤ H → Group.IsPerfect ↥Y → Y ≤ ⨆ i, Q i) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p b) (hYH : Y ≤ H) : ∃ i, Y = Q i := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set θC := inSubgroup (aschbacherSolvableCore p) C with hθC
  obtain ⟨hTn, hTs⟩ := theta_inf_normal_solvable hp hHC
  have hQT : ∀ i, ⁅Q i, θC ⊓ H⁆ = ⊥ := by
    intro i
    have hRs : Group.IsSolvable ((θC ⊓ H).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : θC ⊓ H ≤ H)).toMonoidHom)
        (MulEquiv.injective _)
    have h := (LocalCores.component_solvable_centralizer hRs hTn.isSubnormal).1 _ (hQc i)
    have h2 := congrArg (Subgroup.map H.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hQH i),
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : θC ⊓ H ≤ H), Subgroup.map_bot] at h2
    exact h2
  have hYperf : Group.IsPerfect Y := isPerfect_of_mem_thetaComponentsAt hY
  have hYder : Y ≤ ⨆ i, Q i := hperf Y hYH hYperf
  have hTY : ⁅Y, θC ⊓ H⁆ = ⊥ := by
    rw [eq_bot_iff]
    have hle : ⨆ i, Q i ≤ Subgroup.centralizer ((θC ⊓ H : Subgroup G) : Set G) :=
      iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hQT i)
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hYder.trans hle)
    exact this.le
  obtain ⟨hYC, hL⟩ := mem_thetaComponentsAt_iff.mp hY
  have hθY := theta_eq_inf_of_mem_thetaComponentsAt hp hY
  have hZ : aschbacherSolvableCore p ↥(Y.subgroupOf C) ≤ Subgroup.center ↥(Y.subgroupOf C) := by
    intro x hx
    rw [aschbacherSolvableCore_eq_subgroupOf hp hL.2.1, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxθ : ((x : ↥C) : G) ∈ θC := ⟨(x : ↥C), hx, rfl⟩
    have hxY : ((x : ↥C) : G) ∈ Y := Subgroup.mem_subgroupOf.mp x.2
    have hyY : ((y : ↥C) : G) ∈ Y := Subgroup.mem_subgroupOf.mp y.2
    have hcomm := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTY hyY) ((x : ↥C) : G) ⟨hxθ, hYH hxY⟩
    exact Subtype.ext (Subtype.ext hcomm.symm)
  have hqC : IsQuasisimple ↥(Y.subgroupOf C) :=
    isQuasisimple_of_mem_thetaComponents_of_le_center hL hZ
  have hqY : IsQuasisimple ↥Y :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYC) hqC
  have hYsub : (Y.subgroupOf H).IsSubnormal := by
    have := hL.2.1.comap (Subgroup.inclusion hHC)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hYcomp : IsComponent (Y.subgroupOf H) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYH).symm hqY, hYsub⟩
  by_contra hne
  push Not at hne
  have hcommQ : ∀ i, ⁅Y, Q i⁆ = ⊥ := by
    intro i
    rcases LocalCores.distinct_components_commute hYcomp (hQc i) with h | h
    · exfalso
      refine hne i ?_
      have h' := (Subgroup.subgroupOf_inj (K := H)).1 h
      rwa [inf_eq_left.mpr hYH, inf_eq_left.mpr (hQH i)] at h'
    · have h2 := congrArg (Subgroup.map H.subtype) h
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYH,
        Subgroup.map_subgroupOf_eq_of_le (hQH i), Subgroup.map_bot] at h2
  have hYc : Y ≤ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    refine Subgroup.iSup_induction Q (C := fun x => x * y = y * x) hx ?_ ?_ ?_
    · intro i x hxi
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommQ i) hy) x hxi
    · simp
    · intro a b ha hb
      rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have hYab : ∀ a ∈ Y, ∀ c ∈ Y, a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hYc hc) a (hYder ha)
  have hYcY : Y ≤ Subgroup.centralizer (Y : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => hYab h hh y hy
  have h1 : ⁅Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYcY
  have hbot : Y = ⊥ := by
    have := (Subgroup.isPerfect_iff).1 hYperf
    rw [h1] at this
    exact this.symm
  have hnt : Nontrivial ↥Y := LocalCores.isQuasisimple_nontrivial hqY
  exact (Subgroup.nontrivial_iff_ne_bot Y).1 hnt hbot

theorem eq_component_of_mem_thetaComponentsAt {p : ℕ} (hp : p.Prime) {b : G} {H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer ({b} : Set G)) {ι : Type*} (Q : ι → Subgroup G)
    (hQH : ∀ i, Q i ≤ H) (hQc : ∀ i, IsComponent ((Q i).subgroupOf H))
    (hder : ⁅H, H⁆ = ⨆ i, Q i) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p b)
    (hYH : Y ≤ H) : ∃ i, Y = Q i :=
  eq_component_of_mem_thetaComponentsAt_of_perfect hp hHC Q hQH hQc
    (fun Y' hY'H hY'perf => by
      rw [← hder]
      calc Y' = ⁅Y', Y'⁆ := ((Subgroup.isPerfect_iff).1 hY'perf).symm
        _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hY'H hY'H) hY hYH

end CFSG.RankThree.PartOne.S15K
