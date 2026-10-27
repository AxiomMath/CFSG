module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergCEAschbacherPrimeSelector
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.S12.InputsFischer

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open scoped commutatorElement

theorem theta_le_center_of_commute {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hperf : Group.IsPerfect X) (hq : CFSG.IsQuasisimple (X ⧸ aschbacherSolvableCore p X))
    {c' : X} (hc : ∀ v ∈ aschbacherSolvableCore p X, v * c' = c' * v)
    (hnc : ∃ j : X, c' * j * c'⁻¹ * j⁻¹ ∉ aschbacherSolvableCore p X) :
    aschbacherSolvableCore p X ≤ Subgroup.center X := by
  set θ := aschbacherSolvableCore p X with hθ
  have hθs : Group.IsSolvable θ := (solvable_prime_complement_core_characterization hp).1
  have hθn : θ.Normal := inferInstance
  set C : Subgroup X := Subgroup.centralizer (θ : Set X) with hC
  have hCn : C.Normal := ⟨fun x hx g => by
    rw [hC, Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ θ := by
      have := hθn.conj_mem v hv g⁻¹
      simpa using this
    have h1 := hx (g⁻¹ * v * g) hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * v := by group⟩
  have hc'C : c' ∈ C := Subgroup.mem_centralizer_iff.mpr fun v hv => hc v hv
  have hsup : C ⊔ θ = ⊤ := by
    set π := QuotientGroup.mk' θ with hπ
    have hn : ((C ⊔ θ).map π).Normal :=
      Subgroup.Normal.map (inferInstance) π (QuotientGroup.mk'_surjective θ)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hcen
    · have h1 := Subgroup.comap_map_eq π (C ⊔ θ)
      rw [htop, Subgroup.comap_top, hπ, QuotientGroup.ker_mk', sup_assoc, sup_idem] at h1
      exact h1.symm
    · exfalso
      obtain ⟨j, hj⟩ := hnc
      have hmem : π c' ∈ (C ⊔ θ).map π := ⟨c', Subgroup.mem_sup_left hc'C, rfl⟩
      have hz := Subgroup.mem_center_iff.mp (hcen hmem) (π j)
      apply hj
      rw [← QuotientGroup.eq_one_iff]
      change π (c' * j * c'⁻¹ * j⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc π c' * π j * (π c')⁻¹ * (π j)⁻¹ = (π j * π c') * (π c')⁻¹ * (π j)⁻¹ := by rw [hz]
        _ = 1 := by group
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp θ.subtype) := by
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hy : y₀ ∈ C ⊔ θ := hsup ▸ Subgroup.mem_top y₀
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    refine ⟨⟨b, hb⟩, ?_⟩
    change QuotientGroup.mk' C b = QuotientGroup.mk' C y₀
    have h1 : QuotientGroup.mk' C a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [← hab, map_mul, h1, one_mul]
  have hsol : Group.IsSolvable (X ⧸ C) := Group.isSolvable_of_surjective hsurj
  have hperfQ : Group.IsPerfect (X ⧸ C) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  have hCtop : C = ⊤ := by
    by_contra hne
    obtain ⟨g, hg⟩ : ∃ g : X, g ∉ C := by
      by_contra hall
      push Not at hall
      exact hne (eq_top_iff.mpr fun g _ => hall g)
    have : Nontrivial (X ⧸ C) :=
      ⟨⟨(g : X ⧸ C), 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (X ⧸ C) hsol
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg v hv).symm

theorem inf_solvable_normal_eq_bot {X : Type} [Group X] {K W : Subgroup X}
    (hKperf : Group.IsPerfect ↥K) (hKnt : Nontrivial ↥K) (hK : IsSimpleGroup ↥K) (hW : W.Normal)
    (hWs : Group.IsSolvable ↥W) : K ⊓ W = ⊥ := by
  have hn : (W.subgroupOf K).Normal := Subgroup.Normal.subgroupOf hW K
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥K) ∈ W.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx.2
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  · exfalso
    have hKW : ∀ x : ↥K, (x : X) ∈ W := fun x => by
      have : x ∈ W.subgroupOf K := h ▸ Subgroup.mem_top x
      exact Subgroup.mem_subgroupOf.mp this
    let f : ↥K →* ↥W := (K.subtype).codRestrict W hKW
    have hfinj : Function.Injective f := fun a b hab =>
      Subtype.ext (congrArg (fun y : ↥W => (y : X)) hab)
    have hsolK : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective hfinj
    exact Group.IsPerfect.not_isSolvable ↥K hsolK

theorem le_theta_of_normal {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {J V₀ : Subgroup G} (hVJ : V₀ ≤ J) (hVn : ∀ x ∈ J, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀)
    (hVs : Group.IsSolvable ↥V₀) (hVp : ¬ p ∣ Nat.card ↥V₀) : V₀ ≤ inSubgroup (aschbacherSolvableCore p) J := by
  have hn : (V₀.subgroupOf J).Normal := ⟨fun x hx g => by
    have hxV : (x : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (hVn g g.2 x hxV)⟩
  have hsol : Group.IsSolvable ↥(V₀.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hVJ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVJ).injective
  have hcard : Nat.card ↥(V₀.subgroupOf J) = Nat.card ↥V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVJ).toEquiv
  have hle := (solvable_prime_complement_core_characterization (H := ↥J) hp).2.2.2.1 _ hn hsol
    (by rw [hcard]; exact hVp)
  intro v hv
  exact ⟨⟨v, hVJ hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

theorem center_quot_center_eq_bot {X : Type*} [Group X] (hperf : Group.IsPerfect X) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  set Z := Subgroup.center X with hZdef
  set H₁ : Subgroup X := (Subgroup.center (X ⧸ Z)).comap (QuotientGroup.mk' Z) with hH₁
  have hZ : ⁅Z, (⊤ : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz y _
    exact (Subgroup.mem_center_iff.mp hz y)
  have hcomm1 : ⁅H₁, (⊤ : Subgroup X)⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro w hw x _
    have h1 : Commute (QuotientGroup.mk' Z w) (QuotientGroup.mk' Z x) :=
      (Subgroup.mem_center_iff.mp hw (QuotientGroup.mk' Z x)).symm
    have h2 : QuotientGroup.mk' Z ⁅w, x⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have h2 : ⁅⁅H₁, (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅H₁, (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ ≤ ⁅Z, (⊤ : Subgroup X)⁆ :=
          Subgroup.commutator_mono hcomm1 le_rfl
      _ = ⊥ := hZ
  have h1 : ⁅⁅(⊤ : Subgroup X), H₁⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup X) H₁]
    exact h2
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup X))
    (H₂ := (⊤ : Subgroup X)) (H₃ := H₁) h1 h2
  have hcom : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hperf.commutator_eq_top
  rw [hcom, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  rw [eq_bot_iff]
  intro zb hz
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
  have hzH : z ∈ H₁ := hz
  have hzZ : z ∈ Z := by
    rw [hZdef, Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (h3 (Subgroup.mem_top g)) z hzH).symm
  exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff z).mpr hzZ)

end CFSG.RankThree.PartOne.Q1327
