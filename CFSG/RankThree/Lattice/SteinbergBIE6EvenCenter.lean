module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenExceptional

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
open scoped Pointwise

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusGroup_le_supportedTorus_univ :
    torusGroup τ K ≤ supportedTorus τ K Set.univ := by
  rw [supportedTorus_eq_subsystemTorus]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact Subgroup.subset_closure ⟨i, Set.mem_univ _, t, rfl⟩

theorem eq_one_of_torusRootChar_single {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (h1 : ∀ i : Fin τ.rank, torusRootChar h (Pi.single i 1) = 1) : h = 1 := by
  classical
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 (torusGroup_le_supportedTorus_univ hh)
  refine (supportedTorusHom_eq_one_iff Set.univ a).2 fun i => Units.ext ?_
  have h2 := torusRootChar_supportedTorusHom Set.univ a (isRoot_single τ i)
  rw [h1 i] at h2
  have hs : ∀ j : (Set.univ : Set (Fin τ.rank)), ∑ k, τ.cartan j k *
      (Pi.single i 1 : Fin τ.rank → ℤ) k = τ.cartan j i := fun j => by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
  simp only [hs] at h2
  rw [Units.val_one]
  exact h2.symm

end Torus

section Factors

variable {Ω : Type} [Field Ω]

theorem commute_val_of_mul_eq {g x : ModGL Tag.E6 Ω} (h : g * x = x * g) :
    Commute (g : Module.End Ω (RootModule Tag.E6 Ω)) (x : Module.End Ω (RootModule Tag.E6 Ω)) := by
  show _ * _ = _ * _
  rw [← Units.val_mul, ← Units.val_mul, h]

theorem mul_eq_of_commute_val {g x : ModGL Tag.E6 Ω}
    (h : Commute (g : Module.End Ω (RootModule Tag.E6 Ω))
      (x : Module.End Ω (RootModule Tag.E6 Ω))) :
    g * x = x * g :=
  Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h)

theorem mem_torusGroup_of_commute_of_e6Commutant_eq {S : Set (Fin Tag.E6.rank)}
    {P : Subgroup (ModGL Tag.E6 Ω)}
    (hP : e6Commutant (P : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)))
    {h z : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω) (hz : z ∈ subsystemGroup Tag.E6 Ω S)
    (hc : ∀ x ∈ P, h * z * x = x * (h * z)) : h * z ∈ torusGroup Tag.E6 Ω := by
  have hX : ((h * z : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) ∈
      e6Commutant (P : Set (ModGL Tag.E6 Ω)) := fun x hx => commute_val_of_mul_eq (hc x hx)
  rw [hP] at hX
  exact mem_torusGroup_of_commute_subsystemGroup hh hz fun x hx => mul_eq_of_commute_val (hX x hx)

theorem mem_center_iff_of_e6Commutant_eq {S : Set (Fin Tag.E6.rank)}
    {P : Subgroup (ModGL Tag.E6 Ω)} (hPQ : P ≤ subsystemGroup Tag.E6 Ω S)
    (hP : e6Commutant (P : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω S : Set (ModGL Tag.E6 Ω))) (x : P) :
    x ∈ Subgroup.center P ↔ (x : ModGL Tag.E6 Ω) ∈ torusGroup Tag.E6 Ω ∧
      ∀ α ∈ parabolicRoots Tag.E6 S, torusRootChar (x : ModGL Tag.E6 Ω) α = 1 := by
  have hcomm : x ∈ Subgroup.center P ↔ ∀ y ∈ P, (x : ModGL Tag.E6 Ω) * y = y * x := by
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h y hy
      exact (congrArg Subtype.val (h ⟨y, hy⟩)).symm
    · intro h y
      exact Subtype.ext (h y y.2).symm
  rw [hcomm]
  constructor
  · intro h
    have hH : (x : ModGL Tag.E6 Ω) ∈ torusGroup Tag.E6 Ω := by
      have := mem_torusGroup_of_commute_of_e6Commutant_eq hP (one_mem _) (hPQ x.2)
        (fun y hy => by rw [one_mul]; exact h y hy)
      rwa [one_mul] at this
    have hX : ((x : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) ∈
        e6Commutant (P : Set (ModGL Tag.E6 Ω)) := fun y hy => commute_val_of_mul_eq (h y hy)
    rw [hP] at hX
    refine ⟨hH, fun α hα => (commute_pinnedX_iff hH hα.1).1 fun c => ?_⟩
    have hmem : pinnedX Tag.E6 Ω α c ∈ subsystemGroup Tag.E6 Ω S := by
      rw [subsystemGroup_eq_rootSpan]
      exact pinnedX_mem_rootSpan hα c
    exact mul_eq_of_commute_val (hX _ hmem)
  · rintro ⟨hH, hχ⟩ y hy
    have hle : subsystemGroup Tag.E6 Ω S ≤ Subgroup.centralizer {(x : ModGL Tag.E6 Ω)} := by
      rw [subsystemGroup_eq_rootSpan]
      exact rootSpan_le_centralizer fun α hα c =>
        ((commute_pinnedX_iff hH hα.1).2 (hχ α hα) c).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (hPQ hy))).symm

end Factors

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem e6Commutant_orbitGroup_subsystemGroup :
    e6Commutant (D.orbitGroup : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω D.support : Set (ModGL Tag.E6 Ω)) := by
  rw [D.e6Commutant_orbitGroup, D.rootGroup_eq_subsystemGroup]

theorem orbitGroup_le_subsystemGroup : D.orbitGroup ≤ subsystemGroup Tag.E6 Ω D.support := by
  rw [← D.rootGroup_eq_subsystemGroup]
  exact D.orbitGroup_le_rootGroup

theorem torus_eq_supportedTorus : D.torus = supportedTorus Tag.E6 Ω D.support := by
  rw [torus, D.rootGroup_eq_subsystemGroup, subsystemGroup_inf_torusGroup_eq_supportedTorus]

theorem mem_torusGroup_of_commute_orbitGroup {h z : ModGL Tag.E6 Ω}
    (hh : h ∈ torusGroup Tag.E6 Ω) (hz : z ∈ D.rootGroup)
    (hc : ∀ x ∈ D.orbitGroup, h * z * x = x * (h * z)) : h * z ∈ torusGroup Tag.E6 Ω :=
  mem_torusGroup_of_commute_of_e6Commutant_eq D.e6Commutant_orbitGroup_subsystemGroup hh
    (D.rootGroup_eq_subsystemGroup ▸ hz) hc

theorem mem_center_orbitGroup_iff (x : D.orbitGroup) :
    x ∈ Subgroup.center D.orbitGroup ↔ (x : ModGL Tag.E6 Ω) ∈ D.torus ∧
      ∀ α ∈ D.Ξ, torusRootChar (x : ModGL Tag.E6 Ω) α = 1 := by
  rw [mem_center_iff_of_e6Commutant_eq D.orbitGroup_le_subsystemGroup
    D.e6Commutant_orbitGroup_subsystemGroup, ← D.Ξ_eq_parabolicRoots]
  exact and_congr_left' ⟨fun h => ⟨D.orbitGroup_le_rootGroup x.2, h⟩, fun h => h.2⟩

end E6EvenFixedRootDatum

section Exceptional

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] {J : Set (Fin Tag.E6.rank)}

theorem e6Commutant_e6P24_subsystemGroup (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13)
    {f : ℕ} (hf : 2 ≤ f) :
    e6Commutant (e6P24 Ω J f : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω e6Supp24 : Set (ModGL Tag.E6 Ω)) := by
  rw [e6Commutant_e6P24 hJ f hf, e6Q24_eq_subsystemGroup]

omit [IsAlgClosed Ω] in
theorem e6P24_le_subsystemGroup (f : ℕ) : e6P24 Ω J f ≤ subsystemGroup Tag.E6 Ω e6Supp24 := by
  rw [← e6Q24_eq_subsystemGroup]
  exact e6P24_le_e6Q24 f

end Exceptional

end CFSG.RankThree.Lattice
