module

public import CFSG.Quasithin.EmptyFaithful.S153LKey

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.S1549C
  CFSG.Quasithin.S1549D
open scoped commutatorElement

namespace S153L

section Star

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem starOfSub_preStar (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H) :
    starOfSub h (preStar h A) = A := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (mem_starOfSub h).mp hy
    exact (starHom_mem_iff h (x := x)).mp hx
  · intro hy
    obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp (hA hy)
    exact (mem_starOfSub h).mpr ⟨x, (starHom_mem_iff h (x := x)).mpr hy, rfl⟩

@[expose] noncomputable def starRestrict (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) :
    ↥(preStar h A) →* ↥A :=
  ((starHom h).comp (Subgroup.inclusion (preStar_le h A))).codRestrict A
    (fun x => (mem_preStar_iff h).mp x.2 |>.2)

omit [Finite G] in
theorem starRestrict_coe (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) (x : ↥(preStar h A)) :
    ((starRestrict h A x : ↥A) : MulAut ↥(tildeOf V₁ (conjClosure Vp H))) =
      starHom h ⟨(x : G), preStar_le h A x.2⟩ := rfl

omit [Finite G] in
theorem starRestrict_surjective (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H) :
    Function.Surjective (starRestrict h A) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp (hA hy)
  exact ⟨⟨(x : G), (starHom_mem_iff h (x := x)).mpr hy⟩, Subtype.ext rfl⟩

theorem starRestrict_ker_solvable (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) :
    Group.IsSolvable ↥(starRestrict h A).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(starRestrict h A).ker := by
    intro z
    have hz : starHom h ⟨((z : ↥(preStar h A)) : G), preStar_le h A (z : ↥(preStar h A)).2⟩ = 1 := by
      have := (MonoidHom.mem_ker).mp z.2
      have h2 := congrArg Subtype.val this
      rw [starRestrict_coe] at h2
      simpa using h2
    obtain ⟨k, hk⟩ := starHom_ker_pow h _ hz
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have := hp.isNilpotent
  infer_instance

omit [Finite G] in
theorem starOfSub_eq_map (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) {K : Subgroup G}
    (hK : K ≤ preStar h A) :
    starOfSub h K = ((K.subgroupOf (preStar h A)).map (starRestrict h A)).map A.subtype := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxK, rfl⟩ := (mem_starOfSub h).mp hy
    exact ⟨starRestrict h A ⟨(x : G), hK hxK⟩,
      ⟨⟨(x : G), hK hxK⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact (mem_starOfSub h).mpr ⟨⟨(x : G), preStar_le h A x.2⟩, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem starOfSub_mem_cComp (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H)
    {K : Subgroup G} (hK : K ∈ cComp (preStar h A)) : starOfSub h K ∈ cComp A := by
  have hbij := cComp_map_bijOn (starRestrict h A) (starRestrict_surjective h hA)
    (starRestrict_ker_solvable h A)
  have h1 := (cComp_subgroupOf_bijOn (preStar h A)).mapsTo hK
  have h2 := hbij.mapsTo h1
  have h3 := map_subtype_mem_cComp h2
  rwa [← starOfSub_eq_map h A (le_of_mem_cComp hK)] at h3

theorem starOfSub_injOn (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H) :
    Set.InjOn (starOfSub h) (cComp (preStar h A)) := by
  intro K₁ hK₁ K₂ hK₂ heq
  have hbij := cComp_map_bijOn (starRestrict h A) (starRestrict_surjective h hA)
    (starRestrict_ker_solvable h A)
  have e1 := starOfSub_eq_map h A (le_of_mem_cComp hK₁)
  have e2 := starOfSub_eq_map h A (le_of_mem_cComp hK₂)
  rw [heq, e2] at e1
  have e3 := Subgroup.map_injective A.subtype_injective e1
  have e4 := hbij.injOn ((cComp_subgroupOf_bijOn (preStar h A)).mapsTo hK₁)
    ((cComp_subgroupOf_bijOn (preStar h A)).mapsTo hK₂) e3.symm
  exact (cComp_subgroupOf_bijOn (preStar h A)).injOn hK₁ hK₂ e4

omit [Finite G] in
theorem not_isSolvable_preStar (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H)
    (hns : ¬ Group.IsSolvable ↥A) : ¬ Group.IsSolvable ↥(preStar h A) := fun _ =>
  hns (Group.isSolvable_of_surjective (starRestrict_surjective h hA))

omit [Finite G] in
theorem isSolvable_starOfSub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} (hXH : X ≤ H)
    (hs : Group.IsSolvable ↥X) : Group.IsSolvable ↥(starOfSub h X) := by
  have := hs
  let f : ↥X →* ↥(starOfSub h X) :=
    ((starHom h).comp (Subgroup.inclusion hXH)).codRestrict _
      (fun x => (mem_starOfSub h).mpr ⟨Subgroup.inclusion hXH x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxK, rfl⟩ := (mem_starOfSub h).mp hy
    exact ⟨⟨x, hxK⟩, rfl⟩
  exact Group.isSolvable_of_surjective hf

end Star

section Exists

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_cComp_of_not_solvable {J : Subgroup Ω} (h : ¬ Group.IsSolvable ↥J) :
    (cComp J).Nonempty := by
  have hne : perfectCore J ≠ ⊥ := fun h' => h ((isSolvable_iff_perfectCore_eq_bot J).mpr h')
  obtain ⟨K, hK⟩ := (Set.toFinite {K : Subgroup Ω | K ≠ ⊥ ∧ perfectCore K = K ∧
      IsSubnormal K J}).exists_minimal
    ⟨perfectCore J, hne, perfectCore_eq_self_of_perfect (perfectCore_perfect J),
      A3.subnormal_perfectCore (IsSubnormal.refl J)⟩
  exact ⟨K, mem_cComp_iff_minimal.mpr ⟨hK.prop, fun K' hK' hle => hK.2 hK' hle⟩⟩

end Exists

end S153L

end CFSG.Quasithin
