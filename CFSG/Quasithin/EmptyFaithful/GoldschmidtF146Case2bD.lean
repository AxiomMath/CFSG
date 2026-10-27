module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bC

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.GoldS146R
open scoped MatrixGroups

theorem parabolics_of_type {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsPSL 3 2 m X ∨ IsPSp4 2 m X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (P : Fin 2 → Subgroup X),
      Nat.card F = 2 ^ m ∧ ResidualOvergroupsAt X U P ∧
      (∀ j, Subgroup.normalizer (U : Set X) ≤ P j) ∧ (∀ j, U ≤ perfectCore (P j)) ∧
      ∀ j, ∃ g : ↥(perfectCore (P j)) →* SL(2, F), Function.Surjective g ∧ IsPGroup 2 g.ker := by
  rcases hX with hX | hX
  · exact parabolics_of_isPSL_three hm hX hU
  · exact parabolics_of_isPSp_four hm hX hU

structure ParabData {Y : Type} [Group Y] (m : ℕ) (L U : Subgroup Y) (F : Type) [Field F]
    (P : Fin 2 → Subgroup Y) : Prop where
  card : Nat.card F = 2 ^ m
  le : ∀ j, P j ≤ L
  sylow_le : ∀ j, U ≤ P j
  ne : P 0 ≠ P 1
  max : ∀ A : Subgroup Y, U ≤ A → A ≤ L → (A ⋖ L ↔ ∃ j, A = P j)
  solv : Group.IsSolvable ↥(P 0 ⊓ P 1)
  borel : ∀ j, L ⊓ Subgroup.normalizer (U : Set Y) ≤ P j
  maxPar : ∀ j, IsMaxParabolic2 L (P j)
  perf : ∀ j, U ≤ perfectCore (P j)
  levi : ∀ j, ∃ g : ↥(perfectCore (P j)) →* SL(2, F), Function.Surjective g ∧ IsPGroup 2 g.ker

theorem parabolics_ambient {Y : Type} [Group Y] [Finite Y] {L U : Subgroup Y} {m : ℕ}
    (hm : 2 ≤ m) (hX : IsPSL 3 2 m ↥L ∨ IsPSp4 2 m ↥L) (hU : IsSylowTwoOf U L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (P : Fin 2 → Subgroup Y), ParabData m L U F P := by
  obtain ⟨F, hF, hFin, P₀, hcard, hres, hN, hperf, hlevi⟩ :=
    parabolics_of_type hm hX (isSylowTwoOf_subgroupOf_top hU)
  obtain ⟨hne, hUP, hmax, hsolv, -⟩ := hres
  have hUL : U ≤ L := hU.1
  have hmapU : (U.subgroupOf L).map L.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUL
  have hcov : ∀ j, (P₀ j).map L.subtype ⋖ L := fun j => by
    have h := (hmax (P₀ j) (hUP j)).2 ⟨j, rfl⟩
    exact (covBy_top_iff_map_subtype _).1 h
  have hbor : ∀ j, L ⊓ Subgroup.normalizer (U : Set Y) ≤ (P₀ j).map L.subtype := by
    intro j x ⟨hxL, hxN⟩
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [normalizer_subgroupOf_eq' hUL]
      exact ⟨hxL, hxN⟩
    exact ⟨_, hN j h1, rfl⟩
  refine ⟨F, hF, hFin, fun j => (P₀ j).map L.subtype, ⟨hcard, fun j => Subgroup.map_subtype_le _,
    fun j => ?_, fun h => hne (Subgroup.map_injective L.subtype_injective h), ?_, ?_, hbor,
    fun j => ?_, fun j => ?_, fun j => ?_⟩⟩
  · rw [← hmapU]
    exact Subgroup.map_mono (hUP j)
  · intro A hUA hAL
    have hA : A = (A.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hAL).symm
    have hUA' : U.subgroupOf L ≤ A.subgroupOf L := fun x hx => hUA hx
    have h1 : A ⋖ L ↔ A.subgroupOf L ⋖ ⊤ := by
      rw [covBy_top_iff_map_subtype, Subgroup.map_subgroupOf_eq_of_le hAL]
    rw [h1, hmax _ hUA']
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hA, hj]⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      show A.subgroupOf L = P₀ j
      rw [hj]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective (P₀ j)
  · rw [← Subgroup.map_inf_eq _ _ _ L.subtype_injective]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective _ _ L.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ L.subtype_injective).surjective
  · have hlt : ∀ j, (P₀ j).map L.subtype < L := fun j => (hcov j).lt
    refine ⟨⟨Subgroup.map_subtype_le _, U, hU, hbor j⟩, (hlt j).ne, ?_⟩
    rintro Q ⟨hQL, -⟩ hQne hPQ
    by_contra hne
    exact (hcov j).2 (lt_of_le_of_ne hPQ (Ne.symm hne)) (lt_of_le_of_ne hQL hQne)
  · rw [← hmapU, ← map_perfectCore]
    exact Subgroup.map_mono (hperf j)
  · obtain ⟨g, hg, hk⟩ := hlevi j
    exact levi_transport L.subtype L.subtype_injective _ g hg hk

end CFSG.Quasithin.F146Field.Case2b
