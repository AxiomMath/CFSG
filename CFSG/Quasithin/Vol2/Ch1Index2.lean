module

public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.GroupTheory.BurnsideNormalComplement
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def TwoCosets {X : Type*} [Group X] (A B : Subgroup X) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a⁻¹ * b ∈ A ∨ a⁻¹ * c ∈ A ∨ b⁻¹ * c ∈ A

section Basic

variable {X : Type*} [Group X]

theorem TwoCosets.inf {A B : Subgroup X} (h : TwoCosets A B) (C : Subgroup X) :
    TwoCosets (A ⊓ C) (B ⊓ C) := fun a ha b hb c hc => by
  rcases h a ha.1 b hb.1 c hc.1 with h1 | h1 | h1
  · exact Or.inl ⟨h1, C.mul_mem (C.inv_mem ha.2) hb.2⟩
  · exact Or.inr (Or.inl ⟨h1, C.mul_mem (C.inv_mem ha.2) hc.2⟩)
  · exact Or.inr (Or.inr ⟨h1, C.mul_mem (C.inv_mem hb.2) hc.2⟩)

theorem TwoCosets.map {Y : Type*} [Group Y] {A B : Subgroup X} (h : TwoCosets A B) (f : X →* Y) :
    TwoCosets (A.map f) (B.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
  rcases h a ha b hb c hc with h1 | h1 | h1
  · exact Or.inl ⟨_, h1, by simp⟩
  · exact Or.inr (Or.inl ⟨_, h1, by simp⟩)
  · exact Or.inr (Or.inr ⟨_, h1, by simp⟩)

theorem twoCosets_of_relIndex_le_two [Finite X] {A B : Subgroup X} (h : A.relIndex B ≤ 2) :
    TwoCosets A B := by
  intro a ha b hb c hc
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hne : ∀ {x y : X} (hx : x ∈ B) (hy : y ∈ B), x⁻¹ * y ∉ A →
      (QuotientGroup.mk (⟨x, hx⟩ : ↥B) : ↥B ⧸ A.subgroupOf B) ≠ QuotientGroup.mk ⟨y, hy⟩ := by
    intro x y hx hy hxy heq
    exact hxy (by simpa [Subgroup.mem_subgroupOf] using QuotientGroup.eq.mp heq)
  have hlt : 2 < Nat.card (↥B ⧸ A.subgroupOf B) := by
    have := Fintype.ofFinite (↥B ⧸ A.subgroupOf B)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.mpr ⟨_, _, _, hne ha hb h1, hne ha hc h2, hne hb hc h3⟩
  have hidx : Nat.card (↥B ⧸ A.subgroupOf B) = A.relIndex B := rfl
  omega

end Basic

section Finite

variable {X Z : Type} [Group X] [Finite X] [Group Z] [Finite Z]

theorem isSylowTwoOf_map_hom (f : X →* Z) {D Λ : Subgroup X} (hD : IsSylowTwoOf D Λ) :
    IsSylowTwoOf (D.map f) (Λ.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : Function.Surjective (f.subgroupMap Λ) := f.subgroupMap_surjective Λ
  let Q : Sylow 2 ↥Λ := A4.toSylow hD
  have h1 := A4.isSylowTwoOf_map (Λ.map f) (Q.mapSurjective hg)
  have h2 : ((Q.mapSurjective hg : Subgroup ↥(Λ.map f))).map (Λ.map f).subtype = D.map f := by
    rw [Sylow.coe_mapSurjective hg Q]
    change (((D.subgroupOf Λ).map (f.subgroupMap Λ)).map (Λ.map f).subtype) = D.map f
    rw [Subgroup.map_map]
    have : (Λ.map f).subtype.comp (f.subgroupMap Λ) = f.comp Λ.subtype := rfl
    rw [this, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hD.1]
  rwa [h2] at h1

theorem isSolvable_of_sylow_three (P : Sylow 2 X)
    (h3 : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), ∀ c ∈ (P : Subgroup X),
      a = b ∨ a = c ∨ b = c) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgx : g * x * g⁻¹ ∈ (P : Subgroup X) := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    rcases h3 1 (one_mem _) x hx (g * x * g⁻¹) hgx with h | h | h
    · rw [← h]; simp
    · have hx1 : x = 1 := by
        have : g * x * g⁻¹ = 1 := h.symm
        simpa using this
      rw [hx1]; simp
    · calc x * g = (g * x * g⁻¹) * g := by rw [← h]
        _ = g * x := by group
  obtain ⟨K, hKn, hKp, -, -, -, -, -, -, -, hab⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hnorm
  have hodd : Odd (Nat.card K) := Nat.odd_iff.mpr (by omega)
  have hKs : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hQs : Group.IsSolvable (X ⧸ K) := Group.isSolvable_of_comm hab
  exact Group.isSolvable_of_subgroup_quotient K

end Finite

section Component

variable {Z : Type} [Group Z] [Finite Z]

theorem not_commutator_le_solvRad {P U U₀ : Subgroup Z} (hP : P ∈ cComp P)
    (hU : IsSylowTwoOf U P) (h2 : TwoCosets U₀ U) :
    ¬ ⁅P, U₀⁆ ≤ solvRad P := by
  intro hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnab⟩ := A36A.simple_quotient_of_mem_cComp hP
  obtain ⟨a₀, b₀, hab₀⟩ := hnab
  let N : Subgroup ↥P := CFSG.solvableRadical ↥P
  let π : ↥P →* ↥P ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcenter : Subgroup.center (↥P ⧸ N) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (↥P ⧸ N)) with h | h
    · exact h
    · exfalso
      have ha : a₀ ∈ Subgroup.center (↥P ⧸ N) := by rw [h]; trivial
      exact hab₀ ((Subgroup.mem_center_iff.mp ha b₀).symm)
  have hU₀N : ∀ x : ↥P, (x : Z) ∈ U₀ → x ∈ N := by
    intro x hx
    have hxc : π x ∈ Subgroup.center (↥P ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hπ y
      have h1 : (⁅(y' : ↥P), x⁆ : ↥P) ∈ N := by
        have h2 : (⁅(y' : Z), (x : Z)⁆) ∈ ⁅P, U₀⁆ :=
          Subgroup.commutator_mem_commutator y'.2 hx
        have h3 := hcomm h2
        have h4 : (⁅y', x⁆ : ↥P) ∈ (solvRad P).subgroupOf P := by
          rw [Subgroup.mem_subgroupOf]
          simpa [commutatorElement_def] using h3
        rwa [A36A.subgroupOf_solvRad] at h4
      have h5 : π ⁅y', x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_commutatorElement] at h5
      exact commutatorElement_eq_one_iff_mul_comm.mp h5
    rw [hcenter, Subgroup.mem_bot] at hxc
    exact (QuotientGroup.eq_one_iff x).mp hxc
  let Qs : Sylow 2 ↥P := A4.toSylow hU
  let Qb : Sylow 2 (↥P ⧸ N) := Qs.mapSurjective hπ
  have hQb : (Qb : Subgroup (↥P ⧸ N)) = (U.subgroupOf P).map π := Sylow.coe_mapSurjective hπ Qs
  have h3 : ∀ a ∈ (Qb : Subgroup (↥P ⧸ N)), ∀ b ∈ (Qb : Subgroup (↥P ⧸ N)),
      ∀ c ∈ (Qb : Subgroup (↥P ⧸ N)), a = b ∨ a = c ∨ b = c := by
    intro a ha b hb c hc
    rw [hQb] at ha hb hc
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    have key : ∀ {u v : ↥P}, u ∈ U.subgroupOf P → v ∈ U.subgroupOf P →
        u⁻¹ * v ∈ U₀.subgroupOf P → π u = π v := by
      intro u v _ _ huv
      have : u⁻¹ * v ∈ N := hU₀N _ huv
      have h1 : π (u⁻¹ * v) = 1 := (QuotientGroup.eq_one_iff _).mpr this
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1
    rcases h2 a' ha' b' hb' c' hc' with h | h | h
    · exact Or.inl (key ha' hb' h)
    · exact Or.inr (Or.inl (key ha' hc' h))
    · exact Or.inr (Or.inr (key hb' hc' h))
  have hsolv : Group.IsSolvable (↥P ⧸ N) := isSolvable_of_sylow_three Qb h3
  exact hab₀ ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a₀ b₀)

end Component

end CFSG.Quasithin
