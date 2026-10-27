module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Recognition.HSWales

open MulAction
open scoped Pointwise

universe u v

section Graph

variable (G : Type u) {Ω : Type v} [Group G] [MulAction G Ω]

@[expose] def walesGraph (a : Ω) (Δ : Set Ω) : SimpleGraph Ω :=
  SimpleGraph.fromEdgeSet {e | ∃ g : G, ∃ b ∈ Δ, e = s(g • a, g • b)}

variable {G}

theorem walesGraph_adj {a : Ω} {Δ : Set Ω} {x y : Ω} :
    (walesGraph G a Δ).Adj x y ↔
      x ≠ y ∧ ∃ g : G, ∃ b ∈ Δ, (x = g • a ∧ y = g • b) ∨ (x = g • b ∧ y = g • a) := by
  rw [walesGraph, SimpleGraph.fromEdgeSet_adj, and_comm]
  simp only [Set.mem_ofPred_eq, Sym2.eq_iff]

noncomputable instance (a : Ω) (Δ : Set Ω) : DecidableRel (walesGraph G a Δ).Adj :=
  Classical.decRel _

end Graph

section Orbital

variable (G : Type u) {Ω : Type v} [Group G] [MulAction G Ω]

@[expose] def Orb (a b x y : Ω) : Prop := ∃ g : G, g • a = x ∧ g • b = y

variable {G} {a b : Ω}

theorem orb_smul (g : G) {x y : Ω} : Orb G a b (g • x) (g • y) ↔ Orb G a b x y := by
  constructor
  · rintro ⟨k, hk1, hk2⟩
    exact ⟨g⁻¹ * k, by rw [mul_smul, hk1, inv_smul_smul], by rw [mul_smul, hk2, inv_smul_smul]⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨g * k, mul_smul _ _ _, mul_smul _ _ _⟩

theorem orb_a_iff {y : Ω} : Orb G a b a y ↔ y ∈ orbit (stabilizer G a) b := by
  constructor
  · rintro ⟨g, hg1, hg2⟩
    exact ⟨⟨g, mem_stabilizer_iff.2 hg1⟩, hg2⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, mem_stabilizer_iff.1 s.2, rfl⟩

theorem orbit_stabilizer_self (a : Ω) : orbit (stabilizer G a) a = {a} := by
  ext x
  simp only [mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact mem_stabilizer_iff.1 s.2
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

end Orbital

structure Rank3 (G : Type u) {Ω : Type v} [Group G] [MulAction G Ω] (a b c : Ω) : Prop where
  card_Ω : Nat.card Ω = 100
  cover : ∀ x : Ω, x = a ∨ x ∈ orbit (stabilizer G a) b ∨ x ∈ orbit (stabilizer G a) c
  ncard_Δ : (orbit (stabilizer G a) b).ncard = 22
  ncard_Γ : (orbit (stabilizer G a) c).ncard = 77

namespace Rank3

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω} (D : Rank3 G a b c)

include D

theorem a_notMem_Δ : a ∉ orbit (stabilizer G a) b := by
  intro h
  have h1 := D.ncard_Δ
  rw [← orbit_eq_iff.2 h, orbit_stabilizer_self, Set.ncard_singleton] at h1
  omega

theorem a_notMem_Γ : a ∉ orbit (stabilizer G a) c := by
  intro h
  have h1 := D.ncard_Γ
  rw [← orbit_eq_iff.2 h, orbit_stabilizer_self, Set.ncard_singleton] at h1
  omega

theorem notMem_Γ_of_mem_Δ {x : Ω} (hx : x ∈ orbit (stabilizer G a) b) :
    x ∉ orbit (stabilizer G a) c := by
  intro h
  have h1 := D.ncard_Δ
  rw [← orbit_eq_iff.2 hx, orbit_eq_iff.2 h, D.ncard_Γ] at h1
  omega

theorem b_ne_a : b ≠ a := fun h => D.a_notMem_Δ (h ▸ mem_orbit_self b)

omit D in
theorem of_range_orbit {Δ Γ : Set Ω} (hΩ : Nat.card Ω = 100)
    (horb : Set.range (orbit (stabilizer G a) : Ω → Set Ω) = {{a}, Δ, Γ})
    (hΔ : Δ.ncard = 22) (hΓ : Γ.ncard = 77) :
    ∃ b c : Ω, orbit (stabilizer G a) b = Δ ∧ orbit (stabilizer G a) c = Γ ∧ Rank3 G a b c := by
  have hΔmem : Δ ∈ Set.range (orbit (stabilizer G a) : Ω → Set Ω) := by
    rw [horb]
    simp
  have hΓmem : Γ ∈ Set.range (orbit (stabilizer G a) : Ω → Set Ω) := by
    rw [horb]
    simp
  obtain ⟨b, hb⟩ := hΔmem
  obtain ⟨c, hc⟩ := hΓmem
  refine ⟨b, c, hb, hc, hΩ, fun x => ?_, hb ▸ hΔ, hc ▸ hΓ⟩
  have hx : orbit (stabilizer G a) x ∈ ({{a}, Δ, Γ} : Set (Set Ω)) := by
    rw [← horb]
    exact ⟨x, rfl⟩
  have hxx : x ∈ orbit (stabilizer G a) x := mem_orbit_self x
  rcases hx with h | h | h
  · left
    rw [h] at hxx
    exact hxx
  · right
    left
    rw [h, ← hb] at hxx
    exact hxx
  · right
    right
    rw [h, ← hc] at hxx
    exact hxx

end Rank3

section Count

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite Ω] [IsPretransitive G Ω]

theorem ncard_fiber_eq (r : Ω → Ω → Prop) (hr : ∀ (g : G) (x y : Ω), r (g • x) (g • y) ↔ r x y)
    (x y : Ω) : {z | r x z}.ncard = {z | r z y}.ncard := by
  classical
  have := Fintype.ofFinite Ω
  have h1 : ∀ x x' : Ω, {z | r x z}.ncard = {z | r x' z}.ncard := by
    intro x x'
    obtain ⟨g, rfl⟩ := exists_smul_eq G x x'
    have : {z | r (g • x) z} = (g • ·) '' {z | r x z} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · intro hz
        exact ⟨g⁻¹ • z, (hr g x (g⁻¹ • z)).1 (by rwa [smul_inv_smul]), smul_inv_smul g z⟩
      · rintro ⟨w, hw, rfl⟩
        exact (hr g x w).2 hw
    rw [this, Set.ncard_image_of_injective _ (MulAction.injective g)]
  have h2 : ∀ y y' : Ω, {z | r z y}.ncard = {z | r z y'}.ncard := by
    intro y y'
    obtain ⟨g, rfl⟩ := exists_smul_eq G y y'
    have : {z | r z (g • y)} = (g • ·) '' {z | r z y} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · intro hz
        exact ⟨g⁻¹ • z, (hr g (g⁻¹ • z) y).1 (by rwa [smul_inv_smul]), smul_inv_smul g z⟩
      · rintro ⟨w, hw, rfl⟩
        exact (hr g w y).2 hw
    rw [this, Set.ncard_image_of_injective _ (MulAction.injective g)]
  have key : ∑ x : Ω, {z | r x z}.ncard = ∑ y : Ω, {z | r z y}.ncard := by
    simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
    exact Finset.sum_comm
  have e1 : ∑ x' : Ω, {z | r x' z}.ncard = Fintype.card Ω * {z | r x z}.ncard := by
    rw [Finset.sum_congr rfl fun x' _ => h1 x' x, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have e2 : ∑ y' : Ω, {z | r z y'}.ncard = Fintype.card Ω * {z | r z y}.ncard := by
    rw [Finset.sum_congr rfl fun y' _ => h2 y' y, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [e1, e2] at key
  exact Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨x⟩) key

variable {a b c : Ω}

theorem Rank3.exists_swap (D : Rank3 G a b c) : ∃ τ : G, τ • a = b ∧ τ • b = a := by
  classical
  have hrow : {z | Orb G a b a z} = orbit (stabilizer G a) b := by
    ext z
    exact orb_a_iff
  have hcol := ncard_fiber_eq (G := G) (Orb G a b) (fun g x y => orb_smul g) a a
  rw [hrow, D.ncard_Δ] at hcol
  have hTstab : ∀ (s : stabilizer G a) (z : Ω), Orb G a b z a → Orb G a b (s • z) a := by
    rintro s z ⟨g, hg1, hg2⟩
    refine ⟨(s : G) * g, ?_, ?_⟩
    · rw [mul_smul, hg1]
      rfl
    · rw [mul_smul, hg2]
      exact mem_stabilizer_iff.1 s.2
  have hTsub : {z | Orb G a b z a} ⊆ orbit (stabilizer G a) b := by
    intro z hz
    rcases D.cover z with hza | hzΔ | hzΓ
    · rw [hza] at hz
      obtain ⟨g, hg1, hg2⟩ := hz
      exact absurd (MulAction.injective g (hg2.trans hg1.symm)) D.b_ne_a
    · exact hzΔ
    · exfalso
      have hsub : orbit (stabilizer G a) c ⊆ {z | Orb G a b z a} := by
        rw [← orbit_eq_iff.2 hzΓ]
        rintro w ⟨s, rfl⟩
        exact hTstab s z hz
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [D.ncard_Γ, ← hcol] at this
      omega
  have hTeq : {z | Orb G a b z a} = orbit (stabilizer G a) b :=
    Set.eq_of_subset_of_ncard_le hTsub (by rw [D.ncard_Δ]; exact hcol.le) (Set.toFinite _)
  have hb : b ∈ {z | Orb G a b z a} := hTeq ▸ mem_orbit_self b
  obtain ⟨τ, h1, h2⟩ := hb
  exact ⟨τ, h1, h2⟩

end Count

section GraphFacts

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω}

abbrev rGraph (G : Type u) {Ω : Type v} [Group G] [MulAction G Ω] (a b : Ω) : SimpleGraph Ω :=
  walesGraph G a (orbit (stabilizer G a) b)

theorem rGraph_adj_iff (hτ : ∃ τ : G, τ • a = b ∧ τ • b = a) (hba : b ≠ a) {x y : Ω} :
    (rGraph G a b).Adj x y ↔ Orb G a b x y := by
  rw [rGraph, walesGraph_adj]
  constructor
  · rintro ⟨-, g, b', ⟨s, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨g * s, ?_, ?_⟩
      · rw [mul_smul, mem_stabilizer_iff.1 s.2]
      · rw [mul_smul]
        rfl
    · obtain ⟨τ, h1, h2⟩ := hτ
      refine ⟨g * s * τ, ?_, ?_⟩
      · rw [mul_smul, mul_smul, h1]
        rfl
      · rw [mul_smul, mul_smul, h2, mem_stabilizer_iff.1 s.2]
  · rintro ⟨g, rfl, rfl⟩
    exact ⟨fun h => hba (MulAction.injective g h).symm, g, b, mem_orbit_self b, Or.inl ⟨rfl, rfl⟩⟩

variable [Finite Ω] [IsPretransitive G Ω] (D : Rank3 G a b c)

include D

namespace Rank3

theorem adj_iff {x y : Ω} : (rGraph G a b).Adj x y ↔ Orb G a b x y :=
  rGraph_adj_iff D.exists_swap D.b_ne_a

theorem adj_smul (g : G) {x y : Ω} :
    (rGraph G a b).Adj (g • x) (g • y) ↔ (rGraph G a b).Adj x y := by
  rw [D.adj_iff, D.adj_iff, orb_smul]

theorem adj_a {y : Ω} : (rGraph G a b).Adj a y ↔ y ∈ orbit (stabilizer G a) b := by
  rw [D.adj_iff, orb_a_iff]

theorem ncard_neighbors (x : Ω) : {y | (rGraph G a b).Adj x y}.ncard = 22 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G a x
  have : {y | (rGraph G a b).Adj (g • a) y} = (g • ·) '' orbit (stabilizer G a) b := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
      rw [← D.adj_a, ← D.adj_smul g, smul_inv_smul]
      exact h
    · rintro ⟨w, hw, rfl⟩
      exact (D.adj_smul g).2 ((D.adj_a).2 hw)
  rw [this, Set.ncard_image_of_injective _ (MulAction.injective g), D.ncard_Δ]

theorem not_forall_adj :
    ¬ ∀ x ∈ orbit (stabilizer G a) b, ∀ y ∈ orbit (stabilizer G a) b, x ≠ y →
      (rGraph G a b).Adj x y := by
  intro h
  set S : Set Ω := insert a (orbit (stabilizer G a) b) with hS
  have hSc : S.ncard = 23 := by
    rw [hS, Set.ncard_insert_of_notMem D.a_notMem_Δ (Set.toFinite _), D.ncard_Δ]
  have hcn : ∀ x ∈ S, {y | y = x ∨ (rGraph G a b).Adj x y} = S := by
    intro x hx
    rcases hx with rfl | hxΔ
    · ext y
      simp only [Set.mem_ofPred_eq, hS, Set.mem_insert_iff, D.adj_a]
    · have hsub : S \ {x} ⊆ {y | (rGraph G a b).Adj x y} := by
        rintro y ⟨hyS, hyx⟩
        rcases hyS with rfl | hyΔ
        · exact ((D.adj_a).2 hxΔ).symm
        · exact h x hxΔ y hyΔ (fun e => hyx (e ▸ rfl))
      have hcard : (S \ {x}).ncard = 22 := by
        rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_insert_of_mem _ hxΔ), hSc]
      have heq : S \ {x} = {y | (rGraph G a b).Adj x y} :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, D.ncard_neighbors]) (Set.toFinite _)
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro (rfl | hy)
        · exact Set.mem_insert_of_mem _ hxΔ
        · have : y ∈ S \ {x} := heq ▸ hy
          exact this.1
      · intro hy
        by_cases hyx : y = x
        · exact Or.inl hyx
        · exact Or.inr (show y ∈ {y | (rGraph G a b).Adj x y} from
            heq ▸ (⟨hy, hyx⟩ : y ∈ S \ {x}))
  have hblock : IsBlock G S := by
    rw [isBlock_iff_smul_eq_smul_of_nonempty]
    rintro g₁ g₂ ⟨z, hz1, hz2⟩
    have key : ∀ g : G, z ∈ g • S → g • S = {y | y = z ∨ (rGraph G a b).Adj z y} := by
      intro g hz
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hz
      have hc := hcn _ hz
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem, ← hc]
      simp only [Set.mem_ofPred_eq]
      rw [D.adj_smul g⁻¹, (MulAction.injective g⁻¹).eq_iff]
    rw [key g₁ hz1, key g₂ hz2]
  have hdvd := hblock.ncard_dvd_card ⟨a, Set.mem_insert _ _⟩
  rw [hSc, D.card_Ω] at hdvd
  omega

end Rank3

end GraphFacts

end CFSG.Sporadic.Recognition.HSWales
