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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.F6.GoldAmS

variable {E : Type*} [Group E]

structure ProdStr (A K : Subgroup E) (ε : E) : Prop where
  le : K ≤ A
  mem : ε ∈ A
  sq : ε * ε = 1
  central : ∀ g ∈ A, g * ε = ε * g
  not_mem : ε ∉ K
  split : ∀ g ∈ A, g ∈ K ∨ ε * g ∈ K

namespace ProdStr

variable {A K : Subgroup E} {ε : E}

theorem zmod_cases : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  decide

def epsHom (h : ProdStr A K ε) : Multiplicative (ZMod 2) →* ↥A :=
  MonoidHom.mk' (fun e => if e = 1 then 1 else ⟨ε, h.mem⟩) (by
    intro a b
    rcases zmod_cases a with rfl | rfl <;> rcases zmod_cases b with rfl | rfl
    · simp
    · simp
    · simp
    · have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
        decide
      have h2 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
      simp only [h1, h2, ite_true, ite_false]
      exact Subtype.ext h.sq.symm)

theorem epsHom_one (h : ProdStr A K ε) : h.epsHom (Multiplicative.ofAdd 1) = ⟨ε, h.mem⟩ := by
  have h2 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
  simp [epsHom, h2]

def iotaHom (h : ProdStr A K ε) : Multiplicative (ZMod 2) × ↥K →* ↥A :=
  MonoidHom.noncommCoprod h.epsHom (Subgroup.inclusion h.le) (by
    intro e k
    rcases zmod_cases e with rfl | rfl
    · simp
    · rw [h.epsHom_one]
      exact Subtype.ext (h.central k.1 (h.le k.2)).symm)

theorem iotaHom_apply (h : ProdStr A K ε) (e : Multiplicative (ZMod 2)) (k : ↥K) :
    h.iotaHom (e, k) = h.epsHom e * Subgroup.inclusion h.le k := by
  unfold iotaHom
  rw [MonoidHom.noncommCoprod_apply]

noncomputable def iota (h : ProdStr A K ε) : Multiplicative (ZMod 2) × ↥K ≃* ↥A :=
  MulEquiv.ofBijective h.iotaHom
    ⟨by
      rw [injective_iff_map_eq_one]
      rintro ⟨e, k⟩ hek
      rw [iotaHom_apply] at hek
      rcases zmod_cases e with rfl | rfl
      · simp only [map_one, one_mul] at hek
        have h1 := congrArg Subtype.val hek
        have : k = 1 := Subtype.ext (by simpa using h1)
        simp [this]
      · rw [h.epsHom_one] at hek
        have h1 := congrArg Subtype.val hek
        simp only [Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inclusion] at h1
        exfalso
        apply h.not_mem
        have : (k : E) = ε := by
          calc (k : E) = ε * ε * k := by rw [h.sq, one_mul]
            _ = ε * (ε * k) := by rw [mul_assoc]
            _ = ε := by rw [h1, mul_one]
        rw [← this]
        exact k.2,
     by
      intro g
      rcases h.split g.1 g.2 with hg | hg
      · refine ⟨(1, ⟨g.1, hg⟩), ?_⟩
        rw [iotaHom_apply]
        apply Subtype.ext
        simp
      · refine ⟨(Multiplicative.ofAdd 1, ⟨ε * g.1, hg⟩), ?_⟩
        rw [iotaHom_apply, h.epsHom_one]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
        rw [← mul_assoc, h.sq, one_mul]⟩

theorem iota_apply_one (h : ProdStr A K ε) (k : ↥K) : h.iota (1, k) = ⟨k, h.le k.2⟩ := by
  show h.iotaHom (1, k) = _
  rw [iotaHom_apply]
  apply Subtype.ext
  simp

theorem iota_apply_eps (h : ProdStr A K ε) :
    h.iota (Multiplicative.ofAdd 1, 1) = ⟨ε, h.mem⟩ := by
  show h.iotaHom (Multiplicative.ofAdd 1, 1) = _
  rw [iotaHom_apply, h.epsHom_one]
  apply Subtype.ext
  simp

variable {E' : Type*} [Group E'] {A' K' : Subgroup E'} {ε' : E'}

noncomputable def extIso (h : ProdStr A K ε) (h' : ProdStr A' K' ε') (φ : ↥K ≃* ↥K') :
    ↥A ≃* ↥A' :=
  h.iota.symm.trans (((MulEquiv.refl (Multiplicative (ZMod 2))).prodCongr φ).trans h'.iota)

theorem extIso_apply_K (h : ProdStr A K ε) (h' : ProdStr A' K' ε') (φ : ↥K ≃* ↥K') {k : E}
    (hk : k ∈ K) : ((h.extIso h' φ ⟨k, h.le hk⟩ : ↥A') : E') = φ ⟨k, hk⟩ := by
  have h1 : h.iota.symm ⟨k, h.le hk⟩ = (1, ⟨k, hk⟩) := by
    rw [MulEquiv.symm_apply_eq, h.iota_apply_one]
  show ((h'.iota (((MulEquiv.refl (Multiplicative (ZMod 2))).prodCongr φ)
    (h.iota.symm ⟨k, h.le hk⟩)) : ↥A') : E') = _
  rw [h1]
  show ((h'.iota (1, φ ⟨k, hk⟩) : ↥A') : E') = _
  rw [h'.iota_apply_one]

theorem extIso_apply_eps (h : ProdStr A K ε) (h' : ProdStr A' K' ε') (φ : ↥K ≃* ↥K') :
    ((h.extIso h' φ ⟨ε, h.mem⟩ : ↥A') : E') = ε' := by
  have h1 : h.iota.symm ⟨ε, h.mem⟩ = (Multiplicative.ofAdd 1, 1) := by
    rw [MulEquiv.symm_apply_eq, h.iota_apply_eps]
  show ((h'.iota (((MulEquiv.refl (Multiplicative (ZMod 2))).prodCongr φ)
    (h.iota.symm ⟨ε, h.mem⟩)) : ↥A') : E') = _
  rw [h1]
  show ((h'.iota (Multiplicative.ofAdd 1, φ 1) : ↥A') : E') = _
  rw [show φ 1 = 1 from map_one φ, h'.iota_apply_eps]

theorem extIso_symm (h : ProdStr A K ε) (h' : ProdStr A' K' ε') (φ : ↥K ≃* ↥K') :
    (h.extIso h' φ).symm = h'.extIso h φ.symm := by
  ext a
  rfl

theorem card_eq (h : ProdStr A K ε) : Nat.card A = 2 * Nat.card K := by
  have h1 := Nat.card_congr h.iota.toEquiv
  rw [Nat.card_prod] at h1
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h2] at h1
  exact h1.symm

theorem inf_right (h : ProdStr A K ε) {A' : Subgroup E} (hA' : A' ≤ A) (hε : ε ∈ A') :
    ProdStr A' (K ⊓ A') ε where
  le := inf_le_right
  mem := hε
  sq := h.sq
  central := fun g hg => h.central g (hA' hg)
  not_mem := fun hm => h.not_mem hm.1
  split := by
    intro g hg
    rcases h.split g (hA' hg) with h1 | h1
    · exact Or.inl ⟨h1, hg⟩
    · exact Or.inr ⟨h1, Subgroup.mul_mem _ hε hg⟩

theorem of_hom (A : Subgroup E) {ε : E} (hε : ε ∈ A) (hsq : ε * ε = 1)
    (hc : ∀ g ∈ A, g * ε = ε * g) (V : ↥A →* Multiplicative (ZMod 2))
    (hV : V ⟨ε, hε⟩ = Multiplicative.ofAdd 1) : ProdStr A (V.ker.map A.subtype) ε where
  le := Subgroup.map_subtype_le _
  mem := hε
  sq := hsq
  central := hc
  not_mem := by
    rintro ⟨k, hk, hke⟩
    have hk' : k = ⟨ε, hε⟩ := Subtype.ext hke
    rw [hk'] at hk
    have h2 : V ⟨ε, hε⟩ = 1 := hk
    rw [hV] at h2
    exact absurd h2 (by decide)
  split := by
    intro g hg
    rcases zmod_cases (V ⟨g, hg⟩) with h1 | h1
    · exact Or.inl ⟨⟨g, hg⟩, h1, rfl⟩
    · right
      refine ⟨⟨ε, hε⟩ * ⟨g, hg⟩, ?_, rfl⟩
      show V (⟨ε, hε⟩ * ⟨g, hg⟩) = 1
      rw [map_mul, hV, h1]
      decide

end ProdStr

section Generic

variable {E : Type*} [Group E]

theorem comm_of_exp_two {Q : Subgroup E} (hQ : ∀ q ∈ Q, q * q = 1) {q r : E} (hq : q ∈ Q)
    (hr : r ∈ Q) : q * r = r * q := by
  have h1 : (q * r)⁻¹ = q * r := inv_eq_of_mul_eq_one_right (hQ _ (Subgroup.mul_mem _ hq hr))
  have h2 : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hQ q hq)
  have h3 : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hQ r hr)
  rw [← h1, mul_inv_rev, h2, h3]

theorem mem_of_card_le_four {R : Subgroup E} [Finite R] (hR : Nat.card R ≤ 4) {u v w : E}
    (hu : u ∈ R) (hv : v ∈ R) (hw : w ∈ R) (h1u : (1 : E) ≠ u) (h1v : (1 : E) ≠ v)
    (h1w : (1 : E) ≠ w) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∀ r ∈ R, r = 1 ∨ r = u ∨ r = v ∨ r = w := by
  classical
  have hsub : ({1, u, v, w} : Set E) ⊆ (R : Set E) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [R.one_mem, hu, hv, hw]
  have hn1 : (1 : E) ∉ ({u, v, w} : Set E) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1u, h1v, h1w⟩
  have hn2 : u ∉ ({v, w} : Set E) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨huv, huw⟩
  have h4 : ({1, u, v, w} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2, Set.ncard_pair hvw]
  have hR' : (R : Set E).ncard ≤ ({1, u, v, w} : Set E).ncard := by
    rw [h4, ← Nat.card_coe_set_eq]
    exact hR
  have heq := Set.eq_of_subset_of_ncard_le hsub hR' (Set.toFinite _)
  intro r hr
  have : r ∈ ({1, u, v, w} : Set E) := by rw [heq]; exact hr
  simpa using this

theorem four_le_card {R : Subgroup E} [Finite R] {u v w : E}
    (hu : u ∈ R) (hv : v ∈ R) (hw : w ∈ R) (h1u : (1 : E) ≠ u) (h1v : (1 : E) ≠ v)
    (h1w : (1 : E) ≠ w) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : 4 ≤ Nat.card R := by
  classical
  have hsub : ({1, u, v, w} : Set E) ⊆ (R : Set E) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [R.one_mem, hu, hv, hw]
  have hn1 : (1 : E) ∉ ({u, v, w} : Set E) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1u, h1v, h1w⟩
  have hn2 : u ∉ ({v, w} : Set E) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨huv, huw⟩
  have h4 : ({1, u, v, w} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2, Set.ncard_pair hvw]
  have h5 : (R : Set E).ncard = Nat.card R := (Nat.card_coe_set_eq (R : Set E)).symm
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h4, h5] at this
  exact this

theorem mem_or_mul_mem_of_card {A K : Subgroup E} [Finite A] (hKA : K ≤ A)
    (hA : Nat.card A = 2 * Nat.card K) {b g : E} (hb : b ∈ A) (hbK : b ∉ K) (hg : g ∈ A) :
    g ∈ K ∨ g * b ∈ K := by
  have hfinK : Finite K := Finite.of_injective (Subgroup.inclusion hKA)
    (Subgroup.inclusion_injective hKA)
  have h1 := Subgroup.index_mul_card (K.subgroupOf A)
  have h2 : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have hpos : 0 < Nat.card K := Nat.card_pos
  rw [h2, hA] at h1
  have hidx : (K.subgroupOf A).index = 2 := by
    have : (K.subgroupOf A).index * Nat.card K = 2 * Nat.card K := h1
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨g, hg⟩ : A)) (b := ⟨b, hb⟩)
  by_cases hgK : g ∈ K
  · exact Or.inl hgK
  · right
    have hbK' : (⟨b, hb⟩ : A) ∉ K.subgroupOf A := hbK
    have hgK' : (⟨g, hg⟩ : A) ∉ K.subgroupOf A := hgK
    exact key.2 (iff_of_false hgK' hbK')

end Generic

end CFSG.Quasithin.F6.GoldAmS
