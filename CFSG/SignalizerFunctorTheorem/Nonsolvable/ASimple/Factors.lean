module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem exists_aSimple_factors [Finite G] {A K : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x)
    (hmin : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal →
      A ≤ Subgroup.normalizer (N : Set G) → N = ⊥ ∨ N = K) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ (∀ i, S i ≤ K) ∧
      (∀ i, ((S i).subgroupOf K).Normal) ∧ (∀ i, IsSimpleGroup (S i)) ∧
      (∀ i, ∃ x ∈ S i, ∃ y ∈ S i, x * y ≠ y * x) ∧
      (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) ∧
      (∀ i j, ∃ a ∈ A, S j = (S i).map (MulAut.conj a).toMonoidHom) ∧ (⨆ i, S i) = K := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = A ⊔ K := ⟨_, rfl⟩
  have hAH : A ≤ H := hH ▸ le_sup_left
  have hKH : K ≤ H := hH ▸ le_sup_right
  have hNnormal : (K.subgroupOf H).Normal :=
    hH ▸ Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  have hdecomp : ∀ h ∈ H, ∃ a ∈ A, ∃ k ∈ K, a * k = h := by
    intro h hh
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right A K hA
    rw [← hH] at hmul
    have hh' : h ∈ (H : Set G) := hh
    rw [hmul] at hh'
    exact hh'
  have hN1 : K.subgroupOf H ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    refine hxy ?_
    have hx1 : x = 1 := by
      have hx' : (⟨x, hKH hx⟩ : H) ∈ K.subgroupOf H := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact congrArg Subtype.val hx'
    rw [hx1, one_mul, mul_one]
  have hminH : ∀ M : Subgroup H, M.Normal → M ≤ K.subgroupOf H →
      M = ⊥ ∨ M = K.subgroupOf H := by
    intro M hM hMN
    have hMK : M.map H.subtype ≤ K := by
      rintro _ ⟨m, hm, rfl⟩
      exact hMN hm
    have hMnorm : ((M.map H.subtype).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hMK]
      rintro _ k ⟨m, hm, rfl⟩ hk
      exact ⟨⟨k, hKH hk⟩ * m * ⟨k, hKH hk⟩⁻¹, hM.conj_mem m hm _, rfl⟩
    have hAM : A ≤ Subgroup.normalizer ((M.map H.subtype : Subgroup G) : Set G) := by
      have hfwd : ∀ a ∈ A, ∀ x ∈ M.map H.subtype, a * x * a⁻¹ ∈ M.map H.subtype := by
        rintro a ha _ ⟨m, hm, rfl⟩
        exact ⟨⟨a, hAH ha⟩ * m * ⟨a, hAH ha⟩⁻¹, hM.conj_mem m hm _, rfl⟩
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      refine fun x => ⟨hfwd a ha x, fun hx => ?_⟩
      simpa [mul_assoc] using hfwd a⁻¹ (inv_mem ha) _ hx
    rcases hmin _ hMK hMnorm hAM with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
    · refine Or.inr ?_
      rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective M, h]
      rfl
  obtain ⟨r, S, hr, hSN, hSsimple, hSconj, hSnormal, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNnormal hN1 hminH
  have hS'K : ∀ i, (S i).map H.subtype ≤ K := by
    rintro i _ ⟨s, hs, rfl⟩
    exact hSN i hs
  have hSnorm : ∀ i, ∀ s ∈ S i, ∀ k : H, (k : G) ∈ K → k * s * k⁻¹ ∈ S i := fun i s hs k hk =>
    (Subgroup.normal_subgroupOf_iff (hSN i)).mp (hSnormal i) s k hs hk
  have hS'normal : ∀ i, (((S i).map H.subtype).subgroupOf K).Normal := by
    intro i
    rw [Subgroup.normal_subgroupOf_iff (hS'K i)]
    rintro _ k ⟨s, hs, rfl⟩ hk
    exact ⟨⟨k, hKH hk⟩ * s * ⟨k, hKH hk⟩⁻¹, hSnorm i s hs _ hk, rfl⟩
  have hS'simple : ∀ i, IsSimpleGroup ((S i).map H.subtype) := by
    intro i
    have := hSsimple i
    exact ((S i).equivMapOfInjective H.subtype H.subtype_injective).symm.isSimpleGroup
  have hSnc : ∀ i, ∃ x ∈ S i, ∃ y ∈ S i, x * y ≠ y * x := by
    intro i
    by_contra hcon
    push Not at hcon
    have hall : ∀ j, ∀ x ∈ S j, ∀ y ∈ S j, x * y = y * x := by
      intro j x hx y hy
      obtain ⟨g, hg⟩ := hSconj i j
      rw [hg] at hx hy
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hcon x₀ hx₀ y₀ hy₀]
    have hpi : ∀ u v : ((j : Fin r) → S j), u * v = v * u := fun u v =>
      funext fun j => Subtype.ext (hall j _ (u j).2 _ (v j).2)
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    refine hxy ?_
    let nx : K.subgroupOf H := ⟨⟨x, hKH hx⟩, hx⟩
    let ny : K.subgroupOf H := ⟨⟨y, hKH hy⟩, hy⟩
    have hn : nx * ny = ny * nx :=
      e.symm.injective (by rw [map_mul, map_mul, hpi])
    exact congrArg (fun z : K.subgroupOf H => ((z : H) : G)) hn
  have hgen : (⨆ i, (S i).map H.subtype) = K := by
    refine le_antisymm (iSup_le hS'K) fun k hk => ?_
    let n : K.subgroupOf H := ⟨⟨k, hKH hk⟩, hk⟩
    let ψ : ((j : Fin r) → S j) →* G :=
      H.subtype.comp ((K.subgroupOf H).subtype.comp e.toMonoidHom)
    have hψsingle : ∀ (i : Fin r) (s : S i), ψ (Pi.mulSingle i s) = (s : G) := by
      intro i s
      have := he i (Pi.mulSingle i s) fun j hj =>
        Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hj s
      simpa [ψ] using congrArg (fun z : H => (z : G)) this
    have htop : (⊤ : Subgroup ((j : Fin r) → S j)) ≤ (⨆ i, (S i).map H.subtype).comap ψ := by
      rw [← Subgroup.pi_top (f := fun j => ↥(S j)) Set.univ, Subgroup.pi_le_iff]
      intro i
      rintro _ ⟨s, -, rfl⟩
      rw [Subgroup.mem_comap]
      change ψ (Pi.mulSingle i s) ∈ ⨆ i, (S i).map H.subtype
      rw [hψsingle]
      exact le_iSup (fun i => (S i).map H.subtype) i ⟨s, s.2, rfl⟩
    have hmem := htop (Subgroup.mem_top (e.symm n))
    have hψn : ψ (e.symm n) = k := by simp [ψ, n]
    rwa [Subgroup.mem_comap, hψn] at hmem
  have hSc : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x := by
    intro i j hij x hx y hy
    have h1 := he i (Pi.mulSingle i ⟨x, hx⟩) fun l hl =>
      Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hl _
    have h2 := he j (Pi.mulSingle j ⟨y, hy⟩) fun l hl =>
      Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hl _
    have h3 := congrArg (fun z : (j : Fin r) → S j => ((e z : K.subgroupOf H) : H))
      (Pi.mulSingle_commute hij ⟨x, hx⟩ ⟨y, hy⟩).eq
    simp only [map_mul, Pi.mulSingle_eq_same, Subgroup.coe_mul] at h1 h2 h3
    rw [h1, h2] at h3
    exact h3
  refine ⟨r, fun i => (S i).map H.subtype, hr, hS'K, hS'normal, hS'simple, ?_, ?_, ?_, hgen⟩
  · intro i
    obtain ⟨x, hx, y, hy, hxy⟩ := hSnc i
    exact ⟨x, ⟨x, hx, rfl⟩, y, ⟨y, hy, rfl⟩, fun h => hxy (Subtype.ext h)⟩
  · rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hSc i j hij x hx y hy)
  · intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    obtain ⟨a, ha, k, hk, hak⟩ := hdecomp ((g⁻¹ : H) : G) (g⁻¹).2
    refine ⟨a, ha, ?_⟩
    show (S j).map H.subtype = ((S i).map H.subtype).map (MulAut.conj a).toMonoidHom
    have h1 : (S j).map H.subtype =
        ((S i).map H.subtype).map (MulAut.conj ((g⁻¹ : H) : G)).toMonoidHom := by
      rw [hg]
      unfold CFSG.conjugate
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    have h2 : ((S i).map H.subtype).map (MulAut.conj k).toMonoidHom = (S i).map H.subtype := by
      ext x
      refine ⟨?_, fun hx => ⟨k⁻¹ * x * k, ?_, by simp [mul_assoc]⟩⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨⟨k, hKH hk⟩ * s * ⟨k, hKH hk⟩⁻¹, hSnorm i s hs _ hk, rfl⟩
      · obtain ⟨s, hs, rfl⟩ := hx
        exact ⟨⟨k, hKH hk⟩⁻¹ * s * ⟨k, hKH hk⟩, by
          simpa using hSnorm i s hs ⟨k, hKH hk⟩⁻¹ (by simpa using inv_mem hk), rfl⟩
    have h3 : ∀ Q : Subgroup G, Q.map (MulAut.conj (a * k)).toMonoidHom =
        (Q.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      intro Q
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    rw [h1, ← hak, h3, h2]

end CFSG.SignalizerFunctorTheorem.Nonsolvable
