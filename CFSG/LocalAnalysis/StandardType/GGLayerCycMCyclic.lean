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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.StandardType.LayerCycM

@[expose] def PSubCyclic (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ S : Subgroup G, IsPGroup p S → IsCyclic S

variable {p : ℕ}

theorem PSubCyclic.of_isCyclic {G : Type*} [Group G] [IsCyclic G] : PSubCyclic p G :=
  fun _ _ => inferInstance

theorem PSubCyclic.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : PSubCyclic p H) : PSubCyclic p G := by
  intro S hS
  haveI : IsCyclic (S.map f) := h _ (hS.map f)
  exact isCyclic_of_surjective (S.equivMapOfInjective f hf).symm
    (S.equivMapOfInjective f hf).symm.surjective

theorem PSubCyclic.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : PSubCyclic p G) : PSubCyclic p H :=
  PSubCyclic.of_injective e.symm.toMonoidHom e.symm.injective h

theorem PSubCyclic.of_surjective {M Z : Type*} [Group M] [Finite M] [Group Z] (f : M →* Z)
    (hf : Function.Surjective f) (hp : p.Prime) (h : PSubCyclic p M) : PSubCyclic p Z := by
  intro S hS
  haveI := Fact.mk hp
  set T : Subgroup M := S.comap f with hT
  let g : T →* S := (f.comp T.subtype).codRestrict S fun t => t.2
  have hg : Function.Surjective g := by
    rintro ⟨s, hs⟩
    obtain ⟨m, hm⟩ := hf s
    exact ⟨⟨m, by rw [hT, Subgroup.mem_comap, hm]; exact hs⟩, Subtype.ext hm⟩
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  set Q := P.mapSurjective hg with hQ
  have hQtop : (Q : Subgroup S) = ⊤ := (Q.is_maximal' (hS.to_subgroup ⊤) le_top).symm
  haveI : IsCyclic ((P : Subgroup T).map T.subtype) := h _ (P.isPGroup'.map T.subtype)
  haveI : IsCyclic (P : Subgroup T) :=
    isCyclic_of_surjective ((P : Subgroup T).equivMapOfInjective T.subtype
      T.subtype_injective).symm (MulEquiv.surjective _)
  have hsurj : Function.Surjective (g.comp (P : Subgroup T).subtype) := by
    intro z
    have hz : z ∈ (Q : Subgroup S) := by rw [hQtop]; exact Subgroup.mem_top z
    rw [hQ, Sylow.coe_mapSurjective] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨⟨t, ht⟩, rfl⟩
  exact isCyclic_of_surjective _ hsurj

theorem PSubCyclic.prod_right {A B : Type*} [Group A] [Group B] (hp : p.Prime)
    (hB : ¬ p ∣ Nat.card B) (h : PSubCyclic p A) : PSubCyclic p (A × B) := by
  intro S hS
  let f : S →* A := (MonoidHom.fst A B).comp S.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    obtain ⟨k, hk⟩ := hS s
    have hs1 : (s : A × B).1 = 1 := hs
    have hb : ((s : A × B).2) ^ p ^ k = 1 := by
      have := congrArg (fun x : S => ((x : A × B)).2) hk
      simpa using this
    have hdvd : orderOf (s : A × B).2 ∣ p ^ k := orderOf_dvd_of_pow_eq_one hb
    have hdvd' : orderOf (s : A × B).2 ∣ Nat.card B := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card B) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hB)
    have h1 : orderOf (s : A × B).2 = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hdvd'
    exact Subtype.ext (Prod.ext hs1 (orderOf_eq_one_iff.1 h1))
  have hr : IsPGroup p f.range := hS.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : IsCyclic f.range := h _ hr
  exact isCyclic_of_surjective (MonoidHom.ofInjective hf).symm
    (MonoidHom.ofInjective hf).symm.surjective

theorem PSubCyclic.prod_left {A B : Type*} [Group A] [Group B] (hp : p.Prime)
    (hB : ¬ p ∣ Nat.card B) (h : PSubCyclic p A) : PSubCyclic p (B × A) :=
  PSubCyclic.of_mulEquiv (MulEquiv.prodComm) (PSubCyclic.prod_right hp hB h)

theorem natCard_multiplicative_zmod (m : ℕ) : Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m), Nat.card_zmod]

theorem psubCyclic_zmod_quad_fst (hp : p.Prime) (a₁ : ℕ) {a₂ e₁ e₂ : ℕ} (h2 : ¬ p ∣ a₂)
    (h3 : ¬ p ∣ e₁) (h4 : ¬ p ∣ e₂) :
    PSubCyclic p ((Multiplicative (ZMod a₁) × Multiplicative (ZMod a₂)) ×
      (Multiplicative (ZMod e₁) × Multiplicative (ZMod e₂))) := by
  have hX : PSubCyclic p (Multiplicative (ZMod a₁) × Multiplicative (ZMod a₂)) :=
    PSubCyclic.prod_right hp (by rwa [natCard_multiplicative_zmod]) PSubCyclic.of_isCyclic
  refine PSubCyclic.prod_right hp ?_ hX
  rw [Nat.card_prod, natCard_multiplicative_zmod, natCard_multiplicative_zmod]
  intro hd
  rcases hp.dvd_mul.1 hd with hd | hd
  · exact h3 hd
  · exact h4 hd

theorem psubCyclic_zmod_quad_thd (hp : p.Prime) {a₁ a₂ e₂ : ℕ} (e₁ : ℕ) (h1 : ¬ p ∣ a₁)
    (h2 : ¬ p ∣ a₂) (h4 : ¬ p ∣ e₂) :
    PSubCyclic p ((Multiplicative (ZMod a₁) × Multiplicative (ZMod a₂)) ×
      (Multiplicative (ZMod e₁) × Multiplicative (ZMod e₂))) := by
  have hY : PSubCyclic p (Multiplicative (ZMod e₁) × Multiplicative (ZMod e₂)) :=
    PSubCyclic.prod_right hp (by rwa [natCard_multiplicative_zmod]) PSubCyclic.of_isCyclic
  refine PSubCyclic.prod_left hp ?_ hY
  rw [Nat.card_prod, natCard_multiplicative_zmod, natCard_multiplicative_zmod]
  intro hd
  rcases hp.dvd_mul.1 hd with hd | hd
  · exact h1 hd
  · exact h2 hd

end CFSG.StandardType.LayerCycM

end
