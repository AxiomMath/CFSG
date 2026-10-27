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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis

section CommSpace

variable {k : Type*} [Field k] {D : Type*} [AddCommGroup D] [Module k D]

@[expose] def commSpace (W : Submodule k D) (H : Subgroup (LinearMap.GeneralLinearGroup k D)) :
    Submodule k D :=
  Submodule.span k {v | ∃ h ∈ H, ∃ w ∈ W, (h : Module.End k D) w - w = v}

@[expose] def IsInvariantBy (H : Subgroup (LinearMap.GeneralLinearGroup k D))
    (W : Submodule k D) : Prop :=
  ∀ h ∈ H, ∀ w ∈ W, (h : Module.End k D) w ∈ W

variable {W M : Submodule k D} {H X Y : Subgroup (LinearMap.GeneralLinearGroup k D)}

theorem sub_mem_commSpace {h : LinearMap.GeneralLinearGroup k D} (hh : h ∈ H) {w : D}
    (hw : w ∈ W) : (h : Module.End k D) w - w ∈ commSpace W H :=
  Submodule.subset_span ⟨h, hh, w, hw, rfl⟩

theorem commSpace_le_iff :
    commSpace W H ≤ M ↔ ∀ h ∈ H, ∀ w ∈ W, (h : Module.End k D) w - w ∈ M := by
  rw [commSpace, Submodule.span_le]
  constructor
  · intro h g hg w hw
    exact h ⟨g, hg, w, hw, rfl⟩
  · rintro h _ ⟨g, hg, w, hw, rfl⟩
    exact h g hg w hw

theorem isInvariantBy_commSpace : IsInvariantBy H (commSpace W H) := by
  intro h hh m hm
  have hle : commSpace W H ≤ (commSpace W H).comap (h : Module.End k D) := by
    rw [commSpace_le_iff]
    intro g hg w hw
    rw [Submodule.mem_comap]
    have h1 := Submodule.sub_mem _ (sub_mem_commSpace (H.mul_mem hh hg) hw)
      (sub_mem_commSpace hh hw)
    convert h1 using 1
    rw [map_sub, Units.val_mul, Module.End.mul_apply]
    abel
  exact hle hm

theorem commSpace_le_of_isInvariantBy (hW : IsInvariantBy H W) : commSpace W H ≤ W :=
  commSpace_le_iff.mpr fun h hh w hw => W.sub_mem (hW h hh w hw) hw

theorem commSpace_commSpace_le_comm (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    commSpace (commSpace W X) Y ≤ commSpace (commSpace W Y) X := by
  rw [commSpace_le_iff]
  intro y hy m hm
  have hle : commSpace W X ≤
      (commSpace (commSpace W Y) X).comap ((y : Module.End k D) - 1) := by
    rw [commSpace_le_iff]
    intro x hx w hw
    rw [Submodule.mem_comap]
    have h1 := sub_mem_commSpace hx (sub_mem_commSpace (W := W) hy hw)
    convert h1 using 1
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, ← Module.End.mul_apply,
      ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul, hXY x hx y hy]
    abel
  have h2 := hle hm
  rwa [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at h2

theorem commSpace_le_commSpace_commSpace_of_perfect (hX : ⁅X, X⁆ = X) :
    commSpace W X ≤ commSpace (commSpace W X) X := by
  set M₂ := commSpace (commSpace W X) X
  rw [commSpace_le_iff]
  intro x hx w hw
  let F : X →* Multiplicative (D ⧸ M₂) :=
    { toFun := fun g => Multiplicative.ofAdd (Submodule.Quotient.mk
        (((g : LinearMap.GeneralLinearGroup k D) : Module.End k D) w - w))
      map_one' := by
        simp only [OneMemClass.coe_one, Units.val_one, Module.End.one_apply, sub_self,
          Submodule.Quotient.mk_zero, ofAdd_zero]
      map_mul' := fun g g' => by
        rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
        congr 1
        rw [Submodule.Quotient.eq]
        have h1 := sub_mem_commSpace (W := commSpace W X) g.2 (sub_mem_commSpace g'.2 hw)
        convert h1 using 1
        rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_sub]
        abel }
  have hperf : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  have hker := Abelianization.commutator_subset_ker F
  rw [hperf.commutator_eq_top] at hker
  have h1 : F ⟨x, hx⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : Submodule.Quotient.mk (p := M₂) ((x : Module.End k D) w - w) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [F] using this
  exact (Submodule.Quotient.mk_eq_zero M₂).mp h2

theorem commSpace_le_commSpace_commSpace_of_card [Finite Y] (hY : (Nat.card Y : k) ≠ 0) :
    commSpace W Y ≤ commSpace (commSpace W Y) Y := by
  classical
  let := Fintype.ofFinite Y
  set e : Module.End k D := ∑ y : Y, ((y : LinearMap.GeneralLinearGroup k D) : Module.End k D)
    with he_def
  have he : commSpace W Y ≤ LinearMap.ker e := by
    rw [commSpace_le_iff]
    intro y hy w hw
    have hey : e * (y : Module.End k D) = e := by
      rw [he_def, Finset.sum_mul]
      exact Fintype.sum_equiv (Equiv.mulRight ⟨y, hy⟩) _ _ fun y' => by
        rw [Equiv.coe_mulRight, Subgroup.coe_mul, Units.val_mul]
    rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hey, sub_self]
  intro m hm
  have hem : e m = 0 := he hm
  have hm' : (Nat.card Y : k) • m = -∑ y : Y,
      (((y : LinearMap.GeneralLinearGroup k D) : Module.End k D) m - m) := by
    rw [Finset.sum_sub_distrib, ← LinearMap.sum_apply, ← he_def, hem, zero_sub, neg_neg,
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hm'' : m = (Nat.card Y : k)⁻¹ • -∑ y : Y,
      (((y : LinearMap.GeneralLinearGroup k D) : Module.End k D) m - m) := by
    rw [← hm', smul_smul, inv_mul_cancel₀ hY, one_smul]
  rw [hm'']
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _
    (Submodule.sum_mem _ fun y _ => sub_mem_commSpace y.2 hm))

end CommSpace

section Codim

variable {k : Type*} [Field k] {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module k E]
  [FiniteDimensional k E] {ρ : Representation k G E}

omit [FiniteDimensional k E] in
theorem finrank_invariants_toRepresentation (E₀ : Subrepresentation ρ) :
    Module.finrank k E₀.toRepresentation.invariants =
      Module.finrank k ↥(ρ.invariants ⊓ E₀.toSubmodule) := by
  have hmap : E₀.toRepresentation.invariants.map E₀.toSubmodule.subtype =
      ρ.invariants ⊓ E₀.toSubmodule := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Submodule.mem_inf.mpr ⟨(ρ.mem_invariants _).mpr fun g =>
        congrArg Subtype.val ((E₀.toRepresentation.mem_invariants _).mp hw g), w.2⟩
    · intro hv
      obtain ⟨hv, hvE⟩ := Submodule.mem_inf.mp hv
      exact ⟨⟨v, hvE⟩, (E₀.toRepresentation.mem_invariants _).mpr fun g =>
        Subtype.ext ((ρ.mem_invariants _).mp hv g), rfl⟩
  rw [← Submodule.finrank_map_subtype_eq E₀.toSubmodule E₀.toRepresentation.invariants, hmap]

theorem codim_add_codim_le_codim (E₀ : Subrepresentation ρ) :
    (Module.finrank k E₀.toSubmodule - Module.finrank k E₀.toRepresentation.invariants) +
        (Module.finrank k (E ⧸ E₀.toSubmodule) - Module.finrank k E₀.quotient.invariants) ≤
      Module.finrank k E - Module.finrank k ρ.invariants := by
  let P : Submodule k E :=
    { carrier := {v | ∀ g, ρ g v - v ∈ E₀.toSubmodule}
      add_mem' := fun {v w} hv hw g => by
        rw [map_add, add_sub_add_comm]
        exact E₀.toSubmodule.add_mem (hv g) (hw g)
      zero_mem' := fun g => by rw [map_zero, sub_zero]; exact E₀.toSubmodule.zero_mem
      smul_mem' := fun c v hv g => by
        rw [map_smul, ← smul_sub]
        exact E₀.toSubmodule.smul_mem c (hv g) }
  have hE₀P : E₀.toSubmodule ≤ P := fun v hv g =>
    E₀.toSubmodule.sub_mem (E₀.apply_mem_toSubmodule g hv) hv
  have hIP : ρ.invariants ≤ P := fun v hv g => by
    rw [(ρ.mem_invariants v).mp hv g, sub_self]
    exact E₀.toSubmodule.zero_mem
  have hQ : E₀.quotient.invariants = P.map E₀.toSubmodule.mkQ := by
    ext x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      refine ⟨v, fun g => ?_, rfl⟩
      have h1 : Submodule.Quotient.mk (p := E₀.toSubmodule) (ρ g v) =
          Submodule.Quotient.mk v := (E₀.quotient.mem_invariants _).mp hx g
      exact (Submodule.Quotient.eq _).mp h1
    · rintro ⟨w, hw, hwv⟩
      refine (E₀.quotient.mem_invariants _).mpr fun g => ?_
      rw [← hwv, Submodule.mkQ_apply]
      change Submodule.Quotient.mk (p := E₀.toSubmodule) (ρ g w) = Submodule.Quotient.mk w
      rw [Submodule.Quotient.eq]
      exact hw g
  have hPdim : Module.finrank k (P.map E₀.toSubmodule.mkQ) + Module.finrank k E₀.toSubmodule =
      Module.finrank k P := by
    have h := LinearMap.finrank_range_add_finrank_ker (E₀.toSubmodule.mkQ ∘ₗ P.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ,
      (Submodule.comapSubtypeEquivOfLe hE₀P).finrank_eq] at h
    exact h
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq ρ.invariants E₀.toSubmodule
  have hsupP : Module.finrank k ↥(ρ.invariants ⊔ E₀.toSubmodule) ≤ Module.finrank k P :=
    Submodule.finrank_mono (sup_le hIP hE₀P)
  have hquot := Submodule.finrank_quotient_add_finrank E₀.toSubmodule
  have hinf : Module.finrank k ↥(ρ.invariants ⊓ E₀.toSubmodule) ≤
      Module.finrank k E₀.toSubmodule := Submodule.finrank_mono inf_le_right
  have hPE : Module.finrank k P ≤ Module.finrank k E := Submodule.finrank_le P
  rw [finrank_invariants_toRepresentation, hQ]
  omega

theorem codim_section_le_codim (E₁ : Subrepresentation ρ)
    (E₂ : Subrepresentation E₁.toRepresentation) :
    Module.finrank k (E₁.toSubmodule ⧸ E₂.toSubmodule) - Module.finrank k E₂.quotient.invariants ≤
      Module.finrank k E - Module.finrank k ρ.invariants := by
  have h1 := codim_add_codim_le_codim E₂
  have h2 := codim_add_codim_le_codim E₁
  omega

end Codim

section Head

variable {D : Type*} [AddCommGroup D] [Module (ZMod 2) D]

@[expose] def IsMaxInvariantIn (X Y A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D))
    (U N : Submodule (ZMod 2) D) : Prop :=
  N ≤ U ∧ N ≠ U ∧ IsInvariantBy X N ∧ IsInvariantBy Y N ∧ IsInvariantBy A N ∧
    ∀ N' : Submodule (ZMod 2) D, N ≤ N' → N' ≤ U → IsInvariantBy X N' → IsInvariantBy Y N' →
      IsInvariantBy A N' → N' = N ∨ N' = U

@[expose] def IsMixedHead (X Y A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D))
    (U : Submodule (ZMod 2) D) : Prop :=
  IsInvariantBy X U ∧ IsInvariantBy Y U ∧ IsInvariantBy A U ∧ commSpace U X = U ∧
    commSpace U Y = U ∧ (U ≠ ⊥ → ∃ N, IsMaxInvariantIn X Y A U N) ∧
    ∀ N, IsMaxInvariantIn X Y A U N →
      (∃ x ∈ X, ∃ u ∈ U, (x : Module.End (ZMod 2) D) u - u ∉ N) ∧
      (∃ y ∈ Y, ∃ u ∈ U, (y : Module.End (ZMod 2) D) u - u ∉ N) ∧
      (IsSimpleGroup X → ∀ x ∈ X, (∀ u ∈ U, (x : Module.End (ZMod 2) D) u - u ∈ N) → x = 1) ∧
      (IsSimpleGroup Y → ∀ y ∈ Y, (∀ u ∈ U, (y : Module.End (ZMod 2) D) u - u ∈ N) → y = 1)

variable {X Y A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D)}

theorem isInvariantBy_commSpace_of_normalizer {W : Submodule (ZMod 2) D}
    {H B : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D)}
    (hB : B ≤ Subgroup.normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) D)))
    (hW : IsInvariantBy B W) : IsInvariantBy B (commSpace W H) := by
  intro b hb m hm
  have hle : commSpace W H ≤ (commSpace W H).comap (b : Module.End (ZMod 2) D) := by
    rw [commSpace_le_iff]
    intro h hh w hw
    rw [Submodule.mem_comap]
    have hbh : b * h * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hB hb) h).mp hh
    have h1 := sub_mem_commSpace hbh (hW b hb w hw)
    have hbinv : ((b⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D) : Module.End (ZMod 2) D)
        ((b : Module.End (ZMod 2) D) w) = w := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    convert h1 using 1
    rw [map_sub, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hbinv]
  exact hle hm

theorem isInvariantBy_commSpace_of_commute {W : Submodule (ZMod 2) D}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hW : IsInvariantBy X W) :
    IsInvariantBy X (commSpace W Y) := by
  intro x hx m hm
  have hle : commSpace W Y ≤ (commSpace W Y).comap (x : Module.End (ZMod 2) D) := by
    rw [commSpace_le_iff]
    intro y hy w hw
    rw [Submodule.mem_comap]
    have h1 := sub_mem_commSpace hy (hW x hx w hw)
    convert h1 using 1
    rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul,
      hXY x hx y hy]
  exact hle hm

theorem isInvariantBy_bot (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D)) :
    IsInvariantBy H (⊥ : Submodule (ZMod 2) D) := fun h _ w hw => by
  rw [(Submodule.mem_bot _).mp hw, map_zero]
  exact Submodule.zero_mem _

theorem isMixedHead_commSpace [FiniteDimensional (ZMod 2) D]
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hYY : ∀ W : Submodule (ZMod 2) D, commSpace W Y ≤ commSpace (commSpace W Y) Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set (LinearMap.GeneralLinearGroup (ZMod 2) D)))
    {V : Submodule (ZMod 2) D} (hVX : IsInvariantBy X V) (hVA : IsInvariantBy A V)
    (hV : commSpace V X = V) : IsMixedHead X Y A (commSpace V Y) := by
  classical
  set U := commSpace V Y with hU
  have hUX : IsInvariantBy X U := isInvariantBy_commSpace_of_commute hXY hVX
  have hUY : IsInvariantBy Y U := isInvariantBy_commSpace
  have hUA : IsInvariantBy A U := isInvariantBy_commSpace_of_normalizer hAY hVA
  have hUUX : commSpace U X = U := by
    refine le_antisymm (commSpace_le_of_isInvariantBy hUX) ?_
    calc U = commSpace (commSpace V X) Y := by rw [hV]
      _ ≤ commSpace (commSpace V Y) X := commSpace_commSpace_le_comm hXY
  have hUUY : commSpace U Y = U := le_antisymm (commSpace_le_of_isInvariantBy hUY) (hYY V)
  refine ⟨hUX, hUY, hUA, hUUX, hUUY, fun hU0 => ?_, fun N hN => ?_⟩
  ·
    let Q : ℕ → Prop := fun m => ∃ N : Submodule (ZMod 2) D, N ≤ U ∧ N ≠ U ∧
      IsInvariantBy X N ∧ IsInvariantBy Y N ∧ IsInvariantBy A N ∧
        Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) N = m
    have hQ : ∃ m, Q m := ⟨_, ⊥, bot_le, fun h => hU0 h.symm, isInvariantBy_bot X,
      isInvariantBy_bot Y, isInvariantBy_bot A, rfl⟩
    obtain ⟨N, hNU, hNne, hNX, hNY, hNA, hNm⟩ := Nat.find_spec hQ
    refine ⟨N, hNU, hNne, hNX, hNY, hNA, fun N' hNN' hN'U hN'X hN'Y hN'A => ?_⟩
    by_cases hN'eq : N' = U
    · exact Or.inr hN'eq
    · left
      have hmin := Nat.find_min' hQ ⟨N', hN'U, hN'eq, hN'X, hN'Y, hN'A, rfl⟩
      have h1 := Submodule.finrank_mono hNN'
      have h2 := Submodule.finrank_mono hN'U
      exact (Submodule.eq_of_le_of_finrank_le hNN' (by omega)).symm
  · obtain ⟨hNU, hNne, hNX, hNY, -, -⟩ := hN
    have hnontriv : ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D),
        commSpace U H = U → ∃ h ∈ H, ∃ u ∈ U, (h : Module.End (ZMod 2) D) u - u ∉ N := by
      intro H hH
      by_contra hcon
      push Not at hcon
      apply hNne
      refine le_antisymm hNU ?_
      rw [← hH, commSpace_le_iff]
      exact hcon
    have hfaith : ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D),
        IsInvariantBy H U → IsInvariantBy H N →
        (∃ h ∈ H, ∃ u ∈ U, (h : Module.End (ZMod 2) D) u - u ∉ N) → IsSimpleGroup H →
        ∀ h ∈ H, (∀ u ∈ U, (h : Module.End (ZMod 2) D) u - u ∈ N) → h = 1 := by
      intro H hHU hHN hex hsimple h hh hker
      have hinvU : ∀ g ∈ H, ∀ u ∈ U, (g : Module.End (ZMod 2) D)
          (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D) : Module.End (ZMod 2) D) u) = u :=
        fun g _ u _ => by
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Module.End.one_apply]
      let K : Subgroup H :=
        { carrier := {g | ∀ u ∈ U, ((g : LinearMap.GeneralLinearGroup (ZMod 2) D) :
            Module.End (ZMod 2) D) u - u ∈ N}
          mul_mem' := fun {g g'} hg hg' u hu => by
            have h1 := N.add_mem (hHN g g.2 _ (hg' u hu)) (hg u hu)
            convert h1 using 1
            rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_sub]
            abel
          one_mem' := fun u _ => by
            rw [OneMemClass.coe_one, Units.val_one, Module.End.one_apply, sub_self]
            exact N.zero_mem
          inv_mem' := fun {g} hg u hu => by
            have hu' := hHU _ (H.inv_mem g.2) u hu
            have h1 := hg _ hu'
            rw [hinvU g g.2 u hu] at h1
            have h2 := N.neg_mem h1
            rw [neg_sub] at h2
            exact h2 }
      have hKn : K.Normal := by
        constructor
        intro g hg c u hu
        have hu' := hHU _ (H.inv_mem c.2) u hu
        have h1 := hHN c c.2 _ (hg _ hu')
        convert h1 using 1
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
          Module.End.mul_apply, Module.End.mul_apply, map_sub, Subgroup.coe_inv,
          hinvU c c.2 u hu]
      rcases hsimple.eq_bot_or_eq_top_of_normal K with hK | hK
      · have hmem : (⟨h, hh⟩ : H) ∈ K := hker
        rw [hK, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      · exfalso
        obtain ⟨g, hg, u, hu, hgu⟩ := hex
        have hmem : (⟨g, hg⟩ : H) ∈ K := by
          rw [hK]
          exact Subgroup.mem_top _
        exact hgu (hmem u hu)
    exact ⟨hnontriv X hUUX, hnontriv Y hUUY,
      fun hs => hfaith X hUX hNX (hnontriv X hUUX) hs,
      fun hs => hfaith Y hUY hNY (hnontriv Y hUUY) hs⟩

end Head

theorem perfect_and_odd_commutators_produce_a_mixed_irreducible_head {D : Type*}
    [AddCommGroup D] [Module (ZMod 2) D] [FiniteDimensional (ZMod 2) D]
    {X Y A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D)}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hX : ⁅X, X⁆ = X)
    (hY : ⁅Y, Y⁆ = Y ∨ Odd (Nat.card Y))
    (hAX : A ≤ Subgroup.normalizer (X : Set (LinearMap.GeneralLinearGroup (ZMod 2) D)))
    (hAY : A ≤ Subgroup.normalizer (Y : Set (LinearMap.GeneralLinearGroup (ZMod 2) D))) :
    IsMixedHead X Y A (commSpace (commSpace ⊤ X) Y) ∧
    (∀ V : Submodule (ZMod 2) D, IsInvariantBy X V → IsInvariantBy A V → commSpace V X = V →
      IsMixedHead X Y A (commSpace V Y)) ∧
    ∀ {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
      (ρ : Representation (ZMod 2) A E) (E₀ : Subrepresentation ρ),
      (Module.finrank (ZMod 2) E₀.toSubmodule -
          Module.finrank (ZMod 2) E₀.toRepresentation.invariants) +
        (Module.finrank (ZMod 2) (E ⧸ E₀.toSubmodule) -
          Module.finrank (ZMod 2) E₀.quotient.invariants) ≤
        Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) ρ.invariants ∧
      ∀ (E₁ : Subrepresentation ρ) (E₂ : Subrepresentation E₁.toRepresentation),
        Module.finrank (ZMod 2) (E₁.toSubmodule ⧸ E₂.toSubmodule) -
            Module.finrank (ZMod 2) E₂.quotient.invariants ≤
          Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) ρ.invariants := by
  have : Finite D := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) D) :=
    Finite.of_injective (fun f : D →ₗ[ZMod 2] D => (f : D → D)) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) D) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup (ZMod 2) D =>
      (u : Module.End (ZMod 2) D)) Units.val_injective
  have hYY : ∀ W : Submodule (ZMod 2) D, commSpace W Y ≤ commSpace (commSpace W Y) Y := by
    intro W
    rcases hY with hYp | hYo
    · exact commSpace_le_commSpace_commSpace_of_perfect hYp
    · exact commSpace_le_commSpace_commSpace_of_card
        (ZMod.natCast_eq_zero_iff_even.not.mpr (Nat.not_even_iff_odd.mpr hYo))
  have hDX : IsInvariantBy X (commSpace ⊤ X) := isInvariantBy_commSpace
  have hDA : IsInvariantBy A (commSpace ⊤ X) :=
    isInvariantBy_commSpace_of_normalizer hAX fun _ _ _ _ => Submodule.mem_top
  have hDXX : commSpace (commSpace ⊤ X) X = commSpace ⊤ X :=
    le_antisymm (commSpace_le_of_isInvariantBy hDX)
      (commSpace_le_commSpace_commSpace_of_perfect hX)
  refine ⟨isMixedHead_commSpace hXY hYY hAY hDX hDA hDXX,
    fun V hVX hVA hV => isMixedHead_commSpace hXY hYY hAY hVX hVA hV,
    fun ρ E₀ => ⟨codim_add_codim_le_codim E₀, fun E₁ E₂ => codim_section_le_codim E₁ E₂⟩⟩

end CFSG.LocalAnalysis
