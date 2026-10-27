module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SchurZassenhaus
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Subgroup

theorem exists_lift_of_central_coprime {J : Type*} [Group J] [Finite J] (Z : Subgroup J)
    [Z.Normal] {k : ℕ} (hcop : Nat.Coprime (Nat.card Z) k) (R : Subgroup (J ⧸ Z))
    (hRk : Nat.card R = k) :
    ∃ R' : Subgroup J, R'.map (QuotientGroup.mk' Z) = R ∧ Nat.card R' = k ∧
      ∀ x ∈ R', ∀ y ∈ R', QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
  classical
  set π := QuotientGroup.mk' Z with hπ
  let Pt : Subgroup J := R.comap π
  let ρ : Pt →* R := (π.comp Pt.subtype).codRestrict R (fun x => x.2)
  have hρ : ∀ x : Pt, ((ρ x : R) : J ⧸ Z) = π (x : J) := fun x => rfl
  have hρsurj : Function.Surjective ρ := by
    intro r
    obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective Z (r : J ⧸ Z)
    have hjPt : j ∈ Pt := by
      show π j ∈ R
      rw [hj]
      exact r.2
    exact ⟨⟨j, hjPt⟩, Subtype.ext (by rw [hρ]; exact hj)⟩
  have hkerρ : ∀ x : Pt, x ∈ ρ.ker ↔ (x : J) ∈ Z := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rw [hρ] at this
      exact (QuotientGroup.eq_one_iff (x : J)).mp this
    · intro h
      apply Subtype.ext
      rw [hρ]
      exact (QuotientGroup.eq_one_iff (x : J)).mpr h
  have hZPt : ∀ z ∈ Z, z ∈ Pt := by
    intro z hz
    show π z ∈ R
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h1]
    exact R.one_mem
  have hindex : ρ.ker.index = k := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρsurj, Subgroup.card_top, hRk]
  have hkerCard : Nat.card ρ.ker = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : J), (hkerρ x.1).mp x.2⟩
        invFun := fun z => ⟨⟨z.1, hZPt z.1 z.2⟩, (hkerρ ⟨z.1, hZPt z.1 z.2⟩).mpr z.2⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := ρ.ker)
    (by rw [hindex, hkerCard]; exact hcop)
  have hCcard : Nat.card C = k := by
    rw [← hindex]
    exact (Subgroup.IsComplement'.index_eq_card hC.symm).symm
  refine ⟨C.map Pt.subtype, ?_, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      have h1 : π ((c : Pt) : J) = ((ρ c : R) : J ⧸ Z) := (hρ c).symm
      show π ((c : Pt) : J) ∈ R
      rw [h1]
      exact (ρ c).2
    · intro hr
      obtain ⟨pt, hpt⟩ := hρsurj ⟨r, hr⟩
      obtain ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩ := hC.2 pt
      refine ⟨((c : Pt) : J), ⟨c, hc, rfl⟩, ?_⟩
      have hn1 : ρ n = 1 := hn
      have h2 : ρ pt = ρ c := by
        rw [← hnc]
        simp only [map_mul, hn1, one_mul]
      have h3 : ((ρ c : R) : J ⧸ Z) = r := by
        rw [← h2, hpt]
      rw [← h3, hρ]
  · rw [Subgroup.card_map_of_injective Pt.subtype_injective, hCcard]
  · rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ h
    have h1 : ρ c₁ = ρ c₂ := by
      apply Subtype.ext
      rw [hρ, hρ]
      exact h
    have h2 : c₁⁻¹ * c₂ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : c₁⁻¹ * c₂ ∈ C := C.mul_mem (C.inv_mem hc₁) hc₂
    have h4 : c₁⁻¹ * c₂ = 1 := by
      have := Subgroup.disjoint_def.mp (Subgroup.IsComplement'.disjoint hC) h2 h3
      exact this
    rw [inv_mul_eq_one.mp h4]

theorem exists_aut_invariant_two_subgroup {J : Type*} [Group J] [Finite J] (Z : Subgroup J)
    [Z.Normal] (hZ : Z ≤ Subgroup.center J) (U : Subgroup (J ⧸ Z)) (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) :
    ∃ S : Subgroup J, IsPGroup 2 S ∧ S ≠ ⊥ ∧
      ∀ φ : MulAut J, (∀ x : J, QuotientGroup.mk' Z x ∈ U ↔ QuotientGroup.mk' Z (φ x) ∈ U) →
        ∀ s ∈ S, φ s ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z with hπ
  let Ut : Subgroup J := U.comap π
  let f : Ut →* (J ⧸ Z) := π.comp Ut.subtype
  have hker : f.ker ≤ Subgroup.center Ut := by
    intro x hx
    have hxZ : (x : J) ∈ Z := (QuotientGroup.eq_one_iff (x : J)).mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZ hxZ) (g : J)
  have hrange : f.range = U := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hu
      obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective Z u
      exact ⟨⟨j, by show π j ∈ U; rw [hj]; exact hu⟩, hj⟩
  have : Group.IsNilpotent f.range := by
    rw [hrange]
    exact hU2.isNilpotent
  have : Group.IsNilpotent Ut :=
    Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict (by rwa [MonoidHom.ker_rangeRestrict])
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  have hPchar : (P : Subgroup Ut).Characteristic :=
    Sylow.characteristic_of_normal P inferInstance
  refine ⟨(P : Subgroup Ut).map Ut.subtype, ?_, ?_, ?_⟩
  · exact (P.isPGroup').map Ut.subtype
  ·
    intro hbot
    have hPbot : (P : Subgroup Ut) = ⊥ := by
      have := (Subgroup.map_eq_bot_iff _).mp hbot
      rw [Subgroup.ker_subtype] at this
      exact eq_bot_iff.mpr this
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hU1
      rw [pow_zero] at hm
      exact (Subgroup.card_eq_one).mp hm
    have h2U : 2 ∣ Nat.card U := by
      rw [hm]
      exact dvd_pow_self 2 hm0
    have h2Ut : 2 ∣ Nat.card Ut := by
      have h1 := Subgroup.card_ker_mul_card_range f
      rw [hrange] at h1
      exact h2U.trans (Dvd.intro_left _ h1)
    have hcardP := Sylow.card_eq_multiplicity P
    rw [hPbot, Subgroup.card_bot] at hcardP
    have hpos : 0 < Nat.card Ut := Nat.card_pos
    have : (Nat.card Ut).factorization 2 ≠ 0 := by
      intro h0
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two
        (Nat.pos_iff_ne_zero.mp hpos)).mp h2Ut
      omega
    have h2le : 2 ^ 1 ≤ 2 ^ (Nat.card Ut).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero this)
    omega
  · intro φ hφ s hs
    obtain ⟨x, hx, rfl⟩ := hs
    let φ' : MulAut Ut :=
      { toFun := fun y => ⟨φ (y : J), (hφ (y : J)).mp y.2⟩
        invFun := fun y => ⟨φ.symm (y : J), (hφ (φ.symm (y : J))).mpr (by
          rw [MulEquiv.apply_symm_apply]
          exact y.2)⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (map_mul φ (x : J) (y : J)) }
    have hmap := Subgroup.characteristic_iff_map_eq.mp hPchar φ'
    have hφx : φ' x ∈ (P : Subgroup Ut) := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    exact ⟨φ' x, hφx, rfl⟩

theorem exists_invariant_two_subgroup {J : Type*} [Group J] [Finite J] (Z : Subgroup J)
    [Z.Normal] (hZ : Z ≤ Subgroup.center J) (U : Subgroup (J ⧸ Z)) (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) :
    ∃ S : Subgroup J, IsPGroup 2 S ∧ S ≠ ⊥ ∧
      ∀ g : J, QuotientGroup.mk' Z g ∈ Subgroup.normalizer (U : Set (J ⧸ Z)) →
        ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
  obtain ⟨S, hS2, hS1, hSφ⟩ := exists_aut_invariant_two_subgroup Z hZ U hU2 hU1
  refine ⟨S, hS2, hS1, fun g hg s hs => ?_⟩
  have h := hSφ (MulAut.conj g) (fun x => by
    have h1 := (Subgroup.mem_normalizer_iff.mp hg) (QuotientGroup.mk' Z x)
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact h1) s hs
  rwa [MulAut.conj_apply] at h

theorem exists_lift_of_surjective_coprime {G Q : Type*} [Group G] [Finite G] [Group Q]
    (θ : G →* Q) (hθ : Function.Surjective θ) {k : ℕ} (hcop : Nat.Coprime (Nat.card θ.ker) k)
    (R : Subgroup Q) (hRk : Nat.card R = k) :
    ∃ R' : Subgroup G, R'.map θ = R ∧ Nat.card R' = k ∧
      ∀ x ∈ R', ∀ y ∈ R', θ x = θ y → x = y := by
  let e : (G ⧸ θ.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let R₁ : Subgroup (G ⧸ θ.ker) := R.map e.symm.toMonoidHom
  have hR₁ : Nat.card R₁ = k := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hRk]
  obtain ⟨R', hmap, hcard, hinj⟩ := exists_lift_of_central_coprime θ.ker hcop R₁ hR₁
  have hθmk : ∀ x : G, θ x = e (QuotientGroup.mk' θ.ker x) := fun x => rfl
  refine ⟨R', ?_, hcard, fun x hx y hy hxy => hinj x hx y hy ?_⟩
  · ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : QuotientGroup.mk' θ.ker x ∈ R₁ := by rw [← hmap]; exact ⟨x, hx, rfl⟩
      obtain ⟨r', hr', hr'e⟩ := h1
      rw [hθmk, ← hr'e]
      simpa using hr'
    · intro hr
      have h1 : e.symm r ∈ R₁ := ⟨r, hr, rfl⟩
      rw [← hmap] at h1
      obtain ⟨x, hx, hxe⟩ := h1
      refine ⟨x, hx, ?_⟩
      rw [hθmk, hxe]
      simp
  · apply e.injective
    rw [← hθmk, ← hθmk]
    exact hxy

end CFSG.RankThree.PartOne.Sec66T
