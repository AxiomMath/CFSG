module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBstar
public import CFSG.RankThree.PartOne.LIT.RankAbstract

public section

namespace CFSG.StandardType

namespace OrthRestEnd

open Module CFSG.RankThree.PartOne.LIT
open scoped Matrix

section Average

variable {K : Type*} [Field K] {X : Type*} [AddCommGroup X] [Module K X]

theorem averageMap_apply {G : Type*} [Group G] [Fintype G] [Invertible (Fintype.card G : K)]
    (ρ : Representation K G X) (x : X) :
    ρ.averageMap x = ⅟(Fintype.card G : K) • ∑ g : G, ρ g x := by
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]

theorem averageMap_apply_rep {G : Type*} [Group G] [Fintype G] [Invertible (Fintype.card G : K)]
    (ρ : Representation K G X) (h : G) (x : X) : ρ.averageMap (ρ h x) = ρ.averageMap x := by
  rw [averageMap_apply, averageMap_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => by
    rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]

end Average

section Fixed

variable {K : Type*} [Field K] {X : Type*} [AddCommGroup X] [Module K X]

theorem card_le_pow_half_sub_one [FiniteDimensional K X] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (B : X →ₗ[K] X →ₗ[K] K) (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hAlt : ∀ v, B v v = 0) (E : Subgroup (X ≃ₗ[K] X)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1)
    (hpres : ∀ g ∈ E, ∀ u w, B (g u) (g w) = B u w) {v : X} (hv : v ≠ 0)
    (hfix : ∀ g ∈ E, g v = v) : Nat.card E ≤ r ^ (finrank K X / 2 - 1) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hr
    (fun a : E => Subtype.ext (hexp a a.2))
  have hcardK : (Fintype.card E : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hk, Nat.cast_pow]
    exact pow_ne_zero _ hrK
  have : Invertible (Fintype.card E : K) := invertibleOfNonzero hcardK
  let ρ : Representation K E X :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp E.subtype
  have hρ : ∀ (g : E) (x : X), ρ g x = (g : X ≃ₗ[K] X) x := fun _ _ => rfl
  set P := ρ.averageMap with hP
  have hc : IsCompl ρ.invariants (LinearMap.ker P) := ρ.isProj_averageMap.isCompl
  have hvU : v ∈ ρ.invariants := fun g => hfix g g.2
  have hBP : ∀ u ∈ ρ.invariants, ∀ y, B u (P y) = B u y := by
    intro u hu y
    have hg : ∀ g : E, B u (ρ g y) = B u y := fun g => by
      calc B u (ρ g y) = B (ρ g u) (ρ g y) := by rw [hu g]
        _ = B u y := hpres g g.2 u y
    rw [hP, averageMap_apply, map_smul, map_sum]
    simp only [hg, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul]
    rw [invOf_mul_cancel_left]
  have hUY : ∀ u ∈ ρ.invariants, ∀ y ∈ LinearMap.ker P, B u y = 0 := by
    intro u hu y hy
    rw [← hBP u hu y, LinearMap.mem_ker.mp hy, map_zero]
  have hskew := alt_skew hAlt
  have hsplit : ∀ x : X, ∃ u ∈ ρ.invariants, ∃ y ∈ LinearMap.ker P, u + y = x := fun x => by
    have : x ∈ ρ.invariants ⊔ LinearMap.ker P := by rw [hc.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hYinv : ∀ g : E, ∀ y ∈ LinearMap.ker P, (E.subtype g) y ∈ LinearMap.ker P := by
    intro g y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact (averageMap_apply_rep ρ g y).trans hy
  set ρY := restrictAction E.subtype (LinearMap.ker P) hYinv with hρY
  have hρYinj : Function.Injective ρY := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    refine ext_of_isCompl hc (fun u hu => ?_) (fun y hy => ?_)
    · exact hu g
    · have h1 := congrArg (fun f : LinearMap.ker P ≃ₗ[K] LinearMap.ker P =>
        ((f ⟨y, hy⟩ : LinearMap.ker P) : X)) hg
      simpa [hρY, restrictAction_apply] using h1
  have : Finite ρY.range := Finite.of_equiv E (MonoidHom.ofInjective hρYinj).toEquiv
  have hcardY : Nat.card ρY.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hρYinj).toEquiv).symm
  have hY := card_le_pow_half_of_alt hr hrK (finrank K (LinearMap.ker P)) (LinearMap.ker P) rfl
    (B.compl₁₂ (LinearMap.ker P).subtype (LinearMap.ker P).subtype)
    (fun y hy => by
      apply Subtype.ext
      apply hB
      intro x
      obtain ⟨u, hu, y', hy', rfl⟩ := hsplit x
      rw [map_add, hskew, hUY u hu y y.2, neg_zero, zero_add]
      exact hy ⟨y', hy'⟩)
    (fun y => hAlt y) ρY.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hcomm a a.2 b b.2)])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, show a ^ r = 1 from Subtype.ext (hexp a a.2), map_one])
    (by
      rintro _ ⟨a, rfl⟩ y y'
      exact hpres a a.2 y y')
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hU2 : 2 ≤ finrank K ρ.invariants := by
    have hv' : (⟨v, hvU⟩ : ρ.invariants) ≠ 0 := fun h => hv (congrArg Subtype.val h)
    have hpos : 0 < finrank K ρ.invariants :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hv'⟩
    by_contra hlt
    have h1 : finrank K ρ.invariants = 1 := by omega
    apply hv
    apply hB v
    intro x
    obtain ⟨u, hu, y, hy, rfl⟩ := hsplit x
    rw [map_add, hUY v hvU y hy, add_zero]
    obtain ⟨c, hcu⟩ := (finrank_eq_one_iff_of_nonzero' _ hv').mp h1 ⟨u, hu⟩
    have hu' : u = c • v := by
      have := congrArg Subtype.val hcu
      simpa using this.symm
    rw [hu', map_smul, hAlt, smul_zero]
  rw [← hcardY]
  exact hY.trans (Nat.pow_le_pow_right hr.pos (by omega))

end Fixed

section Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem card_le_of_isometry_fixed (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (GL ι K)) (hiso : ∀ g ∈ E, ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) {v : ι → K}
    (hv : v ≠ 0) (hfix : ∀ g ∈ E, (g : Matrix ι ι K) *ᵥ v = v) :
    Nat.card E ≤ p ^ (Fintype.card ι / 2 - 1) := by
  have : Finite (GL ι K) :=
    Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) Units.val_injective
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_pow_half_sub_one hp hpK (QuadraticMap.polarBilin Q) (fun v hv => hQ.1 v hv)
    (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
        CharTwo.add_self_eq_zero])
    (E.map (glAut ι K)) (map_glAut_comm hcomm) (map_glAut_exp hexp)
    (by
      rintro _ ⟨g, hg, rfl⟩ u w
      simp only [QuadraticMap.polarBilin_apply_apply, glAut_apply]
      rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hiso g hg, hiso g hg,
        hiso g hg])
    hv (by
      rintro _ ⟨g, hg, rfl⟩
      rw [glAut_apply]
      exact hfix g hg)
  rwa [card_map_glAut, Module.finrank_fintype_fun_eq_card] at h

omit [CharP K 2] [DecidableEq ι] in
theorem card_singular_eq_succ (Q : QuadraticForm K (ι → K)) :
    Nat.card {v // Q v = 0} = Nat.card {v // v ≠ 0 ∧ Q v = 0} + 1 := by
  classical
  rw [← Finite.card_option]
  refine Nat.card_congr
    { toFun := fun v => if h : v.1 = 0 then none else some ⟨v.1, h, v.2⟩
      invFun := fun o => o.elim ⟨0, QuadraticMap.map_zero Q⟩ fun w => ⟨w.1, w.2.2⟩
      left_inv := fun v => ?_
      right_inv := fun o => ?_ }
  · by_cases h : v.1 = 0
    · apply Subtype.ext
      simp [h]
    · simp [h]
  · rcases o with _ | w
    · simp
    · simp [w.2.1]

omit [Finite K] [CharP K 2] in
theorem exists_fixed_singular (Q : QuadraticForm K (ι → K)) {p : ℕ} [Fact p.Prime]
    (E : Subgroup (GL ι K)) (hE : IsPGroup p E)
    (hiso : ∀ g ∈ E, ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hS : ¬ p ∣ Nat.card {v : ι → K // v ≠ 0 ∧ Q v = 0}) :
    ∃ v : ι → K, v ≠ 0 ∧ Q v = 0 ∧ ∀ g ∈ E, (g : Matrix ι ι K) *ᵥ v = v := by
  let S := {v : ι → K // v ≠ 0 ∧ Q v = 0}
  have hne : ∀ g : GL ι K, ∀ w : ι → K, w ≠ 0 → (g : Matrix ι ι K) *ᵥ w ≠ 0 := by
    intro g w hw h0
    apply hw
    have h1 := congrArg (fun u => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) h0
    simpa [Matrix.mulVec_mulVec] using h1
  let act : MulAction E S :=
    { smul := fun g s => ⟨((g : GL ι K) : Matrix ι ι K) *ᵥ s.1, hne g s.1 s.2.1,
        by rw [hiso g g.2]; exact s.2.2⟩
      one_smul := fun s => Subtype.ext (by
        change (((1 : E) : GL ι K) : Matrix ι ι K) *ᵥ s.1 = s.1
        rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec])
      mul_smul := fun g h s => Subtype.ext (by
        change (((g * h : E) : GL ι K) : Matrix ι ι K) *ᵥ s.1 =
          ((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ s.1)
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]) }
  obtain ⟨s, hs⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card S hS
  refine ⟨s.1, s.2.1, s.2.2, fun g hg => ?_⟩
  exact congrArg Subtype.val (hs ⟨g, hg⟩)

end Matrix

end OrthRestEnd

end CFSG.StandardType
