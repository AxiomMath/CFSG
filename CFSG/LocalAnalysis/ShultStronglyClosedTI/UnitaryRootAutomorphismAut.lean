module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped commutatorElement

universe u

variable {K : Type u} [Field K] (J : HermitianForm 3 K)

section Field

theorem eq_mul_or_eq_mul_conj {x t c : K} (hN : x * J.conj x = t * J.conj t)
    (hB : c * J.conj x + x * J.conj c = t + J.conj t) (hc : c * J.conj c = 1) :
    x = c * t ∨ x = c * J.conj t := by
  have key : (x * J.conj c - t) * (x * J.conj c - J.conj t) = 0 := by
    linear_combination (x * J.conj c) * hB - hN - (x * J.conj x) * hc
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (by linear_combination -x * hc + c * h)
  · exact Or.inr (by linear_combination -x * hc + c * h)

variable [CharP K 2]

theorem eq_one_of_pow_two_pow_eq_one {x : K} : ∀ {k : ℕ}, x ^ 2 ^ k = 1 → x = 1
  | 0, h => by simpa using h
  | k + 1, h => by
    refine eq_one_of_pow_two_pow_eq_one (k := k) ?_
    have h₂ : (2 : K) = 0 := CharTwo.two_eq_zero
    have hy : (x ^ 2 ^ k) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ, h]
    have hsq : (x ^ 2 ^ k - 1) ^ 2 = 0 := by linear_combination hy + (1 - x ^ 2 ^ k) * h₂
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

end Field

section Coordinates

variable [Finite K] [CharP K 2] (q : ℕ) (hcard : Nat.card K = q ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = q)
include hcard hfixed

theorem coord_aut_fst_eq (ψ : MulAut (hermitianUnipotentCoord J))
    (hψ : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z) :
    ∃ c : K, c * J.conj c = 1 ∧
      ((∀ z, (ψ z).1.1 = c * z.1.1) ∨ ∀ z, (ψ z).1.1 = c * J.conj z.1.1) := by
  obtain ⟨o, ho⟩ := exists_fst_eq J q hcard hfixed 1
  have hN : ∀ z, (ψ z).1.1 * J.conj (ψ z).1.1 = z.1.1 * J.conj z.1.1 := fun z => by
    have h := congrArg (fun w : hermitianUnipotentCoord J => w.1.2) (hψ (z ^ 2) (fst_pow_two J z))
    simpa only [map_pow, snd_pow_two] using h
  have hB : ∀ z w : hermitianUnipotentCoord J,
      (ψ w).1.1 * J.conj (ψ z).1.1 + (ψ z).1.1 * J.conj (ψ w).1.1 =
        w.1.1 * J.conj z.1.1 + z.1.1 * J.conj w.1.1 := fun z w => by
    have h := congrArg (fun x : hermitianUnipotentCoord J => x.1.2)
      (hψ ⁅z, w⁆ (fst_commutator J z w))
    simpa only [map_commutatorElement, snd_commutator] using h
  have hc : (ψ o).1.1 * J.conj (ψ o).1.1 = 1 := by rw [hN o, ho, map_one, mul_one]
  have hc0 : (ψ o).1.1 ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hc
    exact zero_ne_one hc
  have hdich : ∀ z, (ψ z).1.1 = (ψ o).1.1 * z.1.1 ∨
      (ψ z).1.1 = (ψ o).1.1 * J.conj z.1.1 := fun z => by
    have h := hB z o
    rw [ho, map_one, one_mul, mul_one] at h
    exact eq_mul_or_eq_mul_conj J (hN z) (by linear_combination h) hc
  refine ⟨(ψ o).1.1, hc, ?_⟩
  by_contra! hcon
  obtain ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ := hcon
  have hz' := (hdich z).resolve_left hz
  have hw' := (hdich w).resolve_right hw
  have hadd : (ψ (z * w)).1.1 = (ψ z).1.1 + (ψ w).1.1 := by rw [map_mul, fst_mul]
  rcases hdich (z * w) with h | h
  · rw [hadd, hz', hw', fst_mul] at h
    have hzz : J.conj z.1.1 = z.1.1 := mul_left_cancel₀ hc0 (by linear_combination h)
    exact hz (by rw [hz', hzz])
  · rw [hadd, hz', hw', fst_mul, map_add] at h
    have hww : w.1.1 = J.conj w.1.1 := mul_left_cancel₀ hc0 (by linear_combination h)
    exact hw (by rw [hw', ← hww])

theorem coord_two_subgroup_fst_eq (θ : MulAut (hermitianUnipotentCoord J)) {μ : K}
    (hμ : μ * J.conj μ = 1) (hμ1 : μ ≠ 1) (hθ : ∀ z, (θ z).1.1 = μ * z.1.1)
    (P : Subgroup (MulAut (hermitianUnipotentCoord J))) (hP : IsPGroup 2 P)
    (hPE : ∀ ψ ∈ P, ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z)
    (hPθ : ∀ ψ ∈ P, ψ * θ = θ * ψ) :
    ∀ ψ ∈ P, ∀ z, (ψ z).1.1 = z.1.1 := by
  intro ψ hψ
  obtain ⟨c, hc, hσ⟩ := coord_aut_fst_eq J q hcard hfixed ψ (hPE ψ hψ)
  obtain ⟨o, ho⟩ := exists_fst_eq J q hcard hfixed 1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc
    exact zero_ne_one hc
  rcases hσ with hid | hbar
  · obtain ⟨k, hk⟩ := hP ⟨ψ, hψ⟩
    have hk' : ψ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hpow : ∀ (n : ℕ) (z : hermitianUnipotentCoord J), ((ψ ^ n) z).1.1 = c ^ n * z.1.1 := by
      intro n
      induction n with
      | zero => intro z; simp
      | succ n ih => intro z; rw [pow_succ', MulAut.mul_apply, hid, ih, pow_succ', mul_assoc]
    have h1 := hpow (2 ^ k) o
    rw [hk', ho, MulAut.one_apply, ho, mul_one] at h1
    have hc1 : c = 1 := eq_one_of_pow_two_pow_eq_one h1.symm
    intro z
    rw [hid, hc1, one_mul]
  · exfalso
    have h := congrArg (fun x : hermitianUnipotentCoord J => x.1.1)
      (congrArg (fun φ : MulAut (hermitianUnipotentCoord J) => φ o) (hPθ ψ hψ))
    simp only [MulAut.mul_apply, hbar, hθ, ho, mul_one, map_one] at h
    have hμμ : J.conj μ = μ := mul_left_cancel₀ hc0 (by linear_combination h)
    rw [hμμ] at hμ
    have h₂ : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (μ - 1) ^ 2 = 0 := by linear_combination hμ + (1 - μ) * h₂
    exact hμ1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

end Coordinates

section Transport

variable {V : Type*} [Group V] (φ : hermitianUnipotentCoord J ≃* V)

@[expose] def rootFst : V →* Multiplicative K :=
  (unitaryCoverFirstCoord J).comp (φ.symm : V →* hermitianUnipotentCoord J)

@[expose] def rootCenter : Subgroup V :=
  (rootFst J φ).ker

theorem rootFst_apply (v : V) : rootFst J φ v = Multiplicative.ofAdd (φ.symm v).1.1 :=
  rfl

instance : (rootCenter J φ).Normal :=
  (rootFst J φ).normal_ker

theorem mem_rootCenter {v : V} : v ∈ rootCenter J φ ↔ (φ.symm v).1.1 = 0 :=
  Iff.rfl

theorem rootCenter_eq_map : rootCenter J φ = (unitaryCoverFirstCoord J).ker.map φ := by
  rw [rootCenter, rootFst, MonoidHom.ker_comp_mulEquiv, MulEquiv.symm_symm]

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (ι : P ≃* Q) :
    (frattini P).map ι = frattini Q := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · have h := frattini_le_comap_frattini_of_surjective (φ := (ι.symm : Q →* P)) ι.symm.surjective
    exact ⟨ι.symm x, h hx, by simp⟩

variable [Finite K] [CharP K 2] (q : ℕ) (hcard : Nat.card K = q ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = q)
include hcard hfixed

theorem root_structure :
    Nat.card V = q ^ 3 ∧ rootCenter J φ = Subgroup.center V ∧ rootCenter J φ = frattini V ∧
      Nat.card (rootCenter J φ) = q ∧ Function.Surjective (rootFst J φ) ∧
      ∀ v : V, (φ.symm (v ^ 2)).1 = (0, (φ.symm v).1.1 * J.conj (φ.symm v).1.1) := by
  refine ⟨(Nat.card_congr φ.toEquiv).symm.trans (card_coord J q hcard hfixed), ?_, ?_, ?_,
    (firstCoord_surjective J q hcard hfixed).comp φ.symm.surjective, fun v => ?_⟩
  · rw [rootCenter_eq_map, ← center_eq_ker_firstCoord J q hcard hfixed, Subgroup.map_center_eq]
  · rw [rootCenter_eq_map, ← frattini_eq_ker_firstCoord J q hcard hfixed,
      map_frattini_mulEquiv]
  · rw [rootCenter_eq_map, Subgroup.card_map_of_injective φ.injective,
      card_ker_firstCoord J hfixed]
  · rw [map_pow]
    exact Prod.ext (fst_pow_two J _) (snd_pow_two J _)

theorem exists_quotient_mulEquiv :
    ∃ e : V ⧸ rootCenter J φ ≃* Multiplicative K,
      ∀ v : V, e v = Multiplicative.ofAdd (φ.symm v).1.1 :=
  ⟨QuotientGroup.quotientKerEquivOfSurjective (rootFst J φ)
      ((firstCoord_surjective J q hcard hfixed).comp φ.symm.surjective), fun _ => rfl⟩

theorem root_aut_fst_eq (ψ : MulAut V) (hψ : ∀ v ∈ rootCenter J φ, ψ v = v) :
    ∃ c : K, c * J.conj c = 1 ∧
      ((∀ v, (φ.symm (ψ v)).1.1 = c * (φ.symm v).1.1) ∨
        ∀ v, (φ.symm (ψ v)).1.1 = c * J.conj (φ.symm v).1.1) := by
  let ψ' : MulAut (hermitianUnipotentCoord J) := (φ.trans ψ).trans φ.symm
  have hψ' : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ' z = z := fun z hz => by
    change φ.symm (ψ (φ z)) = z
    rw [hψ (φ z) (by rwa [mem_rootCenter, MulEquiv.symm_apply_apply]),
      MulEquiv.symm_apply_apply]
  obtain ⟨c, hc, hσ⟩ := coord_aut_fst_eq J q hcard hfixed ψ' hψ'
  have hψv : ∀ v, φ.symm (ψ v) = ψ' (φ.symm v) := fun v => by
    change φ.symm (ψ v) = φ.symm (ψ (φ (φ.symm v)))
    rw [MulEquiv.apply_symm_apply]
  refine ⟨c, hc, hσ.imp (fun h v => ?_) fun h v => ?_⟩ <;> rw [hψv, h]

theorem root_two_subgroup_fst_eq (θ : MulAut V) {μ : K} (hμ : μ * J.conj μ = 1) (hμ1 : μ ≠ 1)
    (hθ : ∀ v, (φ.symm (θ v)).1.1 = μ * (φ.symm v).1.1) (P : Subgroup (MulAut V))
    (hP : IsPGroup 2 P) (hPE : ∀ ψ ∈ P, ∀ v ∈ rootCenter J φ, ψ v = v)
    (hPθ : ∀ ψ ∈ P, ψ * θ = θ * ψ) :
    ∀ ψ ∈ P, ∀ v, (φ.symm (ψ v)).1.1 = (φ.symm v).1.1 := by
  let c : MulAut V →* MulAut (hermitianUnipotentCoord J) := (MulAut.congr φ.symm).toMonoidHom
  have hc : ∀ (ψ : MulAut V) (z : hermitianUnipotentCoord J), c ψ z = φ.symm (ψ (φ z)) :=
    fun _ _ => rfl
  have hP' : IsPGroup 2 (P.map c) := hP.map _
  have key := coord_two_subgroup_fst_eq J q hcard hfixed (c θ) hμ hμ1
    (fun z => by rw [hc, hθ, MulEquiv.symm_apply_apply]) _ hP'
    (by
      rintro _ ⟨ψ, hψ, rfl⟩ z hz
      rw [hc, hPE ψ hψ (φ z) (by rwa [mem_rootCenter, MulEquiv.symm_apply_apply]),
        MulEquiv.symm_apply_apply])
    (by
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [← map_mul, ← map_mul, hPθ ψ hψ])
  intro ψ hψ v
  have h := key (c ψ) ⟨ψ, hψ, rfl⟩ (φ.symm v)
  rwa [hc, MulEquiv.apply_symm_apply] at h

end Transport

end CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
