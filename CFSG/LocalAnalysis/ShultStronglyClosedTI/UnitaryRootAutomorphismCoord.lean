module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverRootData
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.BenderSuzuki.External
open scoped commutatorElement

universe u

variable {K : Type u} [Field K] (J : HermitianForm 3 K)

section Coordinates

@[simp] theorem fst_mul (z w : hermitianUnipotentCoord J) : (z * w).1.1 = z.1.1 + w.1.1 := rfl

@[simp] theorem snd_mul (z w : hermitianUnipotentCoord J) :
    (z * w).1.2 = z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 := rfl

@[simp] theorem fst_inv (z : hermitianUnipotentCoord J) : (z⁻¹).1.1 = -z.1.1 := rfl

@[simp] theorem snd_inv (z : hermitianUnipotentCoord J) : (z⁻¹).1.2 = J.conj z.1.2 := rfl

@[simp] theorem fst_one : (1 : hermitianUnipotentCoord J).1.1 = 0 := rfl

@[simp] theorem snd_one : (1 : hermitianUnipotentCoord J).1.2 = 0 := rfl

variable {J} in
theorem coord_ext {z w : hermitianUnipotentCoord J} (h₁ : z.1.1 = w.1.1) (h₂ : z.1.2 = w.1.2) :
    z = w :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem mem_ker_firstCoord {z : hermitianUnipotentCoord J} :
    z ∈ (unitaryCoverFirstCoord J).ker ↔ z.1.1 = 0 :=
  Iff.rfl

theorem mul_comm_of_fst_eq_zero {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0)
    (w : hermitianUnipotentCoord J) : z * w = w * z :=
  coord_ext (by rw [fst_mul, fst_mul, add_comm])
    (by rw [snd_mul, snd_mul, hz, map_zero, mul_zero, zero_mul, add_comm])

@[expose] def rootTau : MulAut (hermitianUnipotentCoord J) where
  toFun z := ⟨(J.conj z.1.1, J.conj z.1.2), by
    have h := congrArg J.conj z.2
    rw [map_add, map_add, map_mul, J.conj_involutive z.1.2, J.conj_involutive z.1.1,
      map_zero] at h
    dsimp only
    rw [J.conj_involutive z.1.2, J.conj_involutive z.1.1]
    linear_combination h⟩
  invFun z := ⟨(J.conj z.1.1, J.conj z.1.2), by
    have h := congrArg J.conj z.2
    rw [map_add, map_add, map_mul, J.conj_involutive z.1.2, J.conj_involutive z.1.1,
      map_zero] at h
    dsimp only
    rw [J.conj_involutive z.1.2, J.conj_involutive z.1.1]
    linear_combination h⟩
  left_inv z := coord_ext (J.conj_involutive z.1.1) (J.conj_involutive z.1.2)
  right_inv z := coord_ext (J.conj_involutive z.1.1) (J.conj_involutive z.1.2)
  map_mul' z w := by
    apply coord_ext
    · exact map_add J.conj z.1.1 w.1.1
    · change J.conj (z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1) =
        J.conj z.1.2 + J.conj w.1.2 - J.conj z.1.1 * J.conj (J.conj w.1.1)
      rw [map_sub, map_add, map_mul]

@[simp] theorem fst_rootTau (z : hermitianUnipotentCoord J) : (rootTau J z).1.1 = J.conj z.1.1 :=
  rfl

@[simp] theorem snd_rootTau (z : hermitianUnipotentCoord J) : (rootTau J z).1.2 = J.conj z.1.2 :=
  rfl

theorem rootTau_mul_self : rootTau J * rootTau J = 1 :=
  MulEquiv.ext fun z => coord_ext (J.conj_involutive z.1.1) (J.conj_involutive z.1.2)

theorem fst_commutator (z w : hermitianUnipotentCoord J) : (⁅z, w⁆).1.1 = 0 :=
  CFSG.BenderSuzuki.Background.hermitianUnipotent_commutator_fst J z w

theorem card_fixedField {q : ℕ} (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Nat.card (unitaryCoverFixedField J) = q :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans hfixed

end Coordinates

section CharTwo

variable [CharP K 2]

theorem fst_pow_two (z : hermitianUnipotentCoord J) : (z ^ 2).1.1 = 0 := by
  rw [pow_two, fst_mul, CharTwo.add_self_eq_zero]

theorem snd_pow_two (z : hermitianUnipotentCoord J) : (z ^ 2).1.2 = z.1.1 * J.conj z.1.1 := by
  rw [pow_two, snd_mul, CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq]

theorem snd_commutator (z w : hermitianUnipotentCoord J) :
    (⁅z, w⁆).1.2 = w.1.1 * J.conj z.1.1 + z.1.1 * J.conj w.1.1 := by
  have h₂ : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [commutatorElement_def, snd_mul, fst_mul, snd_inv, fst_inv, map_neg]
  linear_combination z.2 + w.2 - (z.1.1 * J.conj w.1.1) * h₂

theorem conj_snd_of_fst_eq_zero {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) :
    J.conj z.1.2 = z.1.2 := by
  have h := z.2
  rw [hz, zero_mul, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

theorem pow_two_eq_one_of_fst_eq_zero {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) :
    z ^ 2 = 1 :=
  coord_ext (fst_pow_two J z) (by rw [snd_pow_two, hz, zero_mul, snd_one])

theorem pow_four_eq_one (z : hermitianUnipotentCoord J) : z ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul]
  exact pow_two_eq_one_of_fst_eq_zero J (fst_pow_two J z)

theorem isPGroup_two : IsPGroup 2 (hermitianUnipotentCoord J) :=
  fun z => ⟨2, pow_four_eq_one J z⟩

theorem pow_two_eq_one_iff (z : hermitianUnipotentCoord J) : z ^ 2 = 1 ↔ z.1.1 = 0 := by
  refine ⟨fun h => ?_, pow_two_eq_one_of_fst_eq_zero J⟩
  have h₂ := congrArg (fun w : hermitianUnipotentCoord J => w.1.2) h
  simp only [snd_pow_two, snd_one, mul_eq_zero, map_eq_zero, or_self] at h₂
  exact h₂

theorem card_ker_firstCoord {q : ℕ} (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Nat.card (unitaryCoverFirstCoord J).ker = q :=
  (Nat.card_congr (unitaryCoverZeroFirstEquiv J).toEquiv).trans
    ((Nat.card_congr Multiplicative.toAdd).trans (card_fixedField J hfixed))

end CharTwo

section Finite

variable [Finite K] (q : ℕ) (hcard : Nat.card K = q ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = q)
include hcard hfixed

omit hfixed in
theorem pos_of_card_eq_sq : 0 < q := by
  have h := Nat.card_pos (α := K)
  rw [hcard] at h
  exact Nat.pos_of_ne_zero (by rintro rfl; simp at h)

theorem exists_conj_ne : ∃ ξ : K, J.conj ξ ≠ ξ := by
  by_contra! h
  have e : {x : K // J.conj x = x} ≃ K := (Equiv.subtypeUnivEquiv h)
  have hq : q = q ^ 2 := hfixed.symm.trans ((Nat.card_congr e).trans hcard)
  have hK : 1 < Nat.card K := Finite.one_lt_card
  rw [hcard] at hK
  have hq1 : 1 < q := by
    by_contra! hq'
    interval_cases q <;> simp at hK
  nlinarith

theorem exists_trace_eq {c : K} (hc : J.conj c = c) : ∃ b : K, b + J.conj b = c :=
  huppert_II_10_4_trace_surjective J q hcard hfixed c hc

variable [CharP K 2]

theorem exists_fst_eq (a : K) : ∃ z : hermitianUnipotentCoord J, z.1.1 = a := by
  have hN : J.conj (a * J.conj a) = a * J.conj a := by
    rw [map_mul, J.conj_involutive, mul_comm]
  obtain ⟨b, hb⟩ := exists_trace_eq J q hcard hfixed hN
  exact ⟨⟨(a, b), by rw [hb, CharTwo.add_self_eq_zero]⟩, rfl⟩

theorem firstCoord_surjective : Function.Surjective (unitaryCoverFirstCoord J) := fun a => by
  obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed (Multiplicative.toAdd a)
  exact ⟨z, by rw [← ofAdd_toAdd a, ← hz]; rfl⟩

theorem exists_pow_two_eq {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) :
    ∃ w : hermitianUnipotentCoord J, w ^ 2 = z := by
  have hb := conj_snd_of_fst_eq_zero J hz
  by_cases hb0 : z.1.2 = 0
  · exact ⟨1, by rw [one_pow]; exact (coord_ext hz hb0).symm⟩
  obtain ⟨c, -, hc⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed z.1.2 hb hb0
  obtain ⟨w, hw⟩ := exists_fst_eq J q hcard hfixed c
  exact ⟨w, coord_ext (by rw [fst_pow_two, hz]) (by rw [snd_pow_two, hw, hc])⟩

theorem card_coord : Nat.card (hermitianUnipotentCoord J) = q ^ 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryCoverFirstCoord J).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (firstCoord_surjective J q hcard hfixed)).toEquiv, Nat.card_congr Multiplicative.toAdd,
    hcard, card_ker_firstCoord J hfixed] at h
  rw [h]
  ring

theorem center_eq_ker_firstCoord :
    Subgroup.center (hermitianUnipotentCoord J) = (unitaryCoverFirstCoord J).ker := by
  ext z
  rw [mem_ker_firstCoord, Subgroup.mem_center_iff]
  constructor
  · intro hz
    by_contra hz0
    obtain ⟨ξ, hξ⟩ := exists_conj_ne J q hcard hfixed
    obtain ⟨w, hw⟩ := exists_fst_eq J q hcard hfixed (z.1.1 * ξ)
    have h := congrArg (fun x : hermitianUnipotentCoord J => x.1.2) (hz w)
    simp only [snd_mul, hw, map_mul] at h
    have hN : z.1.1 * J.conj z.1.1 ≠ 0 := mul_ne_zero hz0 ((map_ne_zero J.conj).mpr hz0)
    apply hξ
    have h' : z.1.1 * J.conj z.1.1 * (J.conj ξ - ξ) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hN)
  · exact fun hz w => (mul_comm_of_fst_eq_zero J hz w).symm

theorem frattini_eq_ker_firstCoord :
    frattini (hermitianUnipotentCoord J) = (unitaryCoverFirstCoord J).ker := by
  have : Fact (IsPGroup 2 (hermitianUnipotentCoord J)) := ⟨isPGroup_two J⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun z hz => ?_
  · rintro x (hx | ⟨w, rfl⟩)
    · exact unitaryCoverCoord_commutator_le_ker J hx
    · exact fst_pow_two J w
  · obtain ⟨w, rfl⟩ := exists_pow_two_eq J q hcard hfixed hz
    exact Subgroup.subset_closure (Or.inr ⟨w, rfl⟩)

end Finite

end CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
