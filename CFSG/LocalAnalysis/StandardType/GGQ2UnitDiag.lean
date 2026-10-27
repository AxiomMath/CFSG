module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {N : ℕ} {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* Kˣ)

theorem coe_diagOf (w : UnitRaw.W N) :
    ((diagOf ζ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      diagonal fun i => ((ζ (Multiplicative.ofAdd (w i)) : Kˣ) : K) :=
  rfl

theorem diagOf_add (w w' : UnitRaw.W N) : diagOf ζ (w + w') = diagOf ζ w * diagOf ζ w' := by
  rw [diagOf, diagOf, diagOf, ← map_mul]
  congr 1
  funext i
  simp only [Pi.add_apply, ofAdd_add, map_mul, Pi.mul_apply]

theorem diagOf_zero : diagOf ζ (0 : UnitRaw.W N) = 1 := by
  rw [diagOf, ← map_one (diagHom (K := K) N)]
  congr 1
  funext i
  simp

theorem diagOf_neg (w : UnitRaw.W N) : diagOf ζ (-w) = (diagOf ζ w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diagOf_add, neg_add_cancel, diagOf_zero]

theorem diagOf_sub (w w' : UnitRaw.W N) :
    diagOf ζ (w - w') = diagOf ζ w * (diagOf ζ w')⁻¹ := by
  rw [sub_eq_add_neg, diagOf_add, diagOf_neg]

theorem diagOf_comm (w w' : UnitRaw.W N) : diagOf ζ w * diagOf ζ w' = diagOf ζ w' * diagOf ζ w := by
  rw [← diagOf_add, ← diagOf_add, add_comm]

theorem det_diagOf (w : UnitRaw.W N) :
    ((diagOf ζ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det =
      ((ζ (Multiplicative.ofAdd (∑ i, w i)) : Kˣ) : K) := by
  rw [diagOf, det_diagHom, ofAdd_sum, map_prod, Units.coe_prod]

theorem diagOf_const (c : UnitRaw.F) :
    diagOf ζ (fun _ : Fin N => c) =
      Matrix.GeneralLinearGroup.scalar (Fin N) (ζ (Multiplicative.ofAdd c)) :=
  Units.ext (by rw [coe_diagOf, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply])

theorem diagOf_mem_scalars_of_mem_oneLine {w : UnitRaw.W N} (hw : w ∈ UnitRaw.oneLine N) :
    diagOf ζ w ∈ LargeEvenScalars (Fin N) K := by
  obtain ⟨c, rfl⟩ := (UnitRaw.mem_oneLine w).mp hw
  rw [largeEvenScalars_def, diagOf_const]
  exact ⟨_, rfl⟩

theorem diagOf_mem_scalars_iff (hζ : Function.Injective ζ) (w : UnitRaw.W N) :
    diagOf ζ w ∈ LargeEvenScalars (Fin N) K ↔ w ∈ UnitRaw.oneLine N := by
  refine ⟨fun hw => ?_, diagOf_mem_scalars_of_mem_oneLine ζ⟩
  rw [largeEvenScalars_def] at hw
  obtain ⟨u, hu⟩ := hw
  have hi : ∀ i, ζ (Multiplicative.ofAdd (w i)) = u := by
    intro i
    have h1 := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K) i i) hu
    simp only [coe_diagOf, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    exact (Units.ext h1).symm
  have hconst : ∀ i j, w i = w j := fun i j =>
    Multiplicative.ofAdd.injective (hζ ((hi i).trans (hi j).symm))
  rw [UnitRaw.mem_oneLine]
  rcases isEmpty_or_nonempty (Fin N) with hE | ⟨⟨i₀⟩⟩
  · exact ⟨0, funext fun i => (IsEmpty.false i).elim⟩
  · exact ⟨w i₀, funext fun i => hconst i i₀⟩

theorem zeta_pow_three (x : Multiplicative (ZMod 3)) : ζ x ^ 3 = 1 := by
  rw [← map_pow]
  have hx : x ^ 3 = 1 := by
    revert x
    decide
  rw [hx, map_one]

theorem diagOf_pow_three (w : UnitRaw.W N) : diagOf ζ w ^ 3 = 1 := by
  rw [diagOf, ← map_pow, ← map_one (diagHom (K := K) N)]
  congr 1
  funext i
  simp only [Pi.pow_apply, Pi.one_apply]
  exact zeta_pow_three ζ _

theorem diagOf_unitary (w : UnitRaw.W N) :
    (((diagOf ζ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map (fun c => c ^ 2 ^ 1))ᵀ *
      ((diagOf ζ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
  rw [coe_diagOf, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h3 : ((ζ (Multiplicative.ofAdd (w i)) : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, zeta_pow_three, Units.val_one]
  linear_combination h3

theorem diagOf_mem_guSet (w : UnitRaw.W N) : diagOf ζ w ∈ LargeEvenGUSet (Fin N) K (2 ^ 1) :=
  ⟨1, one_ne_zero, one_pow _, by rw [one_smul]; exact diagOf_unitary ζ w⟩

theorem diagOf_mem_normalizer (h : UnitaryFieldData 2 1 K) (w : UnitRaw.W N) :
    diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
  TableBUE.gu_subset_normalizer h (diagOf_mem_guSet ζ w)

theorem diagOf_mem_unitarySU (h : UnitaryFieldData 2 1 K) {w : UnitRaw.W N}
    (hw : ∑ i, w i = 0) : diagOf ζ w ∈ unitarySU 2 1 K N := by
  rw [mem_unitarySU_iff h]
  refine ⟨by rw [det_diagOf, hw, ofAdd_zero, map_one, Units.val_one], ?_⟩
  have hbar : (⇑h.bar : K → K) = fun c => c ^ 2 ^ 1 := funext fun c => h.bar_apply c
  rw [hbar]
  exact diagOf_unitary ζ w

private theorem card_multiplicative_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem card_units_of_card_four (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem exists_injective_zeta (hK : Nat.card K = 4) :
    ∃ ζ : Multiplicative (ZMod 3) →* Kˣ, Function.Injective ζ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e := mulEquivOfPrimeCardEq (p := 3) card_multiplicative_zmod_three
    (card_units_of_card_four hK)
  exact ⟨e.toMonoidHom, e.injective⟩

theorem zeta_surjective [Finite K] (hK : Nat.card K = 4) (hζ : Function.Injective ζ) :
    Function.Surjective ζ :=
  (hζ.bijective_of_nat_card_le (by
    rw [card_units_of_card_four hK, card_multiplicative_zmod_three])).2

theorem exists_diagOf_eq (hζ : Function.Surjective ζ) (D : GL (Fin N) K)
    (hD : (D : Matrix (Fin N) (Fin N) K).IsDiag) : ∃ w : UnitRaw.W N, diagOf ζ w = D := by
  classical
  have hdet : (D : Matrix (Fin N) (Fin N) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdiag : diagonal (fun i => (D : Matrix (Fin N) (Fin N) K) i i) =
      (D : Matrix (Fin N) (Fin N) K) := (Matrix.isDiag_iff_diagonal_diag _).mp hD
  have hne : ∀ i, (D : Matrix (Fin N) (Fin N) K) i i ≠ 0 := by
    intro i
    rw [← hdiag, Matrix.det_diagonal] at hdet
    exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  choose x hx using fun i => hζ (Units.mk0 _ (hne i))
  refine ⟨fun i => Multiplicative.toAdd (x i), Units.ext ?_⟩
  rw [coe_diagOf, ← hdiag]
  congr 1
  funext i
  simp only [ofAdd_toAdd, hx i, Units.val_mk0]

theorem projConj_diagOf_eq_one_iff (h : UnitaryFieldData 2 1 K) [Finite K] (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) (hN : 4 ≤ N) (w : UnitRaw.W N) :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ = 1 ↔
      w ∈ UnitRaw.oneLine N := by
  constructor
  · intro h1
    have hdq : (N, 2 ^ 1) ≠ (3, 2) := fun he => by
      have := congrArg Prod.fst he
      simp only at this
      omega
    rw [← diagOf_mem_scalars_iff ζ hζ]
    exact TableBUE.mem_scalars_of_projConj_eq_one h (by rw [hK]; norm_num) (by omega) hdq
      Nat.prime_three (by norm_num) h1
  · intro hw
    exact TableB.projConj_of_scalar _ (diagOf_mem_scalars_of_mem_oneLine ζ hw)

theorem projConj_diagOf_eq_iff (h : UnitaryFieldData 2 1 K) [Finite K] (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) (hN : 4 ≤ N) (w w' : UnitRaw.W N) :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ ↔
      (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ w' := by
  have hsub : (⟨diagOf ζ (w - w'), diagOf_mem_normalizer ζ h (w - w')⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ *
        (⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ :
          Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))⁻¹ :=
    Subtype.ext (diagOf_sub ζ w w')
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    ← projConj_diagOf_eq_one_iff ζ h hK hζ hN, hsub, map_mul, map_inv, mul_inv_eq_one]

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
