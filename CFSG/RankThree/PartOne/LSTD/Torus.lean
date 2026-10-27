module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.RankThree.PartOne.KF.U4Blk
public import CFSG.RankThree.PartOne.KF.U4Calc
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

section TorusElt

variable {n : ℕ}

theorem torusElt_mul (i j : Fin n) (u w : Kˣ) :
    torusElt i j (u * w) = torusElt i j u * torusElt i j w := by
  simp only [torusElt, mul_inv, Pi.mulSingle_mul]
  exact mul_mul_mul_comm _ _ _ _

theorem torusElt_one (i j : Fin n) : torusElt i j (1 : Kˣ) = 1 := by
  simp [torusElt]

theorem torusElt_pow (i j : Fin n) (u : Kˣ) (m : ℕ) :
    torusElt i j (u ^ m) = torusElt i j u ^ m := by
  induction m with
  | zero => simp [torusElt_one]
  | succ m ih => rw [pow_succ, torusElt_mul, ih, pow_succ]

end TorusElt

theorem exists_pow_eq_of_pow_five {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) {u : Kˣ} (hu : u ^ 5 = 1) :
    ∃ m < 5, ζ ^ m = u := by
  have hζK : IsPrimitiveRoot (ζ : K) 5 := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hu' : (u : K) ^ 5 = 1 := by
    have := congrArg (fun w : Kˣ => (w : K)) hu
    simpa using this
  obtain ⟨m, hm, hmu⟩ := hζK.eq_pow_of_pow_eq_one hu'
  exact ⟨m, hm, Units.ext (by simpa using hmu)⟩

theorem bar_mul_eq_one (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {u : Kˣ}
    (hu : u ^ 5 = 1) : hU.bar (u : K) * (u : K) = 1 :=
  KCUnitaryPlane.bar_eq_inv_of_pow_eq_one hU h5 (by
    have := congrArg (fun w : Kˣ => (w : K)) hu
    simpa using this)

theorem eq_torusElt_of_diagU_mem_blk {hU : UnitaryFieldData 2 f K} {a b : Fin 5} (hab : a ≠ b)
    {v : Fin 5 → Kˣ} (hv : diagU v ∈ blk hU hab) : v = torusElt a b (v a) := by
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hab).mp hv
  rw [diagU_val] at hgX
  have hout : ∀ k : Fin 5, k ≠ a → k ≠ b → v k = 1 := by
    intro k hka hkb
    have h1 := congrArg (fun M : Matrix (Fin 5) (Fin 5) K => M k k) hgX
    simp only [Matrix.diagonal_apply_eq] at h1
    rw [coordEmbed_apply_of_not_mem_left hka hkb] at h1
    exact Units.ext (by simpa using h1)
  have hdet : ((diagU v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    rw [diagU_val] at *
    rw [hgX, det_coordEmbed hab, ((mem_gramSU_iff_unitary hU).mp hX).2]
  rw [det_diagU] at hdet
  have hprod : ∏ i, (v i : K) = (v a : K) * (v b : K) := by
    rw [← Finset.prod_subset (Finset.subset_univ {a, b}) ?_, Finset.prod_pair hab]
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hout k hk.1 hk.2]
    simp
  rw [hprod] at hdet
  have hba : v b = (v a)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, Units.val_one]
    exact hdet
  funext k
  by_cases hka : k = a
  · subst hka
    rw [torusElt_apply_left hab]
  · by_cases hkb : k = b
    · subst hkb
      rw [torusElt_apply_right hab, hba]
    · rw [torusElt_apply_other hka hkb, hout k hka hkb]

@[expose] def tcls (n c k : Fin 5) : Fin 3 := if k = n then 0 else if k = c then 1 else 2

theorem torusElt_apply_eq_iff {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹) {n c : Fin 5} (hnc : n ≠ c)
    (a b : Fin 5) : torusElt n c ζ a = torusElt n c ζ b ↔ tcls n c a = tcls n c b := by
  have hζ3 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  have hval : ∀ k : Fin 5, torusElt n c ζ k =
      (if k = n then ζ else if k = c then ζ⁻¹ else 1) := by
    intro k
    by_cases hkn : k = n
    · subst hkn
      simp [torusElt_apply_left hnc]
    · by_cases hkc : k = c
      · subst hkc
        simp [hkn, torusElt_apply_right hnc]
      · simp [hkn, hkc, torusElt_apply_other hkn hkc]
  rw [hval a, hval b]
  unfold tcls
  by_cases ha : a = n <;> by_cases hb : b = n <;> by_cases ha' : a = c <;> by_cases hb' : b = c <;>
    simp_all [Ne.symm hζ1, Ne.symm hζ2, Ne.symm hζ3]

theorem exists_witness_pair : ∀ a b d e : Fin 5, a ≠ b → d ≠ e →
    ¬ ((a = d ∧ b = e) ∨ (a = e ∧ b = d)) →
      ∃ n c : Fin 5, n ≠ c ∧ tcls n c a = tcls n c b ∧ tcls n c d ≠ tcls n c e := by
  decide

end CFSG.RankThree.PartOne.LSTD
