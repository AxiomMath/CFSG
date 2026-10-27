module

public import CFSG.LieType.SpecialLinear.CurtisDatum
public import CFSG.LieType.SpecialLinear.TypeLabel.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.SpecialLinear CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

private def c2slchi_rot (f p : ℕ) (r : Fin f) : Fin f :=
  ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩

private theorem c2slchi_sum_digit_eq {f n : ℕ} (ε : Fin f → Finset (Fin n)) (p : Fin n → Prop)
    [DecidablePred p] :
    (∑ j : Fin n, if p j then bDigit ε j else 0)
      = ∑ r : Fin f, 2 ^ (r : ℕ) * ((ε r).filter p).card := by
  have h1 : (∑ j : Fin n, if p j then bDigit ε j else 0)
      = ∑ j : Fin n, ∑ r : Fin f, (if p j ∧ j ∈ ε r then 2 ^ (r : ℕ) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : p j
    · simp only [hp, if_true, bDigit]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hj : j ∈ ε r <;> simp [hj]
    · simp [hp]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h2 : (∑ j : Fin n, if p j ∧ j ∈ ε r then 2 ^ (r : ℕ) else 0)
      = ∑ j : Fin n, 2 ^ (r : ℕ) * (if p j ∧ j ∈ ε r then 1 else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : p j ∧ j ∈ ε r <;> simp [h]
  rw [h2]
  have h3 : (∑ j : Fin n, 2 ^ (r : ℕ) * (if p j ∧ j ∈ ε r then 1 else 0))
      = 2 ^ (r : ℕ) * ∑ j : Fin n, (if j ∈ ε r then (if p j then 1 else 0) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ ε r <;> by_cases hp : p j <;> simp [hj, hp]
  rw [h3, Finset.sum_ite_mem, Finset.sum_boole]
  simp

private theorem c2slchi_bExp_eq_sum_bDigit {f n : ℕ} (ε : Fin f → Finset (Fin n)) (a : Fin n) :
    bExp ε a = ∑ j : Fin n, if a < j then bDigit ε j else 0 := by
  rw [bExp]
  exact (c2slchi_sum_digit_eq ε (fun j => a < j)).symm

private theorem c2slchi_dvd_bDigit_mul_pow_sub_one {m f p : ℕ}
    (ε : Fin f → Finset (Fin (m + 1)))
    (hrot : ∀ r : Fin f, ε ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (j : Fin (m + 1)) :
    2 ^ f - 1 ∣ bDigit ε j * (2 ^ p - 1) := by
  classical
  have hSsum : ∑ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r), 2 ^ (r : ℕ) =
      bDigit ε j := by
    rw [bDigit, Finset.sum_filter]
  have hSsub : (Finset.univ.filter (fun r : Fin f => j ∈ ε r)).image (c2slchi_rot f p) ⊆
      Finset.univ.filter (fun r : Fin f => j ∈ ε r) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hr ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    change j ∈ ε (⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ : Fin f)
    rw [hrot r]
    exact hr.2
  have hinj : Set.InjOn (c2slchi_rot f p)
      (↑(Finset.univ.filter (fun r : Fin f => j ∈ ε r)) : Set (Fin f)) := by
    intro x _ y _ hxy
    have h : ((x : ℕ) + p) % f = ((y : ℕ) + p) % f := congrArg Fin.val hxy
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' p h) x.isLt y.isLt)
  have hSimg : (Finset.univ.filter (fun r : Fin f => j ∈ ε r)).image (c2slchi_rot f p) =
      Finset.univ.filter (fun r : Fin f => j ∈ ε r) := by
    refine Finset.eq_of_subset_of_card_le hSsub ?_
    rw [Finset.card_image_of_injOn hinj]
  have hrotsum : ∑ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r),
      2 ^ (((r : ℕ) + p) % f) = bDigit ε j := by
    have h := (Finset.sum_image
      (s := Finset.univ.filter (fun r : Fin f => j ∈ ε r))
      (f := fun x : Fin f => 2 ^ (x : ℕ)) (g := c2slchi_rot f p) hinj).symm
    rw [hSimg] at h
    simpa only [c2slchi_rot] using h.trans hSsum
  have hterm : ∀ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r),
      2 ^ (p + (r : ℕ)) ≡ 2 ^ (((r : ℕ) + p) % f) [MOD 2 ^ f - 1] := by
    intro r _
    have hk : p + (r : ℕ) = ((r : ℕ) + p) % f + f * (((r : ℕ) + p) / f) :=
      (Nat.add_comm p (r : ℕ)).trans (Nat.mod_add_div _ _).symm
    rw [hk, pow_add]
    have h1 : 2 ^ f ≡ 1 [MOD 2 ^ f - 1] := Nat.modEq_sub (Nat.one_le_two_pow (n := f))
    calc 2 ^ (((r : ℕ) + p) % f) * 2 ^ (f * (((r : ℕ) + p) / f))
        = 2 ^ (((r : ℕ) + p) % f) * (2 ^ f) ^ (((r : ℕ) + p) / f) := by rw [pow_mul]
      _ ≡ 2 ^ (((r : ℕ) + p) % f) * 1 ^ (((r : ℕ) + p) / f) [MOD 2 ^ f - 1] :=
          (Nat.ModEq.refl _).mul (h1.pow _)
      _ = 2 ^ (((r : ℕ) + p) % f) := by rw [one_pow, mul_one]
  have hmain : 2 ^ p * bDigit ε j =
      ∑ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r), 2 ^ (p + (r : ℕ)) := by
    rw [← hSsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add]
  have hmod : 2 ^ p * bDigit ε j ≡ bDigit ε j [MOD 2 ^ f - 1] := by
    rw [hmain]
    calc ∑ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r), 2 ^ (p + (r : ℕ))
        ≡ ∑ r ∈ Finset.univ.filter (fun r : Fin f => j ∈ ε r),
            2 ^ (((r : ℕ) + p) % f) [MOD 2 ^ f - 1] := Nat.ModEq.sum hterm
      _ = bDigit ε j := hrotsum
  have hle : bDigit ε j ≤ 2 ^ p * bDigit ε j := by
    calc bDigit ε j = 1 * bDigit ε j := (one_mul _).symm
      _ ≤ 2 ^ p * bDigit ε j := Nat.mul_le_mul_right _ (Nat.one_le_two_pow (n := p))
  have hdvd : 2 ^ f - 1 ∣ 2 ^ p * bDigit ε j - bDigit ε j :=
    (Nat.modEq_iff_dvd' hle).mp hmod.symm
  rw [Nat.mul_sub_one, Nat.mul_comm (bDigit ε j) (2 ^ p)]
  exact hdvd

private theorem c2slchi_bDigit_modEq_mul_pow {m f p : ℕ}
    (ε : Fin f → Finset (Fin (m + 1)))
    (hrot : ∀ r : Fin f, ε ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (j : Fin (m + 1)) :
    bDigit ε j * 2 ^ p ≡ bDigit ε j [MOD 2 ^ f - 1] := by
  have hle : bDigit ε j ≤ bDigit ε j * 2 ^ p := by
    calc bDigit ε j = bDigit ε j * 1 := (mul_one _).symm
      _ ≤ bDigit ε j * 2 ^ p := Nat.mul_le_mul_left _ (Nat.one_le_two_pow (n := p))
  have hdvd : 2 ^ f - 1 ∣ bDigit ε j * 2 ^ p - bDigit ε j := by
    have h := c2slchi_dvd_bDigit_mul_pow_sub_one ε hrot j
    rwa [Nat.mul_sub_one] at h
  exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm

private theorem c2slchi_bExp_modEq {m f p : ℕ}
    (ε : Fin f → Finset (Fin (m + 1)))
    (hrot : ∀ r : Fin f, ε ⟨((r : ℕ) + p) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (a : Fin (m + 1)) :
    bExp ε a * 2 ^ p ≡ bExp ε a [MOD 2 ^ f - 1] := by
  classical
  have hb : bExp ε a = ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => a < j),
      bDigit ε j := by
    rw [c2slchi_bExp_eq_sum_bDigit, Finset.sum_filter]
  rw [hb, Finset.sum_mul]
  exact Nat.ModEq.sum fun j _ => c2slchi_bDigit_modEq_mul_pow ε hrot j

theorem w135c2_slChiEps_pow_of_rotate {m f p : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    {k : Type} [Field k] [Algebra F k] (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1)))
    (hrot : ∀ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ = ε r) :
    ∀ g ∈ (curtisDatum m F 2).H,
      slChiEps m (algebraMap F k) ε g ^ 2 ^ p = slChiEps m (algebraMap F k) ε g := by
  intro g hg
  let d : Fin (m + 1) → F := Matrix.diag (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  have hdiag : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    fun i j hij => (mem_curtisDatum_H_iff m F 2).mp hg i j hij
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [hdiag.diagonal_diag]
    exact g.2
  have hne : ∀ a, d a ≠ 0 := fun a => SpecialLinearGroup.diagonal_neZero d hdet a
  have hpow : ∀ a, d a ^ (2 ^ f - 1) = 1 := by
    intro a
    have h := FiniteField.pow_card_sub_one_eq_one (d a) (hne a)
    rwa [hF] at h
  have hprod : (∏ a, d a ^ bExp ε a) ^ 2 ^ p = ∏ a, d a ^ bExp ε a := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul]
    exact pow_eq_pow_of_modEq (c2slchi_bExp_modEq ε hrot a) (hpow a)
  rw [show slChiEps m (algebraMap F k) ε g =
    algebraMap F k (∏ a, d a ^ bExp ε a) from rfl, ← map_pow, hprod]

end CFSG.LocalAnalysis.WeakClosure81
