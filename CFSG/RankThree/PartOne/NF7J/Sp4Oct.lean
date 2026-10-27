module

public import CFSG.RankThree.PartOne.KF.R7Levi2
public import CFSG.RankThree.PartOne.HESS.SL2Swap
public import CFSG.RankThree.PartOne.NF7J.OctNC

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.HESS

@[expose] def octN2 : Fin 8 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]]

theorem octN2_sq : ∀ i, octN2 i * octN2 i = 0 := by decide

theorem octN2_gram1 : ∀ i, (octN2 i)ᵀ * antidiag 4 = antidiag 4 * octN2 i := by decide

theorem octN2_gram2 : ∀ i, (octN2 i)ᵀ * antidiag 4 * octN2 i = 0 := by decide

theorem octN2_comm : ∀ i j : Fin 8, ¬ OctNC i j → octN2 i * octN2 j = octN2 j * octN2 i := by decide

theorem octN2_ncomm : ∀ i j : Fin 8, OctNC i j → octN2 i * octN2 j ≠ octN2 j * octN2 i := by decide

theorem octN2_ne_zero : ∀ i : Fin 8, ∃ p : Fin 4 × Fin 4, octN2 i p.1 p.2 = 1 := by decide

theorem octN2_even : ∀ p : Fin 8, p.val % 2 = 0 →
    octN2 p * octN2 (p + 3) + octN2 (p + 3) * octN2 p = octN2 (p + 1) ∧
      octN2 p * octN2 (p + 3) * octN2 p = 0 ∧
      octN2 (p + 3) * octN2 p * octN2 (p + 3) = octN2 (p + 2) ∧
      octN2 p * octN2 (p + 3) * octN2 p * octN2 (p + 3) = 0 := by decide

theorem octN2_odd : ∀ p : Fin 8, p.val % 2 = 1 →
    octN2 p * octN2 (p + 3) + octN2 (p + 3) * octN2 p = octN2 (p + 2) ∧
      octN2 p * octN2 (p + 3) * octN2 p = octN2 (p + 1) ∧
      octN2 (p + 3) * octN2 p * octN2 (p + 3) = 0 ∧
      octN2 p * octN2 (p + 3) * octN2 p * octN2 (p + 3) = 0 := by decide


@[expose] def Pm : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]]

@[expose] def wperm (i : Fin 2) (j : Fin 8) : Fin 8 := if i = 0 then 2 - j else 4 - j

theorem Pm_sq : ∀ i, Pm i * Pm i = 1 := by decide

theorem Pm_gram : ∀ i, (Pm i)ᵀ * antidiag 4 * Pm i = antidiag 4 := by decide

theorem Pm_oct : ∀ (i : Fin 2) (j : Fin 8), Pm i * octN2 j = octN2 (wperm i j) * Pm i := by decide

section KLevel

variable {K : Type} [Field K] [CharP K 2]

@[expose] def f2 (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

@[expose] def octN (i : Fin 8) : Matrix (Fin 4) (Fin 4) K := (octN2 i).map (f2 K)

theorem antidiag_map : ((antidiag 4 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (f2 K) : Matrix (Fin 4) (Fin 4) K) =
    antidiag 4 := by
  ext i j
  simp only [antidiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem octN_sq (i : Fin 8) : octN i * octN i = (0 : Matrix (Fin 4) (Fin 4) K) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (octN2_sq i)
  simpa [octN, Matrix.map_mul] using h

theorem octN_gram1 (i : Fin 8) : (octN i)ᵀ * antidiag 4 = antidiag 4 * (octN i : Matrix (Fin 4) (Fin 4) K) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (octN2_gram1 i)
  simpa [octN, Matrix.map_mul, Matrix.transpose_map, antidiag_map] using h

theorem octN_gram2 (i : Fin 8) :
    (octN i)ᵀ * antidiag 4 * octN i = (0 : Matrix (Fin 4) (Fin 4) K) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (octN2_gram2 i)
  simpa [octN, Matrix.map_mul, Matrix.transpose_map, antidiag_map] using h

theorem octN_comm (i j : Fin 8) (h : ¬ OctNC i j) : octN i * octN j = (octN j * octN i : Matrix (Fin 4) (Fin 4) K) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (octN2_comm i j h)
  simpa [octN, Matrix.map_mul] using h

@[expose] def octMat (i : Fin 8) (s : K) : Matrix (Fin 4) (Fin 4) K := 1 + s • octN i

theorem octMat_mul (i : Fin 8) (s t : K) : octMat i s * octMat i t = octMat i (s + t) := by
  have h := octN_sq (K := K) i
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [octMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h, smul_zero, add_zero, add_smul]
  abel

theorem octMat_zero (i : Fin 8) : octMat i (0 : K) = 1 := by simp [octMat]

theorem octMat_sq (i : Fin 8) (s : K) : octMat i s * octMat i s = 1 := by
  rw [octMat_mul, CharTwo.add_self_eq_zero, octMat_zero]

theorem octMat_gram (i : Fin 8) (s : K) :
    (octMat i s)ᵀ * antidiag 4 * octMat i s = antidiag 4 := by
  have g1 := octN_gram1 (K := K) i
  have g2 := octN_gram2 (K := K) i
  simp only [octMat, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [g2, smul_zero, add_zero, g1, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul,
    add_zero]

@[expose] noncomputable def octEl (i : Fin 8) (s : K) : ↥(spRev K) :=
  ⟨{ val := octMat i s, inv := octMat i s, val_inv := octMat_sq i s, inv_val := octMat_sq i s }, by
    rw [mem_spRev_iff]
    exact octMat_gram i s⟩

theorem coe_octEl (i : Fin 8) (s : K) :
    (((octEl i s : ↥(spRev K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = octMat i s := rfl

theorem octEl_mul (i : Fin 8) (s t : K) : octEl i s * octEl i t = octEl i (s + t) := by
  apply Subtype.ext
  apply Units.ext
  exact octMat_mul i s t

theorem octEl_zero (i : Fin 8) : octEl i (0 : K) = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact octMat_zero i

theorem octEl_sq (i : Fin 8) (s : K) : octEl i s * octEl i s = 1 := by
  rw [octEl_mul, CharTwo.add_self_eq_zero, octEl_zero]

theorem octEl_inv (i : Fin 8) (s : K) : (octEl i s)⁻¹ = octEl i s :=
  inv_eq_of_mul_eq_one_right (octEl_sq i s)

theorem octEl_injective (i : Fin 8) : Function.Injective (octEl (K := K) i) := by
  intro s t h
  obtain ⟨⟨a, b⟩, hab⟩ := octN2_ne_zero i
  have h1 : octMat i s = octMat i t := congrArg (fun g : ↥(spRev K) => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  have h2 := congrFun (congrFun h1 a) b
  have hN : (octN i : Matrix (Fin 4) (Fin 4) K) a b = 1 := by
    simp [octN, hab]
  simpa [octMat, Matrix.one_apply, hN] using h2

@[expose] noncomputable def octHom (i : Fin 8) : Multiplicative K →* ↥(spRev K) where
  toFun c := octEl i (Multiplicative.toAdd c)
  map_one' := by simpa using octEl_zero i
  map_mul' a b := (octEl_mul i _ _).symm

@[expose] noncomputable def octSub (K : Type) [Field K] [CharP K 2] (i : Fin 8) : Subgroup ↥(spRev K) :=
  (octHom (K := K) i).range

theorem mem_octSub_iff {i : Fin 8} {g : ↥(spRev K)} : g ∈ octSub K i ↔ ∃ s : K, g = octEl i s :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨s, hs⟩ => ⟨Multiplicative.ofAdd s, hs.symm⟩⟩

theorem octEl_mem (i : Fin 8) (s : K) : octEl i s ∈ octSub K i := mem_octSub_iff.2 ⟨s, rfl⟩

theorem octSub_sq {i : Fin 8} {g : ↥(spRev K)} (hg : g ∈ octSub K i) : g * g = 1 := by
  obtain ⟨s, rfl⟩ := mem_octSub_iff.1 hg
  exact octEl_sq i s

theorem octSub_card (i : Fin 8) : Nat.card (octSub K i) = Nat.card K := by
  have hb : Function.Bijective (fun s : K => (⟨octEl i s, octEl_mem i s⟩ : octSub K i)) :=
    ⟨fun a b h => octEl_injective i (congrArg Subtype.val h), fun g => by
      obtain ⟨s, hs⟩ := mem_octSub_iff.1 g.2
      exact ⟨s, Subtype.ext hs.symm⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

theorem octMat_mul_other (i j : Fin 8) (s t : K) :
    octMat i s * octMat j t = 1 + s • octN i + t • octN j + (s * t) • (octN i * octN j) := by
  simp only [octMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_add]
  rw [mul_comm t s]
  abel

theorem octMat_comm {i j : Fin 8} (h : ¬ OctNC i j) (s t : K) :
    octMat i s * octMat j t = octMat j t * octMat i s := by
  rw [octMat_mul_other, octMat_mul_other j i t s, ← octN_comm i j h, mul_comm t s]
  abel

theorem octEl_comm {i j : Fin 8} (h : ¬ OctNC i j) (s t : K) :
    octEl i s * octEl j t = octEl j t * octEl i s := by
  apply Subtype.ext
  apply Units.ext
  exact octMat_comm h s t

theorem octSub_comm {i j : Fin 8} (h : ¬ OctNC i j) :
    ∀ x ∈ octSub K i, ∀ y ∈ octSub K j, x * y = y * x := by
  intro x hx y hy
  obtain ⟨s, rfl⟩ := mem_octSub_iff.1 hx
  obtain ⟨t, rfl⟩ := mem_octSub_iff.1 hy
  exact octEl_comm h s t

theorem octSub_ncomm {i j : Fin 8} (h : OctNC i j) :
    ∃ x ∈ octSub K i, ∃ y ∈ octSub K j, x * y ≠ y * x := by
  refine ⟨octEl i 1, octEl_mem i 1, octEl j 1, octEl_mem j 1, fun hxy => ?_⟩
  have h1 : octMat i 1 * octMat j 1 = octMat j 1 * octMat i (1 : K) :=
    congrArg (fun g : ↥(spRev K) => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hxy
  rw [octMat_mul_other, octMat_mul_other] at h1
  simp only [one_smul, mul_one] at h1
  have h3 : octN i * octN j = (octN j * octN i : Matrix (Fin 4) (Fin 4) K) := by
    have h1' : (1 : Matrix (Fin 4) (Fin 4) K) + octN i + octN j + octN i * octN j =
        1 + octN i + octN j + octN j * octN i := by
      rw [h1]
      abel
    exact add_left_cancel h1'
  have h6 := octN2_ncomm i j h
  apply h6
  have h7 : ((octN2 i * octN2 j : Matrix (Fin 4) (Fin 4) (ZMod 2))).map (f2 K) =
      ((octN2 j * octN2 i : Matrix (Fin 4) (Fin 4) (ZMod 2))).map (f2 K) := by
    simpa [octN, Matrix.map_mul] using h3
  exact Matrix.map_injective (f2 K).injective h7

theorem four_prod {n : ℕ} (X Y : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (hY : Y * Y = 0)
    (s t : K) :
    (1 + s • X) * (1 + t • Y) * (1 + s • X) * (1 + t • Y) =
      1 + (s * t) • (X * Y + Y * X) + (s * s * t) • (X * Y * X) + (s * t * t) • (Y * X * Y) +
        (s * s * t * t) • (X * Y * X * Y) := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, mul_assoc, hX, hY, smul_zero, mul_zero, add_zero]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) = 1 := by rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
  match_scalars <;> ring_nf <;> simp [h2, h3]

theorem octN2_adj : ∀ p : Fin 8, octN2 (p + 1) * octN2 (p + 2) = 0 := by decide

theorem octN_adj (p : Fin 8) : octN (p + 1) * octN (p + 2) = (0 : Matrix (Fin 4) (Fin 4) K) := by
  simpa [octN, Matrix.map_mul] using congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (octN2_adj p)

theorem octMat_adj (p : Fin 8) (u v : K) :
    octMat (p + 1) u * octMat (p + 2) v = 1 + u • octN (p + 1) + v • octN (p + 2) := by
  rw [octMat_mul_other, octN_adj, smul_zero, add_zero]

theorem map_f2 {a b : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : a = b) :
    (a.map (f2 K)) = b.map (f2 K) := by rw [h]

theorem octEl_commutator_even (p : Fin 8) (hp : p.val % 2 = 0) (s t : K) :
    octEl p s * octEl (p + 3) t * octEl p s * octEl (p + 3) t =
      octEl (p + 1) (s * t) * octEl (p + 2) (s * t ^ 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := octN2_even p hp
  have e1 : octN p * octN (p + 3) + octN (p + 3) * octN p = (octN (p + 1) : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul, Matrix.map_add] using map_f2 (K := K) h1
  have e2 : octN p * octN (p + 3) * octN p = (0 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h2
  have e3 : octN (p + 3) * octN p * octN (p + 3) = (octN (p + 2) : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h3
  have e4 : octN p * octN (p + 3) * octN p * octN (p + 3) = (0 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h4
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_octEl]
  rw [octMat_adj]
  simp only [octMat]
  rw [four_prod _ _ (octN_sq p) (octN_sq (p + 3)), e4, e1, e2, e3,
    show s * t * t = s * t ^ 2 by ring]
  simp only [smul_zero, add_zero]

theorem octEl_commutator_odd (p : Fin 8) (hp : p.val % 2 = 1) (s t : K) :
    octEl p s * octEl (p + 3) t * octEl p s * octEl (p + 3) t =
      octEl (p + 1) (s ^ 2 * t) * octEl (p + 2) (s * t) := by
  obtain ⟨h1, h2, h3, h4⟩ := octN2_odd p hp
  have e1 : octN p * octN (p + 3) + octN (p + 3) * octN p = (octN (p + 2) : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul, Matrix.map_add] using map_f2 (K := K) h1
  have e2 : octN p * octN (p + 3) * octN p = (octN (p + 1) : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h2
  have e3 : octN (p + 3) * octN p * octN (p + 3) = (0 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h3
  have e4 : octN p * octN (p + 3) * octN p * octN (p + 3) = (0 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [octN, Matrix.map_mul] using map_f2 (K := K) h4
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_octEl]
  rw [octMat_adj]
  simp only [octMat]
  rw [four_prod _ _ (octN_sq p) (octN_sq (p + 3)), e4, e1, e2, e3,
    show s * s * t = s ^ 2 * t by ring]
  simp only [smul_zero, add_zero]
  abel

theorem octEl_adj_comm (p : Fin 8) (a b : K) :
    octEl (p + 1) a * octEl (p + 2) b = octEl (p + 2) b * octEl (p + 1) a := by
  apply octEl_comm
  revert p
  decide

theorem octEl_quot (p : Fin 8) (a b b' : K) :
    (octEl (p + 1) a * octEl (p + 2) b) * (octEl (p + 1) a * octEl (p + 2) b')⁻¹ =
      octEl (p + 2) (b + b') := by
  have hY : octEl (p + 1) a * octEl (p + 1) a = 1 := octEl_sq _ _
  calc (octEl (p + 1) a * octEl (p + 2) b) * (octEl (p + 1) a * octEl (p + 2) b')⁻¹
      = octEl (p + 1) a * (octEl (p + 2) b * octEl (p + 2) b') * octEl (p + 1) a := by
        rw [_root_.mul_inv_rev, octEl_inv, octEl_inv]
        simp only [mul_assoc]
    _ = octEl (p + 1) a * octEl (p + 2) (b + b') * octEl (p + 1) a := by rw [octEl_mul]
    _ = octEl (p + 2) (b + b') * octEl (p + 1) a * octEl (p + 1) a := by rw [octEl_adj_comm]
    _ = octEl (p + 2) (b + b') := by rw [mul_assoc, hY, mul_one]

open scoped commutatorElement in
theorem commutator_octEl (p : Fin 8) (s t : K) :
    ⁅octEl p s, octEl (p + 3) t⁆ = octEl p s * octEl (p + 3) t * octEl p s * octEl (p + 3) t := by
  rw [commutatorElement_def, octEl_inv, octEl_inv]

open scoped commutatorElement in
theorem octSub_gen (p : Fin 8) {t₀ : K} (h0 : t₀ ≠ 0) (h1 : t₀ ≠ 1) :
    octSub K (p + 1) ≤ ⁅octSub K p, octSub K (p + 3)⁆ ∧
      octSub K (p + 2) ≤ ⁅octSub K p, octSub K (p + 3)⁆ := by
  have hmem : ∀ s t : K, octEl p s * octEl (p + 3) t * octEl p s * octEl (p + 3) t ∈
      ⁅octSub K p, octSub K (p + 3)⁆ := fun s t => by
    rw [← commutator_octEl]
    exact Subgroup.commutator_mem_commutator (octEl_mem p s) (octEl_mem (p + 3) t)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hq1 : t₀ + 1 ≠ 0 := fun h => h1 (by linear_combination h - h2)
  have hq : t₀ ^ 2 + t₀ ≠ 0 := by
    intro h
    have : t₀ * (t₀ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact h0 h'
    · exact hq1 h'
  have hZ : ∀ u : K, octEl (p + 2) u ∈ ⁅octSub K p, octSub K (p + 3)⁆ ∧
      octEl (p + 1) u ∈ ⁅octSub K p, octSub K (p + 3)⁆ := by
    intro u
    rcases Nat.mod_two_eq_zero_or_one p.val with hp | hp
    ·
      have hZu : octEl (p + 2) u ∈ ⁅octSub K p, octSub K (p + 3)⁆ := by
        set s := u * (t₀ ^ 2 + t₀)⁻¹ with hs
        have hsu : s * t₀ ^ 2 + s * t₀ = u := by
          rw [hs]
          field_simp
        have := Subgroup.mul_mem _ (hmem s t₀) (Subgroup.inv_mem _ (hmem (s * t₀) 1))
        rw [octEl_commutator_even p hp, octEl_commutator_even p hp, mul_one, one_pow, mul_one,
          octEl_quot, hsu] at this
        exact this
      refine ⟨hZu, ?_⟩
      have := Subgroup.mul_mem _ (hmem u 1) (Subgroup.inv_mem _ hZu)
      rw [octEl_commutator_even p hp, mul_one, one_pow, mul_one, ← octEl_inv (p + 2) u,
        mul_inv_cancel_right] at this
      exact this
    ·
      have hp' : p.val % 2 = 1 := hp
      have hq1' : 1 + t₀ ≠ 0 := by rwa [add_comm]
      have hZu : octEl (p + 2) u ∈ ⁅octSub K p, octSub K (p + 3)⁆ := by
        set v := u * (t₀ + t₀ ^ 2)⁻¹ with hv
        have hvu : t₀ * v + t₀ ^ 2 * v = u := by
          rw [hv]
          have : t₀ + t₀ ^ 2 ≠ 0 := by
            have : t₀ + t₀ ^ 2 = t₀ ^ 2 + t₀ := by ring
            rw [this]; exact hq
          field_simp
        have := Subgroup.mul_mem _ (hmem t₀ v) (Subgroup.inv_mem _ (hmem 1 (t₀ ^ 2 * v)))
        rw [octEl_commutator_odd p hp', octEl_commutator_odd p hp'] at this
        simp only [one_pow, one_mul] at this
        rw [octEl_quot, hvu] at this
        exact this
      refine ⟨hZu, ?_⟩
      have := Subgroup.mul_mem _ (hmem 1 u) (Subgroup.inv_mem _ hZu)
      rw [octEl_commutator_odd p hp'] at this
      simp only [one_pow, one_mul] at this
      rw [← octEl_inv (p + 2) u, mul_inv_cancel_right] at this
      exact this
  exact ⟨fun g hg => by
    obtain ⟨v, rfl⟩ := mem_octSub_iff.1 hg
    exact (hZ v).2, fun g hg => by
    obtain ⟨v, rfl⟩ := mem_octSub_iff.1 hg
    exact (hZ v).1⟩

@[expose] def octChar (i : Fin 8) (a b : Kˣ) : Kˣ :=
  ![a ^ 2, a * b, b ^ 2, b * a⁻¹, (a ^ 2)⁻¹, (a * b)⁻¹, (b ^ 2)⁻¹, a * b⁻¹] i

omit [CharP K 2] in
theorem diag_mul_of_support {d : Fin 4 → K} {c : K} {N : Matrix (Fin 4) (Fin 4) K}
    (h : ∀ k l, N k l ≠ 0 → d k = c * d l) :
    Matrix.diagonal d * N = c • (N * Matrix.diagonal d) := by
  ext k l
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hN : N k l = 0
  · simp [hN]
  · rw [h k l hN]
    ring

theorem octN_support (i : Fin 8) (a b : Kˣ) :
    ∀ k l, (octN i : Matrix (Fin 4) (Fin 4) K) k l ≠ 0 →
      ((dvec4 a b k : Kˣ) : K) = (octChar i a b : K) * ((dvec4 a b l : Kˣ) : K) := by
  intro k l hkl
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hb : (b : K) ≠ 0 := b.ne_zero
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [octN, octN2, f2, octChar, dvec4] at hkl ⊢ <;> field_simp

theorem diag_mul_octMat (i : Fin 8) (a b : Kˣ) (s : K) :
    Matrix.diagonal (fun k => ((dvec4 a b k : Kˣ) : K)) * octMat i s =
      octMat i ((octChar i a b : K) * s) * Matrix.diagonal (fun k => ((dvec4 a b k : Kˣ) : K)) := by
  have h := diag_mul_of_support (octN_support (K := K) i a b)
  simp only [octMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, h, smul_smul]
  rw [mul_comm s]

theorem spDiag_mul_octEl (i : Fin 8) (a b : Kˣ) (s : K) :
    spDiag K (a, b) * octEl i s = octEl i ((octChar i a b : K) * s) * spDiag K (a, b) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_octEl, coe_spDiag, diagU_val]
  exact diag_mul_octMat i a b s

theorem spDiag_conj_octEl (i : Fin 8) (a b : Kˣ) (s : K) :
    spDiag K (a, b) * octEl i s * (spDiag K (a, b))⁻¹ = octEl i ((octChar i a b : K) * s) := by
  rw [spDiag_mul_octEl, mul_inv_cancel_right]

theorem spDiag_mem_normalizer_octSub (i : Fin 8) (a b : Kˣ) :
    spDiag K (a, b) ∈ Subgroup.normalizer (octSub K i : Set ↥(spRev K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨s, rfl⟩ := mem_octSub_iff.1 hx
    rw [spDiag_conj_octEl]
    exact octEl_mem i _
  · intro hx
    obtain ⟨s, hs⟩ := mem_octSub_iff.1 hx
    have h1 : x = (spDiag K (a, b))⁻¹ * octEl i s * spDiag K (a, b) := by
      rw [← hs]
      group
    have h2 : (spDiag K (a, b))⁻¹ = spDiag K (a⁻¹, b⁻¹) := by
      rw [← map_inv]
      rfl
    have h3 : spDiag K (a⁻¹, b⁻¹) * octEl i s * (spDiag K (a⁻¹, b⁻¹))⁻¹ =
        octEl i ((octChar i a⁻¹ b⁻¹ : K) * s) := spDiag_conj_octEl i a⁻¹ b⁻¹ s
    rw [h1, h2]
    have h4 : (spDiag K (a⁻¹, b⁻¹))⁻¹ = spDiag K (a, b) := by
      rw [← map_inv]
      simp
    rw [← h4, h3]
    exact octEl_mem i _

@[expose] noncomputable def wEl (i : Fin 2) : ↥(spRev K) :=
  ⟨{ val := (Pm i).map (f2 K), inv := (Pm i).map (f2 K),
     val_inv := by
       have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (Pm_sq i)
       simpa [Matrix.map_mul] using h
     inv_val := by
       have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (Pm_sq i)
       simpa [Matrix.map_mul] using h }, by
    rw [mem_spRev_iff]
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (Pm_gram i)
    simpa [Matrix.map_mul, Matrix.transpose_map, antidiag_map] using h⟩

theorem coe_wEl (i : Fin 2) :
    (((wEl i : ↥(spRev K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (Pm i).map (f2 K) := rfl

theorem wEl_sq (i : Fin 2) : (wEl i : ↥(spRev K)) * wEl i = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (Pm_sq i)
  simpa [coe_wEl, Matrix.map_mul] using h

theorem wEl_inv (i : Fin 2) : (wEl i : ↥(spRev K))⁻¹ = wEl i := inv_eq_of_mul_eq_one_right (wEl_sq i)

theorem wEl_mul_octEl (i : Fin 2) (j : Fin 8) (s : K) :
    wEl i * octEl j s = octEl (wperm i j) s * wEl i := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_wEl, coe_octEl, octMat, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M.map (f2 K)) (Pm_oct i j)
  have h' : (Pm i).map (f2 K) * (octN j : Matrix (Fin 4) (Fin 4) K) =
      (octN (wperm i j) : Matrix (Fin 4) (Fin 4) K) * (Pm i).map (f2 K) := by
    simpa [octN, Matrix.map_mul] using h
  rw [h']

theorem wEl_conj_octEl (i : Fin 2) (j : Fin 8) (s : K) :
    wEl i * octEl j s * (wEl i)⁻¹ = octEl (wperm i j) s := by
  rw [wEl_mul_octEl, mul_inv_cancel_right]

@[expose] def wtor (i : Fin 2) (a b : Kˣ) : Kˣ × Kˣ := if i = 0 then (b, a) else (a⁻¹, b)

theorem wEl_mul_spDiag (i : Fin 2) (a b : Kˣ) :
    (wEl i : ↥(spRev K)) * spDiag K (a, b) = spDiag K (wtor i a b) * wEl i := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_wEl, coe_spDiag, diagU_val]
  fin_cases i <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [Pm, wtor, dvec4, f2, Matrix.mul_apply, Matrix.diagonal_apply]

theorem wEl_conj_spDiag (i : Fin 2) (a b : Kˣ) :
    (wEl i : ↥(spRev K)) * spDiag K (a, b) * (wEl i)⁻¹ = spDiag K (wtor i a b) := by
  rw [wEl_mul_spDiag, mul_inv_cancel_right]

theorem spBlock_xp (c : K) : spBlock (xp c) = (octEl 0 c : ↥(spRev K)) := by
  apply Subtype.ext
  apply Units.ext
  show blk22 ((xp c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [blk22, xp, coe_octEl, octMat, octN, octN2, f2]

theorem spBlock_xm (c : K) : spBlock (xm c) = (octEl 4 c : ↥(spRev K)) := by
  apply Subtype.ext
  apply Units.ext
  show blk22 ((xm c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [blk22, xm, coe_octEl, octMat, octN, octN2, f2]

theorem spBlock'_xp (c : K) : spBlock' (xp c) = (octEl 7 c : ↥(spRev K)) := by
  apply Subtype.ext
  apply Units.ext
  show blk4 ((xp c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [blk4, xp, coe_octEl, octMat, octN, octN2, f2]

theorem spBlock'_xm (c : K) : spBlock' (xm c) = (octEl 3 c : ↥(spRev K)) := by
  apply Subtype.ext
  apply Units.ext
  show blk4 ((xm c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [blk4, xm, coe_octEl, octMat, octN, octN2, f2]

theorem octSub_zero_eq : octSub K 0 = (Uplus K).map (spBlock (K := K)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := mem_octSub_iff.1 hg
    exact ⟨xp c, xp_mem c, spBlock_xp c⟩
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xp_of_mem_Uplus hM, spBlock_xp]
    exact octEl_mem 0 _

theorem octSub_four_eq : octSub K 4 = (Uminus K).map (spBlock (K := K)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := mem_octSub_iff.1 hg
    exact ⟨xm c, xm_mem c, spBlock_xm c⟩
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xm_of_mem_Uminus hM, spBlock_xm]
    exact octEl_mem 4 _

theorem octSub_seven_eq : octSub K 7 = (Uplus K).map (spBlock' (K := K)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := mem_octSub_iff.1 hg
    exact ⟨xp c, xp_mem c, spBlock'_xp c⟩
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xp_of_mem_Uplus hM, spBlock'_xp]
    exact octEl_mem 7 _

theorem octSub_three_eq : octSub K 3 = (Uminus K).map (spBlock' (K := K)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := mem_octSub_iff.1 hg
    exact ⟨xm c, xm_mem c, spBlock'_xm c⟩
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xm_of_mem_Uminus hM, spBlock'_xm]
    exact octEl_mem 3 _

end KLevel

end CFSG.RankThree.PartOne.NF7J
