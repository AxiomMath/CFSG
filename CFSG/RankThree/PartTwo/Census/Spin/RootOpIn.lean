module

public import CFSG.RankThree.PartTwo.Census.Spin.RootOp

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

section Ring

variable {A : Type*} [Ring A]

theorem one_add_mul_eq {X Y : A} (hX : X * X = 0) :
    (1 + X) * Y = (Y + (X * Y - Y * X) - X * Y * X) * (1 + X) := by
  have e : (Y + (X * Y - Y * X) - X * Y * X) * (1 + X) =
      (1 + X) * Y - Y * (X * X) - X * Y * (X * X) := by noncomm_ring
  rw [e, hX, mul_zero, mul_zero, sub_zero, sub_zero]

theorem one_sub_mul_eq {X Y : A} (hX : X * X = 0) :
    (1 - X) * Y = (Y - (X * Y - Y * X) - X * Y * X) * (1 - X) := by
  have e : (Y - (X * Y - Y * X) - X * Y * X) * (1 - X) =
      (1 - X) * Y - Y * (X * X) + X * Y * (X * X) := by noncomm_ring
  rw [e, hX, mul_zero, mul_zero, sub_zero, add_zero]

theorem commute_mul_of_anticomm₂ {g x y : A} (hx : g * x = -(x * g)) (hy : g * y = -(y * g)) :
    g * (x * y) = x * y * g := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, mul_assoc]

theorem commute_weyl_of {E F g : A} (hE : Commute g E) (hF : Commute g F) :
    Commute g ((1 + E) * (1 - F) * (1 + E)) :=
  ((((Commute.one_right g).add_right hE).mul_right ((Commute.one_right g).sub_right hF)).mul_right
    ((Commute.one_right g).add_right hE))

theorem weyl_mul_inv {E F : A} (hE : E * E = 0) (hF : F * F = 0) :
    (1 + E) * (1 - F) * (1 + E) * ((1 - E) * (1 + F) * (1 - E)) = 1 := by
  have h1 : (1 + E) * (1 - E) = 1 := by
    rw [mul_sub, mul_one, add_mul, one_mul, hE, add_zero, add_sub_cancel_right]
  have h2 : (1 - F) * (1 + F) = 1 := by
    rw [mul_add, mul_one, sub_mul, one_mul, hF, sub_zero, sub_add_cancel]
  calc (1 + E) * (1 - F) * (1 + E) * ((1 - E) * (1 + F) * (1 - E))
      = (1 + E) * (1 - F) * ((1 + E) * (1 - E)) * (1 + F) * (1 - E) := by noncomm_ring
    _ = (1 + E) * ((1 - F) * (1 + F)) * (1 - E) := by rw [h1]; noncomm_ring
    _ = 1 := by rw [h2, mul_one, h1]

theorem weyl_inv_mul {E F : A} (hE : E * E = 0) (hF : F * F = 0) :
    (1 - E) * (1 + F) * (1 - E) * ((1 + E) * (1 - F) * (1 + E)) = 1 := by
  have h1 : (1 - E) * (1 + E) = 1 := by
    rw [mul_add, mul_one, sub_mul, one_mul, hE, sub_zero, sub_add_cancel]
  have h2 : (1 + F) * (1 - F) = 1 := by
    rw [mul_sub, mul_one, add_mul, one_mul, hF, add_zero, add_sub_cancel_right]
  calc (1 - E) * (1 + F) * (1 - E) * ((1 + E) * (1 - F) * (1 + E))
      = (1 - E) * (1 + F) * ((1 - E) * (1 + E)) * (1 - F) * (1 + E) := by noncomm_ring
    _ = (1 - E) * ((1 + F) * (1 - F)) * (1 + E) := by rw [h1]; noncomm_ring
    _ = 1 := by rw [h2, mul_one, h1]

end Ring

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

structure RootOpIn (D : Subgroup R.G) (L : Subfield K) (X : Matrix N N K) : Prop where
  sq : X * X = 0
  mem : ∀ u : K, ∃ g : R.G, R.mat g = 1 + u • X
  memD : ∀ u ∈ L, ∃ g ∈ D, R.mat g = 1 + u • X

variable {R} {D : Subgroup R.G} {L : Subfield K}

theorem RootOpIn.conj {X Y : Matrix N N K} (h : R.RootOpIn D L X) (ν : R.G)
    (hν : ∀ g ∈ D, ν * g * ν⁻¹ ∈ D) (hXY : R.mat ν * X = Y * R.mat ν) : R.RootOpIn D L Y := by
  have hinv : R.mat ν * R.mat ν⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have hinv' : R.mat ν⁻¹ * R.mat ν = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have hY : Y = R.mat ν * X * R.mat ν⁻¹ := by rw [hXY, mul_assoc, hinv, mul_one]
  have key : ∀ (g : R.G) (u : K), R.mat g = 1 + u • X →
      R.mat (ν * g * ν⁻¹) = 1 + u • Y := fun g u hg => by
    rw [mat_mul, mat_mul, hg, mul_add, mul_one, add_mul, hinv, mul_smul_comm, smul_mul_assoc,
      ← hY]
  refine ⟨?_, fun u => ?_, fun u hu => ?_⟩
  · rw [hY]
    calc R.mat ν * X * R.mat ν⁻¹ * (R.mat ν * X * R.mat ν⁻¹)
        = R.mat ν * X * (R.mat ν⁻¹ * R.mat ν) * X * R.mat ν⁻¹ := by noncomm_ring
      _ = 0 := by rw [hinv', mul_one, mul_assoc (R.mat ν) X X, h.sq]; simp
  · obtain ⟨g, hg⟩ := h.mem u
    exact ⟨ν * g * ν⁻¹, key g u hg⟩
  · obtain ⟨g, hgD, hg⟩ := h.memD u hu
    exact ⟨ν * g * ν⁻¹, hν g hgD, key g u hg⟩

theorem RootOpIn.neg {X : Matrix N N K} (h : R.RootOpIn D L X) : R.RootOpIn D L (-X) where
  sq := by rw [neg_mul_neg, h.sq]
  mem u := by
    obtain ⟨g, hg⟩ := h.mem (-u)
    exact ⟨g, by rw [hg, smul_neg, neg_smul]⟩
  memD u hu := by
    obtain ⟨g, hgD, hg⟩ := h.memD (-u) (L.neg_mem hu)
    exact ⟨g, hgD, by rw [hg, smul_neg, neg_smul]⟩

theorem RootOpIn.congr {X Y : Matrix N N K} (h : R.RootOpIn D L X) (hXY : X = Y) :
    R.RootOpIn D L Y := hXY ▸ h

theorem RootOpIn.of_x (i : ι) (hD : ∀ u ∈ L, R.x i u ∈ D) : R.RootOpIn D L (R.E i) :=
  ⟨(R.sqZero i).ee, fun u => ⟨R.x i u, by rw [mat_x, SqZeroPair.φ_upper]⟩,
    fun u hu => ⟨R.x i u, hD u hu, by rw [mat_x, SqZeroPair.φ_upper]⟩⟩

theorem RootOpIn.of_y (i : ι) (hD : ∀ u ∈ L, R.y i u ∈ D) : R.RootOpIn D L (R.F i) :=
  ⟨(R.sqZero i).ff, fun u => ⟨R.y i u, by rw [mat_y, SqZeroPair.φ_lower]⟩,
    fun u hu => ⟨R.y i u, hD u hu, by rw [mat_y, SqZeroPair.φ_lower]⟩⟩

theorem conj_mem_commutator {H : Subgroup R.G} {ν : R.G} (hν : ν ∈ H) (g : R.G)
    (hg : g ∈ ⁅H, H⁆) : ν * g * ν⁻¹ ∈ ⁅H, H⁆ := by
  have h1 : ν * g * ν⁻¹ = ⁅ν, g⁆ * g := by rw [commutatorElement_def]; group
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hν (commutator_le_self H hg)) hg

variable (hchar : (2 : K) = 0)
include hchar

theorem three_witness_pairs {F : R.G →* R.G} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X Y : κ → Matrix N N K} (hp : ∀ a, SqZeroPair (X a) (Y a)) (hne : ∀ a, X a ≠ 0)
    (gx gy : κ → R.G) (hgx : ∀ a, R.mat (gx a) = 1 + X a) (hgy : ∀ a, R.mat (gy a) = 1 + Y a)
    (hxD : ∀ a, gx a ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hyD : ∀ a, gy a ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (hXX : ∀ a b, a ≠ b → Commute (X a) (X b)) (hXY : ∀ a b, a ≠ b → Commute (X a) (Y b))
    (hYY : ∀ a b, a ≠ b → Commute (Y a) (Y b)) (t : R.G)
    (htD : t ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) (ht2 : t ^ 2 = 1)
    (htz : ∃ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, t * g ≠ g * t)
    (htx : ∀ a, Commute t (gx a)) (hty : ∀ a, Commute t (gy a)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card κ) := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  let g : κ → R.G := fun a => gx a * gy a
  have hφx : ∀ a, R.mat (gx a) = SqZeroPair.φ (X a) (Y a) 1 1 0 1 := fun a => by
    rw [hgx, SqZeroPair.φ_upper, one_smul]
  have hφy : ∀ a, R.mat (gy a) = SqZeroPair.φ (X a) (Y a) 1 0 1 1 := fun a => by
    rw [hgy, SqZeroPair.φ_lower, one_smul]
  have hφg : ∀ a, R.mat (g a) = SqZeroPair.φ (X a) (Y a) 0 1 1 1 := fun a => by
    show R.mat (gx a * gy a) = _
    rw [mat_mul, hφx, hφy, (hp a).φ_mul]
    simp only [mul_one, mul_zero, zero_add]
    rw [h11]
  have hg3 : ∀ a, g a ^ 3 = 1 := fun a => by
    apply R.mat_injective
    have e2 : SqZeroPair.φ (X a) (Y a) 0 1 1 1 * SqZeroPair.φ (X a) (Y a) 0 1 1 1 =
        SqZeroPair.φ (X a) (Y a) 1 1 1 0 := by
      rw [(hp a).φ_mul]
      simp only [mul_one, mul_zero, zero_add]
      rw [h11]
    have e3 : SqZeroPair.φ (X a) (Y a) 1 1 1 0 * SqZeroPair.φ (X a) (Y a) 0 1 1 1 =
        SqZeroPair.φ (X a) (Y a) 1 0 0 1 := by
      rw [(hp a).φ_mul]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      rw [h11]
    rw [pow_succ, pow_two, mat_mul, mat_mul, hφg, e2, e3, SqZeroPair.φ_one_zero_zero_one,
      mat_one]
  have hnc : ∀ a, ¬ Commute (g a) (gx a) := fun a h => by
    have hm : R.mat (g a) * R.mat (gx a) = R.mat (gx a) * R.mat (g a) := by
      rw [← mat_mul, ← mat_mul]
      exact congrArg R.mat h.eq
    rw [hφg, hφx, (hp a).φ_mul, (hp a).φ_mul] at hm
    simp only [mul_one, mul_zero, add_zero, zero_add] at hm
    rw [h11] at hm
    exact zero_ne_one (SqZeroPair.φ_injective (hp a) (hne a) hm).1
  let ϕ : ∀ _ : κ, Multiplicative (ZMod 3) →* R.G := fun a =>
    { toFun := fun k => g a ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hg3 a)] }
  have cxx : ∀ a b, a ≠ b → Commute (gx a) (gx b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgx, hgx, ← one_smul K (X a), ← one_smul K (X b)]
      exact commute_one_add_smul (hXX a b hab) 1 1)
  have cxy : ∀ a b, a ≠ b → Commute (gx a) (gy b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgx, hgy, ← one_smul K (X a), ← one_smul K (Y b)]
      exact commute_one_add_smul (hXY a b hab) 1 1)
  have cyy : ∀ a b, a ≠ b → Commute (gy a) (gy b) := fun a b hab =>
    R.commute_of_mat (by
      rw [hgy, hgy, ← one_smul K (Y a), ← one_smul K (Y b)]
      exact commute_one_add_smul (hYY a b hab) 1 1)
  have hgg : ∀ a b, a ≠ b → Commute (g a) (g b) := fun a b hab =>
    ((cxx a b hab).mul_right (cxy a b hab)).mul_left
      ((cxy b a (Ne.symm hab)).symm.mul_right (cyy a b hab))
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b hab u v =>
    (hgg a b hab).pow_pow _ _
  have hD : ∀ a u, ϕ a u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun a u =>
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (hxD a) (hyD a)) _
  have hp3 : ∀ (a : κ) (u : ZMod 3), 3 • u = 0 := fun a u => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hcard : Nat.card (κ → Multiplicative (ZMod 3)) = 3 ^ Fintype.card κ := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_eq_fintype_card]
  have hdet : ∀ a u, Commute (ϕ a u) (gx a) → u = 1 := fun a u h => by
    have hv := ZMod.val_lt (Multiplicative.toAdd u)
    change Commute (g a ^ (Multiplicative.toAdd u).val) (gx a) at h
    rcases (show (Multiplicative.toAdd u).val = 0 ∨ (Multiplicative.toAdd u).val = 1 ∨
        (Multiplicative.toAdd u).val = 2 by omega) with h0 | h1 | h2
    · rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective h0
    · rw [h1, pow_one] at h
      exact absurd h (hnc a)
    · rw [h2] at h
      have h4 := h.pow_left 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3 a, one_mul, pow_one] at h4
      exact absurd h4 (hnc a)
  have hoff : ∀ a b, a ≠ b → ∀ u, Commute (ϕ b u) (gx a) := fun a b hab u =>
    ((cxx b a (Ne.symm hab)).mul_left (cxy a b hab).symm).pow_left _
  have ht : ∀ a u, Commute t (ϕ a u) := fun a u => ((htx a).mul_right (hty a)).pow_right _
  exact family_witness ϕ hcomm hD hp3 hcard gx hxD hdet hoff t htD ht2 htz ht

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
