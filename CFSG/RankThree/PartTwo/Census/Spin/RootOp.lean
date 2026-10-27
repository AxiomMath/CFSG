module

public import CFSG.RankThree.PartTwo.Census.Spin.Family
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

theorem mat_inv_of_mul {g : R.G} {A : Matrix N N K} (h : R.mat g * A = 1) :
    R.mat g⁻¹ = A := by
  calc R.mat g⁻¹ = R.mat g⁻¹ * (R.mat g * A) := by rw [h, mul_one]
    _ = R.mat (g⁻¹ * g) * A := by rw [mat_mul, mul_assoc]
    _ = A := by rw [inv_mul_cancel, mat_one, one_mul]

theorem mat_inv_one_add_smul {g : R.G} {X : Matrix N N K} (hX : X * X = 0) {u : K}
    (hg : R.mat g = 1 + u • X) : R.mat g⁻¹ = 1 - u • X := by
  apply R.mat_inv_of_mul
  rw [hg, add_mul, one_mul, mul_sub, mul_one, smul_mul_smul, hX, smul_zero, sub_zero,
    sub_add_cancel]

structure RootOp (H : Subgroup R.G) (L : Subfield K) (X : Matrix N N K) (w : ι → ℤ) :
    Prop where
  sq : X * X = 0
  mem : ∀ u : K, ∃ g : R.G, R.mat g = 1 + u • X
  torus : ∀ s : ι → Kˣ, R.mat (R.torus s) * X =
    ((∏ j, s j ^ w j : Kˣ) : K) • (X * R.mat (R.torus s))
  memD : ∀ u ∈ L, ∃ g ∈ ⁅H, H⁆, R.mat g = 1 + u • X

variable {R} {H : Subgroup R.G} {L : Subfield K}

theorem RootOp.conj_mat {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) (s : ι → Kˣ) :
    R.mat (R.torus s) * X * R.mat (R.torus s)⁻¹ = ((∏ j, s j ^ w j : Kˣ) : K) • X := by
  have hT : R.mat (R.torus s) * R.mat (R.torus s)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [hX.torus, smul_mul_assoc, mul_assoc, hT, mul_one]

theorem RootOp.mat_conj {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) (s : ι → Kˣ)
    {g : R.G} {u : K} (hg : R.mat g = 1 + u • X) :
    R.mat (R.torus s * g * (R.torus s)⁻¹) =
      1 + (((∏ j, s j ^ w j : Kˣ) : K) * u) • X := by
  have hT : R.mat (R.torus s) * R.mat (R.torus s)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, mat_mul, hg, mul_add, mul_one, add_mul, hT, mul_smul_comm, smul_mul_assoc,
    hX.conj_mat, smul_smul, mul_comm]

theorem rootOp_E (i : ι) (hD : ∀ u ∈ L, R.x i u ∈ ⁅H, H⁆) :
    R.RootOp H L (R.E i) (fun j => R.CM j i) where
  sq := (R.sqZero i).ee
  mem u := ⟨R.x i u, by rw [mat_x, SqZeroPair.φ_upper]⟩
  torus s := by
    have h1 := congrArg R.mat (R.torus_conj_x s i 1)
    rw [mat_mul, mat_mul, mat_x, mat_x, SqZeroPair.φ_upper, SqZeroPair.φ_upper, one_smul,
      mul_one] at h1
    have hT : R.mat (R.torus s)⁻¹ * R.mat (R.torus s) = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    have h2 := congrArg (· * R.mat (R.torus s)) h1
    simp only [mul_assoc, hT, mul_one] at h2
    rw [mul_add, mul_one, add_mul, one_mul] at h2
    have h3 := add_left_cancel h2
    rw [h3, smul_mul_assoc]
  memD u hu := ⟨R.x i u, hD u hu, by rw [mat_x, SqZeroPair.φ_upper]⟩

theorem rootOp_F (i : ι) (hD : ∀ u ∈ L, R.y i u ∈ ⁅H, H⁆) :
    R.RootOp H L (R.F i) (fun j => -R.CM j i) where
  sq := (R.sqZero i).ff
  mem u := ⟨R.y i u, by rw [mat_y, SqZeroPair.φ_lower]⟩
  torus s := by
    have h1 := congrArg R.mat (R.torus_conj_y s i 1)
    rw [mat_mul, mat_mul, mat_y, mat_y, SqZeroPair.φ_lower, SqZeroPair.φ_lower, one_smul,
      mul_one] at h1
    have hT : R.mat (R.torus s)⁻¹ * R.mat (R.torus s) = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    have h2 := congrArg (· * R.mat (R.torus s)) h1
    simp only [mul_assoc, hT, mul_one] at h2
    rw [mul_add, mul_one, add_mul, one_mul] at h2
    have h3 := add_left_cancel h2
    rw [h3, smul_mul_assoc]
    congr 2
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [zpow_neg]
  memD u hu := ⟨R.y i u, hD u hu, by rw [mat_y, SqZeroPair.φ_lower]⟩

theorem RootOp.neg {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) :
    R.RootOp H L (-X) w where
  sq := by rw [neg_mul_neg, hX.sq]
  mem u := by
    obtain ⟨g, hg⟩ := hX.mem (-u)
    exact ⟨g, by rw [hg, smul_neg, neg_smul]⟩
  torus s := by rw [mul_neg, hX.torus, neg_mul, smul_neg]
  memD u hu := by
    obtain ⟨g, hgD, hg⟩ := hX.memD (-u) (L.neg_mem hu)
    exact ⟨g, hgD, by rw [hg, smul_neg, neg_smul]⟩

theorem commutator_one_add {A B : Matrix N N K} (hA : A * A = 0) (hB : B * B = 0)
    (hABA : A * B * A = 0) (hBAB : B * A * B = 0) (u : K) :
    (1 + A) * (1 + u • B) * (1 - A) * (1 - u • B) = 1 + u • (A * B - B * A) := by
  have hABA' : A * (B * A) = 0 := by rw [← mul_assoc, hABA]
  have hBAB' : B * (A * B) = 0 := by rw [← mul_assoc, hBAB]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, mul_assoc, hA, hB, hABA', hBAB', smul_zero, mul_zero,
    add_zero]
  module

theorem commutator_le_self (H : Subgroup R.G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun g hg g' hg' => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hg') (H.inv_mem hg)) (H.inv_mem hg')

theorem RootOp.bracket {A B : Matrix N N K} {wA wB : ι → ℤ} (hA : R.RootOp H L A wA)
    (hB : R.RootOp H L B wB) (hABA : A * B * A = 0) (hBAB : B * A * B = 0) :
    R.RootOp H L (A * B - B * A) (wA + wB) where
  sq := by
    have e : (A * B - B * A) * (A * B - B * A) =
        A * B * A * B - A * (B * B) * A - B * (A * A) * B + B * (A * B * A) := by noncomm_ring
    rw [e, hABA, hB.sq, hA.sq]
    simp
  mem u := by
    obtain ⟨g, hg⟩ := hA.mem 1
    obtain ⟨g', hg'⟩ := hB.mem u
    refine ⟨⁅g, g'⁆, ?_⟩
    rw [commutatorElement_def, mat_mul, mat_mul, mat_mul, mat_inv_one_add_smul R hA.sq hg,
      mat_inv_one_add_smul R hB.sq hg', hg, hg', one_smul]
    exact commutator_one_add hA.sq hB.sq hABA hBAB u
  torus s := by
    set χA : K := ((∏ j, s j ^ wA j : Kˣ) : K)
    set χB : K := ((∏ j, s j ^ wB j : Kˣ) : K)
    set T := R.mat (R.torus s)
    have h1 : T * (A * B) = (χA * χB) • (A * B * T) := by
      rw [← mul_assoc, hA.torus, smul_mul_assoc, mul_assoc, hB.torus, mul_smul_comm, smul_smul,
        mul_assoc]
    have h2 : T * (B * A) = (χA * χB) • (B * A * T) := by
      rw [← mul_assoc, hB.torus, smul_mul_assoc, mul_assoc, hA.torus, mul_smul_comm, smul_smul,
        mul_assoc, mul_comm χB]
    rw [mul_sub, h1, h2, ← smul_sub, sub_mul]
    congr 1
    rw [← Units.val_mul, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, zpow_add]
  memD u hu := by
    obtain ⟨g, hgD, hg⟩ := hA.memD 1 L.one_mem
    obtain ⟨g', hgD', hg'⟩ := hB.memD u hu
    refine ⟨⁅g, g'⁆, Subgroup.commutator_mem_commutator (commutator_le_self H hgD)
      (commutator_le_self H hgD'), ?_⟩
    rw [commutatorElement_def, mat_mul, mat_mul, mat_mul, mat_inv_one_add_smul R hA.sq hg,
      mat_inv_one_add_smul R hB.sq hg', hg, hg', one_smul]
    exact commutator_one_add hA.sq hB.sq hABA hBAB u

noncomputable def RootOp.elt {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) (u : K) :
    R.G :=
  (hX.mem u).choose

theorem RootOp.mat_elt {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) (u : K) :
    R.mat (hX.elt u) = 1 + u • X :=
  (hX.mem u).choose_spec

theorem RootOp.elt_add {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) (u v : K) :
    hX.elt (u + v) = hX.elt u * hX.elt v := by
  apply R.mat_injective
  rw [mat_mul, hX.mat_elt, hX.mat_elt, hX.mat_elt, add_mul, one_mul, mul_add, mul_one,
    smul_mul_smul, hX.sq, smul_zero, add_zero, add_smul]
  abel

theorem RootOp.elt_zero {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) :
    hX.elt 0 = 1 := by
  apply R.mat_injective
  rw [hX.mat_elt, zero_smul, add_zero, mat_one]

theorem RootOp.elt_mem {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w) {u : K}
    (hu : u ∈ L) : hX.elt u ∈ ⁅H, H⁆ := by
  obtain ⟨g, hg, hgm⟩ := hX.memD u hu
  rwa [show hX.elt u = g from R.mat_injective (by rw [hX.mat_elt, hgm])]

theorem RootOp.commute_elt {X Y : Matrix N N K} {w w' : ι → ℤ} (hX : R.RootOp H L X w)
    (hY : R.RootOp H L Y w') (hXY : Commute X Y) (u v : K) :
    Commute (hX.elt u) (hY.elt v) :=
  R.commute_of_mat (by rw [hX.mat_elt, hY.mat_elt]; exact commute_one_add_smul hXY u v)

theorem RootOp.commute_torus {X : Matrix N N K} {w : ι → ℤ} (hX : R.RootOp H L X w)
    {s : ι → Kˣ} (hs : (∏ j, s j ^ w j) = 1) (u : K) : Commute (R.torus s) (hX.elt u) := by
  have h1 := hX.mat_conj s (hX.mat_elt u)
  rw [hs, Units.val_one, one_mul, ← hX.mat_elt] at h1
  exact mul_inv_eq_iff_eq_mul.mp (R.mat_injective h1)

theorem RootOp.elt_simple_E (i : ι) (hD : ∀ u ∈ L, R.x i u ∈ ⁅H, H⁆) (u : K) :
    (rootOp_E (R := R) i hD).elt u = R.x i u :=
  R.mat_injective (by rw [RootOp.mat_elt, mat_x, SqZeroPair.φ_upper])

theorem eq_zero_of_commute_sqZeroPair {X Y : Matrix N N K} (hp : SqZeroPair X Y) (hX0 : X ≠ 0)
    {g g' : R.G} {u : K} (hg : R.mat g = 1 + u • X) (hg' : R.mat g' = 1 + Y)
    (h : Commute g g') : u = 0 := by
  have hm := congrArg R.mat h.eq
  rw [mat_mul, mat_mul, hg, hg'] at hm
  have e : (1 + u • X) * (1 + Y) - (1 + Y) * (1 + u • X) = u • (X * Y - Y * X) := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  rw [hm, sub_self] at e
  rcases smul_eq_zero.mp e.symm with hu | hXY
  · exact hu
  · exfalso
    apply hX0
    have h1 := hp.efe
    rw [sub_eq_zero.mp hXY, mul_assoc, hp.ee, mul_zero] at h1
    exact h1.symm

theorem rootOp_witness {p f : ℕ} [CharP K p] (hcard : Nat.card L = p ^ f) {κ : Type*}
    [Fintype κ] [DecidableEq κ] {X Y : κ → Matrix N N K} {w wY : κ → ι → ℤ}
    (hX : ∀ a, R.RootOp H L (X a) (w a)) (hY : ∀ a, R.RootOp H L (Y a) (wY a))
    (hpair : ∀ a, SqZeroPair (X a) (Y a)) (hne : ∀ a, X a ≠ 0)
    (hXX : ∀ a b, a ≠ b → Commute (X a) (X b)) (hXY : ∀ a b, a ≠ b → Commute (X b) (Y a))
    (c : ι → Kˣ) (hc2 : c ^ 2 = 1) (htD : R.torus c ∈ ⁅H, H⁆)
    (hcent : ∀ a, (∏ j, c j ^ w a j) = 1) (j₀ : ι) (hj₀ : (∏ k, c k ^ R.CM k j₀) ≠ 1)
    (hx₀ : R.x j₀ 1 ∈ ⁅H, H⁆) :
    HasWitness (DerivedCentralQuotient H) p (f * Fintype.card κ) := by
  let ϕ : ∀ _ : κ, Multiplicative L →* R.G := fun a =>
    { toFun := fun u => (hX a).elt ((Multiplicative.toAdd u : L) : K)
      map_one' := (hX a).elt_zero
      map_mul' := fun u v => (hX a).elt_add _ _ }
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b hab u v =>
    (hX a).commute_elt (hX b) (hXX a b hab) _ _
  have hD : ∀ a u, ϕ a u ∈ ⁅H, H⁆ := fun a u => (hX a).elt_mem (Multiplicative.toAdd u).2
  have hpc : ∀ (a : κ) (u : L), p • u = 0 := fun a u => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl)
  have hcard' : Nat.card (κ → Multiplicative L) = p ^ (f * Fintype.card κ) := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative L ≃ L), hcard,
      Nat.card_eq_fintype_card, ← pow_mul]
  refine family_witness ϕ hcomm hD hpc hcard' (fun a => (hY a).elt 1)
    (fun a => (hY a).elt_mem L.one_mem) (fun a u h => ?_) (fun a b hab u => ?_) (R.torus c)
    htD ?_ ⟨R.x j₀ 1, hx₀, fun h => hj₀ ?_⟩ fun a u => (hX a).commute_torus (hcent a) _
  · have h0 := R.eq_zero_of_commute_sqZeroPair (hpair a) (hne a) ((hX a).mat_elt _)
      (by rw [(hY a).mat_elt, one_smul]) h
    exact Multiplicative.toAdd.injective (Subtype.ext h0)
  · exact (hX b).commute_elt (hY a) (hXY a b hab) _ _
  · rw [← map_pow, hc2, map_one]
  · have h1 := R.torus_conj_x c j₀ 1
    rw [h, mul_inv_cancel_right, mul_one] at h1
    exact Units.ext (R.x_injective j₀ h1).symm

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
