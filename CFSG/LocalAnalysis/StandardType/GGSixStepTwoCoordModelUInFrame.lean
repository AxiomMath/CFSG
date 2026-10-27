module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUMoves

public section

namespace CFSG.StandardType

namespace CoordSUIn

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CoordSU Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

section Powers

theorem not_dvd_val_unit (hp : p.Prime) (u : (ZMod p)ˣ) : ¬ p ∣ (u : ZMod p).val := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  apply u.ne_zero
  rw [← ZMod.natCast_zmod_val (u : ZMod p)]
  exact (ZMod.natCast_eq_zero_iff _ p).mpr hd

theorem exists_pow_pow_eq (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) {k : ℕ}
    (hk : ¬ p ∣ k) : ∃ k' : ℕ, (y ^ k) ^ k' = y := by
  obtain ⟨k', -, hkk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hk).symm hA.prime.one_lt
  exact ⟨k', by rw [← pow_mul, pow_eq_pow_mod _ (hA.pow y hy), hkk', pow_one]⟩

theorem pow_ne_one_of_not_dvd (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A)
    (hy1 : y ≠ 1) {k : ℕ} (hk : ¬ p ∣ k) : y ^ k ≠ 1 := by
  obtain ⟨k', hk'⟩ := exists_pow_pow_eq hA hy hk
  intro h1
  apply hy1
  rw [← hk', h1, one_pow]

theorem rng_pow_eq (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) {k : ℕ}
    (hk : ¬ p ∣ k) : rng (y ^ k) = rng y := by
  apply le_antisymm
  · change LinearMap.range (lin (y ^ k) - 1) ≤ LinearMap.range (lin y - 1)
    rw [SUTB.lin_pow]
    exact SUTB.range_pow_sub_one_le (lin y) k
  · obtain ⟨k', hk'⟩ := exists_pow_pow_eq hA hy hk
    have h1 : LinearMap.range (lin ((y ^ k) ^ k') - 1) ≤ LinearMap.range (lin (y ^ k) - 1) := by
      rw [SUTB.lin_pow (y ^ k) k']
      exact SUTB.range_pow_sub_one_le (lin (y ^ k)) k'
    rw [hk'] at h1
    exact h1

end Powers

section Rescale

@[expose] def scaleHom {r : ℕ} (η : Fin r → (ZMod p)ˣ) :
    Multiplicative (Fin r → ZMod p) →* Multiplicative (Fin r → ZMod p) where
  toFun s := ofAdd fun i => (η i : ZMod p) * toAdd s i
  map_one' := by
    apply toAdd.injective
    funext i
    simp
  map_mul' s t := by
    apply toAdd.injective
    funext i
    simp [mul_add]

theorem scaleHom_apply {r : ℕ} (η : Fin r → (ZMod p)ˣ) (s : Multiplicative (Fin r → ZMod p)) :
    scaleHom η s = ofAdd fun i => (η i : ZMod p) * toAdd s i := rfl

theorem scaleHom_inv_apply {r : ℕ} (η : Fin r → (ZMod p)ˣ) (s : Multiplicative (Fin r → ZMod p)) :
    scaleHom η (scaleHom (fun i => (η i)⁻¹) s) = s := by
  apply toAdd.injective
  funext i
  simp only [scaleHom_apply, toAdd_ofAdd]
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

variable (hA : MaxElemAb p A)
include hA

theorem rng_rescale (F : PieceFrame f n K h p A) (η : Fin F.r → (ZMod p)ˣ) (i : Fin F.r) :
    rng (F.y i ^ (η i : ZMod p).val) = rng (F.y i) :=
  rng_pow_eq hA (F.y_mem i) (not_dvd_val_unit hA.prime (η i))

theorem lin_ι_rescale_on (F : PieceFrame f n K h p A) (η : Fin F.r → (ZMod p)ˣ)
    (s : Multiplicative (Fin F.r → ZMod p)) (j : Fin F.r) {u : Fin n → K}
    (hu : u ∈ rng (F.y j)) :
    lin (F.ι (scaleHom η s)) u = lin ((F.y j ^ (η j : ZMod p).val) ^ (toAdd s j).val) u := by
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  rw [F.ι_on _ j u hu, scaleHom_apply, toAdd_ofAdd, ← pow_mul, ZMod.val_mul,
    ← pow_eq_pow_mod _ (hA.pow _ (F.y_mem j))]

@[expose] noncomputable def rescale (F : PieceFrame f n K h p A) (η : Fin F.r → (ZMod p)ˣ) :
    PieceFrame f n K h p A where
  r := F.r
  y i := F.y i ^ (η i : ZMod p).val
  b i := F.b i ^ (η i : ZMod p).val
  ι := F.ι.comp (scaleHom η)
  y_mem i := A.pow_mem (F.y_mem i) _
  y_ne_one i := pow_ne_one_of_not_dvd hA (F.y_mem i) (F.y_ne_one i)
    (not_dvd_val_unit hA.prime (η i))
  b_mem i := A.pow_mem (F.b_mem i) _
  orth i j hij u hu v hv := F.orth i j hij u (by rwa [rng_rescale hA F η i] at hu) v
    (by rwa [rng_rescale hA F η j] at hv)
  cyc i c hc := by
    obtain ⟨k₀, hk₀⟩ := F.cyc i c hc
    obtain ⟨k', hk'⟩ := exists_pow_pow_eq hA (F.y_mem i) (not_dvd_val_unit hA.prime (η i))
    refine ⟨k' * k₀, fun u hu => ?_⟩
    rw [rng_rescale hA F η i] at hu
    rw [hk₀ u hu, pow_mul, hk']
  minimal i := by
    intro W hW hW0 hWnd hWA
    rw [rng_rescale hA F η i] at hW ⊢
    exact F.minimal i W hW hW0 hWnd hWA
  b_on i u hu := by
    rw [rng_rescale hA F η i] at hu
    exact lin_b_pow_on hA F i _ hu
  b_off i v hv := by
    rw [rng_rescale hA F η i] at hv
    exact lin_pow_apply_of_fix (F.b_off i v hv) _
  ι_single i := by
    have : NeZero p := ⟨hA.prime.ne_zero⟩
    rw [MonoidHom.comp_apply, scaleHom_apply, toAdd_ofAdd]
    have h1 : (fun j => (η j : ZMod p) * Pi.single (M := fun _ => ZMod p) i 1 j) =
        Pi.single i (((η i : ZMod p).val : ℕ) : ZMod p) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [h1, F.ι_single_pow]
  ι_on s j u hu := by
    rw [rng_rescale hA F η j] at hu
    exact lin_ι_rescale_on hA F η s j hu
  ι_injective s t hst := by
    have : Fact p.Prime := ⟨hA.prime⟩
    have h1 := F.ι_injective hst
    apply toAdd.injective
    funext i
    have h2 := congrFun (congrArg toAdd h1) i
    simp only [scaleHom_apply, toAdd_ofAdd] at h2
    exact mul_left_cancel₀ (η i).ne_zero h2
  ι_range := by
    ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact ι_mem F _
    · intro hc
      rw [← F.ι_range] at hc
      obtain ⟨t, rfl⟩ := hc
      exact ⟨scaleHom (fun i => (η i)⁻¹) t, by
        rw [MonoidHom.comp_apply, scaleHom_inv_apply]⟩
  ι_fix s v := by
    have : Fact p.Prime := ⟨hA.prime⟩
    rw [MonoidHom.comp_apply, F.ι_fix]
    constructor
    · intro H j hj
      rw [rng_rescale hA F η j]
      refine H j ?_
      rw [scaleHom_apply, toAdd_ofAdd]
      exact mul_ne_zero (η j).ne_zero hj
    · intro H j hj
      rw [scaleHom_apply, toAdd_ofAdd] at hj
      have hj' : toAdd s j ≠ 0 := fun h0 => hj (by rw [h0, mul_zero])
      have := H j hj'
      rwa [rng_rescale hA F η j] at this

end Rescale

section Align

theorem exists_aligned_frame (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {g : K[X]}
    (hg : Irreducible g) (hgd : g ∣ cyclotomic p K) :
    ∃ F' : PieceFrame f n K h p A, ∀ i, LinearMap.ker (aeval (lin (F'.y i)) g) ≠ ⊥ := by
  classical
  have : Fact (Irreducible g) := ⟨hg⟩
  have hp := hA.prime
  have hpK := hA.natCast_ne_zero h
  have hj : ∀ i, ∃ j : ℕ, LinearMap.ker (aeval (lin (F.y i) ^ j) g) ≠ ⊥ := fun i =>
    NSFrame.exists_pow_ker_ne_bot hp hpK hgd (hA.lin_pow (F.y_mem i))
      (fun h1 => F.y_ne_one i (lin_injective (h1.trans lin_one.symm)))
  choose j hj using hj
  have hjp : ∀ i, ¬ p ∣ j i := by
    rintro i ⟨t, ht⟩
    apply hj i
    rw [ht, pow_mul, hA.lin_pow (F.y_mem i), one_pow]
    refine le_bot_iff.mp ((ker_aeval_le_range hpK hp hgd).trans ?_)
    rw [sub_self, LinearMap.range_zero]
  set η : Fin F.r → (ZMod p)ˣ := fun i => ZMod.unitOfCoprime (j i)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr (hjp i)).symm with hη
  refine ⟨rescale hA F η, fun i => ?_⟩
  change LinearMap.ker (aeval (lin (F.y i ^ (η i : ZMod p).val)) g) ≠ ⊥
  rw [hη, ZMod.coe_unitOfCoprime, ZMod.val_natCast, SUTB.lin_pow,
    ← pow_eq_pow_mod _ (hA.lin_pow (F.y_mem i))]
  exact hj i

end Align

end CoordSUIn

end CFSG.StandardType
