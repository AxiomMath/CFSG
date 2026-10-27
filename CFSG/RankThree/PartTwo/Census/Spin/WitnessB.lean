module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierB
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessOdd
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierB

open TauCeti TauCeti.TypeBSpinCarrier

variable (b : TypeBLieIndex)

noncomputable abbrev frob : b.1.Closure →+* b.1.Closure :=
  iterateFrobenius b.1.Closure b.1.characteristic b.1.fieldExponent

theorem frob_apply (u : b.1.Closure) : frob b u = u ^ b.1.fieldOrder := by
  rw [frob, iterateFrobenius_def, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem isFrobenius : (rootData b.carrierRank b.1.Closure).IsFrobenius (frob b) b.steinberg where
  map_x i u := by
    rw [TypeBLieIndex.steinberg_def, TypeBLieIndex.frobenius_def]
    change TypeBSpinCarrier.frobenius _ _ _ _ (rootSubgroupPoints _ (.inl i) _ _) =
      rootSubgroupPoints _ (.inl i) _ _
    rw [frobenius_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]
  map_y i u := by
    rw [TypeBLieIndex.steinberg_def, TypeBLieIndex.frobenius_def]
    change TypeBSpinCarrier.frobenius _ _ _ _ (rootSubgroupPoints _ (.inr i) _ _) =
      rootSubgroupPoints _ (.inr i) _ _
    rw [frobenius_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]
  map_torus s := by
    rw [TypeBLieIndex.steinberg_def, TypeBLieIndex.frobenius_def]
    change TypeBSpinCarrier.frobenius _ _ _ _ (weightTorusPoints _ _ s) = weightTorusPoints _ _ _
    rw [frobenius_weightTorusPoints]
    congr 1

theorem mem_fixedField_iff (u : b.1.Closure) :
    u ∈ RootData.fixedField (frob b) ↔ u ∈ b.1.fixedField := by
  rw [RootData.mem_fixedField, frob_apply, ValidLieTypeIndex.mem_fixedField]

theorem fixedField_eq : RootData.fixedField (frob b) = b.1.fixedField :=
  Subfield.ext (mem_fixedField_iff b)

theorem hasWitness_torus (h2 : b.1.characteristic = 2) (hq : 4 ≤ b.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hsq : s ∣ b.1.fieldOrder - 1) {κ : Type} [Fintype κ] [DecidableEq κ]
    (J rw : κ → Fin (b.carrierRank + 1))
    (hdet : (Matrix.of fun a c =>
      (((CartanMatrix.B (b.carrierRank + 1)).transpose (J c) (rw a) : ℤ) : ZMod s)).det ≠ 0) :
    HasWitness b.Group s (Fintype.card κ) := by
  have : NeZero s := ⟨hs.ne_zero⟩
  have hcard : Nat.card b.1.fixedField = b.1.fieldOrder := b.1.card_fixedField
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one b.1.fixedField (hcard ▸ hq)
  obtain ⟨ζ, hζL, hζ⟩ := exists_unit_orderOf b.1.fixedField (hcard ▸ hsq)
  have hchar : (2 : b.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → b.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero b.1.Closure b.1.characteristic)
    exact_mod_cast h
  obtain ⟨E, P, hW⟩ := torus_witness (R := rootData b.carrierRank b.1.Closure) (isFrobenius b)
    (fun j => CartanMatrix.B_diag _ j) ((mem_fixedField_iff b _).mpr hμL) hμ2 hchar hs
    ((mem_fixedField_iff b _).mpr hζL) hζ J rw hdet 0
  exact hW.hasWitness

theorem det_full_ne_zero (m : ℕ) (hm : m = 3 ∨ m = 4) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) :
    (Matrix.of fun a c : Fin m =>
      (((CartanMatrix.B m).transpose c a : ℤ) : ZMod s)).det ≠ 0 := by
  have hmap : (Matrix.of fun a c : Fin m => (((CartanMatrix.B m).transpose c a : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix (CartanMatrix.B m) := by
    ext a c
    simp [Matrix.transpose_apply]
  rw [hmap, ← RingHom.map_det]
  rcases hm with rfl | rfl
  · rw [show (CartanMatrix.B 3).det = 2 by decide]
    exact two_ne_zero_zmod hs hs2
  · rw [show (CartanMatrix.B 4).det = 2 by decide]
    exact two_ne_zero_zmod hs hs2

theorem minor_tri_eq (m : ℕ) (hm : 5 ≤ m) :
    (Matrix.of fun a c : Fin 4 => ((CartanMatrix.B m).transpose ⟨c, by omega⟩
      ⟨a + 1, by omega⟩ : ℤ)) =
      !![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, 0, -1] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply] <;> omega

theorem det_tri_ne_zero (m : ℕ) (hm : 5 ≤ m) {s : ℕ} (hs : s.Prime) :
    (Matrix.of fun a c : Fin 4 =>
      (((CartanMatrix.B m).transpose ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)).det ≠ 0 := by
  have : Fact s.Prime := ⟨hs⟩
  have hmap : (Matrix.of fun a c : Fin 4 =>
      (((CartanMatrix.B m).transpose ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix
        (Matrix.of fun a c : Fin 4 => ((CartanMatrix.B m).transpose ⟨c, by omega⟩
          ⟨a + 1, by omega⟩ : ℤ)) := by
    ext a c
    simp
  rw [hmap, ← RingHom.map_det, minor_tri_eq m hm,
    show (!![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, 0, -1] :
      Matrix (Fin 4) (Fin 4) ℤ).det = 1 by decide, map_one]
  exact one_ne_zero

theorem B_apply_pred (m : ℕ) (i j : Fin m) (h : j.val + 1 = i.val) :
    CartanMatrix.B m i j = -1 := by
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [ite_eq_right (by rintro rfl; omega), ite_eq_right (by omega), ite_eq_left h]

theorem B_apply_succ (m : ℕ) (i j : Fin m) (h : i.val + 1 = j.val) (hj : j.val + 1 ≠ m) :
    CartanMatrix.B m i j = -1 := by
  have := j.isLt
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [ite_eq_right (by rintro rfl; omega), ite_eq_left h, ite_eq_right (by omega)]

theorem B_apply_far (m : ℕ) (i j : Fin m) (h1 : i.val ≠ j.val) (h2 : i.val + 1 ≠ j.val)
    (h3 : j.val + 1 ≠ i.val) : CartanMatrix.B m i j = 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [ite_eq_right (fun h => h1 (congrArg Fin.val h)), ite_eq_right h2, ite_eq_right h3]

theorem odd_B_transpose (m : ℕ) (hm : 3 ≤ m) (i : Fin m) :
    ∃ j : Fin m, Odd ((CartanMatrix.B m).transpose j i) := by
  rcases Nat.eq_zero_or_pos i.val with hi | hi
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [Matrix.transpose_apply, B_apply_succ m i ⟨1, by omega⟩ (by simp [hi]) (by simp; omega)]
    exact odd_neg_one_int
  · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    rw [Matrix.transpose_apply, B_apply_pred m i ⟨i.val - 1, by omega⟩ (by simp; omega)]
    exact odd_neg_one_int

theorem two_ne_zero_closure (hodd : b.1.characteristic ≠ 2) : (2 : b.1.Closure) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : b.1.Closure) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff b.1.Closure b.1.characteristic] at h'
  exact hodd ((Nat.prime_dvd_prime_iff_eq b.1.characteristic_prime Nat.prime_two).mp h')

theorem rootsInCommutator_odd (hodd : b.1.characteristic ≠ 2) (h3 : 3 ≤ b.carrierRank + 1) :
    (rootData b.carrierRank b.1.Closure).RootsInCommutator (frob b) b.steinberg :=
  RootData.rootsInCommutator_of_odd _ (isFrobenius b) (two_ne_zero_closure b hodd)
    (odd_B_transpose _ h3)

theorem card_fixedField_frob :
    Nat.card (RootData.fixedField (frob b)) = b.1.characteristic ^ b.1.fieldExponent := by
  rw [fixedField_eq, b.1.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem hasWitness_unipotent (hodd : b.1.characteristic ≠ 2) (h3 : 3 ≤ b.carrierRank + 1)
    {κ : Type} [Fintype κ] [DecidableEq κ] (J : κ → Fin (b.carrierRank + 1))
    (hJ : Function.Injective J)
    (horth : ∀ a a', a ≠ a' → (CartanMatrix.B (b.carrierRank + 1)).transpose (J a) (J a') = 0)
    (k : Fin (b.carrierRank + 1))
    (hk : ∀ a, Even ((CartanMatrix.B (b.carrierRank + 1)).transpose k (J a)))
    (j₀ : Fin (b.carrierRank + 1))
    (hj₀ : Odd ((CartanMatrix.B (b.carrierRank + 1)).transpose k j₀)) :
    HasWitness b.Group b.1.characteristic (b.1.fieldExponent * Fintype.card κ) :=
  (rootData b.carrierRank b.1.Closure).unipotent_witness_h (rootsInCommutator_odd b hodd h3)
    (two_ne_zero_closure b hodd) (card_fixedField_frob b) J hJ horth k hk j₀ hj₀

theorem hasWitness_unipotent_even (hodd : b.1.characteristic ≠ 2) (k : ℕ) (hk : 2 ≤ k)
    (hkr : 2 * k ≤ b.carrierRank + 2) :
    HasWitness b.Group b.1.characteristic (b.1.fieldExponent * k) := by
  have h3 : 3 ≤ b.carrierRank + 1 := by omega
  let J : Fin k → Fin (b.carrierRank + 1) := fun a => ⟨2 * a.val, by omega⟩
  have hJ : Function.Injective J := fun a a' h => by
    have h' : 2 * a.val = 2 * a'.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  have horth : ∀ a a', a ≠ a' →
      (CartanMatrix.B (b.carrierRank + 1)).transpose (J a) (J a') = 0 := fun a a' h => by
    have h' : a.val ≠ a'.val := fun h'' => h (Fin.ext h'')
    rw [Matrix.transpose_apply]
    exact B_apply_far _ _ _ (by change 2 * a'.val ≠ 2 * a.val; omega)
      (by change 2 * a'.val + 1 ≠ 2 * a.val; omega) (by change 2 * a.val + 1 ≠ 2 * a'.val; omega)
  have hk0 : ∀ a, Even ((CartanMatrix.B (b.carrierRank + 1)).transpose ⟨0, by omega⟩ (J a)) := by
    intro a
    rw [Matrix.transpose_apply]
    rcases Nat.eq_zero_or_pos a.val with ha | ha
    · have : J a = ⟨0, by omega⟩ := Fin.ext (by simp [J, ha])
      rw [this, CartanMatrix.B_diag]
      exact even_two
    · rw [B_apply_far _ _ _ (by change 2 * a.val ≠ 0; omega)
        (by change 2 * a.val + 1 ≠ 0; omega) (by change 0 + 1 ≠ 2 * a.val; omega)]
      exact ⟨0, rfl⟩
  have hj : Odd ((CartanMatrix.B (b.carrierRank + 1)).transpose ⟨0, by omega⟩ ⟨1, by omega⟩) := by
    rw [Matrix.transpose_apply, B_apply_pred _ _ _ (by simp)]
    exact odd_neg_one_int
  have h := hasWitness_unipotent b hodd h3 J hJ horth ⟨0, by omega⟩ hk0 ⟨1, by omega⟩ hj
  rwa [Fintype.card_fin] at h

end CFSG.RankThree.PartTwo.Census.Spin.CarrierB
