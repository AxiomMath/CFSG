module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessOdd
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierD

open TauCeti TauCeti.TypeDSpinCarrier

variable (d : TypeDLieIndex)

noncomputable abbrev frob : d.1.Closure →+* d.1.Closure :=
  iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent

theorem frob_apply (u : d.1.Closure) : frob d u = u ^ d.1.fieldOrder := by
  rw [frob, iterateFrobenius_def, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem isFrobenius :
    (rootData d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure).IsFrobenius (frob d)
      d.steinberg where
  map_x i u := by
    rw [TypeDLieIndex.steinberg_def, TypeDDiagramLieIndex.frobenius_def]
    change TypeDSpinCarrier.frobenius _ _ _ _ _ (rootSubgroupPoints _ _ (.inl i) _ _) =
      rootSubgroupPoints _ _ (.inl i) _ _
    rw [frobenius_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]
  map_y i u := by
    rw [TypeDLieIndex.steinberg_def, TypeDDiagramLieIndex.frobenius_def]
    change TypeDSpinCarrier.frobenius _ _ _ _ _ (rootSubgroupPoints _ _ (.inr i) _ _) =
      rootSubgroupPoints _ _ (.inr i) _ _
    rw [frobenius_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]
  map_torus s := by
    rw [TypeDLieIndex.steinberg_def, TypeDDiagramLieIndex.frobenius_def]
    change TypeDSpinCarrier.frobenius _ _ _ _ _ (weightTorusPoints _ _ _ s) =
      weightTorusPoints _ _ _ _
    rw [frobenius_weightTorusPoints]
    congr 1

theorem mem_fixedField_iff (u : d.1.Closure) :
    u ∈ RootData.fixedField (frob d) ↔ u ∈ d.1.fixedField := by
  rw [RootData.mem_fixedField, frob_apply, ValidLieTypeIndex.mem_fixedField]

theorem hasWitness_torus (h2 : d.1.characteristic = 2) (hq : 4 ≤ d.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hsq : s ∣ d.1.fieldOrder - 1) {κ : Type} [Fintype κ] [DecidableEq κ]
    (J rw : κ → Fin d.1.rank)
    (hdet : (Matrix.of fun a c =>
      ((CartanMatrix.D d.1.rank (J c) (rw a) : ℤ) : ZMod s)).det ≠ 0) :
    HasWitness d.Group s (Fintype.card κ) := by
  have : NeZero s := ⟨hs.ne_zero⟩
  have hcard : Nat.card d.1.fixedField = d.1.fieldOrder := d.1.card_fixedField
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one d.1.fixedField (hcard ▸ hq)
  obtain ⟨ζ, hζL, hζ⟩ := exists_unit_orderOf d.1.fixedField (hcard ▸ hsq)
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  have h4 := d.toTypeDDiagramLieIndex.four_le_rank
  obtain ⟨E, P, hW⟩ := torus_witness
    (R := rootData d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure) (isFrobenius d)
    (fun j => CartanMatrix.D_diag _ j) ((mem_fixedField_iff d _).mpr hμL) hμ2 hchar hs
    ((mem_fixedField_iff d _).mpr hζL) hζ J rw hdet ⟨0, lt_of_lt_of_le (by norm_num) h4⟩
  exact hW.hasWitness

theorem det_full_ne_zero (m : ℕ) (hm : m = 4) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) :
    (Matrix.of fun a c : Fin m => ((CartanMatrix.D m c a : ℤ) : ZMod s)).det ≠ 0 := by
  subst hm
  have hmap : (Matrix.of fun a c : Fin 4 => ((CartanMatrix.D 4 c a : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix (CartanMatrix.D 4) := by
    ext a c
    simp [D_symm 4 c a]
  rw [hmap, ← RingHom.map_det, show (CartanMatrix.D 4).det = 4 by decide]
  exact four_ne_zero_zmod hs hs2

theorem minor_five_eq :
    (Matrix.of fun a c : Fin 4 => (CartanMatrix.D 5 ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ)) =
      !![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, -1, 0] := by
  decide

theorem det_five_ne_zero (m : ℕ) (hm : m = 5) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) :
    (Matrix.of fun a c : Fin 4 =>
      ((CartanMatrix.D m ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)).det ≠ 0 := by
  subst hm
  have hmap : (Matrix.of fun a c : Fin 4 =>
      ((CartanMatrix.D 5 ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix
        (Matrix.of fun a c : Fin 4 => (CartanMatrix.D 5 ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ)) := by
    ext a c
    simp
  rw [hmap, ← RingHom.map_det, minor_five_eq,
    show (!![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, -1, 0] :
      Matrix (Fin 4) (Fin 4) ℤ).det = 2 by decide]
  exact two_ne_zero_zmod hs hs2

theorem minor_tri_eq (m : ℕ) (hm : 6 ≤ m) :
    (Matrix.of fun a c : Fin 4 => (CartanMatrix.D m ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ)) =
      !![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, 0, -1] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [CartanMatrix.D, Matrix.of_apply] <;> omega

theorem det_tri_ne_zero (m : ℕ) (hm : 6 ≤ m) {s : ℕ} (hs : s.Prime) :
    (Matrix.of fun a c : Fin 4 =>
      ((CartanMatrix.D m ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)).det ≠ 0 := by
  have : Fact s.Prime := ⟨hs⟩
  have hmap : (Matrix.of fun a c : Fin 4 =>
      ((CartanMatrix.D m ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix
        (Matrix.of fun a c : Fin 4 => (CartanMatrix.D m ⟨c, by omega⟩ ⟨a + 1, by omega⟩ : ℤ)) := by
    ext a c
    simp
  rw [hmap, ← RingHom.map_det, minor_tri_eq m hm,
    show (!![-1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2; 0, 0, 0, -1] :
      Matrix (Fin 4) (Fin 4) ℤ).det = 1 by decide, map_one]
  exact one_ne_zero

theorem odd_D (m : ℕ) (hm : 4 ≤ m) (i : Fin m) : ∃ j : Fin m, Odd (CartanMatrix.D m j i) := by
  have hi := i.isLt
  have key : ∀ j : Fin m, CartanMatrix.D m j i = -1 → Odd (CartanMatrix.D m j i) := fun j h => by
    rw [h]
    exact odd_neg_one_int
  by_cases h0 : i.val = 0
  · refine ⟨⟨1, by omega⟩, key _ ?_⟩
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · by_cases h1 : i.val + 2 < m
    · refine ⟨⟨i.val - 1, by omega⟩, key _ ?_⟩
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    · refine ⟨⟨m - 3, by omega⟩, key _ ?_⟩
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega

theorem two_ne_zero_closure (hodd : d.1.characteristic ≠ 2) : (2 : d.1.Closure) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : d.1.Closure) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff d.1.Closure d.1.characteristic] at h'
  exact hodd ((Nat.prime_dvd_prime_iff_eq d.1.characteristic_prime Nat.prime_two).mp h')

theorem rootsInCommutator_odd (hodd : d.1.characteristic ≠ 2) :
    (rootData d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure).RootsInCommutator
      (frob d) d.steinberg :=
  RootData.rootsInCommutator_of_odd _ (isFrobenius d) (two_ne_zero_closure d hodd)
    (odd_D _ d.toTypeDDiagramLieIndex.four_le_rank)

theorem card_fixedField_frob :
    Nat.card (RootData.fixedField (frob d)) = d.1.characteristic ^ d.1.fieldExponent := by
  rw [Subfield.ext (mem_fixedField_iff d), d.1.card_fixedField,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem hasWitness_unipotent (hodd : d.1.characteristic ≠ 2) {κ : Type} [Fintype κ]
    [DecidableEq κ] (J : κ → Fin d.1.rank)
    (horth : ∀ a a', a ≠ a' → CartanMatrix.D d.1.rank (J a) (J a') = 0)
    (k : Fin d.1.rank) (hk : ∀ a, Even (CartanMatrix.D d.1.rank k (J a)))
    (j₀ : Fin d.1.rank) (hj₀ : Odd (CartanMatrix.D d.1.rank k j₀)) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * Fintype.card κ) := by
  have hJ : Function.Injective J := fun a a' h => by
    by_contra hne
    have h1 := horth a a' hne
    rw [h, CartanMatrix.D_diag] at h1
    exact absurd h1 (by norm_num)
  exact (rootData d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure).unipotent_witness_h
    (rootsInCommutator_odd d hodd) (two_ne_zero_closure d hodd) (card_fixedField_frob d) J hJ
    horth k hk j₀ hj₀

theorem hasWitness_unipotent_three (hodd : d.1.characteristic ≠ 2) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 3) := by
  have hm := d.toTypeDDiagramLieIndex.four_le_rank
  set m := d.1.rank
  have h := hasWitness_unipotent d hodd
    (![⟨0, by omega⟩, ⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩] : Fin 3 → Fin m) ?_ ⟨0, by omega⟩
    ?_ ⟨1, by omega⟩ ?_
  · rwa [Fintype.card_fin] at h
  · intro a a' h
    fin_cases a <;> fin_cases a' <;>
      simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h ⊢ <;> omega
  · intro a
    rw [Int.even_iff]
    fin_cases a <;> simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      omega
  · rw [Int.odd_iff]
    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem hasWitness_unipotent_four (hodd : d.1.characteristic ≠ 2) (h6 : 6 ≤ d.1.rank) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 4) := by
  set m := d.1.rank
  have h := hasWitness_unipotent d hodd
    (![⟨0, by omega⟩, ⟨2, by omega⟩, ⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩] : Fin 4 → Fin m) ?_
    ⟨0, by omega⟩ ?_ ⟨1, by omega⟩ ?_
  · rwa [Fintype.card_fin] at h
  · intro a a' h
    fin_cases a <;> fin_cases a' <;>
      simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h ⊢ <;> omega
  · intro a
    rw [Int.even_iff]
    fin_cases a <;> simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      omega
  · rw [Int.odd_iff]
    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

end CFSG.RankThree.PartTwo.Census.Spin.CarrierD
