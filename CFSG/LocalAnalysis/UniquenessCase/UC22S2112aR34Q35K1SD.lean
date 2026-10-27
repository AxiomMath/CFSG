module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Lift
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1M4
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.RankThree.PartOne.KC.UnitaryDefiningGramChange
import CFSG.CGT.Stroth77.L4Sylow.Recognition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.CGT.Stroth77.L4Sylow
open CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv CFSG.LocalAnalysis.Mason73
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryDefining
open CFSG.Blueprint (LieModel)

private def uc22s2112r34q35_rho : Perm (Fin 4) := swap 0 1 * swap 2 3

private lemma uc22s2112r34q35_rho_zero : uc22s2112r34q35_rho 0 = 1 := by
  decide

private lemma uc22s2112r34q35_rho_one : uc22s2112r34q35_rho 1 = 0 := by
  decide

private lemma uc22s2112r34q35_rho_two : uc22s2112r34q35_rho 2 = 3 := by
  decide

private lemma uc22s2112r34q35_rho_three : uc22s2112r34q35_rho 3 = 2 := by
  decide

private lemma uc22s2112r34q35_rho_commute (π : Fin81.R0) :
    Commute (π : Perm (Fin 4)) uc22s2112r34q35_rho := by
  have h : (π : Perm (Fin 4)) * uc22s2112r34q35_rho =
      uc22s2112r34q35_rho * (π : Perm (Fin 4)) := by
    revert π
    decide
  exact h

private lemma uc22s2112r34q35_rho_apply_comm (π : Fin81.R0) (i : Fin 4) :
    uc22s2112r34q35_rho ((π : Perm (Fin 4)) i) =
      (π : Perm (Fin 4)) (uc22s2112r34q35_rho i) := by
  have h := congrFun (congrArg (fun e : Perm (Fin 4) => (e : Fin 4 → Fin 4))
    (uc22s2112r34q35_rho_commute π).eq) i
  simpa [Equiv.Perm.mul_apply] using h.symm

private lemma uc22s2112r34q35_rho_apply_comm_inv (π : Fin81.R0) (i : Fin 4) :
    uc22s2112r34q35_rho (((π : Perm (Fin 4))⁻¹) i) =
      ((π : Perm (Fin 4))⁻¹) (uc22s2112r34q35_rho i) := by
  simpa using uc22s2112r34q35_rho_apply_comm (π⁻¹) i

private def uc22s2112r34q35_rel (d : Fin 4 → ZMod 8) : Prop :=
  d 1 = 3 * d 0 ∧ d 3 = 3 * d 2

private lemma uc22s2112r34q35_rel_iff (d : Fin 4 → ZMod 8) :
    uc22s2112r34q35_rel d ↔ ∀ i, d (uc22s2112r34q35_rho i) = 3 * d i := by
  constructor
  · rintro ⟨h1, h3⟩ i
    fin_cases i
    · simpa [uc22s2112r34q35_rho_zero] using h1
    · change d (uc22s2112r34q35_rho 1) = 3 * d 1
      have h9 : (3 * 3 : ZMod 8) = 1 := by decide
      rw [uc22s2112r34q35_rho_one, h1, ← mul_assoc, h9, one_mul]
    · simpa [uc22s2112r34q35_rho_two] using h3
    · change d (uc22s2112r34q35_rho 3) = 3 * d 3
      have h9 : (3 * 3 : ZMod 8) = 1 := by decide
      rw [uc22s2112r34q35_rho_three, h3, ← mul_assoc, h9, one_mul]
  · intro h
    exact ⟨by simpa [uc22s2112r34q35_rho_zero] using h 0,
      by simpa [uc22s2112r34q35_rho_two] using h 2⟩

private lemma uc22s2112r34q35_four_mul_val (x : ZMod 8) :
    4 * x = 0 ∨ 4 * x = 4 := by
  revert x
  decide

private lemma uc22s2112r34q35_sgnH_val (π : Fin81.R0) :
    sgnH (n := 3) π = 0 ∨ sgnH (n := 3) π = 4 := by
  revert π
  decide

@[expose] def uc22s2112r34q35_RSD : Subgroup (L4Hat 3) where
  carrier := {a | Multiplicative.toAdd a.left 1 = 3 * Multiplicative.toAdd a.left 0 ∧
    Multiplicative.toAdd a.left 3 = 3 * Multiplicative.toAdd a.left 2}
  mul_mem' := by
    intro a b ha hb
    have hda : uc22s2112r34q35_rel (Multiplicative.toAdd a.left) := ha
    have hdb : uc22s2112r34q35_rel (Multiplicative.toAdd b.left) := hb
    rw [← hat_left a, ← hat_left b, hat_mul]
    change uc22s2112r34q35_rel
      (Multiplicative.toAdd a.left + pv (a.right : Perm (Fin 4)) (Multiplicative.toAdd b.left))
    rw [uc22s2112r34q35_rel_iff] at hda hdb ⊢
    intro i
    have hcomm := uc22s2112r34q35_rho_apply_comm_inv a.right i
    simp only [Pi.add_apply, pv]
    rw [hda i, ← hcomm, hdb]
    ring
  one_mem' := by
    change uc22s2112r34q35_rel (Multiplicative.toAdd (1 : L4Hat 3).left)
    simp [uc22s2112r34q35_rel]
  inv_mem' := by
    intro a ha
    have hda : uc22s2112r34q35_rel (Multiplicative.toAdd a.left) := ha
    rw [← hat_left a]
    have hinv : (hat (Multiplicative.toAdd a.left) a.right)⁻¹ =
        hat (-(pv ((a.right : Perm (Fin 4))⁻¹) (Multiplicative.toAdd a.left))) a.right⁻¹ := by
      rw [inv_eq_iff_mul_eq_one, hat_mul]
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        funext i
        simp only [Pi.add_apply, Pi.neg_apply, pv, toAdd_ofAdd, inv_inv]
        simp
      · simp
    rw [hinv]
    change uc22s2112r34q35_rel
      (-(pv ((a.right : Perm (Fin 4))⁻¹) (Multiplicative.toAdd a.left)))
    rw [uc22s2112r34q35_rel_iff] at hda ⊢
    intro i
    have hcomm := uc22s2112r34q35_rho_apply_comm a.right i
    simp only [Pi.neg_apply, pv, inv_inv]
    rw [← hcomm, hda]
    ring

private lemma uc22s2112r34q35_rsd_vector {a : L4Hat 3}
    (ha : a ∈ uc22s2112r34q35_RSD) :
    (![Multiplicative.toAdd a.left 0, 3 * Multiplicative.toAdd a.left 0,
      Multiplicative.toAdd a.left 2, 3 * Multiplicative.toAdd a.left 2] :
        Fin 4 → ZMod 8) = Multiplicative.toAdd a.left := by
  have hrel := (uc22s2112r34q35_rel_iff _).mp ha
  funext i
  fin_cases i
  · rfl
  · change 3 * Multiplicative.toAdd a.left 0 = Multiplicative.toAdd a.left 1
    simpa [uc22s2112r34q35_rho_zero] using (hrel 0).symm
  · rfl
  · change 3 * Multiplicative.toAdd a.left 2 = Multiplicative.toAdd a.left 3
    simpa [uc22s2112r34q35_rho_two] using (hrel 2).symm

private noncomputable def uc22s2112r34q35_rsdEquiv :
    (ZMod 8 × ZMod 8 × Fin81.R0) ≃ uc22s2112r34q35_RSD where
  toFun p :=
    ⟨hat (n := 3) ![p.1, 3 * p.1, p.2.1, 3 * p.2.1] p.2.2, by
      change uc22s2112r34q35_rel
        (Multiplicative.toAdd (hat (n := 3) ![p.1, 3 * p.1, p.2.1, 3 * p.2.1] p.2.2).left)
      simp [uc22s2112r34q35_rel]⟩
  invFun a :=
    (Multiplicative.toAdd a.val.left 0, Multiplicative.toAdd a.val.left 2, a.val.right)
  left_inv p := by
    rcases p with ⟨x, y, π⟩
    simp
  right_inv a := by
    apply Subtype.ext
    rw [← hat_left a.val]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      simpa using uc22s2112r34q35_rsd_vector a.2
    · rfl

private lemma uc22s2112r34q35_card_RSD :
    Nat.card uc22s2112r34q35_RSD = 2 ^ 9 := by
  rw [← Nat.card_congr uc22s2112r34q35_rsdEquiv]
  simp only [Nat.card_prod, Nat.card_zmod, Fin81.card_R0]
  norm_num

private lemma uc22s2112r34q35_detL4_RSD {a : L4Hat 3}
    (ha : a ∈ uc22s2112r34q35_RSD) :
    detL4 3 a = 1 ∨ detL4 3 a = Multiplicative.ofAdd (4 : ZMod 8) := by
  have hrel := (uc22s2112r34q35_rel_iff _).mp ha
  have hsum : Multiplicative.toAdd (detL4 3 a) =
      4 * (Multiplicative.toAdd a.left 0 + Multiplicative.toAdd a.left 2) + sgnH a.right := by
    rw [detL4_apply, Fin.sum_univ_four]
    have h1 : Multiplicative.toAdd a.left 1 = 3 * Multiplicative.toAdd a.left 0 := by
      simpa [uc22s2112r34q35_rho_zero] using hrel 0
    have h3 : Multiplicative.toAdd a.left 3 = 3 * Multiplicative.toAdd a.left 2 := by
      simpa [uc22s2112r34q35_rho_two] using hrel 2
    rw [h1, h3]
    simp only [sgnH]
    ring
  rcases uc22s2112r34q35_four_mul_val
    (Multiplicative.toAdd a.left 0 + Multiplicative.toAdd a.left 2) with h | h <;>
    rcases uc22s2112r34q35_sgnH_val a.right with hs | hs
  · left
    apply Multiplicative.toAdd.injective
    rw [hsum, h, hs]
    decide
  · right
    apply Multiplicative.toAdd.injective
    rw [hsum, h, hs]
    decide
  · right
    apply Multiplicative.toAdd.injective
    rw [hsum, h, hs]
    decide
  · left
    apply Multiplicative.toAdd.injective
    rw [hsum, h, hs]
    decide

private lemma uc22s2112r34q35_card_RSD_inf_L4P :
    Nat.card (uc22s2112r34q35_RSD ⊓ L4P 3 : Subgroup (L4Hat 3)) = 2 ^ 8 := by
  let detR : uc22s2112r34q35_RSD →* Multiplicative (ZMod 8) :=
    (detL4 3).domRestrict uc22s2112r34q35_RSD
  have hrange : detR.range =
      Subgroup.zpowers (Multiplicative.ofAdd (4 : ZMod 8)) := by
    apply le_antisymm
    · rintro z ⟨a, rfl⟩
      change detL4 3 (a : L4Hat 3) ∈
        Subgroup.zpowers (Multiplicative.ofAdd (4 : ZMod 8))
      rcases uc22s2112r34q35_detL4_RSD a.2 with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨hat (n := 3) ![1, 3, 0, 0] (1 : Fin81.R0), ?_⟩, ?_⟩
      · change uc22s2112r34q35_rel
          (Multiplicative.toAdd (hat (n := 3) ![1, 3, 0, 0] (1 : Fin81.R0)).left)
        simp [uc22s2112r34q35_rel]
      · change Multiplicative.toAdd
          (detL4 3 (hat (n := 3) ![1, 3, 0, 0] (1 : Fin81.R0))) =
          Multiplicative.toAdd (Multiplicative.ofAdd (4 : ZMod 8))
        rw [detL4_apply]
        norm_num [sgnH, signZ, Fin.sum_univ_four]
  have hcardrange : Nat.card detR.range = 2 := by
    rw [hrange, Nat.card_zpowers]
    rw [orderOf_eq_iff (x := Multiplicative.ofAdd (4 : ZMod 8)) (by norm_num)]
    refine ⟨?_, ?_⟩
    · decide
    · intro m hm hm0
      interval_cases m
      · decide
  have h := Subgroup.card_ker_mul_card_range detR
  rw [hcardrange, uc22s2112r34q35_card_RSD, show (2 ^ 9 : ℕ) = 2 ^ 8 * 2 by norm_num] at h
  have hker : Nat.card detR.ker = 2 ^ 8 := Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hker_eq : detR.ker = (L4P 3).subgroupOf uc22s2112r34q35_RSD :=
    MonoidHom.ker_domRestrict uc22s2112r34q35_RSD (detL4 3)
  rw [hker_eq] at hker
  have hcard : Nat.card ((L4P 3).subgroupOf uc22s2112r34q35_RSD) =
      Nat.card (uc22s2112r34q35_RSD ⊓ L4P 3 : Subgroup (L4Hat 3)) := by
    rw [← Subgroup.inf_subgroupOf_left (L4P 3) uc22s2112r34q35_RSD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : (uc22s2112r34q35_RSD ⊓ L4P 3 : Subgroup (L4Hat 3)) ≤
        uc22s2112r34q35_RSD)).toEquiv
  rw [hcard] at hker
  exact hker

@[expose] def uc22s2112r34q35_C4mat (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 3, 0, 0; 2, 4, 0, 0; 0, 0, 1, 3; 0, 0, 2, 4]

private lemma uc22s2112r34q35_C4mat_eq_block (K : Type) [Field K] :
    uc22s2112r34q35_C4mat K =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (!![1, 3; 2, 4] : Matrix (Fin 2) (Fin 2) K) 0 0
          (!![1, 3; 2, 4] : Matrix (Fin 2) (Fin 2) K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma uc22s2112r34q35_det_C4mat (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    (uc22s2112r34q35_C4mat K).det ≠ 0 := by
  have hdet : (uc22s2112r34q35_C4mat K).det = (4 : K) := by
    rw [uc22s2112r34q35_C4mat_eq_block, Matrix.det_reindex_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_two_of]
    ring_nf
  rw [hdet]
  have h4 : (4 : K) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero h2 h2

private lemma uc22s2112r34q35_natCast_pow_five {K : Type} [Field K] [CharP K 5] (n : ℕ) :
    ((n : K) ^ 5) = (n : K) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  conv_lhs => rw [CharP.natCast_eq_natCast_mod (R := K) (p := 5) n]
  conv_rhs => rw [CharP.natCast_eq_natCast_mod (R := K) (p := 5) n]
  set k := n % 5 with hk
  have hklt : k < 5 := by rw [hk]; exact Nat.mod_lt _ (by norm_num)
  interval_cases k
  · simp
  · simp
  · rw [← Nat.cast_pow, show (2 ^ 5 : ℕ) = 32 by norm_num,
      show (32 : ℕ) = 5 * 6 + 2 by norm_num, Nat.cast_add, Nat.cast_mul,
      show ((5 : ℕ) : K) = 0 by simpa using h5]
    ring
  · rw [← Nat.cast_pow, show (3 ^ 5 : ℕ) = 243 by norm_num,
      show (243 : ℕ) = 5 * 48 + 3 by norm_num, Nat.cast_add, Nat.cast_mul,
      show ((5 : ℕ) : K) = 0 by simpa using h5]
    ring
  · rw [← Nat.cast_pow, show (4 ^ 5 : ℕ) = 1024 by norm_num,
      show (1024 : ℕ) = 5 * 204 + 4 by norm_num, Nat.cast_add, Nat.cast_mul,
      show ((5 : ℕ) : K) = 0 by simpa using h5]
    ring

private lemma uc22s2112r34q35_C4mat_map_pow (K : Type) [Field K] [CharP K 5] :
    (uc22s2112r34q35_C4mat K).map (· ^ 5) = uc22s2112r34q35_C4mat K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uc22s2112r34q35_C4mat]
  all_goals
    first
      | exact uc22s2112r34q35_natCast_pow_five 2
      | exact uc22s2112r34q35_natCast_pow_five 3
      | exact uc22s2112r34q35_natCast_pow_five 4

private def uc22s2112r34q35_G4 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  uc22s2112r34q35_rho.permMatrix K

private lemma uc22s2112r34q35_permMatrix_apply {K : Type} [Field K] (π : Perm (Fin 4))
    (a b : Fin 4) : (π.permMatrix K) a b = if π a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private lemma uc22s2112r34q35_G4_apply (K : Type) [Field K] (i l : Fin 4) :
    uc22s2112r34q35_G4 K i l =
      if l = uc22s2112r34q35_rho i then 1 else 0 := by
  rw [uc22s2112r34q35_G4, uc22s2112r34q35_permMatrix_apply]
  by_cases h : l = uc22s2112r34q35_rho i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

private lemma uc22s2112r34q35_C4mat_transpose_mul (K : Type) [Field K] [CharP K 5] :
    Matrix.transpose (uc22s2112r34q35_C4mat K) * uc22s2112r34q35_C4mat K =
      uc22s2112r34q35_G4 K := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h11 : (11 : K) = 1 := by
    have h : (11 : K) = (5 : K) * 2 + 1 := by norm_num
    rw [h, h5]; ring
  have h25 : (25 : K) = 0 := by
    have h : (25 : K) = (5 : K) * 5 := by norm_num
    rw [h, h5]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_C4mat, uc22s2112r34q35_G4,
      Matrix.mul_apply, Fin.sum_univ_four, uc22s2112r34q35_rho_zero,
      uc22s2112r34q35_rho_one, uc22s2112r34q35_rho_two, uc22s2112r34q35_rho_three]
  all_goals
    ring_nf
    first | exact h5 | exact h11 | exact h25

private lemma uc22s2112r34q35_five_add_three (x : ZMod 8) :
    5 * x + 3 * x = 0 := by
  have h : 5 * x + 3 * x = 8 * x := by ring
  rw [h, show (8 : ZMod 8) = 0 by decide, zero_mul]

private lemma uc22s2112r34q35_zeta_pow_add_eq_one {K : Type} [Field K]
    (D : L4Data K 3) {z w : ZMod 8} (h : z + w = 0) :
    (D.ζ : K) ^ z.val * (D.ζ : K) ^ w.val = 1 := by
  have hz : ((D.chi (Multiplicative.ofAdd z) : Kˣ) : K) = (D.ζ : K) ^ z.val := by
    rw [D.chi_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val]
  have hw : ((D.chi (Multiplicative.ofAdd w) : Kˣ) : K) = (D.ζ : K) ^ w.val := by
    rw [D.chi_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val]
  rw [← hz, ← hw, ← Units.val_mul, ← map_mul, ← ofAdd_add, h, ofAdd_zero, map_one,
    Units.val_one]

private lemma uc22s2112r34q35_zeta_pow_five_val {K : Type} [Field K]
    (D : L4Data K 3) (z : ZMod 8) :
    ((D.ζ : K) ^ z.val) ^ 5 = (D.ζ : K) ^ ((5 * z).val) := by
  rw [← pow_mul]
  refine pow_eq_pow_of_modEq (n := 8) ?_ ?_
  · have h : ((z.val * 5 : ℕ) : ZMod 8) = (((5 * z).val : ℕ) : ZMod 8) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      ring
    exact (ZMod.natCast_eq_natCast_iff (z.val * 5) ((5 * z).val) 8).mp h
  · rw [show (8 : ℕ) = orderOf D.ζ by rw [D.orderOf_ζ]; norm_num]
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one D.ζ, Units.val_one]

private lemma uc22s2112r34q35_permMatrix_map {K : Type} [Field K] [ExpChar K 5]
    (π : Perm (Fin 4)) :
    (π.permMatrix K).map (⇑(frobenius K 5)) = π.permMatrix K := by
  ext i j
  rw [Matrix.map_apply, uc22s2112r34q35_permMatrix_apply]
  by_cases h : π i = j
  · simp [h]
  · simp [h]

private lemma uc22s2112r34q35_embed_map_pow_eq {K : Type} [Field K] [ExpChar K 5]
    (D : L4Data K 3) (a : L4Hat 3) :
    (((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 5)) =
      Matrix.diagonal
        (fun i => (D.ζ : K) ^ ((5 * Multiplicative.toAdd a.left i).val)) *
        ((a.right : Perm (Fin 4))⁻¹).permMatrix K := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hf : (fun x : K => x ^ 5) = ⇑(frobenius K 5) := by
    funext x
    rw [frobenius_def]
  rw [hf, D.coe_embed, Matrix.map_mul,
    Matrix.diagonal_map (f := ⇑(frobenius K 5)) (by rw [frobenius_def]; simp),
    uc22s2112r34q35_permMatrix_map]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, frobenius_def]
    exact uc22s2112r34q35_zeta_pow_five_val D _
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

private lemma uc22s2112r34q35_diag_G_diag {K : Type} [Field K]
    (D : L4Data K 3) {a : L4Hat 3} (ha : a ∈ uc22s2112r34q35_RSD) :
    Matrix.diagonal
        (fun i => (D.ζ : K) ^ ((5 * Multiplicative.toAdd a.left i).val)) *
      uc22s2112r34q35_G4 K *
      Matrix.diagonal (fun i => (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val) =
      uc22s2112r34q35_G4 K := by
  have hrel := (uc22s2112r34q35_rel_iff (Multiplicative.toAdd a.left)).mp ha
  ext i j
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal,
    uc22s2112r34q35_G4_apply]
  by_cases h : j = uc22s2112r34q35_rho i
  · rw [if_pos h, one_mul]
    have hzw : 5 * Multiplicative.toAdd a.left i + Multiplicative.toAdd a.left j = 0 := by
      rw [h, hrel i]
      exact uc22s2112r34q35_five_add_three _
    exact uc22s2112r34q35_zeta_pow_add_eq_one D hzw
  · rw [if_neg h, zero_mul, mul_zero]

private lemma uc22s2112r34q35_permMatrix_conj_G4 (K : Type) [Field K]
    (π : Fin81.R0) :
    Matrix.transpose (((π : Perm (Fin 4))⁻¹).permMatrix K) *
      uc22s2112r34q35_G4 K * ((π : Perm (Fin 4))⁻¹).permMatrix K =
      uc22s2112r34q35_G4 K := by
  rw [Matrix.transpose_permMatrix, inv_inv, uc22s2112r34q35_G4,
    ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1
  have hcomm := (uc22s2112r34q35_rho_commute π).inv_left.eq
  calc ((π : Perm (Fin 4))⁻¹) * (uc22s2112r34q35_rho * (π : Perm (Fin 4))) =
      (((π : Perm (Fin 4))⁻¹) * uc22s2112r34q35_rho) * (π : Perm (Fin 4)) := by group
    _ = (uc22s2112r34q35_rho * ((π : Perm (Fin 4))⁻¹)) * (π : Perm (Fin 4)) := by
        rw [hcomm]
    _ = uc22s2112r34q35_rho := by group

private lemma uc22s2112r34q35_embed_map_transpose_G {K : Type} [Field K] [ExpChar K 5]
    (D : L4Data K 3) {a : L4Hat 3} (ha : a ∈ uc22s2112r34q35_RSD) :
    Matrix.transpose
        ((((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 5))) *
      uc22s2112r34q35_G4 K *
      ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      uc22s2112r34q35_G4 K := by
  rw [uc22s2112r34q35_embed_map_pow_eq, D.coe_embed]
  calc
    Matrix.transpose
        (Matrix.diagonal
            (fun i => (D.ζ : K) ^ ((5 * Multiplicative.toAdd a.left i).val)) *
          ((a.right : Perm (Fin 4))⁻¹).permMatrix K) *
        uc22s2112r34q35_G4 K *
        (Matrix.diagonal (fun i => (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val) *
          ((a.right : Perm (Fin 4))⁻¹).permMatrix K) =
      (Matrix.transpose (((a.right : Perm (Fin 4))⁻¹).permMatrix K) *
        Matrix.diagonal
          (fun i => (D.ζ : K) ^ ((5 * Multiplicative.toAdd a.left i).val))) *
        uc22s2112r34q35_G4 K *
        (Matrix.diagonal (fun i => (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val) *
          ((a.right : Perm (Fin 4))⁻¹).permMatrix K) := by
        rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    _ = Matrix.transpose (((a.right : Perm (Fin 4))⁻¹).permMatrix K) *
        (Matrix.diagonal
          (fun i => (D.ζ : K) ^ ((5 * Multiplicative.toAdd a.left i).val)) *
          uc22s2112r34q35_G4 K *
          Matrix.diagonal (fun i => (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val)) *
        ((a.right : Perm (Fin 4))⁻¹).permMatrix K := by noncomm_ring
    _ = Matrix.transpose (((a.right : Perm (Fin 4))⁻¹).permMatrix K) *
        uc22s2112r34q35_G4 K * ((a.right : Perm (Fin 4))⁻¹).permMatrix K := by
        rw [uc22s2112r34q35_diag_G_diag D ha]
    _ = uc22s2112r34q35_G4 K := uc22s2112r34q35_permMatrix_conj_G4 K a.right

@[expose] noncomputable def uc22s2112r34q35_C4 (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uc22s2112r34q35_C4mat K)
    (uc22s2112r34q35_det_C4mat K h2)

private lemma uc22s2112r34q35_coe_C4 (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    ((uc22s2112r34q35_C4 K h2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      uc22s2112r34q35_C4mat K :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma uc22s2112r34q35_det_embed_eq_one {K : Type} [Field K]
    (D : L4Data K 3) {a : L4Hat 3} (ha : a ∈ L4P 3) :
    ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [D.det_embed (by norm_num), mem_L4P.mp ha]
  simp

private theorem uc22s2112r34q35_unitaryFive (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) : UnitaryFieldData 5 1 K :=
  ⟨Nat.prime_five, by norm_num, by rw [hK]; norm_num⟩

private lemma uc22s2112r34q35_C4_conj_mem_statedSU {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) {a : L4Hat 3}
    (ha : a ∈ (uc22s2112r34q35_RSD ⊓ L4P 3 : Subgroup (L4Hat 3))) :
    uc22s2112r34q35_C4 K h2 * D.embed a * (uc22s2112r34q35_C4 K h2)⁻¹ ∈
      StatedSU 4 5 K := by
  have : CharP K 5 := (uc22s2112r34q35_unitaryFive K hK).charP
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  let hU : UnitaryFieldData 5 1 K := uc22s2112r34q35_unitaryFive K hK
  have hbar : ⇑hU.bar = fun x : K => x ^ 5 := by
    funext x
    simpa using hU.bar_apply x
  have hQ : Matrix.transpose
        (((uc22s2112r34q35_C4 K h2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hU.bar) *
        1 * ((uc22s2112r34q35_C4 K h2 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = uc22s2112r34q35_G4 K := by
    rw [hbar, uc22s2112r34q35_coe_C4 K h2, uc22s2112r34q35_C4mat_map_pow K,
      Matrix.mul_one, uc22s2112r34q35_C4mat_transpose_mul K]
  have hg : D.embed a ∈ gramSU hU (uc22s2112r34q35_G4 K) := by
    rw [mem_gramSU]
    refine ⟨?_, uc22s2112r34q35_det_embed_eq_one D ha.2⟩
    rw [hbar]
    simpa using uc22s2112r34q35_embed_map_transpose_G D ha.1
  have hconj := conj_mem_gramSU_of_gram hU hQ hg
  have hEq : StatedSU 4 5 K = gramSU hU (1 : Matrix (Fin 4) (Fin 4) K) := by
    change unitarySU 5 1 K 4 = gramSU hU (1 : Matrix (Fin 4) (Fin 4) K)
    exact unitarySU_eq_gramSU hU 4
  rw [hEq]
  exact hconj

private lemma uc22s2112r34q35_scalar_one_transpose {K : Type} [Field K] (c : K) :
    Matrix.transpose (Matrix.scalar (Fin 1) c) = Matrix.scalar (Fin 1) c := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.scalar, Matrix.transpose]

private lemma uc22s2112r34q35_scalar_one_det {K : Type} [Field K] (c : K) :
    (Matrix.scalar (Fin 1) c).det = c := by
  rw [show Matrix.scalar (Fin 1) c =
      Matrix.diagonal (fun _ : Fin 1 => c) by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.scalar]]
  simp

private lemma uc22s2112r34q35_blk5_mul {K : Type} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K) (c d : K) :
    uc22s2112r34q35_blk5 A c * uc22s2112r34q35_blk5 B d =
      uc22s2112r34q35_blk5 (A * B) (c * d) := by
  simp only [uc22s2112r34q35_blk5]
  rw [← Matrix.coe_reindexRingEquiv]
  rw [← (Matrix.reindexRingEquiv K finSumFinEquiv).map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul]

private lemma uc22s2112r34q35_blk5_one {K : Type} [Field K] :
    uc22s2112r34q35_blk5 (1 : Matrix (Fin 4) (Fin 4) K) 1 = 1 := by
  rw [uc22s2112r34q35_blk5,
    show Matrix.scalar (Fin 1) (1 : K) = 1 by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.scalar],
    Matrix.fromBlocks_one,
    ← Matrix.toEquiv_reindexLinearEquiv (R := K) (A := K)
      (eₘ := finSumFinEquiv) (eₙ := finSumFinEquiv)]
  exact Matrix.reindexLinearEquiv_one (R := K) (A := K) finSumFinEquiv

private lemma uc22s2112r34q35_blk5_transpose {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    Matrix.transpose (uc22s2112r34q35_blk5 A c) =
      uc22s2112r34q35_blk5 (Matrix.transpose A) c := by
  simp only [uc22s2112r34q35_blk5, Matrix.transpose_reindex,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    uc22s2112r34q35_scalar_one_transpose]

private lemma uc22s2112r34q35_reindex_finSum_map {K : Type} [Field K]
    (M : Matrix (Fin 4 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) K) (f : K → K) :
    (Matrix.reindex (finSumFinEquiv (m := 4) (n := 1))
      (finSumFinEquiv (m := 4) (n := 1)) M).map f =
      Matrix.reindex (finSumFinEquiv (m := 4) (n := 1))
        (finSumFinEquiv (m := 4) (n := 1)) (M.map f) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.map_apply]

private lemma uc22s2112r34q35_blk5_map {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (f : K → K) (hf0 : f 0 = 0) :
    (uc22s2112r34q35_blk5 A c).map f = uc22s2112r34q35_blk5 (A.map f) (f c) := by
  rw [uc22s2112r34q35_blk5, uc22s2112r34q35_blk5,
    show Matrix.scalar (Fin 1) c = Matrix.diagonal (fun _ : Fin 1 => c) by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.scalar],
    show Matrix.scalar (Fin 1) (f c) = Matrix.diagonal (fun _ : Fin 1 => f c) by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.scalar],
    uc22s2112r34q35_reindex_finSum_map, Matrix.fromBlocks_map,
    Matrix.diagonal_map (f := f) hf0]
  simp [Matrix.map_zero, hf0]

private lemma uc22s2112r34q35_det_blk5 {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    (uc22s2112r34q35_blk5 A c).det = A.det * c := by
  rw [uc22s2112r34q35_blk5, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, uc22s2112r34q35_scalar_one_det]

private lemma uc22s2112r34q35_det_embed_eq_one_or_neg_one {K : Type} [Field K]
    (D : L4Data K 3) {a : L4Hat 3} (ha : a ∈ uc22s2112r34q35_RSD) :
    ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 ∨
      ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1 := by
  rcases uc22s2112r34q35_detL4_RSD ha with h | h
  · left
    rw [D.det_embed (by norm_num), h]
    simp
  · right
    rw [D.det_embed (by norm_num), h, toAdd_ofAdd]
    exact D.zeta_pow_two_pow_pred (by norm_num : 1 ≤ 3)

private lemma uc22s2112r34q35_blockDet_coe {K : Type} [Field K] (A : GL (Fin 4) K) :
    ((uc22s2112r34q35_blockDet K A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 (A : Matrix (Fin 4) (Fin 4) K)
        (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) :=
  rfl

private def uc22s2112r34q35_topLeft {K : Type} [Field K]
    (M : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => M ((finSumFinEquiv (m := 4) (n := 1)) (Sum.inl i))
    ((finSumFinEquiv (m := 4) (n := 1)) (Sum.inl j))

private lemma uc22s2112r34q35_topLeft_blk5 {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    uc22s2112r34q35_topLeft (uc22s2112r34q35_blk5 A c) = A := by
  ext i j
  simp [uc22s2112r34q35_topLeft, uc22s2112r34q35_blk5, Matrix.reindex_apply,
    Matrix.fromBlocks]

private lemma uc22s2112r34q35_blockDet_injective (K : Type) [Field K] :
    Function.Injective (uc22s2112r34q35_blockDet K) := by
  intro A B h
  have hval : ((uc22s2112r34q35_blockDet K A : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) =
      ((uc22s2112r34q35_blockDet K B : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) :=
    congrArg (fun X : GL (Fin 5) K => (X : Matrix (Fin 5) (Fin 5) K)) h
  rw [uc22s2112r34q35_blockDet_coe, uc22s2112r34q35_blockDet_coe] at hval
  have htop := congrArg (fun M : Matrix (Fin 5) (Fin 5) K =>
    uc22s2112r34q35_topLeft M) hval
  rw [uc22s2112r34q35_topLeft_blk5, uc22s2112r34q35_topLeft_blk5] at htop
  exact Units.ext htop

private lemma uc22s2112r34q35_blockDet_mem_gramSU {K : Type} [Field K] [Finite K]
    (hU : UnitaryFieldData 5 1 K) (D : L4Data K 3) {a : L4Hat 3}
    (ha : a ∈ uc22s2112r34q35_RSD) :
    uc22s2112r34q35_blockDet K (D.embed a) ∈
      gramSU hU (uc22s2112r34q35_blk5 (uc22s2112r34q35_G4 K) 1) := by
  have : CharP K 5 := hU.charP
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  have hbar : ⇑hU.bar = fun x : K => x ^ 5 := by
    funext x
    simpa using hU.bar_apply x
  let M : Matrix (Fin 4) (Fin 4) K := (D.embed a : GL (Fin 4) K)
  let δ : K := ((Matrix.GeneralLinearGroup.det (D.embed a))⁻¹ : Kˣ)
  have hMbar : (((uc22s2112r34q35_blockDet K (D.embed a) : GL (Fin 5) K)) :
      Matrix (Fin 5) (Fin 5) K).map hU.bar =
      uc22s2112r34q35_blk5 (M.map hU.bar) (hU.bar δ) := by
    rw [uc22s2112r34q35_blockDet_coe,
      uc22s2112r34q35_blk5_map _ _ _ (map_zero hU.bar)]
  have hiso : Matrix.transpose (M.map hU.bar) * uc22s2112r34q35_G4 K * M =
      uc22s2112r34q35_G4 K := by
    rw [hbar]
    exact uc22s2112r34q35_embed_map_transpose_G D ha
  have hdet : M.det = 1 ∨ M.det = -1 :=
    uc22s2112r34q35_det_embed_eq_one_or_neg_one D ha
  have hδ : hU.bar δ * δ = 1 := by
    rcases hdet with h | h
    · rw [show δ = (1 : K) by
        simp only [δ, Units.val_inv_eq_inv_val]
        rw [show ((Matrix.GeneralLinearGroup.det (D.embed a) : Kˣ) : K) = M.det by rfl, h]
        norm_num]
      simp [hbar]
    · rw [show δ = (-1 : K) by
        simp only [δ, Units.val_inv_eq_inv_val]
        rw [show ((Matrix.GeneralLinearGroup.det (D.embed a) : Kˣ) : K) = M.det by rfl, h]
        norm_num]
      simp [hbar]
      norm_num
  rw [mem_gramSU]
  constructor
  · rw [hMbar, uc22s2112r34q35_blockDet_coe, uc22s2112r34q35_blk5_transpose,
      uc22s2112r34q35_blk5_mul, uc22s2112r34q35_blk5_mul, hiso]
    change uc22s2112r34q35_blk5 (uc22s2112r34q35_G4 K) (hU.bar δ * 1 * δ) =
      uc22s2112r34q35_blk5 (uc22s2112r34q35_G4 K) 1
    rw [mul_one, hδ]
  · rw [uc22s2112r34q35_blockDet_coe, uc22s2112r34q35_det_blk5]
    rw [Units.val_inv_eq_inv_val]
    rw [show ((Matrix.GeneralLinearGroup.det (D.embed a) : Kˣ) : K) = M.det by rfl]
    exact mul_inv_cancel₀ (Units.ne_zero (Matrix.GeneralLinearGroup.det (D.embed a)))

private def uc22s2112r34q35_R4 : Subgroup (L4Hat 3) :=
  (uc22s2112r34q35_RSD ⊓ L4P 3 : Subgroup (L4Hat 3))

private noncomputable def uc22s2112r34q35_psi4 (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (D : L4Data K 3) : uc22s2112r34q35_R4 →* GL (Fin 4) K where
  toFun a := uc22s2112r34q35_C4 K h2 * D.embed (a : L4Hat 3) *
    (uc22s2112r34q35_C4 K h2)⁻¹
  map_one' := by simp
  map_mul' := by
    intro a b
    change uc22s2112r34q35_C4 K h2 *
        D.embed ((a : L4Hat 3) * (b : L4Hat 3)) *
        (uc22s2112r34q35_C4 K h2)⁻¹ =
      (uc22s2112r34q35_C4 K h2 * D.embed (a : L4Hat 3) *
          (uc22s2112r34q35_C4 K h2)⁻¹) *
        (uc22s2112r34q35_C4 K h2 * D.embed (b : L4Hat 3) *
          (uc22s2112r34q35_C4 K h2)⁻¹)
    rw [map_mul]
    group

private lemma uc22s2112r34q35_psi4_injective (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Function.Injective (uc22s2112r34q35_psi4 K h2 D) := by
  intro a b h
  apply Subtype.ext
  apply D.embed_injective
  have h' := congrArg (fun x : GL (Fin 4) K =>
    (uc22s2112r34q35_C4 K h2)⁻¹ * x * (uc22s2112r34q35_C4 K h2)) h
  simpa [uc22s2112r34q35_psi4, mul_assoc] using h'

private noncomputable def uc22s2112r34q35_phi4 (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    uc22s2112r34q35_R4 →* StatedSU 4 5 K :=
  (uc22s2112r34q35_psi4 K h2 D).codRestrict (StatedSU 4 5 K) fun a =>
    uc22s2112r34q35_C4_conj_mem_statedSU hK h2 D
      (by simpa [uc22s2112r34q35_R4] using a.2)

private lemma uc22s2112r34q35_phi4_injective (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Function.Injective (uc22s2112r34q35_phi4 K hK h2 D) := by
  intro a b h
  apply uc22s2112r34q35_psi4_injective K h2 D
  exact congrArg (fun x : StatedSU 4 5 K => (x : GL (Fin 4) K)) h

private lemma uc22s2112r34q35_card_phi4_range (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Nat.card (uc22s2112r34q35_phi4 K hK h2 D).range = 2 ^ 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (uc22s2112r34q35_phi4_injective K hK h2 D)).toEquiv]
  simpa [uc22s2112r34q35_R4] using uc22s2112r34q35_card_RSD_inf_L4P

private lemma uc22s2112r34q35_card_statedSU_four_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    Nat.card (StatedSU 4 5 K) = 2 ^ 8 * 115171875 := by
  have hU : UnitaryFieldData 5 1 K := uc22s2112r34q35_unitaryFive K hK
  have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 4, ((((5 : ℕ) : ℤ) ^ i - (-1) ^ i)) = 1886976 := by
    decide
  rw [show (5 ^ 1 : ℕ) = 5 by norm_num, hprod] at h
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  norm_num

private lemma uc22s2112r34q35_card_statedSU_five_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    Nat.card (StatedSU 5 5 K) = 2 ^ 9 * 11520873 * 5 ^ 10 := by
  have hU : UnitaryFieldData 5 1 K := uc22s2112r34q35_unitaryFive K hK
  have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 5) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 5, ((((5 : ℕ) : ℤ) ^ i - (-1) ^ i)) = 5898686976 := by
    decide
  rw [show (5 ^ 1 : ℕ) = 5 by norm_num, hprod] at h
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  norm_num

private lemma uc22s2112r34q35_det_C4 (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    ((uc22s2112r34q35_C4 K h2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 4 := by
  rw [uc22s2112r34q35_coe_C4, uc22s2112r34q35_C4mat_eq_block,
    Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fin_two_of]
  ring

private lemma uc22s2112r34q35_blockDet_conj_mem_statedSU {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) {a : L4Hat 3}
    (ha : a ∈ uc22s2112r34q35_RSD) :
    uc22s2112r34q35_blockDet K
        (uc22s2112r34q35_C4 K h2 * D.embed a * (uc22s2112r34q35_C4 K h2)⁻¹) ∈
      StatedSU 5 5 K := by
  let hU : UnitaryFieldData 5 1 K := uc22s2112r34q35_unitaryFive K hK
  have : CharP K 5 := hU.charP
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  have hbar : ⇑hU.bar = fun x : K => x ^ 5 := by
    funext x
    simpa using hU.bar_apply x
  let δC : K := ((Matrix.GeneralLinearGroup.det (uc22s2112r34q35_C4 K h2))⁻¹ : Kˣ)
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h4 : (4 : K) = -1 := by
    have h : (4 : K) + 1 = 0 := by
      rw [show (4 : K) + 1 = (5 : K) by norm_num, h5]
    exact eq_neg_of_add_eq_zero_left h
  have hC5 : ((uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2) :
      GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 (uc22s2112r34q35_C4mat K) δC := by
    rw [uc22s2112r34q35_blockDet_coe, uc22s2112r34q35_coe_C4]
  have hδC : hU.bar δC * δC = 1 := by
    rw [show δC = ((4 : K)⁻¹) by
      simp [δC, uc22s2112r34q35_det_C4 K h2]]
    rw [hbar, h4]
    norm_num
  have hC4bar : (uc22s2112r34q35_C4mat K).map hU.bar =
      uc22s2112r34q35_C4mat K := by
    rw [hbar]
    exact uc22s2112r34q35_C4mat_map_pow K
  have hQ : Matrix.transpose
        (((uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2) :
          GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map hU.bar) *
        1 * ((uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2) :
          GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 (uc22s2112r34q35_G4 K) 1 := by
    rw [hC5, Matrix.mul_one, uc22s2112r34q35_blk5_map _ _ _ (map_zero hU.bar),
      uc22s2112r34q35_blk5_transpose,
      uc22s2112r34q35_blk5_mul, hC4bar,
      uc22s2112r34q35_C4mat_transpose_mul, hδC]
  have hM5 : uc22s2112r34q35_blockDet K (D.embed a) ∈
      gramSU hU (uc22s2112r34q35_blk5 (uc22s2112r34q35_G4 K) 1) :=
    uc22s2112r34q35_blockDet_mem_gramSU hU D ha
  have hconj := conj_mem_gramSU_of_gram hU hQ hM5
  have hEq : StatedSU 5 5 K = gramSU hU (1 : Matrix (Fin 5) (Fin 5) K) := by
    change unitarySU 5 1 K 5 = gramSU hU (1 : Matrix (Fin 5) (Fin 5) K)
    exact unitarySU_eq_gramSU hU 5
  rw [hEq]
  have hmap : uc22s2112r34q35_blockDet K
        (uc22s2112r34q35_C4 K h2 * D.embed a * (uc22s2112r34q35_C4 K h2)⁻¹) =
      uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2) *
        uc22s2112r34q35_blockDet K (D.embed a) *
        (uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap]
  exact hconj

private noncomputable def uc22s2112r34q35_B (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    GL (Fin 5) K :=
  uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2)

private lemma uc22s2112r34q35_blockDet_conj_mem_statedSU' {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3)
    {a : L4Hat 3} (ha : a ∈ uc22s2112r34q35_RSD) :
    uc22s2112r34q35_B K h2 * uc22s2112r34q35_blockDet K (D.embed a) *
        (uc22s2112r34q35_B K h2)⁻¹ ∈ StatedSU 5 5 K := by
  have h := uc22s2112r34q35_blockDet_conj_mem_statedSU hK h2 D ha
  have hmap : uc22s2112r34q35_blockDet K
        (uc22s2112r34q35_C4 K h2 * D.embed a * (uc22s2112r34q35_C4 K h2)⁻¹) =
      uc22s2112r34q35_B K h2 * uc22s2112r34q35_blockDet K (D.embed a) *
        (uc22s2112r34q35_B K h2)⁻¹ := by
    change uc22s2112r34q35_blockDet K
        (uc22s2112r34q35_C4 K h2 * D.embed a * (uc22s2112r34q35_C4 K h2)⁻¹) =
      uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2) *
        uc22s2112r34q35_blockDet K (D.embed a) *
        (uc22s2112r34q35_blockDet K (uc22s2112r34q35_C4 K h2))⁻¹
    rw [map_mul, map_mul, map_inv]
  rwa [hmap] at h

private noncomputable def uc22s2112r34q35_psi5 (K : Type) [Field K] (_hK : Nat.card K = 25)
    (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    uc22s2112r34q35_RSD →* GL (Fin 5) K where
  toFun a := uc22s2112r34q35_B K h2 * uc22s2112r34q35_blockDet K
    (D.embed (a : L4Hat 3)) * (uc22s2112r34q35_B K h2)⁻¹
  map_one' := by simp
  map_mul' := by
    intro a b
    change uc22s2112r34q35_B K h2 *
        uc22s2112r34q35_blockDet K
          (D.embed ((a : L4Hat 3) * (b : L4Hat 3))) *
        (uc22s2112r34q35_B K h2)⁻¹ =
      (uc22s2112r34q35_B K h2 * uc22s2112r34q35_blockDet K
          (D.embed (a : L4Hat 3)) * (uc22s2112r34q35_B K h2)⁻¹) *
        (uc22s2112r34q35_B K h2 * uc22s2112r34q35_blockDet K
          (D.embed (b : L4Hat 3)) * (uc22s2112r34q35_B K h2)⁻¹)
    rw [map_mul, map_mul]
    group

private lemma uc22s2112r34q35_psi5_injective (K : Type) [Field K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Function.Injective (uc22s2112r34q35_psi5 K hK h2 D) := by
  intro a b h
  apply Subtype.ext
  apply D.embed_injective
  apply uc22s2112r34q35_blockDet_injective K
  have h' := congrArg (fun x : GL (Fin 5) K =>
    (uc22s2112r34q35_B K h2)⁻¹ * x * (uc22s2112r34q35_B K h2)) h
  simpa [uc22s2112r34q35_psi5, mul_assoc] using h'

private noncomputable def uc22s2112r34q35_phi5 (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    uc22s2112r34q35_RSD →* StatedSU 5 5 K :=
  (uc22s2112r34q35_psi5 K hK h2 D).codRestrict (StatedSU 5 5 K) fun a =>
    uc22s2112r34q35_blockDet_conj_mem_statedSU' hK h2 D a.2

private lemma uc22s2112r34q35_phi5_injective (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Function.Injective (uc22s2112r34q35_phi5 K hK h2 D) := by
  intro a b h
  apply uc22s2112r34q35_psi5_injective K hK h2 D
  exact congrArg (fun x : StatedSU 5 5 K => (x : GL (Fin 5) K)) h

private lemma uc22s2112r34q35_card_phi5_range (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 25) (h2 : (2 : K) ≠ 0) (D : L4Data K 3) :
    Nat.card (uc22s2112r34q35_phi5 K hK h2 D).range = 2 ^ 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (uc22s2112r34q35_phi5_injective K hK h2 D)).toEquiv]
  exact uc22s2112r34q35_card_RSD

private lemma uc22s2112r34q35_fact_card_SU4_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    (Nat.card (StatedSU 4 5 K)).factorization 2 = 8 := by
  rw [uc22s2112r34q35_card_statedSU_four_five hK]
  rw [Nat.factorization_mul (by norm_num : 2 ^ 8 ≠ 0)
    (by norm_num : 115171875 ≠ 0)]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 115171875)]

private lemma uc22s2112r34q35_fact_card_SU5_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    (Nat.card (StatedSU 5 5 K)).factorization 2 = 9 := by
  rw [uc22s2112r34q35_card_statedSU_five_five hK]
  rw [Nat.factorization_mul (by norm_num : 2 ^ 9 * 11520873 ≠ 0)
    (by norm_num : 5 ^ 10 ≠ 0)]
  rw [Nat.factorization_mul (by norm_num : 2 ^ 9 ≠ 0)
    (by norm_num : 11520873 ≠ 0)]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 11520873),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9765625)]

private lemma uc22s2112r34q35_card_Z_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 5 K)) = 2 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (p := 5) (f := 1)
    Nat.prime_five (by rw [hK]; norm_num) (n := 4) (by norm_num)).2.2
  simpa using h

private lemma uc22s2112r34q35_card_Z_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    Nat.card ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 5 K)) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (p := 5) (f := 1)
    Nat.prime_five (by rw [hK]; norm_num) (n := 5) (by norm_num)).2.2
  simpa using h

private lemma uc22s2112r34q35_isPGroup_Z_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    IsPGroup 2 ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 5 K)) :=
  IsPGroup.of_card (n := 1) (by
    rw [uc22s2112r34q35_card_Z_four hK]
    norm_num)

private lemma uc22s2112r34q35_isPGroup_Z_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) :
    IsPGroup 2 ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 5 K)) :=
  IsPGroup.of_card (n := 0) (by
    rw [uc22s2112r34q35_card_Z_five hK]
    norm_num)

private lemma uc22s2112r34q35_not_dvd_GL2_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) (hs13 : s ≠ 13) :
    ¬ s ∣ Nat.card (GL (Fin 2) K) := by
  have hcard : Nat.card (GL (Fin 2) K) = 374400 := by
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_gl_two, hK]
    norm_num
  rw [hcard]
  intro hd
  have hfact : 374400 = 2 ^ 7 * (3 ^ 2 * (5 ^ 2 * 13)) := by norm_num
  rw [hfact] at hd
  rcases hs.dvd_mul.mp hd with h2 | hd
  · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hs h2)
    omega
  rcases hs.dvd_mul.mp hd with h3 | hd
  · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow hs h3)
    omega
  rcases hs.dvd_mul.mp hd with h5 | h13
  · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).mp
      (Nat.Prime.dvd_of_dvd_pow hs h5)
    omega
  · exact hs13 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 13)).mp h13)

private lemma uc22s2112r34q35_not_dvd_card_sub_one_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 25) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ Nat.card K - 1 := by
  have hcard : Nat.card K - 1 = 2 ^ 3 * 3 := by
    rw [hK]
    norm_num
  rw [hcard]
  intro hd
  rcases hs.dvd_mul.mp hd with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hs h2)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h3
    omega

theorem uc22s2112r34q35_alpha_psu4_five {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSU 4 5 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s)
    (hs13 : s ≠ 13) : orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hfield, hfinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have hK' : Nat.card K = 25 := by simpa using hK
  have : CharP K 5 := (uc22s2112r34q35_unitaryFive K hK').charP
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    have hdvd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp hzero
    norm_num at hdvd
  obtain ⟨D⟩ : Nonempty (L4Data K 3) :=
    exists_l4Data_of_dvd (K := K) (n := 3) (by rw [hK']; norm_num)
  let H := StatedSU 4 5 K
  let Z : Subgroup H := (StatedScalars (Fin 4) K).subgroupOf H
  have : Z.Normal := Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 4) K) H
  have hZ : IsPGroup 2 Z := uc22s2112r34q35_isPGroup_Z_four hK'
  let φ : uc22s2112r34q35_R4 →* H := uc22s2112r34q35_phi4 K hK' h2 D
  let Ssub : Subgroup H := φ.range
  have hScard : Nat.card Ssub = 2 ^ 8 := uc22s2112r34q35_card_phi4_range K hK' h2 D
  have hfac : (Nat.card H).factorization 2 = 8 := uc22s2112r34q35_fact_card_SU4_five hK'
  let S : Sylow 2 H := Sylow.ofCard Ssub (by rw [hScard, hfac])
  have hScoe : (S : Subgroup H) = Ssub := Sylow.coe_ofCard _ _
  obtain ⟨h, hpow, hne, hnorm⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hnorm' : h ∈ normalizer (Ssub : Set H) := by simpa [hScoe] using hnorm
  let C : GL (Fin 4) K := uc22s2112r34q35_C4 K h2
  let h' : GL (Fin 4) K := C⁻¹ * (h : GL (Fin 4) K) * C
  have hh : h' ^ s = 1 := by
    have hpowGL : (h : GL (Fin 4) K) ^ s = 1 := by
      rw [← Subgroup.coe_pow]
      exact congrArg (fun y : H => (y : GL (Fin 4) K)) hpow
    have := conj_pow (i := s) (a := C⁻¹) (b := (h : GL (Fin 4) K))
    simpa [h', hpowGL, mul_assoc] using this
  have hN : ∀ a ∈ uc22s2112r34q35_R4, ∃ a' ∈ uc22s2112r34q35_R4,
      h' * D.embed a * h'⁻¹ = D.embed a' := by
    intro a ha
    have haS : φ ⟨a, ha⟩ ∈ Ssub := ⟨⟨a, ha⟩, rfl⟩
    have hmem : h * (φ ⟨a, ha⟩) * h⁻¹ ∈ Ssub :=
      ((Subgroup.mem_normalizer_iff.mp hnorm') (φ ⟨a, ha⟩)).mp haS
    have hmem' : ∃ b : uc22s2112r34q35_R4, φ b = h * (φ ⟨a, ha⟩) * h⁻¹ := by
      simpa [Ssub] using hmem
    obtain ⟨a', hEq⟩ := hmem'
    have hEqGL : C * D.embed a' * C⁻¹ =
        (h : GL (Fin 4) K) * (C * D.embed a * C⁻¹) * (h : GL (Fin 4) K)⁻¹ := by
      have := congrArg (fun y : H => (y : GL (Fin 4) K)) hEq
      simpa [φ, C, uc22s2112r34q35_phi4, uc22s2112r34q35_psi4] using this
    refine ⟨a', a'.2, ?_⟩
    have hconj := congrArg (fun y : GL (Fin 4) K => C⁻¹ * y * C) hEqGL
    have hleft : C⁻¹ * (C * D.embed a' * C⁻¹) * C = D.embed a' := by group
    have hright : C⁻¹ * ((h : GL (Fin 4) K) * (C * D.embed a * C⁻¹) *
        (h : GL (Fin 4) K)⁻¹) * C = h' * D.embed a * h'⁻¹ := by
      simp only [h']
      group
    rw [hleft, hright] at hconj
    exact hconj.symm
  have hN' : ∀ a ∈ uc22s2112r34q35_R4, ∃ a' ∈ uc22s2112r34q35_R4,
      h'⁻¹ * D.embed a * h' = D.embed a' := by
    intro a ha
    have haS : φ ⟨a, ha⟩ ∈ Ssub := ⟨⟨a, ha⟩, rfl⟩
    have hmem : h⁻¹ * (φ ⟨a, ha⟩) * h ∈ Ssub :=
      ((Subgroup.mem_normalizer_iff''.mp hnorm') (φ ⟨a, ha⟩)).mp haS
    have hmem' : ∃ b : uc22s2112r34q35_R4, φ b = h⁻¹ * (φ ⟨a, ha⟩) * h := by
      simpa [Ssub] using hmem
    obtain ⟨a', hEq⟩ := hmem'
    have hEqGL : C * D.embed a' * C⁻¹ =
        (h : GL (Fin 4) K)⁻¹ * (C * D.embed a * C⁻¹) * (h : GL (Fin 4) K) := by
      have := congrArg (fun y : H => (y : GL (Fin 4) K)) hEq
      simpa [φ, C, uc22s2112r34q35_phi4, uc22s2112r34q35_psi4] using this
    refine ⟨a', a'.2, ?_⟩
    have hconj := congrArg (fun y : GL (Fin 4) K => C⁻¹ * y * C) hEqGL
    have hleft : C⁻¹ * (C * D.embed a' * C⁻¹) * C = D.embed a' := by group
    have hright : C⁻¹ * ((h : GL (Fin 4) K)⁻¹ * (C * D.embed a * C⁻¹) *
        (h : GL (Fin 4) K)) * C = h'⁻¹ * D.embed a * h' := by
      simp only [h']
      group
    rw [hleft, hright] at hconj
    exact hconj.symm
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (n := 3) ((pv (n := 3) (π : Perm (Fin 4)) (![1, 3, 1, 3] : Fin 4 → ZMod 8) -
        (![1, 3, 1, 3] : Fin 4 → ZMod 8)) : Fin 4 → ZMod 8) ∨
      ¬ IsConst (n := 3) ((pv (n := 3) (π : Perm (Fin 4)) (![1, 3, 7, 5] : Fin 4 → ZMod 8) -
        (![1, 3, 7, 5] : Fin 4 → ZMod 8)) : Fin 4 → ZMod 8) := by
    intro π hπ
    rcases r0_eq_words π with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hπ rfl).elim
    all_goals
      simp only [IsConst]
      decide
  have he₁ : hat (n := 3) ![1, 3, 1, 3] (1 : Fin81.R0) ∈ uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel ![1, 3, 1, 3]
      simp [uc22s2112r34q35_rel]
    · show hat (n := 3) ![1, 3, 1, 3] (1 : Fin81.R0) ∈ L4P 3
      rw [mem_L4P]
      decide
  have he₂ : hat (n := 3) ![1, 3, 7, 5] (1 : Fin81.R0) ∈ uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel ![1, 3, 7, 5]
      simp [uc22s2112r34q35_rel]
      decide
    · show hat (n := 3) ![1, 3, 7, 5] (1 : Fin81.R0) ∈ L4P 3
      rw [mem_L4P]
      decide
  have hy₀₁ : hat (n := 3) ![1, 3, 0, 0] uc22s2112r34q35_r01 ∈
      uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel ![1, 3, 0, 0]
      simp [uc22s2112r34q35_rel]
    · show hat (n := 3) ![1, 3, 0, 0] uc22s2112r34q35_r01 ∈ L4P 3
      rw [mem_L4P]
      decide
  have hy₂₃ : hat (n := 3) ![1, 3, 0, 0] uc22s2112r34q35_r23 ∈
      uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel ![1, 3, 0, 0]
      simp [uc22s2112r34q35_rel]
    · show hat (n := 3) ![1, 3, 0, 0] uc22s2112r34q35_r23 ∈ L4P 3
      rw [mem_L4P]
      decide
  have hy₀₂ : hat (n := 3) ![0, 0, 0, 0] uc22s2112r34q35_r02 ∈
      uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel ![0, 0, 0, 0]
      simp [uc22s2112r34q35_rel]
    · show hat (n := 3) ![0, 0, 0, 0] uc22s2112r34q35_r02 ∈ L4P 3
      rw [mem_L4P]
      decide
  have hz : hat (n := 3) (uc22s2112r34q35_zvec 3) (1 : Fin81.R0) ∈
      uc22s2112r34q35_R4 := by
    refine ⟨?_, ?_⟩
    · change uc22s2112r34q35_rel (uc22s2112r34q35_zvec 3)
      simp [uc22s2112r34q35_rel, uc22s2112r34q35_zvec]
      decide
    · show hat (n := 3) (uc22s2112r34q35_zvec 3) (1 : Fin81.R0) ∈ L4P 3
      rw [mem_L4P]
      decide
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) :=
    uc22s2112r34q35_not_dvd_GL2_five hK' hs hs7 hs13
  have hOne := uc22s2112r34q35_eq_one_of_normalizes_embed (K := K) (n := 3)
    (by norm_num) D uc22s2112r34q35_R4 hsep he₁ he₂ hy₀₁ hy₂₃ hy₀₂ rfl rfl rfl hz
    hs (by omega) hh hGL hN hN'
  have hh1 : (h : GL (Fin 4) K) = 1 := by
    have h'one : h' = 1 := hOne
    calc (h : GL (Fin 4) K) = C * h' * C⁻¹ := by
          simp only [h']
          group
      _ = 1 := by rw [h'one]; group
  exact hne (Subtype.ext hh1)

theorem uc22s2112r34q35_alpha_psu5_five {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSU 5 5 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s)
    (hs13 : s ≠ 13) : orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hfield, hfinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have hK' : Nat.card K = 25 := by simpa using hK
  have : CharP K 5 := (uc22s2112r34q35_unitaryFive K hK').charP
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    have hdvd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp hzero
    norm_num at hdvd
  obtain ⟨D⟩ : Nonempty (L4Data K 3) :=
    exists_l4Data_of_dvd (K := K) (n := 3) (by rw [hK']; norm_num)
  let H := StatedSU 5 5 K
  let Z : Subgroup H := (StatedScalars (Fin 5) K).subgroupOf H
  have : Z.Normal := Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 5) K) H
  have hZ : IsPGroup 2 Z := uc22s2112r34q35_isPGroup_Z_five hK'
  let φ : uc22s2112r34q35_RSD →* H := uc22s2112r34q35_phi5 K hK' h2 D
  let Ssub : Subgroup H := φ.range
  have hScard : Nat.card Ssub = 2 ^ 9 := uc22s2112r34q35_card_phi5_range K hK' h2 D
  have hfac : (Nat.card H).factorization 2 = 9 := uc22s2112r34q35_fact_card_SU5_five hK'
  let S : Sylow 2 H := Sylow.ofCard Ssub (by rw [hScard, hfac])
  have hScoe : (S : Subgroup H) = Ssub := Sylow.coe_ofCard _ _
  obtain ⟨h, hpow, hne, hnorm⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hnorm' : h ∈ normalizer (Ssub : Set H) := by simpa [hScoe] using hnorm
  let B : GL (Fin 5) K := uc22s2112r34q35_B K h2
  let h' : GL (Fin 5) K := B⁻¹ * (h : GL (Fin 5) K) * B
  have hh : h' ^ s = 1 := by
    have hpowGL : (h : GL (Fin 5) K) ^ s = 1 := by
      rw [← Subgroup.coe_pow]
      exact congrArg (fun y : H => (y : GL (Fin 5) K)) hpow
    have := conj_pow (i := s) (a := B⁻¹) (b := (h : GL (Fin 5) K))
    simpa [h', hpowGL, mul_assoc] using this
  have hN : ∀ a ∈ uc22s2112r34q35_RSD, ∃ a' ∈ uc22s2112r34q35_RSD,
      h' * uc22s2112r34q35_blockDet K (D.embed a) * h'⁻¹ =
        uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have haS : φ ⟨a, ha⟩ ∈ Ssub := ⟨⟨a, ha⟩, rfl⟩
    have hmem : h * (φ ⟨a, ha⟩) * h⁻¹ ∈ Ssub :=
      ((Subgroup.mem_normalizer_iff.mp hnorm') (φ ⟨a, ha⟩)).mp haS
    have hmem' : ∃ b : uc22s2112r34q35_RSD, φ b = h * (φ ⟨a, ha⟩) * h⁻¹ := by
      simpa [Ssub] using hmem
    obtain ⟨a', hEq⟩ := hmem'
    have hEqGL : B * uc22s2112r34q35_blockDet K (D.embed a') * B⁻¹ =
        (h : GL (Fin 5) K) *
          (B * uc22s2112r34q35_blockDet K (D.embed a) * B⁻¹) *
          (h : GL (Fin 5) K)⁻¹ := by
      have := congrArg (fun y : H => (y : GL (Fin 5) K)) hEq
      simpa [φ, B, uc22s2112r34q35_phi5, uc22s2112r34q35_psi5] using this
    refine ⟨a', a'.2, ?_⟩
    have hconj := congrArg (fun y : GL (Fin 5) K => B⁻¹ * y * B) hEqGL
    have hleft : B⁻¹ * (B * uc22s2112r34q35_blockDet K (D.embed a') * B⁻¹) * B =
        uc22s2112r34q35_blockDet K (D.embed a') := by group
    have hright : B⁻¹ * ((h : GL (Fin 5) K) *
        (B * uc22s2112r34q35_blockDet K (D.embed a) * B⁻¹) *
        (h : GL (Fin 5) K)⁻¹) * B =
        h' * uc22s2112r34q35_blockDet K (D.embed a) * h'⁻¹ := by
      simp only [h']
      group
    rw [hleft, hright] at hconj
    exact hconj.symm
  have hN' : ∀ a ∈ uc22s2112r34q35_RSD, ∃ a' ∈ uc22s2112r34q35_RSD,
      h'⁻¹ * uc22s2112r34q35_blockDet K (D.embed a) * h' =
        uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have haS : φ ⟨a, ha⟩ ∈ Ssub := ⟨⟨a, ha⟩, rfl⟩
    have hmem : h⁻¹ * (φ ⟨a, ha⟩) * h ∈ Ssub :=
      ((Subgroup.mem_normalizer_iff''.mp hnorm') (φ ⟨a, ha⟩)).mp haS
    have hmem' : ∃ b : uc22s2112r34q35_RSD, φ b = h⁻¹ * (φ ⟨a, ha⟩) * h := by
      simpa [Ssub] using hmem
    obtain ⟨a', hEq⟩ := hmem'
    have hEqGL : B * uc22s2112r34q35_blockDet K (D.embed a') * B⁻¹ =
        (h : GL (Fin 5) K)⁻¹ *
          (B * uc22s2112r34q35_blockDet K (D.embed a) * B⁻¹) *
          (h : GL (Fin 5) K) := by
      have := congrArg (fun y : H => (y : GL (Fin 5) K)) hEq
      simpa [φ, B, uc22s2112r34q35_phi5, uc22s2112r34q35_psi5] using this
    refine ⟨a', a'.2, ?_⟩
    have hconj := congrArg (fun y : GL (Fin 5) K => B⁻¹ * y * B) hEqGL
    have hleft : B⁻¹ * (B * uc22s2112r34q35_blockDet K (D.embed a') * B⁻¹) * B =
        uc22s2112r34q35_blockDet K (D.embed a') := by group
    have hright : B⁻¹ * ((h : GL (Fin 5) K)⁻¹ *
        (B * uc22s2112r34q35_blockDet K (D.embed a) * B⁻¹) *
        (h : GL (Fin 5) K)) * B =
        h'⁻¹ * uc22s2112r34q35_blockDet K (D.embed a) * h' := by
      simp only [h']
      group
    rw [hleft, hright] at hconj
    exact hconj.symm
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (n := 3) ((pv (n := 3) (π : Perm (Fin 4)) (![1, 3, 0, 0] : Fin 4 → ZMod 8) -
        (![1, 3, 0, 0] : Fin 4 → ZMod 8)) : Fin 4 → ZMod 8) ∨
      ¬ IsConst (n := 3) ((pv (n := 3) (π : Perm (Fin 4)) (![0, 0, 1, 3] : Fin 4 → ZMod 8) -
        (![0, 0, 1, 3] : Fin 4 → ZMod 8)) : Fin 4 → ZMod 8) := by
    intro π hπ
    rcases r0_eq_words π with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hπ rfl).elim
    all_goals
      simp only [IsConst]
      decide
  have he₁ : hat (n := 3) ![1, 3, 0, 0] (1 : Fin81.R0) ∈ uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel ![1, 3, 0, 0]
    simp [uc22s2112r34q35_rel]
  have he₂ : hat (n := 3) ![0, 0, 1, 3] (1 : Fin81.R0) ∈ uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel ![0, 0, 1, 3]
    simp [uc22s2112r34q35_rel]
  have hy₀₁ : hat (n := 3) ![0, 0, 0, 0] uc22s2112r34q35_r01 ∈
      uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel ![0, 0, 0, 0]
    simp [uc22s2112r34q35_rel]
  have hy₂₃ : hat (n := 3) ![0, 0, 0, 0] uc22s2112r34q35_r23 ∈
      uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel ![0, 0, 0, 0]
    simp [uc22s2112r34q35_rel]
  have hy₀₂ : hat (n := 3) ![0, 0, 0, 0] uc22s2112r34q35_r02 ∈
      uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel ![0, 0, 0, 0]
    simp [uc22s2112r34q35_rel]
  have hz : hat (n := 3) (uc22s2112r34q35_zvec 3) (1 : Fin81.R0) ∈
      uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel (uc22s2112r34q35_zvec 3)
    simp [uc22s2112r34q35_rel, uc22s2112r34q35_zvec]
    decide
  have hc : hat (n := 3) (uc22s2112r34q35_cvec 3) (1 : Fin81.R0) ∈
      uc22s2112r34q35_RSD := by
    change uc22s2112r34q35_rel (uc22s2112r34q35_cvec 3)
    simp [uc22s2112r34q35_rel, uc22s2112r34q35_cvec]
    decide
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) :=
    uc22s2112r34q35_not_dvd_GL2_five hK' hs hs7 hs13
  have hKsub : ¬ s ∣ Nat.card K - 1 :=
    uc22s2112r34q35_not_dvd_card_sub_one_five hK' hs hs7
  have hOne := uc22s2112r34q35_eq_one_of_normalizes_blockDet_embed (K := K) (n := 3)
    (by norm_num) D uc22s2112r34q35_RSD hsep he₁ he₂ hy₀₁ hy₂₃ hy₀₂ rfl rfl rfl hz hc
    hs (by omega) hh hGL hKsub hN hN'
  have hh1 : (h : GL (Fin 5) K) = 1 := by
    have h'one : h' = 1 := hOne
    calc (h : GL (Fin 5) K) = B * h' * B⁻¹ := by
          simp only [h']
          group
      _ = 1 := by rw [h'one]; group
  exact hne (Subtype.ext hh1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
