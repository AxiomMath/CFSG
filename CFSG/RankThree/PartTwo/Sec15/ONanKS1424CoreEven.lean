module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open Module

section LinAlg

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem pow_eq_zero_of_isNilpotent_of_finrank_le [Module.Finite K V] {f : Module.End K V}
    (hf : IsNilpotent f) {d : ℕ} (hd : Module.finrank K V ≤ d) : f ^ d = 0 := by
  have h : f ^ Module.finrank K V = 0 := by
    have h1 := hf.charpoly_eq_X_pow_finrank
    simpa [h1] using f.aeval_self_charpoly
  calc f ^ d = f ^ (Module.finrank K V) * f ^ (d - Module.finrank K V) := by
        rw [← pow_add]
        congr 1
        omega
    _ = 0 := by rw [h, zero_mul]

theorem restrict_pow_apply {f : Module.End K V} {W : Submodule K V} (hfW : ∀ w ∈ W, f w ∈ W)
    (n : ℕ) (x : W) : (((f.restrict hfW) ^ n) x : V) = (f ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    simp [LinearMap.restrict_apply, ih]

theorem mapQ_pow_apply {f : Module.End K V} {W : Submodule K V} (hle : W ≤ W.comap f) (n : ℕ)
    (v : V) : ((W.mapQ W f hle) ^ n) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((f ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    simp [Submodule.mapQ_apply]

theorem sq_of_nilpotent [Module.Finite K V] {f : Module.End K V} (hf : IsNilpotent f)
    (W : Submodule K V) (hfW : ∀ w ∈ W, f w ∈ W) (h1 : Module.finrank K W ≤ 2)
    (h2 : Module.finrank K (V ⧸ W) ≤ 2) : (∀ w ∈ W, (f ^ 2) w = 0) ∧ ∀ v, (f ^ 2) v ∈ W := by
  obtain ⟨m, hm⟩ := hf
  constructor
  · have hnil : IsNilpotent (f.restrict hfW) := by
      refine ⟨m, ?_⟩
      ext ⟨x, hx⟩
      have := congr($hm x)
      simp only [LinearMap.zero_apply] at this
      simp [restrict_pow_apply, this]
    have h := pow_eq_zero_of_isNilpotent_of_finrank_le hnil h1
    intro w hw
    have := congr($h ⟨w, hw⟩)
    have h3 := restrict_pow_apply hfW 2 ⟨w, hw⟩
    rw [this] at h3
    simpa using h3.symm
  · have hle : W ≤ W.comap f := fun w hw => hfW w hw
    have hnil : IsNilpotent (W.mapQ W f hle) := by
      refine ⟨m, ?_⟩
      ext v
      simp [mapQ_pow_apply, hm]
    have h := pow_eq_zero_of_isNilpotent_of_finrank_le hnil h2
    intro v
    have := congr($h (Submodule.Quotient.mk v))
    rw [mapQ_pow_apply hle 2 v] at this
    simpa [Submodule.Quotient.mk_eq_zero] using this

end LinAlg

section Matrices

variable {K : Type} [Field K]

def fixSpace (S : Subgroup (GL (Fin 3) K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ g ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v = v}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := by
    intro g hg
    simp
  smul_mem' := by
    intro c v hv g hg
    rw [Matrix.mulVec_smul, hv g hg]

theorem mem_fixSpace {S : Subgroup (GL (Fin 3) K)} {v : Fin 3 → K} :
    v ∈ fixSpace S ↔ ∀ g ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v = v := Iff.rfl

theorem fixSpace_ne_bot [Finite K] [CharP K 2] {S : Subgroup (GL (Fin 3) K)} (hS : IsPGroup 2 S) :
    fixSpace S ≠ ⊥ := by
  let _ : MulAction S (Fin 3 → K) :=
    { smul := fun g v => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v
      one_smul := fun v => by
        show ((((1 : S) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).mulVec v = v
        simp
      mul_smul := fun g h v => by
        show (((g * h : S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v =
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            (((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v)
        simp [Matrix.mulVec_mulVec] }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hS.card_modEq_card_fixedPoints (Fin 3 → K)
  by_contra hbot
  have hF : (MulAction.fixedPoints S (Fin 3 → K)) = {0} := by
    ext v
    constructor
    · intro hv
      have : v ∈ fixSpace S := fun g hg => hv ⟨g, hg⟩
      rw [hbot] at this
      simpa using this
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      intro g
      show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec 0 = 0
      simp
  have hcard : Nat.card (MulAction.fixedPoints S (Fin 3 → K)) = 1 := by rw [hF]; simp
  rw [hcard] at h1
  have := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have h3 : Nat.card (Fin 3 → K) = 2 ^ (3 * (m : ℕ)) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin,
      Nat.card_eq_fintype_card, hm, ← pow_mul, mul_comm]
  rw [h3] at h1
  have h4 : 2 ^ (3 * (m : ℕ)) % 2 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_pow_self 2 (by have := m.pos; omega)
  have h5 := h1
  unfold Nat.ModEq at h5
  omega

theorem fixSpace_ne_top {S : Subgroup (GL (Fin 3) K)} (hS : S ≠ ⊥) : fixSpace S ≠ ⊤ := by
  intro htop
  apply hS
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have h : ∀ v : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K).mulVec v = v := fun v =>
    (mem_fixSpace.mp (htop ▸ Submodule.mem_top (x := v))) g hg
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp [Matrix.toLin'_apply, h v]

theorem mulVec_mem_fixSpace {S Hh : Subgroup (GL (Fin 3) K)}
    (hn : Hh ≤ Subgroup.normalizer (S : Set (GL (Fin 3) K))) {h : GL (Fin 3) K} (hh : h ∈ Hh)
    {w : Fin 3 → K} (hw : w ∈ fixSpace S) :
    (h : Matrix (Fin 3) (Fin 3) K).mulVec w ∈ fixSpace S := by
  intro g hg
  have hg' : h⁻¹ * g * h ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (hn (inv_mem hh)) g).mp hg
    simpa using this
  have h1 := hw _ hg'
  have h2 : (g : Matrix (Fin 3) (Fin 3) K).mulVec ((h : Matrix (Fin 3) (Fin 3) K).mulVec w) =
      (h : Matrix (Fin 3) (Fin 3) K).mulVec
        (((h⁻¹ * g * h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w) := by
    simp [Matrix.mulVec_mulVec, mul_assoc]
  rw [h2, h1]

def unipW (W : Submodule K (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | (∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K).mulVec w = w) ∧
    ∀ v, (g : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ W}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · show ((a * b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb1 w hw, ha1 w hw]
    · have h1 := ha2 ((b : Matrix (Fin 3) (Fin 3) K).mulVec v)
      have h2 := hb2 v
      have : ((a * b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v - v =
          ((a : Matrix (Fin 3) (Fin 3) K).mulVec ((b : Matrix (Fin 3) (Fin 3) K).mulVec v) -
            (b : Matrix (Fin 3) (Fin 3) K).mulVec v) +
            ((b : Matrix (Fin 3) (Fin 3) K).mulVec v - v) := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        abel
      show ((a * b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ W
      rw [this]
      exact W.add_mem h1 h2
  one_mem' := ⟨fun w _ => by simp, fun v => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hinv : ∀ v : Fin 3 → K, (a : Matrix (Fin 3) (Fin 3) K).mulVec
        (((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have h : (a : Matrix (Fin 3) (Fin 3) K).mulVec w = w := ha1 w hw
      calc ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w =
          ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            ((a : Matrix (Fin 3) (Fin 3) K).mulVec w) := by rw [h]
        _ = w := by
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.one_mulVec]
    · have h := ha2 (((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v)
      rw [hinv v] at h
      have := W.neg_mem h
      simpa using this

theorem sq_eq_one_of_mem_unipW [CharP K 2] {W : Submodule K (Fin 3 → K)} {g : GL (Fin 3) K}
    (hg : g ∈ unipW W) : g ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := hg
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  have hu := h2 v
  have hfix := h1 _ hu
  rw [Matrix.mulVec_sub] at hfix
  ext i
  have hi := congrFun hfix i
  simp only [Pi.sub_apply] at hi
  have e1 : (((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) i =
      ((g : Matrix (Fin 3) (Fin 3) K).mulVec ((g : Matrix (Fin 3) (Fin 3) K).mulVec v)) i := by
    rw [Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec]
  simp only [Matrix.toLin'_apply, Units.val_one, Matrix.one_mulVec]
  rw [e1]
  linear_combination hi + CharTwo.add_self_eq_zero (((g : Matrix (Fin 3) (Fin 3) K).mulVec v) i) -
    CharTwo.add_self_eq_zero (v i)

theorem sq_mem_unipW [CharP K 2] {W : Submodule K (Fin 3 → K)} {g : GL (Fin 3) K} {k : ℕ}
    (hk : g ^ (2 ^ k) = 1)
    (hgW : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K).mulVec w ∈ W)
    (h1 : finrank K W ≤ 2) (h2 : finrank K ((Fin 3 → K) ⧸ W) ≤ 2) : g ^ 2 ∈ unipW W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hA
  set f : Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv' (A - 1) with hf
  have hnil : IsNilpotent f := by
    refine ⟨2 ^ k, ?_⟩
    rw [hf, ← map_pow]
    have h0 : (A - 1) ^ (2 ^ k) = 0 := by
      have h := sub_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) K) (x := A) (y := 1) 2 k
        (Commute.one_right A)
      rw [h, one_pow, hA, ← Units.val_pow_eq_pow_val, hk, Units.val_one, sub_self]
    rw [h0, map_zero]
  have hfW : ∀ w ∈ W, f w ∈ W := by
    intro w hw
    simp only [hf, Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact W.sub_mem (hgW w hw) hw
  obtain ⟨hW0, hWV⟩ := sq_of_nilpotent hnil W hfW h1 h2
  have hsq : (A - 1) ^ 2 = A ^ 2 - 1 := by
    have h := sub_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) K) (x := A) (y := 1) 2 1
      (Commute.one_right A)
    simpa using h
  have hf2 : ∀ v, (f ^ 2) v = (A ^ 2).mulVec v - v := fun v => by
    rw [hf, ← map_pow, hsq, Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hg2 : ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A ^ 2 := by
    rw [Units.val_pow_eq_pow_val]
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · have := hW0 w hw
    rw [hf2] at this
    rw [hg2]
    exact sub_eq_zero.mp this
  · rw [hg2, ← hf2]
    exact hWV v

theorem exists_unipotent_normal [Finite K] [CharP K 2] {S Hh : Subgroup (GL (Fin 3) K)}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hn : Hh ≤ Subgroup.normalizer (S : Set (GL (Fin 3) K))) :
    ∃ N : Subgroup (GL (Fin 3) K), N ≤ Hh ∧ (∀ g ∈ N, g ^ 2 = 1) ∧
      (∀ h ∈ Hh, ∀ g ∈ N, h * g * h⁻¹ ∈ N) ∧
      ∀ h ∈ Hh, ∀ k : ℕ, h ^ (2 ^ k) = 1 → h ^ 2 ∈ N := by
  set W := fixSpace S with hW
  have hpos : 1 ≤ finrank K W := Submodule.one_le_finrank_iff.mpr (fixSpace_ne_bot hS2)
  have hlt : finrank K W < 3 := by
    have := Submodule.finrank_lt (fixSpace_ne_top hS1)
    simpa using this
  have hquot : finrank K ((Fin 3 → K) ⧸ W) + finrank K W = 3 := by
    have := Submodule.finrank_quotient_add_finrank W
    simpa using this
  have hstab : ∀ h ∈ Hh, ∀ w ∈ W, (h : Matrix (Fin 3) (Fin 3) K).mulVec w ∈ W :=
    fun h hh w hw => mulVec_mem_fixSpace hn hh hw
  refine ⟨unipW W ⊓ Hh, inf_le_right, fun g hg => sq_eq_one_of_mem_unipW hg.1, ?_, ?_⟩
  · intro h hh g hg
    refine ⟨?_, Hh.mul_mem (Hh.mul_mem hh hg.2) (Hh.inv_mem hh)⟩
    obtain ⟨hg1, hg2⟩ := hg.1
    have hhinv : ∀ v : Fin 3 → K, (h : Matrix (Fin 3) (Fin 3) K).mulVec
        (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have hw' := hstab h⁻¹ (Hh.inv_mem hh) w hw
      have e : ((h * g * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w =
          (h : Matrix (Fin 3) (Fin 3) K).mulVec ((g : Matrix (Fin 3) (Fin 3) K).mulVec
            (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w)) := by
        simp [Matrix.mulVec_mulVec, mul_assoc]
      rw [e, hg1 _ hw', hhinv]
    · have e : ((h * g * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v - v =
          (h : Matrix (Fin 3) (Fin 3) K).mulVec
            ((g : Matrix (Fin 3) (Fin 3) K).mulVec
              (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) -
              ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) := by
        rw [Matrix.mulVec_sub, hhinv]
        simp [Matrix.mulVec_mulVec, mul_assoc]
      rw [e]
      exact hstab h hh _ (hg2 _)
  · intro h hh k hk
    exact ⟨sq_mem_unipW hk (hstab h hh) (by omega) (by omega), Hh.pow_mem hh 2⟩

end Matrices

end CFSG.RankThree.PartTwo.Sec15.KS1424
