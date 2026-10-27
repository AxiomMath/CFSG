module

public import Certificates.Data.J2H2Sylow
public import CFSG.RankThree.PartTwo.J2Residue.C4725Module
public import CFSG.RankThree.PartTwo.J2Residue.H2Transfer

public section

namespace CFSG.RankThree.PartTwo.J2Residue.H2

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.J2Residue.C4725 CFSG.RankThree.PartTwo.J2Residue.H2S

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev V12 : Type := Fin 12 → ZMod 2

theorem matOfCols_mulColsMat (P Q : List ℕ) :
    matOfCols (mulColsMat P Q) = matOfCols P * matOfCols Q := by
  ext r c
  have e := congrFun (bv_mulCols P (Q.getD c 0)) r
  have hc : (mulColsMat P Q).getD c 0 = mulCols P (Q.getD c 0) := by
    simp [mulColsMat, List.getD_eq_getElem?_getD, c.isLt]
  simp only [matOfCols, Matrix.of_apply, Matrix.mul_apply] at e ⊢
  rw [hc, e]
  rfl

theorem matOfCols_idCols : matOfCols idCols = 1 := by
  decide +kernel

theorem matOfCols_matWord_aux (w : List ℕ) (A : List ℕ) :
    matOfCols (w.foldl (fun acc j => mulColsMat acc (colsJ j)) A) =
      matOfCols A * (w.map Mj).prod := by
  induction w generalizing A with
  | nil => simp
  | cons j w ih =>
    rw [List.foldl_cons, ih, matOfCols_mulColsMat, List.map_cons, List.prod_cons, mul_assoc]
    rfl

theorem matOfCols_matWord (w : List ℕ) : matOfCols (matWord w) = (w.map Mj).prod := by
  rw [matWord, matOfCols_matWord_aux, matOfCols_idCols, one_mul]

theorem matOfCols_matWordInv_aux (w : List ℕ) (A : List ℕ) :
    matOfCols (w.foldl (fun acc j => mulColsMat (invColsJ j) acc) A) =
      (w.reverse.map fun j => matOfCols (invColsJ j)).prod * matOfCols A := by
  induction w generalizing A with
  | nil => simp
  | cons j w ih =>
    rw [List.foldl_cons, ih, matOfCols_mulColsMat, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc]

section Rep

variable (ρ : ↥P →* Module.End (ZMod 2) V12)

@[expose] noncomputable def IsMRep : Prop := ∀ (j : ℕ) (v : V12), ρ (letterP j) v = (Mj j).mulVec v

variable {ρ}

theorem rho_wordP (hρ : IsMRep ρ) (w : List ℕ) (v : V12) :
    ρ (wordP w) v = (matOfCols (matWord w)).mulVec v := by
  rw [matOfCols_matWord]
  induction w generalizing v with
  | nil =>
    show ρ 1 v = _
    simp
  | cons j w ih =>
    rw [wordP, List.map_cons, List.prod_cons, ← wordP, map_mul, Module.End.mul_apply, ih,
      List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, hρ]

@[expose] noncomputable def rhoS (ρ : ↥P →* Module.End (ZMod 2) V12) :
    ↥S →* Module.End (ZMod 2) V12 :=
  ρ.comp incl

theorem incl_yS {k : ℕ} (hk : k < 3) : incl (yS k) = wordP (nth [] yWords k) :=
  Subtype.ext (by rw [incl_coe, yS_coe hk, coe_wordP, y_eq])

theorem rhoS_yS (hρ : IsMRep ρ) {k : ℕ} (hk : k < 3) (v : V12) :
    rhoS ρ (yS k) v = (matOfCols (yCols k)).mulVec v := by
  rw [rhoS, MonoidHom.comp_apply, incl_yS hk, rho_wordP hρ]
  rfl

theorem rho_letterP_inv (hρ : IsMRep ρ) (j : ℕ) (v : V12) :
    ρ (letterP j)⁻¹ v = (matOfCols (invColsJ j)).mulVec v := by
  by_cases hj : j = 0
  · subst hj
    have e : (letterP 0)⁻¹ = letterP 0 := Subtype.ext (by
      rw [Subgroup.coe_inv]
      exact gA_inv)
    rw [e, hρ]
    rfl
  · have e : (letterP j)⁻¹ = letterP j * letterP j := Subtype.ext (by
      rw [Subgroup.coe_inv, Subgroup.coe_mul]
      simp only [letterP, letter, hj, if_false]
      exact gB_inv)
    rw [e, map_mul, Module.End.mul_apply, hρ, hρ, Matrix.mulVec_mulVec, invColsJ, if_neg hj,
      matOfCols_mulColsMat]
    simp [Mj, colsJ, hj]

theorem rho_wordP_inv (hρ : IsMRep ρ) (w : List ℕ) (v : V12) :
    ρ (wordP w)⁻¹ v = (matOfCols (matWordInv w)).mulVec v := by
  rw [matWordInv, matOfCols_matWordInv_aux, matOfCols_idCols, mul_one]
  induction w generalizing v with
  | nil =>
    show ρ 1⁻¹ v = _
    simp
  | cons j w ih =>
    rw [wordP, List.map_cons, List.prod_cons, ← wordP, mul_inv_rev, map_mul,
      Module.End.mul_apply, rho_letterP_inv hρ, ih, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, Matrix.mulVec_mulVec]

end Rep

section Cocycles

variable {V : Type*}
  [AddCommGroup V] [Module (ZMod 2) V] (σ : ↥S →* Module.End (ZMod 2) V)

@[expose] noncomputable def defect (f : ↥S → ↥S → V) (a b c : ↥S) : V :=
  σ a (f b c) - f (a * b) c + f a (b * c) - f a b

theorem defect_mul (f : ↥S → ↥S → V) (y p v w : ↥S) :
    defect σ f (y * p) v w = σ y (defect σ f p v w) + defect σ f y (p * v) w -
      defect σ f y p (v * w) + defect σ f y p v := by
  simp only [defect, map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]
  abel

theorem isNormCoc_of_gen {f : ↥S → ↥S → V} (h1 : ∀ t, f 1 t = 0)
    (hgen : ∀ k < 3, ∀ s t, defect σ f (yS k) s t = 0) (h2 : ∀ s, f s 1 = 0) :
    IsNormCoc σ f := by
  have key : ∀ x, x < 128 → ∀ v w, defect σ f (elt x) v w = 0 := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx v w
      by_cases hx0 : x = 0
      · subst hx0
        simp [defect, elt_zero, h1]
      · rw [elt_cons hx0 hx, defect_mul, ih _ (par_lt hx0) ((par_lt hx0).trans hx),
          hgen _ (gen_lt x), hgen _ (gen_lt x), hgen _ (gen_lt x), map_zero]
        abel
  refine ⟨h1, h2, fun g h k => ?_⟩
  obtain ⟨x, hx, rfl⟩ := elt_surjective g
  exact key x hx h k

theorem eq_zero_of_gen {f : ↥S → ↥S → V} (hf : IsNormCoc σ f)
    (hgen : ∀ k < 3, ∀ t, f (yS k) t = 0) (s t : ↥S) : f s t = 0 := by
  have key : ∀ x, x < 128 → ∀ t, f (elt x) t = 0 := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx t
      by_cases hx0 : x = 0
      · subst hx0
        rw [elt_zero]
        exact hf.1 t
      · have e := hf.2.2 (yS (gen x)) (elt (par x)) t
        rw [ih _ (par_lt hx0) ((par_lt hx0).trans hx), map_zero, hgen _ (gen_lt x),
          hgen _ (gen_lt x), zero_sub, add_zero, sub_zero, neg_eq_zero, ← elt_cons hx0 hx] at e
        exact e
  obtain ⟨x, hx, rfl⟩ := elt_surjective s
  exact key x hx t

theorem eq_of_gen {f f' : ↥S → ↥S → V} (hf : IsNormCoc σ f) (hf' : IsNormCoc σ f')
    (hgen : ∀ k < 3, ∀ t, f (yS k) t = f' (yS k) t) : f = f' := by
  have hd : IsNormCoc σ (f - f') := by
    have := hf.add (hf'.smul (-1 : ZMod 2))
    convert this using 1
    funext s t
    simp [sub_eq_add_neg, neg_smul, neg_eq_self_zmod2]
  funext s t
  have := eq_zero_of_gen σ hd (fun k hk t => by simp [hgen k hk t]) s t
  rwa [Pi.sub_apply, Pi.sub_apply, sub_eq_zero] at this

@[expose] noncomputable def treeB (f : ↥S → ↥S → V) : ℕ → V
  | 0 => 0
  | x + 1 => f (yS (gen (x + 1))) (elt (par (x + 1))) +
      σ (yS (gen (x + 1))) (treeB f (par (x + 1)))
decreasing_by exact par_lt (Nat.succ_ne_zero x)

theorem treeB_succ (f : ↥S → ↥S → V) {x : ℕ} (hx0 : x ≠ 0) :
    treeB σ f x = f (yS (gen x)) (elt (par x)) + σ (yS (gen x)) (treeB σ f (par x)) := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx0
  rw [treeB]

theorem exists_treeNormal {f : ↥S → ↥S → V} (hf : IsNormCoc σ f) :
    ∃ β : ↥S → V, β 1 = 0 ∧ ∀ x, x ≠ 0 → x < 128 →
      (f + cob σ β) (yS (gen x)) (elt (par x)) = 0 := by
  refine ⟨fun s => treeB σ f (idx s), ?_, fun x hx0 hx => ?_⟩
  · show treeB σ f (idx 1) = 0
    rw [← elt_zero, idx_elt (by norm_num), treeB]
  · have hp : par x < 128 := (par_lt hx0).trans hx
    have hk := gen_lt x
    have hy : idx (yS (gen x)) = gen x + 1 := by
      rw [← elt_succ hk, idx_elt (by omega)]
    have hyz : treeB σ f (gen x + 1) = 0 := by
      rw [treeB_succ σ f (Nat.succ_ne_zero _), (gen_par_succ hk).1, (gen_par_succ hk).2,
        elt_zero, hf.2.1, treeB, map_zero, add_zero]
    simp only [Pi.add_apply, cob]
    rw [← elt_cons hx0 hx, idx_elt hx, idx_elt hp, hy, hyz, treeB_succ σ f hx0]
    abel

end Cocycles

end CFSG.RankThree.PartTwo.J2Residue.H2
