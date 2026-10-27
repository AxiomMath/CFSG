module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdSLPCore

namespace CFSG
end CFSG
open CFSG

/-!
# A prime-field `SL₂(3)` subgroup in the exceptional `F₉` image

The exceptional two-transvection subgroup over `F₉` is an aligned copy of
`SL₂(5)`.  This module exhibits, inside that concrete image, a 24-element
subgroup containing the distinguished lower transvection and having trivial
3-core.  It is the exceptional-branch input to paper step 6 of Glauberman
Lemma 6.3.
-/

namespace CFSG.Glauberman.Dickson

open Matrix
open QuadraticAlgebra

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private local instance f9_irreducible :
    Fact (∀ r : ZMod 3, r ^ 2 ≠ (-1 : ZMod 3) + 0 * r) := ⟨by decide⟩

local instance : Fintype ExceptionalF9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

private abbrev ExceptionalSL3 :=
  Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private def exceptionalSL3Y : ExceptionalSL3 :=
  ⟨!![1, 0; 1, 1], by decide⟩

private def exceptionalSL3Z : ExceptionalSL3 :=
  ⟨!![0, 2; 1, 0], by decide⟩

private def exceptionalSL3Z5 : ExceptionalSL5 :=
  ⟨!![1, 1; 3, 4], by decide⟩

private def exceptionalSL3MatrixKey (g : ExceptionalSL3) : Nat :=
  (g.1 0 0).val + 3 * (g.1 0 1).val +
    9 * (g.1 1 0).val + 27 * (g.1 1 1).val

/-- Normal words in the lower transvection and the symplectic generator of
`SL₂(3)`.  The first component stores generator bits least-significant first;
the second stores the word length. -/
private def exceptionalSL3WordCode : Nat → Nat × Nat
  | 15 => (1, 1)
  | 16 => (1, 3)
  | 17 => (1, 2)
  | 21 => (7, 3)
  | 22 => (13, 4)
  | 23 => (10, 4)
  | 28 => (0, 0)
  | 31 => (26, 5)
  | 34 => (4, 5)
  | 37 => (0, 1)
  | 41 => (20, 5)
  | 42 => (4, 3)
  | 46 => (0, 2)
  | 48 => (14, 4)
  | 53 => (4, 4)
  | 56 => (3, 2)
  | 59 => (5, 3)
  | 62 => (2, 3)
  | 65 => (12, 4)
  | 67 => (5, 5)
  | 69 => (2, 2)
  | 74 => (6, 3)
  | 75 => (5, 4)
  | 79 => (2, 4)
  | _ => (0, 0)

private def evalExceptionalSL3Code {G : Type*} [Group G]
    (Y Z : G) : Nat → Nat → G
  | _, 0 => 1
  | code, n + 1 =>
      (if code % 2 = 0 then Y else Z) *
        evalExceptionalSL3Code Y Z (code / 2) n

private def exceptionalSL3Fn (g : ExceptionalSL3) : ExceptionalSL5 :=
  let code := exceptionalSL3WordCode (exceptionalSL3MatrixKey g)
  evalExceptionalSL3Code exceptionalY5 exceptionalSL3Z5 code.1 code.2

private theorem exceptionalSL3Fn_one : exceptionalSL3Fn 1 = 1 := by
  decide

set_option maxHeartbeats 2000000 in
private theorem exceptionalSL3Fn_mul : ∀ a b : ExceptionalSL3,
    exceptionalSL3Fn (a * b) = exceptionalSL3Fn a * exceptionalSL3Fn b := by
  decide

private def exceptionalSL3Hom : ExceptionalSL3 →* ExceptionalSL5 where
  toFun := exceptionalSL3Fn
  map_one' := exceptionalSL3Fn_one
  map_mul' := exceptionalSL3Fn_mul

set_option maxHeartbeats 2000000 in
private theorem exceptionalSL3Hom_injective :
    Function.Injective exceptionalSL3Hom := by
  intro a b
  change exceptionalSL3Fn a = exceptionalSL3Fn b → a = b
  revert a b
  decide

private theorem exceptionalSL3Hom_Y :
    exceptionalSL3Hom exceptionalSL3Y = exceptionalY5 := by
  decide

set_option backward.isDefEq.respectTransparency false in
/-- In the exceptional order-nine branch, the aligned two-transvection
closure contains a 24-element subgroup containing the lower transvection and
having trivial 3-core. -/
public theorem exceptionalF9_exists_pCore_trivial_subgroup
    {K : Type*} [Field K] [Algebra (ZMod 3) K] [Finite K]
    (hKcard : Nat.card K = 9) (r : K) (hr : r ^ 2 + 1 = 0) :
    let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    ∃ L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      L ≤ Subgroup.closure ({XK, YK} : Set _) ∧
        YK ∈ L ∧ Nat.card L = 24 ∧ pCore 3 L = ⊥ := by
  dsimp only
  let liftHom : ExceptionalF9 →ₐ[ZMod 3] K := QuadraticAlgebra.lift ⟨r, by
    have hr' : r * r = -(1 : K) := by
      rw [show r * r = r ^ 2 by ring]
      exact eq_neg_of_add_eq_zero_left hr
    simpa [Algebra.smul_def] using hr'⟩
  let : Fintype K := Fintype.ofFinite K
  have hF9card : Fintype.card ExceptionalF9 = 9 := by
    rw [Fintype.card_congr
      (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0)]
    decide
  have hlift_bij : Function.Bijective liftHom := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · exact RingHom.injective liftHom.toRingHom
    · rw [hF9card, ← Nat.card_eq_fintype_card]
      exact hKcard.symm
  let e : ExceptionalF9 ≃ₐ[ZMod 3] K :=
    AlgEquiv.ofBijective liftHom hlift_bij
  let E : ExceptionalSL9 ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    specialLinearMapEquiv e.toRingEquiv
  let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
  let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hEX : E exceptionalX9 = XK := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, specialLinearMapEquiv, exceptionalX9, XK, e, liftHom,
        Matrix.SpecialLinearGroup.map_apply_coe]
  have hEY : E exceptionalY9 = YK := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, specialLinearMapEquiv, exceptionalY9, YK, e, liftHom,
        Matrix.SpecialLinearGroup.map_apply_coe]
  let f : ExceptionalSL3 →* Matrix.SpecialLinearGroup (Fin 2) K :=
    E.toMonoidHom.comp (exceptionalHom.comp exceptionalSL3Hom)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply exceptionalSL3Hom_injective
    apply exceptionalHom_injective
    apply E.injective
    simpa [f] using hab
  let L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := f.range
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨g, rfl⟩
    have hmid : exceptionalHom (exceptionalSL3Hom g) ∈
        Subgroup.closure ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9) := by
      rw [← exceptional_range_eq_closure]
      exact ⟨exceptionalSL3Hom g, rfl⟩
    have hmap :
        (Subgroup.closure ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9)).map
            E.toMonoidHom =
          Subgroup.closure ({XK, YK} : Set _) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor <;> aesop
    rw [← hmap]
    exact ⟨exceptionalHom (exceptionalSL3Hom g), hmid, rfl⟩
  · change YK ∈ f.range
    refine ⟨exceptionalSL3Y, ?_⟩
    change E (exceptionalHom (exceptionalSL3Hom exceptionalSL3Y)) = YK
    rw [exceptionalSL3Hom_Y, exceptionalHom_Y, hEY]
  · let eL : ExceptionalSL3 ≃* L :=
      MulEquiv.ofBijective f.rangeRestrict
        ⟨(MonoidHom.rangeRestrict_injective_iff (f := f)).2 hf_inj,
          MonoidHom.rangeRestrict_surjective f⟩
    calc
      Nat.card L = Nat.card ExceptionalSL3 := Nat.card_congr eL.symm.toEquiv
      _ = Nat.card (ZMod 3) * (Nat.card (ZMod 3) ^ 2 - 1) :=
        GorensteinWalter.sl2_card_formula (ZMod 3)
      _ = 24 := by norm_num
  · let eL : ExceptionalSL3 ≃* L :=
      MulEquiv.ofBijective f.rangeRestrict
        ⟨(MonoidHom.rangeRestrict_injective_iff (f := f)).2 hf_inj,
          MonoidHom.rangeRestrict_surjective f⟩
    have hmap := pCore_map_iso (G := ExceptionalSL3) (G' := L) (p := 3) eL
    rw [Glauberman.qdSL_pCore_eq_bot 3 (by omega)] at hmap
    simpa using hmap.symm

end CFSG.Glauberman.Dickson
