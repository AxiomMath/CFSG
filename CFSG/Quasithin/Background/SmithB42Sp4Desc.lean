module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFields

public section

namespace CFSG.Quasithin.B42Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Frob

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]

theorem natRepS_add_two_mul_pow (i d : ℕ) (g : antiSp F) :
    natRepS k (i + 2 * d) g = (natRepS k i g).map fun x => x ^ 2 ^ d := by
  induction d with
  | zero =>
    ext a b
    simp
  | succ d ih =>
    rw [show i + 2 * (d + 1) = (i + 2 * d) + 2 by ring, natRepS_add_two, ih]
    ext a b
    simp only [Matrix.map_apply]
    rw [← pow_mul, ← pow_succ]

variable [CharP k 2]

theorem tensorRepS_map_frob (S : Finset ℕ) (d : ℕ) (g : antiSp F) :
    (tensorRepS k S g).map (iterateFrobenius k 2 d) =
      tensorRepS k S ((minorAut F ^ (2 * d)) g) := by
  ext x' x
  rw [Matrix.map_apply, tensorRepS_apply, tensorRepS_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [natRepS_comp_pow, natRepS_add_two_mul_pow, Matrix.map_apply, iterateFrobenius_def]

theorem shiftSet_eq_of_frob {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {S : Finset ℕ}
    (hS : S ⊆ Finset.range (2 * f)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : antiSp F →* Matrix ι ι k) (d : ℕ)
    (hR : ∀ g, (R g).map (iterateFrobenius k 2 d) = R g)
    (e : (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS k S)).Equiv
      (CFSG.QuasithinUnique.Setup.X7.matRep R)) :
    shiftSet f (2 * d) S = S := by
  obtain ⟨P, Q, h⟩ := CFSG.QuasithinUnique.Setup.X7.MatIso.exists_of_equiv e
  have h1 := h.map (iterateFrobenius k 2 d)
  have hT : CFSG.QuasithinUnique.Setup.X7.matMap (iterateFrobenius k 2 d) (tensorRepS k S) =
      (tensorRepS k S).comp (minorAut F ^ (2 * d)).toMonoidHom :=
    MonoidHom.ext fun g => tensorRepS_map_frob k S d g
  have hR' : CFSG.QuasithinUnique.Setup.X7.matMap (iterateFrobenius k 2 d) R = R :=
    MonoidHom.ext fun g => hR g
  rw [hT, hR'] at h1
  obtain ⟨e1⟩ := h1.equiv
  obtain ⟨e2⟩ := tensorRepS_comp_shift k hF hS (2 * d)
  exact (tensorRepS_absolutely_irreducible_and_distinct k hF hf).2 _ (shiftSet_subset hf _ S) S hS
    ⟨(e2.symm.trans e1).trans e.symm⟩

end Frob

section Descent

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) (antiSp F) W) [Fact ρ.IsIrreducible]

@[expose] noncomputable def matHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type}
    [Field E] (ι : EndRing ρ →+* E) : antiSp F →* Matrix (Fin m) (Fin m) E :=
  CFSG.QuasithinUnique.Setup.X7.matMap ι (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b)

omit [CharP F 2] [Fintype F] in
theorem matHomE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) (g : antiSp F) :
    matHomE ρ b ι g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ι := rfl

omit [CharP F 2] [Fintype F] in
theorem matRep_matHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) :
    CFSG.QuasithinUnique.Setup.X7.matRep (matHomE ρ b ι) = matRepE b ι := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, matRepE_apply, matHomE_apply]

variable {ρ}

theorem exists_label {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (hnt : ∃ g, ρ g ≠ 1)
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) :
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.range (2 * f) ∧
      (letI := ιF.toAlgebra
       Nonempty ((CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)).Equiv
         (matRepE b ιD))) ∧ m = 4 ^ S.card := by
  classical
  let _ : Algebra F E := ιF.toAlgebra
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨⟨S, ⟨hS, ⟨Φ⟩⟩, -⟩, hdim⟩ :=
    split_simple_module_production (k := E) hF hf (matRepE b ιD) hirr
  obtain ⟨hdimS, htriv⟩ := hdim S hS ⟨Φ⟩
  have hSne : S.Nonempty := by
    by_contra hS0
    rw [Finset.not_nonempty_iff_eq_empty] at hS0
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have hid : ∀ x, matRepE b ιD g x = x := htriv.mp hS0 g
    have hmat : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      have := hid x
      rw [matRepE_apply] at this
      simpa [Matrix.toLin'_apply] using this
    have hmat' : CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g = 1 := by
      have : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD =
          (1 : Matrix (Fin _) (Fin _) (EndRing ρ)).map ιD := by
        rw [hmat, Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
      exact Matrix.map_injective ιD.injective this
    have hrep : repD ρ g = 1 := by
      apply (LinearMap.toMatrix b b).injective
      rw [show LinearMap.toMatrix b b (repD ρ g) =
        CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g from rfl, hmat', LinearMap.toMatrix_one]
    apply LinearMap.ext
    intro w
    have h1 := congrArg (fun φ : Module.End (EndRing ρ) W => φ w) hrep
    have h2 : repD ρ g w = w := by simpa using h1
    exact h2
  refine ⟨S, hSne, hS, ⟨Φ⟩, ?_⟩
  rw [← hdimS, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem sp4_descent {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιF : F →+* E)
        (ιD : EndRing ρ →+* E) (S : Finset ℕ), S.Nonempty ∧ S ⊆ Finset.range (2 * f) ∧
        (letI := ιF.toAlgebra
         Nonempty ((CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)).Equiv
           (matRepE b ιD))) ∧
        shiftSet f (2 * d) S = S ∧ Module.finrank (EndRing ρ) W = 4 ^ S.card := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) (EndRing ρ) = d := ⟨_, rfl⟩
  have hDcard : Nat.card (EndRing ρ) = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
    rw [hd, Nat.card_zmod] at this
    exact this
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      have h1 : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
      have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
      omega
    · exact h
  refine ⟨d, hd1, hDcard, fun b => ?_⟩
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hFcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨e, E, hEF, hEfin, hEchar, ιF, ιD, -, -, -, -, -, -, -, hfrobD, -⟩ :=
    finite_fields_common_extension 2 hf hd1 hFcard hDcard
  let _ : Algebra F E := ιF.toAlgebra
  obtain ⟨S, hSne, hS, ⟨Φ⟩, hdimW⟩ := exists_label hF hf hnt b ιF ιD
  have hshift : shiftSet f (2 * d) S = S := by
    refine shiftSet_eq_of_frob E hF hf hS (matHomE ρ b ιD) d (fun g => ?_)
      (Φ.trans (Representation.Equiv.mk (LinearEquiv.refl E _) (fun g => ?_)))
    · ext i j
      rw [Matrix.map_apply, matHomE_apply, Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    · rw [matRep_matHomE]
      rfl
  exact ⟨E, hEF, hEfin, hEchar, ιF, ιD, S, hSne, hS, ⟨Φ⟩, hshift, hdimW⟩

theorem natCard_fix_pow {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    [Finite E] (ιF : F →+* E) (ιD : EndRing ρ →+* E) (S : Finset ℕ)
    (Φ : (letI := ιF.toAlgebra
      (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)).Equiv (matRepE b ιD)))
    (z : antiSp F) :
    Nat.card {w : W // ρ z w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : (S → Fin 4) → E //
        (letI := ιF.toAlgebra; (tensorRepS (F := F) E S z).mulVec y) = y} := by
  let _ := ιF.toAlgebra
  have hcoord : ∀ (g : antiSp F) (w : W),
      (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).mulVec (b.equivFun w) =
        b.equivFun (ρ g w) := fun g w =>
    LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h1 : {w : W // ρ z w = w} ≃
      {x : Fin m → EndRing ρ //
        ∀ _ : Unit, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).mulVec x = 0} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
      change ρ z w = w ↔
        ∀ _ : Unit, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).mulVec
          (b.equivFun w) = 0
      constructor
      · intro h _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, h, sub_self]
      · intro h
        have := h ()
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, sub_eq_zero] at this
        exact b.equivFun.injective this)
  have h2 := natCard_common_ker_map ιD
    (fun _ : Unit => CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1)
  have h3 : {x : Fin m → E // ∀ _ : Unit,
      ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x = 0} ≃
      {y : (S → Fin 4) → E // (tensorRepS (F := F) E S z).mulVec y = y} :=
    Equiv.subtypeEquiv Φ.symm.toLinearEquiv.toEquiv (fun x => by
      have hsub : ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x =
          matRepE b ιD z x - x := by
        rw [matRepE_apply, Matrix.map_sub _ (fun a b => map_sub ιD a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec]
      have hint : Φ.symm (matRepE b ιD z x) =
          (tensorRepS (F := F) E S z).mulVec (Φ.symm x) :=
        equiv_apply Φ.symm z x
      change (∀ _ : Unit, _ = 0) ↔ (tensorRepS (F := F) E S z).mulVec (Φ.symm x) = Φ.symm x
      rw [← hint, hsub]
      constructor
      · intro h
        rw [sub_eq_zero.mp (h ())]
      · intro h _
        rw [sub_eq_zero]
        exact Φ.symm.toLinearEquiv.injective h)
  rw [Nat.card_congr h1]
  rw [Nat.card_congr h3] at h2
  exact h2.symm

omit [CharP F 2] [Fintype F] [Fact ρ.IsIrreducible] in
theorem natCard_eq_two_pow_finrank (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_range_eq {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (S : Finset ℕ)
    (Φ : (letI := ιF.toAlgebra
      (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)).Equiv (matRepE b ιD)))
    (hdim : Module.finrank (EndRing ρ) W = 4 ^ S.card) (z : antiSp F) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) =
      d * (letI := ιF.toAlgebra; (tensorRepS (F := F) E S z - 1).rank) := by
  classical
  let _ := ιF.toAlgebra
  let _ := ιD.toAlgebra
  have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  set e := Module.finrank (EndRing ρ) E with he
  have he0 : 0 < e := Module.finrank_pos
  set r := (tensorRepS (F := F) E S z - 1).rank with hr
  have hfixT : Nat.card {y : (S → Fin 4) → E // (tensorRepS (F := F) E S z).mulVec y = y} =
      Nat.card E ^ (4 ^ S.card - r) := by
    have hc := fixedCodim_matRep (tensorRepS (F := F) E S) z
    rw [finrank_tensorRepS] at hc
    have hle : Module.finrank E (repFixedSpace
        (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)) {z}) ≤ 4 ^ S.card := by
      have := Submodule.finrank_le (repFixedSpace
        (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)) {z})
      rwa [finrank_tensorRepS] at this
    have heq : {y : (S → Fin 4) → E // (tensorRepS (F := F) E S z).mulVec y = y} ≃
        ↥(repFixedSpace (CFSG.QuasithinUnique.Setup.X7.matRep (tensorRepS (F := F) E S)) {z}) :=
      Equiv.subtypeEquivRight fun y => by
        rw [mem_repFixedSpace]
        simp [CFSG.QuasithinUnique.Setup.X7.matRep_apply]
    rw [Nat.card_congr heq, Module.natCard_eq_pow_finrank (K := E)]
    congr 1
    omega
  have hrle : r ≤ 4 ^ S.card := by
    have := fixedCodim_matRep (tensorRepS (F := F) E S) z
    rw [finrank_tensorRepS] at this
    omega
  have hcount := natCard_fix_pow b ιF ιD S Φ z
  rw [hfixT, natCard_E_eq ιD, hDcard, ← pow_mul, ← pow_mul, ← he] at hcount
  have hfixW : Nat.card {w : W // ρ z w = w} = 2 ^ (d * (4 ^ S.card - r)) := by
    have h1 : Nat.card {w : W // ρ z w = w} ^ e = (2 ^ (d * (4 ^ S.card - r))) ^ e := by
      rw [hcount, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_left_injective he0.ne' h1
  have hker : Nat.card {w : W // ρ z w = w} = Nat.card (LinearMap.ker (ρ z - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
  have hkerF : Module.finrank (ZMod 2) (LinearMap.ker (ρ z - 1)) = d * (4 ^ S.card - r) := by
    have h1 := natCard_eq_two_pow_finrank (LinearMap.ker (ρ z - 1))
    rw [← hker, hfixW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hWF : Module.finrank (ZMod 2) W = d * 4 ^ S.card := by
    have h1 := natCard_eq_two_pow_finrank W
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ z - 1)
  rw [hkerF, hWF] at hrn
  have h4 : d * (4 ^ S.card - r) + d * r = d * 4 ^ S.card := by
    rw [← mul_add, Nat.sub_add_cancel hrle]
  omega

end Descent

end CFSG.Quasithin.B42Sp4
