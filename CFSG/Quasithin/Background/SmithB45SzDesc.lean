module

public import CFSG.Quasithin.Background.SmithB45SzSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal

public section

namespace CFSG.Quasithin

namespace B45Sz

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Blueprint
open Representation Matrix

section Generic

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) G W} [Fact ρ.IsIrreducible]

theorem natCard_fix_pow_gen {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type}
    [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD)) (z : G) :
    Nat.card {w : W // ρ z w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : κ → E // (R z).mulVec y = y} := by
  have hcoord : ∀ (g : G) (w : W),
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
      {y : κ → E // (R z).mulVec y = y} :=
    Equiv.subtypeEquiv Φ.symm.toLinearEquiv.toEquiv (fun x => by
      have hsub : ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x =
          matRepE b ιD z x - x := by
        rw [matRepE_apply, Matrix.map_sub _ (fun a b => map_sub ιD a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec]
      have hint : Φ.symm (matRepE b ιD z x) = (R z).mulVec (Φ.symm x) :=
        equiv_apply Φ.symm z x
      change (∀ _ : Unit, _ = 0) ↔ (R z).mulVec (Φ.symm x) = Φ.symm x
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

omit [Fact ρ.IsIrreducible] in
theorem natCard_eq_two_pow_finrank' (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_range_eq_gen {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E]
    (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD))
    (hdim : Module.finrank (EndRing ρ) W = Fintype.card κ) (z : G) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = d * (R z - 1).rank := by
  classical
  let _ := ιD.toAlgebra
  have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  set e := Module.finrank (EndRing ρ) E with he
  have he0 : 0 < e := Module.finrank_pos
  set r := (R z - 1).rank with hr
  have hfixR : Nat.card {y : κ → E // (R z).mulVec y = y} =
      Nat.card E ^ (Fintype.card κ - r) := by
    have hc := fixedCodim_matRep R z
    rw [Module.finrank_fintype_fun_eq_card] at hc
    have heq : {y : κ → E // (R z).mulVec y = y} ≃
        ↥(repFixedSpace (CFSG.QuasithinUnique.Setup.X7.matRep R) {z}) :=
      Equiv.subtypeEquivRight fun y => by
        rw [mem_repFixedSpace]
        simp [CFSG.QuasithinUnique.Setup.X7.matRep_apply]
    have hle : Module.finrank E (repFixedSpace
        (CFSG.QuasithinUnique.Setup.X7.matRep R) {z}) ≤ Fintype.card κ := by
      have := Submodule.finrank_le (repFixedSpace (CFSG.QuasithinUnique.Setup.X7.matRep R) {z})
      rwa [Module.finrank_fintype_fun_eq_card] at this
    rw [Nat.card_congr heq, Module.natCard_eq_pow_finrank (K := E)]
    congr 1
    omega
  have hrle : r ≤ Fintype.card κ := by
    have := fixedCodim_matRep R z
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega
  have hcount := natCard_fix_pow_gen b ιD R Φ z
  rw [hfixR, natCard_E_eq ιD, hDcard, ← pow_mul, ← pow_mul, ← he] at hcount
  have hfixW : Nat.card {w : W // ρ z w = w} = 2 ^ (d * (Fintype.card κ - r)) := by
    have h1 : Nat.card {w : W // ρ z w = w} ^ e = (2 ^ (d * (Fintype.card κ - r))) ^ e := by
      rw [hcount, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_left_injective he0.ne' h1
  have hker : Nat.card {w : W // ρ z w = w} = Nat.card (LinearMap.ker (ρ z - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
  have hkerF : Module.finrank (ZMod 2) (LinearMap.ker (ρ z - 1)) =
      d * (Fintype.card κ - r) := by
    have h1 := natCard_eq_two_pow_finrank' (LinearMap.ker (ρ z - 1))
    rw [← hker, hfixW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hWF : Module.finrank (ZMod 2) W = d * Fintype.card κ := by
    have h1 := natCard_eq_two_pow_finrank' W
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ z - 1)
  rw [hkerF, hWF] at hrn
  have h4 : d * (Fintype.card κ - r) + d * r = d * Fintype.card κ := by
    rw [← mul_add, Nat.sub_add_cancel hrle]
  omega

end Generic

section Label

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W} [Fact ρ.IsIrreducible]

@[expose] noncomputable def szMatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] (ι : EndRing ρ →+* E) :
    ↥(suzukiGroup a K) →* Matrix (Fin m) (Fin m) E :=
  CFSG.QuasithinUnique.Setup.X7.matMap ι (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b)

omit [CharP K 2] [Fintype K] in
theorem szMatHomE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) (g : ↥(suzukiGroup a K)) :
    szMatHomE b ι g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ι := rfl

omit [CharP K 2] [Fintype K] in
theorem matRep_szMatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) :
    CFSG.QuasithinUnique.Setup.X7.matRep (szMatHomE b ι) = matRepE b ι := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, matRepE_apply, szMatHomE_apply]

theorem sz_exists_label (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hnt : ∃ g, ρ g ≠ 1) {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    [CharP E 2] (ιK : K →+* E) (ιD : EndRing ρ →+* E) :
    ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ szOmega a ∧
      (letI := ιK.toAlgebra
       Nonempty ((CFSG.QuasithinUnique.Setup.X7.matRep (szT E hK A)).Equiv (matRepE b ιD))) ∧
      m = 4 ^ A.card := by
  classical
  let _ : Algebra K E := ιK.toAlgebra
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨A, hA, ⟨Φ⟩⟩ := exists_szT_equiv E hK (matRepE b ιD) hirr
  have hdimE : m = 4 ^ A.card := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [finrank_tensorRepS, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    exact h1.symm
  have hAne : A.Nonempty := by
    by_contra hA0
    rw [Finset.not_nonempty_iff_eq_empty] at hA0
    subst hA0
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have hid : ∀ x, matRepE b ιD g x = x := by
      intro x
      have h1 := equiv_apply Φ g (Φ.symm x)
      rw [Representation.Equiv.apply_symm_apply] at h1
      rw [← h1]
      have h2 : CFSG.QuasithinUnique.Setup.X7.matRep (szT E hK (∅ : Finset ℕ)) g (Φ.symm x) =
          Φ.symm x := by
        rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, szT_apply, tensorRepS_empty,
          Matrix.one_mulVec]
      rw [h2, Representation.Equiv.apply_symm_apply]
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
  exact ⟨A, hAne, hA, ⟨Φ⟩, hdimE⟩

omit [CharP K 2] [Fintype K] in
theorem shiftSet_subset_szOmega {A : Finset ℕ} (hA : A ⊆ szOmega a) (d : ℕ) :
    shiftSet (2 * a + 1) (2 * d) A ⊆ szOmega a := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c, -, rfl⟩ := mem_szOmega.mp (hA hi)
  refine mem_szOmega.mpr ⟨(c + d) % (2 * a + 1), Nat.mod_lt _ (by omega), ?_⟩
  rw [← mul_add, Nat.mul_mod_mul_left]

theorem szT_frob_equiv (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Type) [Field k] [Algebra K k] [CharP k 2] {A : Finset ℕ} (hA : A ⊆ szOmega a)
    (d : ℕ) :
    Nonempty ((CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.matMap (iterateFrobenius k 2 d) (szT k hK A))).Equiv
        (CFSG.QuasithinUnique.Setup.X7.matRep (szT k hK (shiftSet (2 * a + 1) (2 * d) A)))) := by
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hT : CFSG.QuasithinUnique.Setup.X7.matMap (iterateFrobenius k 2 d) (szT k hK A) =
      ((tensorRepS (F := K) k A).comp (minorAut K ^ (2 * d)).toMonoidHom).comp (szIncl hK) :=
    MonoidHom.ext fun g => B42Sp4.tensorRepS_map_frob k A d (szIncl hK g)
  obtain ⟨e⟩ := tensorRepS_comp_shift (F := K) k hcard (hA.trans szOmega_subset) (2 * d)
  rw [hT]
  exact ⟨equivComp (szIncl hK) e⟩

theorem szShift_eq_of_frob (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Type) [Field k] [Algebra K k] [CharP k 2] {A : Finset ℕ} (hA : A ⊆ szOmega a)
    {ι : Type} [Fintype ι] [DecidableEq ι] (R : ↥(suzukiGroup a K) →* Matrix ι ι k) (d : ℕ)
    (hR : ∀ g, (R g).map (iterateFrobenius k 2 d) = R g)
    (e : (CFSG.QuasithinUnique.Setup.X7.matRep (szT k hK A)).Equiv
      (CFSG.QuasithinUnique.Setup.X7.matRep R)) :
    shiftSet (2 * a + 1) (2 * d) A = A := by
  obtain ⟨P, Q, h⟩ := CFSG.QuasithinUnique.Setup.X7.MatIso.exists_of_equiv e
  have h1 := h.map (iterateFrobenius k 2 d)
  have hR' : CFSG.QuasithinUnique.Setup.X7.matMap (iterateFrobenius k 2 d) R = R :=
    MonoidHom.ext fun g => hR g
  rw [hR'] at h1
  obtain ⟨e1⟩ := h1.equiv
  obtain ⟨e2⟩ := szT_frob_equiv hK k hA d
  exact szT_eq_of_equiv k hK (shiftSet_subset_szOmega hA d) hA ⟨(e2.symm.trans e1).trans e.symm⟩

theorem sz_descent (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιK : K →+* E)
        (ιD : EndRing ρ →+* E) (A : Finset ℕ), A.Nonempty ∧ A ⊆ szOmega a ∧
        (letI := ιK.toAlgebra
         Nonempty ((CFSG.QuasithinUnique.Setup.X7.matRep (szT E hK A)).Equiv (matRepE b ιD))) ∧
        shiftSet (2 * a + 1) (2 * d) A = A ∧ Module.finrank (EndRing ρ) W = 4 ^ A.card := by
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
  obtain ⟨e, E, hEF, hEfin, hEchar, ιK, ιD, -, -, -, -, -, -, -, hfrobD, -⟩ :=
    finite_fields_common_extension 2 (by omega : 1 ≤ 2 * a + 1) hd1 hK hDcard
  let _ : Algebra K E := ιK.toAlgebra
  obtain ⟨A, hAne, hA, ⟨Φ⟩, hdimW⟩ := sz_exists_label hK hnt b ιK ιD
  have hshift : shiftSet (2 * a + 1) (2 * d) A = A := by
    refine szShift_eq_of_frob hK E hA (szMatHomE b ιD) d (fun g => ?_)
      (Φ.trans (Representation.Equiv.mk (LinearEquiv.refl E _) (fun g => ?_)))
    · ext i j
      rw [Matrix.map_apply, szMatHomE_apply, Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    · rw [matRep_szMatHomE]
      rfl
  exact ⟨E, hEF, hEfin, hEchar, ιK, ιD, A, hAne, hA, ⟨Φ⟩, hshift, hdimW⟩

theorem le_card_mul_of_shiftSet {A : Finset ℕ} (hA : A ⊆ szOmega a) (hAne : A.Nonempty)
    {d : ℕ} (hd1 : 1 ≤ d) (hshift : shiftSet (2 * a + 1) (2 * d) A = A) :
    2 * a + 1 ≤ A.card * d := by
  have h := n_le_card_mul (n := 2 * (2 * a + 1)) (d := 2 * d) (by omega) (by omega)
    (fun i hi => Finset.mem_range.mp (szOmega_subset (hA hi))) hAne hshift
  nlinarith

end Label

end B45Sz

end CFSG.Quasithin
