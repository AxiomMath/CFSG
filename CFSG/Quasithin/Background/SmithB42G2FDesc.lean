module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.Quasithin.Background.SmithB42G2TenClass

public section

namespace CFSG.Quasithin.B42G2F

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.B42G2Ten
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing repD matRepE matRepE_apply
  matRepE_isIrreducible finite_endRing natCard_common_ker_map natCard_E_eq
  finite_fields_common_extension n_le_card_mul equiv_apply natCard_eq_pow_finrank)

section Support

variable {f : ℕ}

theorem le_card_support_mul (lab : Fin f → G2L) {d : ℕ} (hd : 1 ≤ d)
    (hshift : ∀ j : Fin f, lab ⟨(j.val + d) % f, Nat.mod_lt _ (Fin.pos j)⟩ = lab j)
    (hne : ∃ j, lab j ≠ .one) :
    f ≤ (Finset.univ.filter fun j => lab j ≠ .one).card * d := by
  classical
  obtain ⟨j₀, hj₀⟩ := hne
  have hf : 0 < f := Fin.pos j₀
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  set J : Finset ℕ := S.image Fin.val with hJ
  have hJc : J.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
  have hJn : ∀ i ∈ J, i < f := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact j.2
  have hJne : J.Nonempty := ⟨j₀.val, Finset.mem_image.mpr ⟨j₀, by simpa [hS] using hj₀, rfl⟩⟩
  have hsub : J.image (fun i => (i + d) % f) ⊆ J := by
    intro i hi
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi'
    refine Finset.mem_image.mpr ⟨⟨(j.val + d) % f, Nat.mod_lt _ hf⟩, ?_, rfl⟩
    have hj' : lab j ≠ .one := by simpa [hS] using hj
    simpa [hS, hshift j] using hj'
  have hinj : Set.InjOn (fun i => (i + d) % f) J := by
    intro i hi i' hi' h
    have h1 := hJn i hi
    have h2 := hJn i' hi'
    have h3 : (i + d) % f = (i' + d) % f := h
    have h4 : i % f = i' % f := by
      have := Nat.ModEq.add_right_cancel' d h3
      exact this
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h4
  have hcard : (J.image fun i => (i + d) % f).card = J.card := Finset.card_image_of_injOn hinj
  have heq : J.image (fun i => (i + d) % f) = J :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  have := n_le_card_mul hf hd hJn hJne heq
  rwa [hJc] at this

theorem dvd_of_single (lab : Fin f → G2L) {d : ℕ} (j₀ : Fin f)
    (hshift : ∀ j : Fin f, lab ⟨(j.val + d) % f, Nat.mod_lt _ (Fin.pos j)⟩ = lab j)
    (hj₀ : lab j₀ ≠ .one) (hlab : ∀ j ≠ j₀, lab j = .one) : f ∣ d := by
  have hf : 0 < f := Fin.pos j₀
  have h1 : (⟨(j₀.val + d) % f, Nat.mod_lt _ hf⟩ : Fin f) = j₀ := by
    by_contra hne
    exact hj₀ ((hshift j₀).symm.trans (hlab _ hne))
  have h2 : (j₀.val + d) % f = j₀.val := congrArg Fin.val h1
  have h3 : (j₀.val + d) % f = (j₀.val + 0) % f := by
    rw [h2, add_zero, Nat.mod_eq_of_lt j₀.2]
  have h4 : d % f = 0 % f := Nat.ModEq.add_left_cancel' j₀.val h3
  rw [Nat.zero_mod] at h4
  exact Nat.dvd_of_mod_eq_zero h4

end Support

section Descent

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  (ρ : Representation (ZMod 2) ↥(cayleyGroup K) M) [Fact ρ.IsIrreducible]

@[expose] noncomputable def matHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type}
    [Field E] (ι : EndRing ρ →+* E) : ↥(cayleyGroup K) →* Matrix (Fin m) (Fin m) E :=
  matMap ι (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b)

omit [CharP K 2] [Fintype K] in
theorem matHomE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) (g : ↥(cayleyGroup K)) :
    matHomE ρ b ι g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ι := rfl

omit [CharP K 2] [Fintype K] in
theorem matRep_matHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) : matRep (matHomE ρ b ι) = matRepE b ι := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [matRep_apply, matRepE_apply, matHomE_apply]

variable {ρ}

theorem exists_label {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E] [CharP E 2]
    (ιF : K →+* E) (ιD : EndRing ρ →+* E) :
    ∃ lab : Fin f → G2L,
      (letI := ιF.toAlgebra
       Nonempty ((matRep (tRep K E lab)).Equiv (matRepE b ιD))) ∧
      m = ∏ j, Fintype.card (lab j).idx := by
  classical
  let _ : Algebra K E := ιF.toAlgebra
  have hsimple : CFSG.Quasithin.SmithCurtis.IsSimpleRep (matRepE b ιD) :=
    (isIrreducible_iff _).mp (matRepE_isIrreducible b ιD)
  obtain ⟨lab, β, hβ⟩ := cayley_simple_iso_tRep hK hsimple
  refine ⟨lab, ⟨Representation.Equiv.mk β.symm (fun g => LinearMap.ext fun y => ?_)⟩, ?_⟩
  · change β.symm (matRep (tRep K E lab) g y) = matRepE b ιD g (β.symm y)
    apply β.injective
    rw [hβ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · have h1 := β.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_pi] at h1
    exact h1

omit [Fintype K] in
theorem tRep_eq_one_of_forall (E : Type) [Field E] [Algebra K E] [CharP E 2] {f : ℕ}
    (lab : Fin f → G2L) (hlab : ∀ j, lab j = .one) (g : ↥(cayleyGroup K)) :
    tRep K E lab g = (1 : Matrix (TIdx lab) (TIdx lab) E) := by
  have h1 : ∀ (l : G2L), l = .one → l.rep (F := K) g = 1 := by
    rintro l rfl
    rfl
  change (CFSG.QuasithinUnique.Setup.X7a.kron fun j => ((lab j).rep (F := K) g).map
      (CFSG.QuasithinUnique.Setup.X7a.frK E (j : ℕ))) = (1 : Matrix (TIdx lab) (TIdx lab) E)
  have e : (fun j => ((lab j).rep (F := K) g).map
      (CFSG.QuasithinUnique.Setup.X7a.frK E (j : ℕ))) = fun j => 1 := by
    funext j
    rw [h1 (lab j) (hlab j), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact CFSG.QuasithinUnique.Setup.X7a.kron_one

theorem lab_shift_of_equiv {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E] [CharP E 2]
    (ιF : K →+* E) (ιD : EndRing ρ →+* E) {d : ℕ} (hfrobD : ∀ a, (ιD a) ^ (2 ^ d) = ιD a)
    (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD))) :
    ∀ j : Fin f, lab ⟨(j.val + d) % f, Nat.mod_lt _ (Fin.pos j)⟩ = lab j := by
  let _ : Algebra K E := ιF.toAlgebra
  have hR : ∀ g, (matHomE ρ b ιD g).map (iterateFrobenius E 2 d) = matHomE ρ b ιD g := by
    intro g
    ext i j
    rw [Matrix.map_apply, matHomE_apply, Matrix.map_apply, iterateFrobenius_def]
    exact hfrobD _
  have hβ : ∀ g v, Φ.symm.toLinearEquiv (matRep (matHomE ρ b ιD) g v) =
      matRep (tRep K E lab) g (Φ.symm.toLinearEquiv v) := by
    intro g v
    rw [matRep_matHomE]
    exact equiv_apply Φ.symm g v
  have h := lab_comp_finRotate_pow E hK (matHomE ρ b ιD) d hR Φ.symm.toLinearEquiv hβ
  intro j
  have h1 := congrFun h j
  rw [Function.comp_apply] at h1
  rw [← h1]
  congr 1
  exact Fin.ext (val_finRotate_pow d j).symm

omit [Fintype K] in
theorem exists_ne_one_of_equiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type}
    [Field E] [CharP E 2] (ιF : K →+* E) (ιD : EndRing ρ →+* E) {f : ℕ} (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD)))
    (hnt : ∃ g, ρ g ≠ 1) : ∃ j, lab j ≠ .one := by
  let _ : Algebra K E := ιF.toAlgebra
  by_contra hall
  push Not at hall
  obtain ⟨g, hg⟩ := hnt
  apply hg
  have htriv : ∀ x, matRepE b ιD g x = x := fun x => by
    have h1 : Φ.symm (matRepE b ιD g x) = (tRep K E lab g).mulVec (Φ.symm x) :=
      (equiv_apply Φ.symm g x).trans (matRep_apply _ _ _)
    rw [tRep_eq_one_of_forall E lab hall g, Matrix.one_mulVec] at h1
    apply Φ.symm.toLinearEquiv.injective
    change Φ.symm (matRepE b ιD g x) = Φ.symm x
    exact h1
  have hmat : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have := htriv x
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
      CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g from rfl, hmat',
      LinearMap.toMatrix_one]
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun φ : Module.End (EndRing ρ) M => φ w) hrep
  have h2 : repD ρ g w = w := by simpa using h1
  exact h2

theorem g2_descent {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 1 ≤ f) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) M)) (EndRing ρ) M,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιF : K →+* E)
        (ιD : EndRing ρ →+* E) (lab : Fin f → G2L),
        (letI := ιF.toAlgebra
         Nonempty ((matRep (tRep K E lab)).Equiv (matRepE b ιD))) ∧
        (∀ j : Fin f, lab ⟨(j.val + d) % f, Nat.mod_lt _ (Fin.pos j)⟩ = lab j) ∧
        (∃ j, lab j ≠ .one) ∧
        Module.finrank (EndRing ρ) M = ∏ j, Fintype.card (lab j).idx := by
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
  have hFcard : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, E, hEF, hEfin, hEchar, ιF, ιD, -, -, -, -, -, -, -, hfrobD, -⟩ :=
    finite_fields_common_extension 2 hf hd1 hFcard hDcard
  obtain ⟨lab, ⟨Φ⟩, hdimW⟩ := exists_label hK b ιF ιD
  exact ⟨E, hEF, hEfin, hEchar, ιF, ιD, lab, ⟨Φ⟩,
    lab_shift_of_equiv hK b ιF ιD hfrobD lab Φ,
    exists_ne_one_of_equiv b ιF ιD lab Φ hnt, hdimW⟩

omit [CharP K 2] [Fintype K] [Fact ρ.IsIrreducible] [Finite M] in
@[expose] noncomputable def fixWEquiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M)
    (z : ↥(cayleyGroup K)) :
    {w : M // ρ z w = w} ≃
      {x : Fin m → EndRing ρ //
        ∀ _ : Unit, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).mulVec x = 0} :=
  Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
    have hcoord : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z).mulVec (b.equivFun w) =
        b.equivFun (ρ z w) :=
      LinearMap.toMatrix_mulVec_repr b b (repD ρ z) w
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

omit [Fintype K] [Fact ρ.IsIrreducible] [Finite M] in
@[expose] noncomputable def fixTEquiv {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M)
    {E : Type} [Field E] [CharP E 2] (ιF : K →+* E) (ιD : EndRing ρ →+* E) {f : ℕ}
    (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD)))
    (z : ↥(cayleyGroup K)) :
    {x : Fin m → E // ∀ _ : Unit,
      ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x = 0} ≃
      {y : TIdx lab → E // (letI := ιF.toAlgebra; (tRep K E lab z).mulVec y) = y} :=
  let _ := ιF.toAlgebra
  Equiv.subtypeEquiv Φ.symm.toLinearEquiv.toEquiv (fun x => by
    have hsub : ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x =
        matRepE b ιD z x - x := by
      rw [matRepE_apply, Matrix.map_sub _ (fun a b => map_sub ιD a b),
        Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec]
    have hint : Φ.symm (matRepE b ιD z x) = (tRep K E lab z).mulVec (Φ.symm x) :=
      (equiv_apply Φ.symm z x).trans (matRep_apply _ _ _)
    change (∀ _ : Unit, _ = 0) ↔ (tRep K E lab z).mulVec (Φ.symm x) = Φ.symm x
    rw [← hint, hsub]
    constructor
    · intro h
      rw [sub_eq_zero.mp (h ())]
    · intro h _
      rw [sub_eq_zero]
      exact Φ.symm.toLinearEquiv.injective h)

omit [Fintype K] in
theorem natCard_fix_pow {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E]
    [Finite E] [CharP E 2] (ιF : K →+* E) (ιD : EndRing ρ →+* E) {f : ℕ} (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD)))
    (z : ↥(cayleyGroup K)) :
    Nat.card {w : M // ρ z w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : TIdx lab → E //
        (letI := ιF.toAlgebra; (tRep K E lab z).mulVec y) = y} := by
  have h2 := natCard_common_ker_map ιD
    (fun _ : Unit => CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1)
  rw [Nat.card_congr (fixWEquiv b z)]
  rw [Nat.card_congr (fixTEquiv b ιF ιD lab Φ z)] at h2
  exact h2.symm

omit [CharP K 2] [Fintype K] [Fact ρ.IsIrreducible] in
theorem natCard_eq_two_pow_finrank (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

omit [Fintype K] in
theorem finrank_range_eq {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type} [Field E] [Finite E] [CharP E 2]
    (ιF : K →+* E) (ιD : EndRing ρ →+* E) {f : ℕ} (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD)))
    (hdim : Module.finrank (EndRing ρ) M = ∏ j, Fintype.card (lab j).idx)
    (z : ↥(cayleyGroup K)) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) =
      d * (letI := ιF.toAlgebra; (tRep K E lab z - 1).rank) := by
  classical
  let _ := ιF.toAlgebra
  let _ := ιD.toAlgebra
  have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  set e := Module.finrank (EndRing ρ) E with he
  have he0 : 0 < e := Module.finrank_pos
  set r := (tRep K E lab z - 1).rank with hr
  set N := ∏ j, Fintype.card (lab j).idx with hN
  have hcardT : Module.finrank E (TIdx lab → E) = N := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_pi]
  have hfixT : Nat.card {y : TIdx lab → E // (tRep K E lab z).mulVec y = y} =
      Nat.card E ^ (N - r) := by
    have hc := fixedCodim_matRep (tRep K E lab) z
    rw [hcardT] at hc
    have hle := Submodule.finrank_le (repFixedSpace (matRep (tRep K E lab)) {z})
    rw [hcardT] at hle
    have heq : {y : TIdx lab → E // (tRep K E lab z).mulVec y = y} ≃
        ↥(repFixedSpace (matRep (tRep K E lab)) {z}) :=
      Equiv.subtypeEquivRight fun y => by
        rw [mem_repFixedSpace]
        simp [matRep_apply]
    rw [Nat.card_congr heq, Module.natCard_eq_pow_finrank (K := E)]
    congr 1
    omega
  have hrle : r ≤ N := by
    have := fixedCodim_matRep (tRep K E lab) z
    rw [hcardT] at this
    omega
  have hcount := natCard_fix_pow b ιF ιD lab Φ z
  rw [hfixT, natCard_E_eq ιD, hDcard, ← pow_mul, ← pow_mul, ← he] at hcount
  have hfixW : Nat.card {w : M // ρ z w = w} = 2 ^ (d * (N - r)) := by
    have h1 : Nat.card {w : M // ρ z w = w} ^ e = (2 ^ (d * (N - r))) ^ e := by
      rw [hcount, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_left_injective he0.ne' h1
  have hker : Nat.card {w : M // ρ z w = w} = Nat.card (LinearMap.ker (ρ z - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
  have hkerF : Module.finrank (ZMod 2) (LinearMap.ker (ρ z - 1)) = d * (N - r) := by
    have h1 := natCard_eq_two_pow_finrank (LinearMap.ker (ρ z - 1))
    rw [← hker, hfixW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hWF : Module.finrank (ZMod 2) M = d * N := by
    have h1 := natCard_eq_two_pow_finrank M
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ z - 1)
  rw [hkerF, hWF] at hrn
  have h4 : d * (N - r) + d * r = d * N := by
    rw [← mul_add, Nat.sub_add_cancel hrle]
  omega

end Descent

end CFSG.Quasithin.B42G2F
