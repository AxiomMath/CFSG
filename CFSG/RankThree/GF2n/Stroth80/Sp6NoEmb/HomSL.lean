module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.SlotPat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFiltration

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open Representation CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor tensorRep twistMat twistMat_apply optCons
  optCons_none optCons_some tensorRep_option_apply reindexEquiv equiv_apply liftZ liftS projQ sectT
  projZ projS succHead tensorRep_liftZ tensorRep_projQ tensorRep_liftS projQ_sectT projQ_liftZ
  projQ_liftS projZ_liftZ projS_liftS projS_liftZ ker_projQ_le)

section LinHom

variable {k G U X Y : Type} [Field k] [Group G] [AddCommGroup U] [Module k U] [AddCommGroup X]
  [Module k X] [AddCommGroup Y] [Module k Y]

@[expose] def linHomCongrRight (ν : Representation k G U) {ρ : Representation k G X}
    {σ : Representation k G Y} (e : ρ.Equiv σ) : (linHom ν ρ).Equiv (linHom ν σ) :=
  Representation.Equiv.mk (LinearEquiv.congrRight e.toLinearEquiv) fun g => by
    ext f u
    exact equiv_apply e g (f (ν g⁻¹ u))

@[expose] def linHomPiEquiv (ν : Representation k G U) {ι : Type}
    (ρ : ι → Representation k G X) :
    (linHom ν (piRep ρ)).Equiv (piRep fun i => linHom ν (ρ i)) :=
  Representation.Equiv.mk (LinearEquiv.linearMapPi k).symm fun g => by
    ext f i u
    rfl

@[expose] def linHomTrivEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {ν : Representation k G (ι → k)} (hν : ∀ g, ν g = 1) (ρ : Representation k G X) :
    (linHom ν ρ).Equiv (piRep fun _ : ι => ρ) :=
  Representation.Equiv.mk (LinearEquiv.piRing k X ι k) fun g => by
    ext f i
    simp [hν, piRep_apply]

@[expose] def linHomCompEquiv {H : Type} [Group H] (ν : Representation k G U)
    (ρ : Representation k G X) (φ : H →* G) :
    Representation.Equiv ((linHom ν ρ).comp φ) (linHom (ν.comp φ) (ρ.comp φ)) :=
  Representation.Equiv.mk (LinearEquiv.refl k _) fun h => by
    ext f u
    simp [map_inv]

theorem repMultiplicity_linHom_sub_quot [Module.Finite k U] [Module.Finite k X]
    (ν : Representation k G U) (ρ : Representation k G X) (W : Subrepresentation ρ)
    {E : Type} [AddCommGroup E] [Module k E] (σ : Representation k G E) :
    repMultiplicity (linHom ν ρ) σ =
      repMultiplicity (linHom ν W.toRepresentation) σ +
        repMultiplicity (linHom ν W.quotient) σ := by
  let f₁ : (linHom ν W.toRepresentation).IntertwiningMap (linHom ν ρ) :=
    { toFun := fun f => W.toSubmodule.subtype ∘ₗ f
      map_add' := fun f f' => LinearMap.comp_add _ _ _
      map_smul' := fun c f => LinearMap.comp_smul _ _ _
      isIntertwining' := fun g => by
        ext f u
        rfl }
  let f₂ : (linHom ν ρ).IntertwiningMap (linHom ν W.quotient) :=
    { toFun := fun f => W.toSubmodule.mkQ ∘ₗ f
      map_add' := fun f f' => LinearMap.comp_add _ _ _
      map_smul' := fun c f => LinearMap.comp_smul _ _ _
      isIntertwining' := fun g => by
        ext f u
        rfl }
  refine repMultiplicity_eq_add_of_exact f₁ f₂ (fun f f' h => ?_) (fun h => ?_) (fun f => ?_) σ
  · exact LinearMap.ext fun u => Subtype.ext (LinearMap.congr_fun h u)
  · obtain ⟨f, hf⟩ := Module.projective_lifting_property W.toSubmodule.mkQ h
      W.toSubmodule.mkQ_surjective
    exact ⟨f, hf⟩
  · constructor
    · intro hf
      have hmem : ∀ u, f u ∈ W.toSubmodule := fun u =>
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun hf u)
      exact ⟨LinearMap.codRestrict W.toSubmodule f hmem, LinearMap.ext fun u => rfl⟩
    · rintro ⟨f', rfl⟩
      ext u
      exact (Submodule.Quotient.mk_eq_zero _).mpr (f' u).2

end LinHom

section Nat

variable {K : Type} [Field K]

@[expose] noncomputable def natSL : Representation K SL(2, K) (Fin 2 → K) where
  toFun g := Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl

theorem natSL_apply (g : SL(2, K)) (v : Fin 2 → K) :
    natSL g v = Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v :=
  rfl

theorem natSL_single (g : SL(2, K)) (c : Fin 2) :
    natSL g (Pi.single c 1) = ∑ j, (g : Matrix (Fin 2) (Fin 2) K) j c • Pi.single j 1 := by
  funext i
  simp [natSL_apply, Pi.single_apply]

theorem inv_rev_rev [CharP K 2] (g : SL(2, K)) (a b : Fin 2) :
    ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) a.rev b.rev =
      (g : Matrix (Fin 2) (Fin 2) K) b a := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases a <;> fin_cases b <;> simp [CharTwo.neg_eq]

end Nat

section HomOpt

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def homOptEquiv :
    ((Fin 2 → K) →ₗ[K] ((ι → Fin 2) → K)) ≃ₗ[K] ((Option ι → Fin 2) → K) where
  toFun f x := f (Pi.single (x none).rev 1) fun i => x (some i)
  map_add' f f' := rfl
  map_smul' c f := rfl
  invFun v := (LinearEquiv.piRing K ((ι → Fin 2) → K) (Fin 2) K).symm
    fun j y => v (optCons j.rev y)
  left_inv f := by
    apply (LinearEquiv.piRing K ((ι → Fin 2) → K) (Fin 2) K).injective
    rw [LinearEquiv.apply_symm_apply]
    funext j y
    simp only [optCons_none, optCons_some, Fin.rev_rev, LinearEquiv.piRing_apply]
  right_inv v := by
    funext x
    simp only [LinearEquiv.piRing_symm_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Fin.rev_rev]
    congr 1
    funext o
    cases o <;> rfl

theorem homOptEquiv_apply (f : (Fin 2 → K) →ₗ[K] ((ι → Fin 2) → K)) (a : Fin 2) (y : ι → Fin 2) :
    homOptEquiv f (optCons a y) = f (Pi.single a.rev 1) y :=
  rfl

variable [CharP K 2]

theorem homOptEquiv_linHom (e : ι → ℕ) (g : SL(2, K))
    (f : (Fin 2 → K) →ₗ[K] ((ι → Fin 2) → K)) :
    homOptEquiv (linHom natSL (tensorRep K K e) g f) =
      tensorRep K K (fun o : Option ι => o.elim 0 e) g (homOptEquiv f) := by
  funext x
  obtain ⟨a', y', rfl⟩ : ∃ a' y', x = optCons a' y' :=
    ⟨x none, fun i => x (some i), by funext o; cases o <;> rfl⟩
  rw [tensorRep_option_apply, homOptEquiv_apply, linHom_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, natSL_single, map_sum, map_sum, Finset.sum_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, Fin.revPerm_apply, inv_rev_rev,
    twistMat_apply]
  simp only [Option.elim, Algebra.algebraMap_self, RingHom.id_apply, pow_zero, pow_one]
  rfl

@[expose] noncomputable def linHomTensorEquiv (e : ι → ℕ) :
    (linHom natSL (tensorRep K K e)).Equiv (tensorRep K K fun o : Option ι => o.elim 0 e) :=
  Representation.Equiv.mk homOptEquiv fun g => LinearMap.ext fun f => homOptEquiv_linHom e g f

end HomOpt

section Frob

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def linHomFrobEquiv {J : Finset ℕ} (h0 : 0 ∉ J) :
    (linHom natSL (frobTensor K K J)).Equiv (frobTensor K K (insert 0 J)) :=
  (linHomTensorEquiv fun i : J => (i : ℕ)).trans
    (reindexEquiv (Finset.subtypeInsertEquivOption h0).symm _ _ fun o => by cases o <;> rfl)

variable [Fintype K] {n : ℕ}

theorem pos_of_card_eq_two_pow (hK : Fintype.card K = 2 ^ n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have := Fintype.one_lt_card (α := K)
    rw [hK] at this
    simp at this
  · exact h

theorem slPat_linHom_natSL_of_notMem (hK : Fintype.card K = 2 ^ n) {A : Finset ℕ}
    (hA : ∀ i ∈ A, i < n) (h0 : 0 ∉ A) {J'' : Finset ℕ} (hJ'' : ∀ i ∈ J'', i < n) :
    slPat (linHom natSL (frobTensor K K A)) J'' = if J'' = insert 0 A then 1 else 0 := by
  rw [slPat_congr (linHomFrobEquiv h0) J'']
  refine slPat_frobTensor hK (fun i hi => ?_) hJ''
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact pos_of_card_eq_two_pow hK
  · exact hA i hi

theorem slPat_linHom_natSL_empty (hK : Fintype.card K = 2 ^ n) {J'' : Finset ℕ}
    (hJ'' : ∀ i ∈ J'', i < n) :
    slPat (linHom natSL (frobTensor K K ∅)) J'' = if J'' = {0} then 1 else 0 :=
  slPat_linHom_natSL_of_notMem hK (fun i hi => absurd hi (Finset.notMem_empty i))
    (Finset.notMem_empty 0) hJ''

theorem slPat_linHom_natSL_single (hK : Fintype.card K = 2 ^ n) {a : ℕ} (ha0 : 0 < a)
    (ha : a < n) {J'' : Finset ℕ} (hJ'' : ∀ i ∈ J'', i < n) :
    slPat (linHom natSL (frobTensor K K {a})) J'' = if J'' = {0, a} then 1 else 0 :=
  slPat_linHom_natSL_of_notMem hK (fun i hi => (Finset.mem_singleton.mp hi) ▸ ha)
    (by simpa using ha0.ne) hJ''

end Frob

section End

variable {K : Type} [Field K] [CharP K 2]

abbrev eEnd : Option (Option ↥(∅ : Finset ℕ)) → ℕ := fun o => o.elim 0 fun _ => 0

@[expose] noncomputable def frobZeroEquiv :
    (frobTensor K K {0}).Equiv (tensorRep K K fun _ : Option ↥(∅ : Finset ℕ) => 0) :=
  reindexEquiv (Finset.subtypeInsertEquivOption (Finset.notMem_empty 0)) _ _
    fun i => (Finset.mem_singleton.mp i.2).symm

@[expose] noncomputable def linHomFrobZeroEquiv :
    (linHom natSL (frobTensor K K {0})).Equiv (tensorRep K K eEnd) :=
  (linHomCongrRight (natSL (K := K)) (frobZeroEquiv (K := K))).trans
    (linHomTensorEquiv (K := K) fun _ : Option ↥(∅ : Finset ℕ) => 0)

theorem twistMat_eEnd (g : SL(2, K)) :
    twistMat K (eEnd none) g = twistMat K (eEnd (some none)) g :=
  rfl

@[expose] def endSub : Subrepresentation (tensorRep K K eEnd) where
  toSubmodule := LinearMap.ker projQ
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [tensorRep_projQ eEnd twistMat_eEnd, hv, map_zero]

theorem repMultiplicity_eEnd {W : Type} [AddCommGroup W] [Module K W]
    (σ : Representation K SL(2, K) W) :
    repMultiplicity (tensorRep K K eEnd) σ =
      repMultiplicity (endSub (K := K)).toRepresentation σ +
        repMultiplicity (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))) σ := by
  let f₂ : (tensorRep K K eEnd).IntertwiningMap
      (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))) :=
    ⟨projQ, fun g => LinearMap.ext fun v => tensorRep_projQ eEnd twistMat_eEnd g v⟩
  have hf₂ : ∀ v, f₂ v = projQ v := fun v => rfl
  refine repMultiplicity_eq_add_of_exact (subIncl (tensorRep K K eEnd) endSub) f₂
    (endSub (K := K)).toSubmodule.injective_subtype
    (fun u => ⟨sectT u, by rw [hf₂, projQ_sectT]⟩) (fun v => ⟨fun hv => ?_, ?_⟩) σ
  · rw [hf₂] at hv
    exact ⟨⟨v, LinearMap.mem_ker.mpr hv⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact LinearMap.mem_ker.mp w.2

theorem repMultiplicity_endSub {W : Type} [AddCommGroup W] [Module K W]
    (σ : Representation K SL(2, K) W) :
    repMultiplicity (endSub (K := K)).toRepresentation σ =
      repMultiplicity (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))) σ +
        repMultiplicity (tensorRep K K (succHead eEnd)) σ := by
  have hdec : ∀ v ∈ (endSub (K := K)).toSubmodule, ∃ u w, v = liftZ u + liftS w := by
    intro v hv
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨w, rfl⟩, h⟩ := Submodule.mem_sup.mp (ker_projQ_le v hv)
    exact ⟨u, w, h.symm⟩
  have hS : ∀ (g : SL(2, K)) w, tensorRep K K eEnd g (liftS w) =
      liftS (tensorRep K K (succHead eEnd) g w) + liftZ (fun y => ∑ a : Fin 2,
        twistMat K (eEnd none) g 0 a * twistMat K (eEnd none) g 1 a *
          tensorRep K K (fun z => eEnd (some (some z))) g (fun z => w (optCons a z)) y) :=
    fun g w => sub_eq_iff_eq_add'.mp (tensorRep_liftS eEnd twistMat_eEnd g w)
  let f₁ : (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))).IntertwiningMap
      (endSub (K := K)).toRepresentation :=
    ⟨LinearMap.codRestrict endSub.toSubmodule liftZ fun u => projQ_liftZ u, fun g =>
      LinearMap.ext fun u => Subtype.ext (tensorRep_liftZ eEnd twistMat_eEnd g u).symm⟩
  let f₂ : (endSub (K := K)).toRepresentation.IntertwiningMap
      (tensorRep K K (succHead eEnd)) :=
    ⟨projS ∘ₗ endSub.toSubmodule.subtype, fun g => LinearMap.ext fun ⟨v, hv⟩ => by
      obtain ⟨u, w, rfl⟩ := hdec v hv
      show projS (tensorRep K K eEnd g (liftZ u + liftS w)) =
        tensorRep K K (succHead eEnd) g (projS (liftZ u + liftS w))
      rw [map_add, tensorRep_liftZ eEnd twistMat_eEnd, hS, map_add, map_add, map_add,
        projS_liftZ, projS_liftZ, projS_liftS, projS_liftS, projS_liftZ, zero_add, zero_add,
        add_zero]⟩
  have hf₁ : ∀ u, ((f₁ u : (endSub (K := K)).toSubmodule) :
      (Option (Option ↥(∅ : Finset ℕ)) → Fin 2) → K) = liftZ u := fun u => rfl
  refine repMultiplicity_eq_add_of_exact f₁ f₂ (fun u u' h => ?_) (fun w => ?_) (fun v => ?_) σ
  · have h1 := congrArg (fun v : endSub.toSubmodule => projZ (v : (Option (Option
      ↥(∅ : Finset ℕ)) → Fin 2) → K)) h
    simpa only [hf₁, projZ_liftZ] using h1
  · exact ⟨⟨liftS w, projQ_liftS w⟩, projS_liftS w⟩
  · obtain ⟨v, hv⟩ := v
    obtain ⟨u, w, rfl⟩ := hdec v hv
    have h2 : f₂ ⟨liftZ u + liftS w, hv⟩ = w := by
      show projS (liftZ u + liftS w) = w
      rw [map_add, projS_liftZ, projS_liftS, zero_add]
    rw [h2]
    constructor
    · rintro rfl
      refine ⟨u, Subtype.ext ?_⟩
      rw [hf₁]
      show liftZ u = liftZ u + liftS 0
      rw [map_zero, add_zero]
    · rintro ⟨u', hu'⟩
      have h3 := congrArg f₂ hu'
      rw [h2] at h3
      rw [← h3]
      show projS (liftZ u') = 0
      exact projS_liftZ u'

@[expose] noncomputable def endTrivEquiv :
    (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))).Equiv (frobTensor K K ∅) :=
  reindexEquiv (Equiv.refl _) _ _ fun z => absurd z.2 (Finset.notMem_empty _)

@[expose] noncomputable def endNatOneEquiv :
    (tensorRep K K (succHead eEnd)).Equiv (frobTensor K K {1}) :=
  reindexEquiv (Finset.subtypeInsertEquivOption (Finset.notMem_empty 1)).symm _ _ fun o => by
    cases o with
    | none => rfl
    | some z => exact absurd z.2 (Finset.notMem_empty _)

variable [Fintype K] {n : ℕ}

theorem slPat_linHom_natSL_zero (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n) {J'' : Finset ℕ}
    (hJ'' : ∀ i ∈ J'', i < n) :
    slPat (linHom natSL (frobTensor K K {0})) J'' =
      (if J'' = ∅ then 2 else 0) + (if J'' = {1} then 1 else 0) := by
  have h0 : slPat (tensorRep K K fun z : ↥(∅ : Finset ℕ) => eEnd (some (some z))) J'' =
      if J'' = ∅ then 1 else 0 := by
    rw [slPat_congr endTrivEquiv]
    exact slPat_frobTensor hK (fun i hi => absurd hi (Finset.notMem_empty i)) hJ''
  have h1 : slPat (tensorRep K K (succHead eEnd)) J'' = if J'' = {1} then 1 else 0 := by
    rw [slPat_congr endNatOneEquiv]
    exact slPat_frobTensor hK (fun i hi => by rw [Finset.mem_singleton.mp hi]; omega) hJ''
  simp only [slPat] at h0 h1
  rw [slPat_congr linHomFrobZeroEquiv, slPat, repMultiplicity_eEnd, repMultiplicity_endSub, h0,
    h1]
  rcases eq_or_ne J'' ∅ with rfl | h
  · simp
  · simp [h]

end End

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
