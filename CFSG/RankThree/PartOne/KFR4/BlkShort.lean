module

public import CFSG.RankThree.PartOne.KFR4.Std
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

namespace CFSG.RankThree.PartOne.KFR4.Blk

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.OrthogonalInvolutions

section Ext

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

@[expose] def extLin (ι : W →ₗ[R] V) (π : V →ₗ[R] W) (g : W →ₗ[R] W) : V →ₗ[R] V :=
  LinearMap.id + ι ∘ₗ (g - LinearMap.id) ∘ₗ π

theorem extLin_apply (ι : W →ₗ[R] V) (π : V →ₗ[R] W) (g : W →ₗ[R] W) (v : V) :
    extLin ι π g v = v + ι (g (π v) - π v) := rfl

variable {ι : W →ₗ[R] V} {π : V →ₗ[R] W}

theorem extLin_comp (hπι : ∀ w, π (ι w) = w) (g h : W →ₗ[R] W) :
    extLin ι π g ∘ₗ extLin ι π h = extLin ι π (g ∘ₗ h) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, extLin_apply, map_add, map_sub, hπι, add_sub_cancel]
  abel

theorem extLin_id : extLin ι π LinearMap.id = LinearMap.id :=
  LinearMap.ext fun v => by simp [extLin_apply]

theorem extLin_symm (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[R] W) :
    extLin ι π g ∘ₗ extLin ι π g.symm = LinearMap.id := by
  rw [extLin_comp hπι]
  convert extLin_id (ι := ι) (π := π)
  exact LinearMap.ext fun w => g.apply_symm_apply w

theorem extLin_symm' (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[R] W) :
    extLin ι π g.symm ∘ₗ extLin ι π g = LinearMap.id := by
  rw [extLin_comp hπι]
  convert extLin_id (ι := ι) (π := π)
  exact LinearMap.ext fun w => g.symm_apply_apply w

@[expose] def extEquiv (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[R] W) : V ≃ₗ[R] V :=
  LinearEquiv.ofLinearMap (extLin ι π g) (extLin ι π g.symm) (extLin_symm hπι g)
    (extLin_symm' hπι g)

@[expose] def extHom (hπι : ∀ w, π (ι w) = w) : (W ≃ₗ[R] W) →* (V ≃ₗ[R] V) where
  toFun := extEquiv hπι
  map_one' := LinearEquiv.ext fun v => by
    show extLin ι π _ v = v
    simp [extLin_apply]
  map_mul' g h := LinearEquiv.ext fun v => by
    show extLin ι π _ v = extLin ι π g (extLin ι π h v)
    simp only [extLin_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_add, map_sub, hπι,
      add_sub_cancel]
    abel

theorem extHom_apply (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[R] W) (v : V) :
    extHom hπι g v = v + ι (g (π v) - π v) := rfl

end Ext

section ExtField

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι : W →ₗ[K] V} {π : V →ₗ[K] W}

theorem extHom_injective (hπι : ∀ w, π (ι w) = w) : Function.Injective (extHom hπι) := by
  intro g h hgh
  refine LinearEquiv.ext fun w => ?_
  have := congrArg (fun e : V ≃ₗ[K] V => π (e (ι w))) hgh
  simpa only [extHom_apply, map_add, map_sub, hπι, add_sub_cancel] using this

theorem commSpace_extHom (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[K] W) :
    commSpace (extHom hπι g) = (commSpace g).map ι := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨g (π v) - π v, sub_mem_commSpace g (π v), ?_⟩
    rw [extHom_apply]
    abel
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hy
    exact ⟨ι w, by rw [extHom_apply, hπι]; abel⟩

theorem finrank_commSpace_extHom (hπι : ∀ w, π (ι w) = w) (g : W ≃ₗ[K] W) :
    finrank K (commSpace (extHom hπι g)) = finrank K (commSpace g) := by
  have hι : Function.Injective ι := fun a b h => by rw [← hπι a, ← hπι b, h]
  rw [commSpace_extHom hπι, ← (Submodule.equivMapOfInjective ι hι (commSpace g)).finrank_eq]

end ExtField

section Short

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

@[expose] def shortIn (i : Fin 3) : ((Fin 1 → K) × (Fin 1 → K)) × E →ₗ[K] Vs K E where
  toFun w := (Pi.single i w.2, (w.1.1 0, w.1.2 0))
  map_add' u w := by
    refine Prod.ext ?_ rfl
    exact Pi.single_add (f := fun _ : Fin 3 => E) i u.2 w.2
  map_smul' c w := by
    refine Prod.ext ?_ rfl
    exact Pi.single_smul' (I := Fin 3) i c w.2

@[expose] def shortOut (i : Fin 3) : Vs K E →ₗ[K] ((Fin 1 → K) × (Fin 1 → K)) × E where
  toFun v := ((fun _ => v.2.1, fun _ => v.2.2), v.1 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite K] [CharP K 2] in
theorem shortOut_shortIn (i : Fin 3) (w : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    shortOut i (shortIn (E := E) i w) = w := by
  obtain ⟨⟨x, y⟩, z⟩ := w
  refine Prod.ext (Prod.ext (funext fun l => ?_) (funext fun l => ?_)) ?_
  · rw [Subsingleton.elim l 0]
    rfl
  · rw [Subsingleton.elim l 0]
    rfl
  · show (Pi.single i z : Fin 3 → E) i = z
    simp

variable (D : EvenNormPlane K E) (i : Fin 3)

@[expose] noncomputable def inclS : hermFourSpace D.σ →ₗ[K] Vs K E :=
  shortIn i ∘ₗ (hermFourCoord D).symm.toLinearMap

@[expose] noncomputable def projS : Vs K E →ₗ[K] hermFourSpace D.σ :=
  (hermFourCoord D).toLinearMap ∘ₗ shortOut i

theorem projS_inclS (X : hermFourSpace D.σ) : projS D i (inclS D i X) = X := by
  simp [projS, inclS, shortOut_shortIn]

theorem inclS_fst (X : hermFourSpace D.σ) :
    (inclS D i X).1 = Pi.single i ((hermFourCoord D).symm X).2 := rfl

theorem projS_apply (v : Vs K E) :
    projS D i v = hermFourCoord D ((fun _ => v.2.1, fun _ => v.2.2), v.1 i) := rfl

theorem hermFourForm_projS (v : Vs K E) :
    hermFourForm D (projS D i v) = v.2.1 * v.2.2 + D.N (v.1 i) := by
  rw [projS_apply, hermFourForm_coord]

theorem Qs_eq_projS (v : Vs K E) :
    Qs D v = hermFourForm D (projS D i v) + ∑ l, if l = i then 0 else D.N (v.1 l) := by
  rw [Qs_apply, hermFourForm_projS]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

theorem inclS_fst_of_ne (X : hermFourSpace D.σ) {j : Fin 3} (hj : j ≠ i) :
    (inclS D i X).1 j = 0 := by
  rw [inclS_fst, Pi.single_eq_of_ne hj]

theorem Qs_inclS (X : hermFourSpace D.σ) : Qs D (inclS D i X) = hermFourForm D X := by
  rw [Qs_eq_projS D i, projS_inclS]
  have : ∀ l, (if l = i then 0 else D.N ((inclS D i X).1 l)) = 0 := fun l => by
    by_cases hl : l = i
    · rw [ite_eq_left hl]
    · rw [ite_eq_right hl, inclS_fst_of_ne D i X hl, map_zero]
  simp [this]

omit [Finite K] [CharP K 2] in
theorem mem_Ufix_singleton {v : Vs K E} : v ∈ Ufix K E {i} ↔ ∀ j, j ≠ i → v.1 j = 0 := by
  show (∀ j, j ∉ ({i} : Finset (Fin 3)) → v.1 j = 0) ↔ _
  simp only [Finset.mem_singleton]

theorem inclS_mem (X : hermFourSpace D.σ) : inclS D i X ∈ Ufix K E {i} :=
  (mem_Ufix_singleton i).2 fun _ hj => inclS_fst_of_ne D i X hj

theorem inclS_projS_fst (v : Vs K E) : (inclS D i (projS D i v)).1 i = v.1 i := by
  simp [inclS_fst, projS_apply]

theorem inclS_projS_snd (v : Vs K E) : (inclS D i (projS D i v)).2 = v.2 := by
  simp [inclS, projS_apply, shortIn]

theorem inclS_projS_of_mem {v : Vs K E} (hv : v ∈ Ufix K E {i}) :
    inclS D i (projS D i v) = v := by
  have hv' := (mem_Ufix_singleton i).1 hv
  refine Prod.ext (funext fun j => ?_) (inclS_projS_snd D i v)
  by_cases hj : j = i
  · subst hj
    exact inclS_projS_fst D j v
  · rw [inclS_fst_of_ne D i _ hj, hv' j hj]

theorem projS_eq_zero {v : Vs K E} (h1 : v.1 i = 0) (h2 : v.2 = 0) : projS D i v = 0 := by
  rw [projS_apply, h1, h2]
  exact map_zero (hermFourCoord D)

@[expose] noncomputable def extS : (hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) →*
    (Vs K E ≃ₗ[K] Vs K E) :=
  extHom (projS_inclS D i)

theorem extS_apply (h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) (v : Vs K E) :
    extS D i h v = v + inclS D i (h (projS D i v) - projS D i v) := rfl

theorem extS_injective : Function.Injective (extS D i) := extHom_injective (projS_inclS D i)

theorem finrank_commSpace_extS (h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) :
    finrank K (commSpace (extS D i h)) = finrank K (commSpace h) :=
  finrank_commSpace_extHom (projS_inclS D i) h

theorem projS_extS (h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) (v : Vs K E) :
    projS D i (extS D i h v) = h (projS D i v) := by
  rw [extS_apply, map_add, projS_inclS, add_sub_cancel]

theorem extS_fst_of_ne (h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) (v : Vs K E) {j : Fin 3}
    (hj : j ≠ i) : (extS D i h v).1 j = v.1 j := by
  rw [extS_apply, Prod.fst_add, Pi.add_apply, inclS_fst_of_ne D i _ hj, add_zero]

theorem extS_mem_supp {h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)) : extS D i h ∈ Supp D {i} := by
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_, fun v => ?_,
    fun v hv1 hv2 => ?_⟩
  · rw [Qs_eq_projS D i (extS D i h v), Qs_eq_projS D i v, projS_extS,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hh]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · rw [ite_eq_left hl, ite_eq_left hl]
    · rw [ite_eq_right hl, ite_eq_right hl, extS_fst_of_ne D i h v hl]
  · rw [extS_apply]
    exact (Submodule.add_mem_iff_left _ (inclS_mem D i _)).symm
  · have h1 : v.1 i = 0 := hv1 i (Finset.mem_singleton_self i)
    rw [extS_apply, projS_eq_zero D i h1 hv2, map_zero, sub_zero, map_zero, add_zero]

theorem exists_extS_of_mem_supp {g : Vs K E ≃ₗ[K] Vs K E} (hg : g ∈ Supp D {i}) :
    ∃ h ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D), extS D i h = g := by
  obtain ⟨hgO, hgU, hgfix⟩ := hg
  have hU : ∀ X, inclS D i (projS D i (g (inclS D i X))) = g (inclS D i X) := fun X =>
    inclS_projS_of_mem D i ((hgU _).1 (inclS_mem D i X))
  have hU' : ∀ X, inclS D i (projS D i (g.symm (inclS D i X))) = g.symm (inclS D i X) := by
    intro X
    apply inclS_projS_of_mem D i
    rw [hgU, LinearEquiv.apply_symm_apply]
    exact inclS_mem D i X
  let h : hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ := LinearEquiv.ofLinearMap
    (projS D i ∘ₗ (g : Vs K E →ₗ[K] Vs K E) ∘ₗ inclS D i)
    (projS D i ∘ₗ (g.symm : Vs K E →ₗ[K] Vs K E) ∘ₗ inclS D i)
    (LinearMap.ext fun X => by simp [hU', projS_inclS])
    (LinearMap.ext fun X => by simp [hU, projS_inclS])
  have hh : ∀ X, h X = projS D i (g (inclS D i X)) := fun X => rfl
  refine ⟨h, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun X => ?_, ?_⟩
  · rw [hh, ← Qs_inclS D i, hU, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO,
      Qs_inclS]
  · refine LinearEquiv.ext fun v => ?_
    have hr : g (v - inclS D i (projS D i v)) = v - inclS D i (projS D i v) :=
      hgfix _ (fun j hj => by
        rw [Finset.mem_singleton] at hj
        subst hj
        rw [Prod.fst_sub, Pi.sub_apply, inclS_projS_fst, sub_self])
        (by rw [Prod.snd_sub, inclS_projS_snd, sub_self])
    have hv : g v = g (inclS D i (projS D i v)) + (v - inclS D i (projS D i v)) := by
      rw [← hr, ← map_add, add_sub_cancel]
    rw [extS_apply, hh, map_sub, hU, hv]
    abel

end Short

section Block

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  (D : EvenNormPlane K E)

theorem omegaGroup_hermFour (hnd : (polarBilin (hermFourForm D)).Nondegenerate) :
    omegaGroup (hermFourForm D) hnd = (hermFourRho D).range := by
  obtain ⟨-, -, -, -, hfin, -, -, -, -, -, -, -, -, -, hidx, -, hcomm, -⟩ :=
    even_minus_four_hermitian_derived_model D
  have : Nontrivial (hermFourSpace D.σ) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [hfin]; norm_num)
  have hle : (hermFourRho D).range ≤ omegaGroup (hermFourForm D) hnd := by
    rw [← hcomm]
    exact CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle (omegaGroup_le (hermFourForm D) hnd)
  rw [relIndex_omegaGroup] at hmul
  have h2 : (hermFourRho D).range.relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)) = 2 := hidx
  rw [h2] at hmul
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (by omega)) hle

theorem supp_inf_Om_eq_range (i : Fin 3) :
    Supp D {i} ⊓ Om D = ((extS D i).comp (hermFourRho D)).range := by
  obtain ⟨-, -, -, -, -, hnd, -, hmem, -⟩ := even_minus_four_hermitian_derived_model D
  have hΩ := omegaGroup_hermFour D hnd
  ext g
  constructor
  · intro hg
    obtain ⟨hgS, hgΩ⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨h, hh, rfl⟩ := exists_extS_of_mem_supp D i hgS
    rw [Om_eq_omegaGroup, mem_omegaGroup] at hgΩ
    have : h ∈ omegaGroup (hermFourForm D) hnd :=
      ⟨hh, by rw [← finrank_commSpace_extS D i]; exact hgΩ.2⟩
    rw [hΩ] at this
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    have hS := extS_mem_supp D i (hmem x)
    have hx : hermFourRho D x ∈ omegaGroup (hermFourForm D) hnd := by
      rw [hΩ]
      exact ⟨x, rfl⟩
    have hΩ' : extS D i (hermFourRho D x) ∈ Om D := by
      rw [Om_eq_omegaGroup, mem_omegaGroup]
      exact ⟨hS.1, by rw [finrank_commSpace_extS]; exact hx.2⟩
    exact Subgroup.mem_inf.mpr ⟨hS, hΩ'⟩

omit [Module.Finite K E] in
theorem extS_comp_rho_injective (i : Fin 3) (h4 : 4 ≤ Nat.card E) :
    Function.Injective ((extS D i).comp (hermFourRho D)) :=
  (extS_injective D i).comp (hermFourRho_injective D h4)

end Block

section Torus

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p) (i : Fin 3)

theorem rot_ne_zero (a : ZMod p) : S.rot a ≠ 0 :=
  left_ne_zero_of_mul_eq_one (S.rot_mul_neg a)

theorem tor_inclS {a : Fin 3 → ZMod p} (ha : a i = 0) (X : hermFourSpace S.D.σ) :
    tor S a (inclS S.D i X) = inclS S.D i X := by
  refine Prod.ext (funext fun j => ?_) rfl
  show S.rot (a j) * (inclS S.D i X).1 j = (inclS S.D i X).1 j
  by_cases hj : j = i
  · subst hj
    rw [ha, S.rot_zero, one_mul]
  · rw [inclS_fst_of_ne S.D i X hj, mul_zero]

theorem projS_tor {a : Fin 3 → ZMod p} (ha : a i = 0) (v : Vs K E) :
    projS S.D i (tor S a v) = projS S.D i v := by
  rw [projS_apply, projS_apply]
  show hermFourCoord S.D ((fun _ => v.2.1, fun _ => v.2.2), S.rot (a i) * v.1 i) = _
  rw [ha, S.rot_zero, one_mul]

theorem tor_commute_of_mem_supp {a : Fin 3 → ZMod p} (ha : a i = 0) {g : Vs K E ≃ₗ[K] Vs K E}
    (hg : g ∈ Supp S.D {i}) : g * tor S a = tor S a * g := by
  obtain ⟨h, -, rfl⟩ := exists_extS_of_mem_supp S.D i hg
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, extS_apply, extS_apply, map_add,
    tor_inclS S i ha, projS_tor S i ha]

variable [Module.Finite K E]

theorem tor_mem_supp_inf_Om_iff (a : Fin 3 → ZMod p) :
    tor S a ∈ Supp S.D {i} ⊓ Om S.D ↔ ∀ j, j ≠ i → a j = 0 := by
  constructor
  · rintro ⟨⟨-, -, hfix⟩, -⟩ j hj
    have h1 := congrArg (fun v : Vs K E => v.1 j) (hfix ((Pi.single j 1 : Fin 3 → E), 0)
      (fun l hl => by
        rw [Finset.mem_singleton] at hl
        subst hl
        exact Pi.single_eq_of_ne (Ne.symm hj) 1) rfl)
    have h2 : S.rot (a j) = 1 := by simpa [tor_apply] using h1
    exact S.rot_injective (h2.trans S.rot_zero.symm)
  · intro ha
    refine ⟨⟨tor_mem_orthogonalGroup S a, fun v => ?_, fun v hv1 hv2 => ?_⟩,
      Tstd_le_Om S ⟨Multiplicative.ofAdd a, rfl⟩⟩
    · rw [mem_Ufix_singleton, mem_Ufix_singleton]
      refine forall_congr' fun j => imp_congr_right fun _ => ?_
      show v.1 j = 0 ↔ S.rot (a j) * v.1 j = 0
      rw [mul_eq_zero, or_iff_right (rot_ne_zero S (a j))]
    · refine Prod.ext (funext fun j => ?_) rfl
      show S.rot (a j) * v.1 j = v.1 j
      by_cases hj : j = i
      · subst hj
        rw [hv1 j (Finset.mem_singleton_self j), mul_zero]
      · rw [ha j hj, S.rot_zero, one_mul]

end Torus

end CFSG.RankThree.PartOne.KFR4.Blk
