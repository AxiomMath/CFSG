module

public import CFSG.Quasithin.Background.RonanH164Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def beta6Cols : List ℕ := [0, 60, 60, 60, 3, 5, 48, 40, 0, 0]

@[expose] def beta6Lin : (Fin 10 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun v i := ∑ j : Fin 10, v j * bvec 6 (beta6Cols.getD j 0) i
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp [add_mul, Finset.sum_add_distrib]

theorem beta6Lin_cols : ∀ j < 10, beta6Lin (bvec 10 (2 ^ j)) = bvec 6 (beta6Cols.getD j 0) := by
  decide +kernel

@[expose] def beta6Hom : W10 →* G6.PermMod 6 := AddMonoidHom.toMultiplicative beta6Lin

theorem beta6Hom_toW (k : ℕ) : beta6Hom (toW 10 k) = toW 6 (actM beta6Cols k) :=
  congrArg Multiplicative.ofAdd (addHom_bvec beta6Lin beta6Cols rfl beta6Lin_cols k)

@[expose] def beta6U : ↥(⊤ : Subgroup W10) →* G6.PermMod 6 :=
  beta6Hom.comp (⊤ : Subgroup W10).subtype

theorem beta6Cols_lt : ∀ c ∈ beta6Cols, c < 2 ^ 6 := by decide +kernel

theorem b6_ker : ∀ m < 2 ^ 10, actM beta6Cols m = 0 ↔ m ∈ combos c5 := by
  decide +kernel

theorem b6_range : ∀ y : Fin 6 → ZMod 2,
    (∑ i, y i = 0) ↔ ∃ m < 2 ^ 10, bvec 6 (actM beta6Cols m) = y := by
  decide +kernel

@[expose] def perm6X : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 5, 3]
  invFun := ![0, 2, 1, 5, 3, 4]
  left_inv := fun x => by fin_cases x <;> rfl
  right_inv := fun x => by fin_cases x <;> rfl

@[expose] def perm6T : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := fun x => by fin_cases x <;> rfl
  right_inv := fun x => by fin_cases x <;> rfl

theorem b6_x6 : ∀ m < 2 ^ 10, ∀ i : Fin 6,
    bvec 6 (actM beta6Cols (actC10 x6Arr m)) i = bvec 6 (actM beta6Cols m) (perm6X⁻¹ i) := by
  decide +kernel

theorem b6_tau : ∀ m < 2 ^ 10, ∀ i : Fin 6,
    bvec 6 (actM beta6Cols (actC10 tauArr m)) i = bvec 6 (actM beta6Cols m) (perm6T⁻¹ i) := by
  decide +kernel

theorem b6_ko : ∀ t : Fin 16, ∀ m < 2 ^ 10,
    actM beta6Cols (actC10 (koArr (t : ℕ)) m) = actM beta6Cols m := by
  have hmat : ∀ t : Fin 16, matOf 10 (actM beta6Cols ∘ actC10 (koArr (t : ℕ))) =
      matOf 10 (actM beta6Cols) := by
    decide +kernel
  intro t m hm
  have h1 := actM_matOf ((actM_xor beta6Cols).comp (xorLin_actC10 (koArr (t : ℕ)))) 10 m hm
  rw [hmat t, actM_matOf (actM_xor beta6Cols) 10 m hm] at h1
  exact h1.symm

theorem perm6_closure : Subgroup.closure ({perm6X, perm6T} : Set (Equiv.Perm (Fin 6))) = ⊤ := by
  have hs : perm6X ∈ Subgroup.closure ({perm6X, perm6T} : Set (Equiv.Perm (Fin 6))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have ht : perm6T ∈ Subgroup.closure ({perm6X, perm6T} : Set (Equiv.Perm (Fin 6))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc : finRotate 6 ∈ Subgroup.closure ({perm6X, perm6T} : Set (Equiv.Perm (Fin 6))) := by
    have e : finRotate 6 = perm6T * perm6X * perm6T * perm6X ^ 4 * perm6T * perm6X ^ 5 := by
      decide +kernel
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ht hs) ht) (pow_mem hs 4)) ht) (pow_mem hs 5)
  have hw : Equiv.swap (0 : Fin 6) (finRotate 6 0) ∈
      Subgroup.closure ({perm6X, perm6T} : Set (Equiv.Perm (Fin 6))) := by
    have e : Equiv.swap (0 : Fin 6) (finRotate 6 0) =
        perm6T * perm6X ^ 2 * perm6T * perm6X ^ 2 * perm6T * perm6X ^ 2 := by
      decide +kernel
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ht (pow_mem hs 2)) ht) (pow_mem hs 2)) ht)
      (pow_mem hs 2)
  have key : Subgroup.closure
      ({finRotate 6, Equiv.swap (0 : Fin 6) (finRotate 6 0)} : Set (Equiv.Perm (Fin 6))) = ⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 4))
      (support_finRotate (n := 4)) 0
  rw [eq_top_iff, ← key, Subgroup.closure_le]
  rintro τ (rfl | rfl)
  · exact hc
  · exact hw

theorem beta6_x6 (u : W10) : beta6Hom (R x6Elt u) = G6.permAct 6 perm6X (beta6Hom u) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 u
  rw [R_x6, beta6Hom_toW, beta6Hom_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact b6_x6 m hm i

theorem beta6_tau (u : W10) : beta6Hom (R tauElt u) = G6.permAct 6 perm6T (beta6Hom u) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 u
  rw [R_tau, beta6Hom_toW, beta6Hom_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact b6_tau m hm i

theorem beta6_ko (t : Fin 16) (u : W10) : beta6Hom (R (koElt t) u) = beta6Hom u := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 u
  rw [R_ko, beta6Hom_toW, beta6Hom_toW, b6_ko t m hm]

theorem beta6Hom_toW_eq_one {m : ℕ} (hm : m < 2 ^ 10) :
    beta6Hom (toW 10 m) = 1 ↔ toW 10 m ∈ V5 := by
  rw [toW_mem_V5_iff hm, beta6Hom_toW, ← b6_ker m hm]
  have hlt : actM beta6Cols m < 2 ^ 6 := actM_lt beta6Cols_lt m
  constructor
  · intro h
    exact toW_inj hlt (by norm_num) (by rw [h, toW_zero])
  · intro h
    rw [h, toW_zero]

theorem beta6U_eq_one (u : ↥(⊤ : Subgroup W10)) : beta6U u = 1 ↔ (u : W10) ∈ V5 := by
  obtain ⟨m, hm, hmu⟩ := toW_surj 10 (u : W10)
  change beta6Hom (u : W10) = 1 ↔ (u : W10) ∈ V5
  rw [← hmu]
  exact beta6Hom_toW_eq_one hm

theorem beta6U_range : beta6U.range = G6.coreMod 6 := by
  ext x
  rw [MonoidHom.mem_range, G6.mem_coreMod]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨m, hm, hmu⟩ := toW_surj 10 (u : W10)
    have h1 : beta6U u = toW 6 (actM beta6Cols m) := by
      change beta6Hom (u : W10) = _
      rw [← hmu, beta6Hom_toW]
    rw [h1]
    exact (b6_range (bvec 6 (actM beta6Cols m))).2 ⟨m, hm, rfl⟩
  · intro hx
    obtain ⟨m, hm, hmx⟩ := (b6_range (Multiplicative.toAdd x)).1 hx
    refine ⟨⟨toW 10 m, Subgroup.mem_top _⟩, ?_⟩
    change beta6Hom (toW 10 m) = x
    rw [beta6Hom_toW]
    exact congrArg Multiplicative.ofAdd hmx

theorem beta6_mul_aux {x y : ↥mog22plus} {σ τ : Equiv.Perm (Fin 6)}
    (hσ : ∀ u : W10, beta6Hom (R x u) = G6.permAct 6 σ (beta6Hom u))
    (hτ : ∀ u : W10, beta6Hom (R y u) = G6.permAct 6 τ (beta6Hom u)) (u : W10) :
    beta6Hom (R (x * y) u) = G6.permAct 6 (σ * τ) (beta6Hom u) := by
  rw [map_mul R x y, MulAut.mul_apply, hσ, hτ, map_mul (G6.permAct 6) σ τ, MulAut.mul_apply]

theorem beta6_inv_aux {x : ↥mog22plus} {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ u : W10, beta6Hom (R x u) = G6.permAct 6 σ (beta6Hom u)) (u : W10) :
    beta6Hom (R x⁻¹ u) = G6.permAct 6 σ⁻¹ (beta6Hom u) := by
  have hx : R x * R x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h1 : R x (R x⁻¹ u) = u := by rw [← MulAut.mul_apply, hx, MulAut.one_apply]
  have h2 : beta6Hom u = G6.permAct 6 σ (beta6Hom (R x⁻¹ u)) := by
    rw [← hσ (R x⁻¹ u), h1]
  have h3 : G6.permAct 6 σ⁻¹ (G6.permAct 6 σ (beta6Hom (R x⁻¹ u))) = beta6Hom (R x⁻¹ u) := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  rw [h2, h3]

@[expose] def GoodSub6 : Subgroup ↥mog22plus where
  carrier := {x | ∃ σ : Equiv.Perm (Fin 6), ∀ u : W10, beta6Hom (R x u) = G6.permAct 6 σ (beta6Hom u)}
  mul_mem' := by
    rintro x y ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, beta6_mul_aux hσ hτ⟩
  one_mem' := ⟨1, fun u => by simp⟩
  inv_mem' := by
    rintro x ⟨σ, hσ⟩
    exact ⟨σ⁻¹, beta6_inv_aux hσ⟩

@[expose] def SigSub6 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∃ x : ↥mog22plus, (x : P24) ∈ MY mog22plus Hstd ∧
    ∀ u : W10, beta6Hom (R x u) = G6.permAct 6 σ (beta6Hom u)}
  mul_mem' := by
    rintro σ τ ⟨x, hx, hσ⟩ ⟨y, hy, hτ⟩
    exact ⟨x * y, mul_mem hx hy, beta6_mul_aux hσ hτ⟩
  one_mem' := ⟨1, (MY mog22plus Hstd).one_mem, fun u => by simp⟩
  inv_mem' := by
    rintro σ ⟨x, hx, hσ⟩
    exact ⟨x⁻¹, (MY mog22plus Hstd).inv_mem hx, beta6_inv_aux hσ⟩

theorem koElt_good (t : Fin 16) : koElt t ∈ GoodSub6 :=
  ⟨1, fun u => by rw [beta6_ko t u, map_one, MulAut.one_apply]⟩

theorem x6Elt_good : x6Elt ∈ GoodSub6 := ⟨perm6X, beta6_x6⟩

theorem tauElt_good : tauElt ∈ GoodSub6 := ⟨perm6T, beta6_tau⟩

theorem gens_le_good : Subgroup.closure ((fixO : Set P24) ∪ {x6Perm, tauPerm}) ≤
    GoodSub6.map mog22plus.subtype := by
  rw [Subgroup.closure_le]
  rintro g (hg | rfl | rfl)
  · obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
    exact Subgroup.mem_map_of_mem mog22plus.subtype (koElt_good t)
  · exact Subgroup.mem_map_of_mem mog22plus.subtype x6Elt_good
  · exact Subgroup.mem_map_of_mem mog22plus.subtype tauElt_good

theorem beta6_good_of_mem
    {x : ↥mog22plus} (hx : (x : P24) ∈ MY mog22plus Hstd) : x ∈ GoodSub6 := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (gens_le_good (MH_le_closure hx))
  have hxy : y = x := Subtype.ext hyx
  rw [← hxy]
  exact hy

theorem sig_all : ∀ σ : Equiv.Perm (Fin 6), σ ∈ SigSub6 := by
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≤ SigSub6 := by
    rw [← perm6_closure, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · exact ⟨x6Elt, x6_mem_MY_H, beta6_x6⟩
    · exact ⟨tauElt, tau_mem_MY_H, beta6_tau⟩
  intro σ
  exact htop (Subgroup.mem_top σ)

theorem induces6_std :
    InducesOnSub (rImg R (MY mog22plus Hstd)) ⊤ V5 (G6.PermMod 6) (G6.coreMod 6)
      (G6.permAct 6).range := by
  unfold InducesOnSub
  refine ⟨le_top, fun _ _ _ _ => Subgroup.mem_top _, fun g hg z hz => inv_V5 g hg z hz,
    beta6U, beta6U_range, beta6U_eq_one, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨σ, hσ⟩ := beta6_good_of_mem (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨G6.permAct 6 σ, MonoidHom.mem_range.2 ⟨σ, rfl⟩, ?_⟩
    intro u u' huu'
    change beta6Hom (u' : W10) = G6.permAct 6 σ (beta6Hom (u : W10))
    rw [huu']
    exact hσ (u : W10)
  · intro γ hγ
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.1 hγ
    obtain ⟨x, hx, hσ⟩ := sig_all σ
    refine ⟨R x, Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 hx), ?_⟩
    intro u u' huu'
    change beta6Hom (u' : W10) = G6.permAct 6 σ (beta6Hom (u : W10))
    rw [huu']
    exact hσ (u : W10)

end CFSG.Quasithin.RonanH163
