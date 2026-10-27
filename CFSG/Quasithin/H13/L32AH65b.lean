module

public import CFSG.Quasithin.H13.L32AH65a
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

theorem zsm_zero_left {M : Type} [Zero M] (x : M) : zsm 0 x = 0 := by simp [zsm]

theorem zsm_one_left {M : Type} [Zero M] (x : M) : zsm 1 x = x := by simp [zsm]

theorem zsm_one_right (c : ZMod 2) : zsm c (1 : ZMod 2) = c := by
  rcases zmod2_cases c with rfl | rfl <;> simp [zsm]

theorem zsm_apply {α β : Type} [Zero β] (c : ZMod 2) (f : α → β) (a : α) :
    zsm c f a = zsm c (f a) := by
  unfold zsm
  split_ifs <;> rfl

theorem eq_of_add_eq_zero_two {M : Type} [AddCommGroup M] (h2 : ∀ m : M, m + m = 0) {x y : M}
    (h : x + y = 0) : x = y := by
  rw [← add_zero x, ← h2 y, ← add_assoc, h, zero_add]

theorem five_le_card {M : Type} [AddGroup M] [Finite M] (S : AddSubgroup M) {a b c d e : M}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ Nat.card ↥S := by
  classical
  have hsub : (({a, b, c, d, e} : Finset M) : Set M) ⊆ S := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d, e} : Finset M).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair_eq_two_iff.mpr hde]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

@[expose] def actP (g : Γ) (c : Γ ⧸ borel → ZMod 2) : Γ ⧸ borel → ZMod 2 := fun q => c (g⁻¹ • q)

section Flag

variable {M : Type} [AddCommGroup M] (ρ : Γ →* AddMonoid.End M) (m : M)
  (hm : ∀ t ∈ borel, ρ t m = m)

@[expose] def orbPt : Γ ⧸ borel → M :=
  Quotient.lift (fun g : Γ => ρ g m) fun g g' hgg => by
    have h : g⁻¹ * g' ∈ borel := QuotientGroup.leftRel_apply.mp hgg
    show ρ g m = ρ g' m
    rw [show g' = g * (g⁻¹ * g') by group, rho_mul, hm _ h]

theorem orbPt_mk (g : Γ) : orbPt ρ m hm (g : Γ ⧸ borel) = ρ g m := rfl

theorem orbPt_smul (g : Γ) (q : Γ ⧸ borel) : orbPt ρ m hm (g • q) = ρ g (orbPt ρ m hm q) := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    show orbPt ρ m hm ((g * h : Γ) : Γ ⧸ borel) = ρ g (orbPt ρ m hm (h : Γ ⧸ borel))
    rw [orbPt_mk, orbPt_mk, rho_mul]

variable (h2 : ∀ x : M, x + x = 0)

@[expose] noncomputable def flagMap : (Γ ⧸ borel → ZMod 2) →+ M where
  toFun c := ∑ q, zsm (c q) (orbPt ρ m hm q)
  map_zero' := Finset.sum_eq_zero fun q _ => zsm_zero_left _
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => zsm_add h2 _ _ _

theorem flagMap_apply (c : Γ ⧸ borel → ZMod 2) :
    flagMap ρ m hm h2 c = ∑ q, zsm (c q) (orbPt ρ m hm q) := by
  simp only [flagMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem flagMap_single (q : Γ ⧸ borel) :
    flagMap ρ m hm h2 (Pi.single q 1) = orbPt ρ m hm q := by
  rw [flagMap_apply, Finset.sum_eq_single q (fun q' _ hq' => by
      rw [Pi.single_eq_of_ne hq']
      exact zsm_zero_left _) (fun h => absurd (Finset.mem_univ q) h),
    Pi.single_eq_same]
  exact zsm_one_left _

theorem flagMap_act (g : Γ) (c : Γ ⧸ borel → ZMod 2) :
    flagMap ρ m hm h2 (actP g c) = ρ g (flagMap ρ m hm h2 c) := by
  rw [flagMap_apply, flagMap_apply, map_sum]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_).symm
  rw [MulAction.toPerm_apply, zsm_end, ← orbPt_smul]
  show zsm (c q) _ = zsm (c (g⁻¹ • g • q)) _
  rw [inv_smul_smul]

end Flag

@[expose] noncomputable def lineVec (y : Γ) : Γ ⧸ borel → ZMod 2 :=
  Pi.single (y : Γ ⧸ borel) 1 + Pi.single ((y * llA : Γ) : Γ ⧸ borel) 1 +
    Pi.single ((y * (llA * llA) : Γ) : Γ ⧸ borel) 1

theorem flagMap_lineVec {M : Type} [AddCommGroup M] (ρ : Γ →* AddMonoid.End M) (m : M)
    (hm : ∀ t ∈ borel, ρ t m = m) (h2 : ∀ x : M, x + x = 0)
    (hrel : m + ρ llA m + ρ (llA * llA) m = 0) (y : Γ) : flagMap ρ m hm h2 (lineVec y) = 0 := by
  rw [lineVec, map_add, map_add, flagMap_single, flagMap_single, flagMap_single, orbPt_mk,
    orbPt_mk, orbPt_mk, rho_mul, rho_mul, ← map_add, ← map_add, hrel, map_zero]

theorem ind_Ll : ∀ u : Γ, ((if u⁻¹ ∈ borel then 1 else 0 : ZMod 2) +
    (if u⁻¹ * llA ∈ borel then 1 else 0) + (if u⁻¹ * (llA * llA) ∈ borel then 1 else 0)) =
      if u ∈ Ll then 1 else 0 := by
  decide +kernel

theorem single_mk (z h : Γ) : (Pi.single (z : Γ ⧸ borel) (1 : ZMod 2) : Γ ⧸ borel → ZMod 2)
    (h : Γ ⧸ borel) = if h⁻¹ * z ∈ borel then 1 else 0 := by
  rw [Pi.single_apply]
  exact if_congr QuotientGroup.eq rfl rfl

theorem lineVec_mk (y h : Γ) : lineVec y (h : Γ ⧸ borel) = if y⁻¹ * h ∈ Ll then 1 else 0 := by
  rw [lineVec, Pi.add_apply, Pi.add_apply, single_mk, single_mk, single_mk, ← ind_Ll (y⁻¹ * h)]
  have e1 : h⁻¹ * y = (y⁻¹ * h)⁻¹ := by group
  have e2 : h⁻¹ * (y * llA) = (y⁻¹ * h)⁻¹ * llA := by group
  have e3 : h⁻¹ * (y * (llA * llA)) = (y⁻¹ * h)⁻¹ * (llA * llA) := by group
  rw [e1, e2, e3]

theorem lineRep_mem_iff : ∀ j k : Fin 7, (lineRep k)⁻¹ * lineRep j ∈ Ll ↔ k = j := by
  decide +kernel

theorem fun_add_self (c : Γ ⧸ borel → ZMod 2) : c + c = 0 := funext fun q => by
  show c q + c q = 0
  rcases zmod2_cases (c q) with h | h <;> rw [h] <;> decide

@[expose] noncomputable def lineMap : (Fin 7 → ZMod 2) →+ (Γ ⧸ borel → ZMod 2) where
  toFun a := ∑ k, zsm (a k) (lineVec (lineRep k))
  map_zero' := Finset.sum_eq_zero fun k _ => zsm_zero_left _
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => zsm_add fun_add_self _ _ _

theorem lineMap_rep (a : Fin 7 → ZMod 2) (j : Fin 7) :
    lineMap a (lineRep j : Γ ⧸ borel) = a j := by
  show (∑ k, zsm (a k) (lineVec (lineRep k))) (lineRep j : Γ ⧸ borel) = a j
  rw [Finset.sum_apply, Finset.sum_eq_single j (fun k _ hk => ?_)
    (fun h => absurd (Finset.mem_univ j) h)]
  · rw [zsm_apply, lineVec_mk, ite_eq_left ((lineRep_mem_iff j j).mpr rfl)]
    exact zsm_one_right _
  · rw [zsm_apply, lineVec_mk, ite_eq_right fun h => hk ((lineRep_mem_iff j k).mp h)]
    exact zsm_zero _

theorem lineMap_injective : Function.Injective lineMap :=
  (injective_iff_map_eq_zero lineMap).mpr fun a ha => funext fun j => by
    rw [← lineMap_rep a j, ha]
    rfl

theorem card_range_lineMap : Nat.card ↥lineMap.range = 2 ^ 7 := by
  have e1 : Nat.card ↥lineMap.range = Nat.card (Set.range lineMap) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => AddMonoidHom.mem_range (f := lineMap))
  have e2 := Nat.card_congr (Equiv.ofInjective lineMap lineMap_injective)
  rw [e1, ← e2, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem flagMap_lineMap {M : Type} [AddCommGroup M] (ρ : Γ →* AddMonoid.End M) (m : M)
    (hm : ∀ t ∈ borel, ρ t m = m) (h2 : ∀ x : M, x + x = 0)
    (hrel : m + ρ llA m + ρ (llA * llA) m = 0) (a : Fin 7 → ZMod 2) :
    flagMap ρ m hm h2 (lineMap a) = 0 := by
  show flagMap ρ m hm h2 (∑ k, zsm (a k) (lineVec (lineRep k))) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_zsm, flagMap_lineVec ρ m hm h2 hrel, zsm_zero]

theorem prod_add_self (x : Core × St) : x + x = 0 :=
  Prod.ext (core_add_self x.1) (st_add_self x.2)

@[expose] def x0 : Core × St := (coreU2, stE13)

theorem coreU2_fix_bel : ∀ i : Fin 8, bel i • coreU2 = coreU2 := by decide +kernel

theorem x0_fix : ∀ t ∈ borel, prodRep ρCore ρSt t x0 = x0 := fun t ht => by
  obtain ⟨i, rfl⟩ := exists_bel t ht
  exact Prod.ext (coreU2_fix_bel i) (stE13_fix_bel i)

theorem coreU2_rel : coreU2 + llA • coreU2 + (llA * llA) • coreU2 = 0 := by decide +kernel

theorem stE13_rel : stE13 + llA • stE13 + (llA * llA) • stE13 = 0 := by decide +kernel

theorem x0_rel : x0 + prodRep ρCore ρSt llA x0 + prodRep ρCore ρSt (llA * llA) x0 = 0 :=
  Prod.ext coreU2_rel stE13_rel

@[expose] noncomputable def psi : (Γ ⧸ borel → ZMod 2) →+ Core × St :=
  flagMap (prodRep ρCore ρSt) x0 x0_fix prod_add_self

theorem psi_act (g : Γ) (c : Γ ⧸ borel → ZMod 2) :
    psi (actP g c) = prodRep ρCore ρSt g (psi c) :=
  flagMap_act _ _ _ _ g c

theorem psi_surjective : Function.Surjective psi := by
  have hW : ∀ g : Γ, ∀ x ∈ psi.range, prodRep ρCore ρSt g x ∈ psi.range := by
    intro g x hx
    obtain ⟨c, rfl⟩ := AddMonoidHom.mem_range.mp hx
    exact AddMonoidHom.mem_range.mpr ⟨actP g c, psi_act g c⟩
  obtain ⟨W₁, W₂, hWe, h1, h2⟩ := prod_sub psi.range hW
  have hx0 : x0 ∈ psi.range := AddMonoidHom.mem_range.mpr ⟨Pi.single ((1 : Γ) : Γ ⧸ borel) 1,
    (flagMap_single _ _ _ _ _).trans (show prodRep ρCore ρSt 1 x0 = x0 by rw [map_one]; rfl)⟩
  rw [hWe, AddSubgroup.mem_prod] at hx0
  have e1 : W₁ = ⊤ := by
    rcases h1 with h | h | h
    · rw [h, AddSubgroup.mem_bot] at hx0
      exact absurd hx0.1 coreU2_ne
    · rw [h, AddMonoidHom.mem_ker] at hx0
      exact absurd (hx0.1.symm.trans kappa_u2) (by decide)
    · exact h
  have e2 : W₂ = ⊤ := by
    rcases h2 with h | h
    · rw [h, AddSubgroup.mem_bot] at hx0
      exact absurd hx0.2 stE13_ne
    · exact h
  intro x
  have hx : x ∈ psi.range := by
    rw [hWe, e1, e2, AddSubgroup.top_prod_top]
    exact AddSubgroup.mem_top x
  exact AddMonoidHom.mem_range.mp hx

theorem card_ker_psi : Nat.card ↥psi.ker = 2 ^ 7 := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective psi_surjective
  have hq : Nat.card (Γ ⧸ borel) = 21 := index_borel
  rw [Nat.card_prod, card_core, card_st, Nat.card_fun, Nat.card_zmod, hq] at h
  have h' : Nat.card ↥psi.ker * (64 * 256) = 2 ^ 7 * (64 * 256) := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem ker_psi_eq : psi.ker = lineMap.range := by
  symm
  refine AddSubgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
    exact flagMap_lineMap _ _ _ _ x0_rel a
  · rw [card_ker_psi, card_range_lineMap]

theorem llA_cube : llA * (llA * llA) = 1 := by decide

theorem Ll_cases : ∀ g : Γ, g ∈ Ll → g ∈ borel ∨ llA⁻¹ * g ∈ borel ∨ (llA * llA)⁻¹ * g ∈ borel := by
  decide +kernel

theorem line_rel {M : Type} [AddCommGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ x : M, x + x = 0) {m : M} (hm : ∀ t ∈ borel, ρ t m = m)
    (hl : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) = 4) :
    m + ρ llA m + ρ (llA * llA) m = 0 := by
  set S := AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y} with hS
  have hmem : ∀ g ∈ Ll, ρ g m ∈ S := fun g hg => AddSubgroup.subset_closure ⟨g, hg, rfl⟩
  have hx1 : m ∈ S := by
    have := hmem 1 (one_mem _)
    rwa [rho_one] at this
  have hx2 := hmem llA llA_mem
  have hx3 := hmem (llA * llA) (mul_mem llA_mem llA_mem)
  have hgen : ∀ g ∈ Ll, ρ g m = m ∨ ρ g m = ρ llA m ∨ ρ g m = ρ (llA * llA) m := by
    intro g hg
    rcases Ll_cases g hg with h | h | h
    · exact Or.inl (hm g h)
    · refine Or.inr (Or.inl ?_)
      rw [show g = llA * (llA⁻¹ * g) by group, rho_mul, hm _ h]
    · refine Or.inr (Or.inr ?_)
      rw [show g = (llA * llA) * ((llA * llA)⁻¹ * g) by group, rho_mul, hm _ h]
  have hinj : ∀ (g : Γ) (x y : M), ρ g x = ρ g y → x = y := fun g x y e => by
    have := congrArg (ρ g⁻¹) e
    rwa [← rho_mul, ← rho_mul, inv_mul_cancel, rho_one, rho_one] at this
  by_contra hs
  by_cases h12 : ρ llA m = m
  ·
    have h3 : ρ (llA * llA) m = m := by rw [rho_mul, h12, h12]
    have hle : S ≤ AddSubgroup.zmultiples m := by
      rw [hS, AddSubgroup.closure_le]
      rintro y ⟨g, hg, rfl⟩
      rcases hgen g hg with e | e | e
      · rw [e]
        exact AddSubgroup.mem_zmultiples m
      · rw [e, h12]
        exact AddSubgroup.mem_zmultiples m
      · rw [e, h3]
        exact AddSubgroup.mem_zmultiples m
    have hsub : (S : Set M) ⊆ {0, m} := fun y hy => by
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hle hy)
      rcases zsmul_mem_pair h2 k m with e | e
      · exact Or.inl e
      · exact Or.inr e
    have hc : Nat.card ↥S ≤ 2 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  · have hm0 : m ≠ 0 := fun h0 => h12 (by rw [h0, map_zero])
    have h13 : ρ (llA * llA) m ≠ m := fun e => h12 (by
      have := congrArg (ρ llA) e
      rw [← rho_mul, llA_cube, rho_one] at this
      exact this.symm)
    have h23 : ρ (llA * llA) m ≠ ρ llA m := fun e => h12 (by
      rw [rho_mul] at e
      exact hinj llA _ _ e)
    have h20 : ρ llA m ≠ 0 := fun e => hm0 (hinj llA _ _ (e.trans (map_zero _).symm))
    have h30 : ρ (llA * llA) m ≠ 0 := fun e => hm0 (hinj _ _ _ (e.trans (map_zero _).symm))
    have hs1 : m + ρ llA m + ρ (llA * llA) m ≠ m := fun e => h23 (by
      have key : ρ llA m + ρ (llA * llA) m = (m + ρ llA m + ρ (llA * llA) m) - m := by abel
      rw [e, sub_self] at key
      exact (eq_of_add_eq_zero_two h2 key).symm)
    have hs2 : m + ρ llA m + ρ (llA * llA) m ≠ ρ llA m := fun e => h13 (by
      have key : m + ρ (llA * llA) m = (m + ρ llA m + ρ (llA * llA) m) - ρ llA m := by abel
      rw [e, sub_self] at key
      exact (eq_of_add_eq_zero_two h2 key).symm)
    have hs3 : m + ρ llA m + ρ (llA * llA) m ≠ ρ (llA * llA) m := fun e => h12 (by
      have key : m + ρ llA m = (m + ρ llA m + ρ (llA * llA) m) - ρ (llA * llA) m := by abel
      rw [e, sub_self] at key
      exact (eq_of_add_eq_zero_two h2 key).symm)
    have h5 := five_le_card S (zero_mem S) hx1 hx2 hx3 (add_mem (add_mem hx1 hx2) hx3)
      hm0.symm h20.symm h30.symm (Ne.symm hs) (fun e => h12 e.symm) (fun e => h13 e.symm)
      (Ne.symm hs1) (fun e => h23 e.symm) (Ne.symm hs2) (Ne.symm hs3)
    omega

theorem exists_factor {M : Type} [AddGroup M] (ρ : Γ →* AddMonoid.End M)
    (F : (Γ ⧸ borel → ZMod 2) →+ M) (hF : ∀ (g : Γ) c, F (actP g c) = ρ g (F c))
    (hker : ∀ c, psi c = 0 → F c = 0) :
    ∃ f : Core × St →+ M, (∀ c, f (psi c) = F c) ∧
      ∀ (g : Γ) (x : Core × St), f (prodRep ρCore ρSt g x) = ρ g (f x) := by
  have hps : ∀ x, psi (Function.surjInv psi_surjective x) = x :=
    Function.surjInv_eq psi_surjective
  have key : ∀ c c', psi c = psi c' → F c = F c' := fun c c' e => by
    have h0 := hker (c - c') (by rw [map_sub]; exact sub_eq_zero.mpr e)
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  let f : Core × St →+ M :=
    { toFun := fun x => F (Function.surjInv psi_surjective x)
      map_zero' := by
        rw [key _ 0 (by rw [hps, map_zero]), map_zero]
      map_add' := fun x y => by
        rw [← map_add]
        exact key _ _ (by rw [hps, map_add, hps, hps]) }
  refine ⟨f, fun c => key _ _ (hps _), fun g x => ?_⟩
  show F (Function.surjInv psi_surjective (prodRep ρCore ρSt g x)) =
    ρ g (F (Function.surjInv psi_surjective x))
  rw [← hF]
  exact key _ _ (by rw [hps, psi_act, hps])

theorem isoMod_of_ker {A B M : Type} [AddGroup A] [AddGroup B] [AddGroup M]
    {σA : Γ →* AddMonoid.End A} {σB : Γ →* AddMonoid.End B} {ρ : Γ →* AddMonoid.End M}
    (π : A →+ B) (hπ : Function.Surjective π)
    (hπe : ∀ (g : Γ) (a : A), π (σA g a) = σB g (π a)) (f : A →+ M)
    (hf : Function.Surjective f) (hfe : ∀ (g : Γ) (a : A), f (σA g a) = ρ g (f a))
    (hker : ∀ a, π a = 0 ↔ f a = 0) : IsoMod ρ σB := by
  have hps : ∀ b, π (Function.surjInv hπ b) = b := Function.surjInv_eq hπ
  have key : ∀ a a', π a = π a' → f a = f a' := fun a a' e => by
    have h0 := (hker (a - a')).mp (by rw [map_sub]; exact sub_eq_zero.mpr e)
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  let f' : B →+ M :=
    { toFun := fun b => f (Function.surjInv hπ b)
      map_zero' := by rw [key _ 0 (by rw [hps, map_zero]), map_zero]
      map_add' := fun x y => by
        rw [← map_add]
        exact key _ _ (by rw [hps, map_add, hps, hps]) }
  refine ⟨f', ⟨fun x y e => ?_, fun z => ?_⟩, fun g b => ?_⟩
  · have e' : f (Function.surjInv hπ x) = f (Function.surjInv hπ y) := e
    have h0 := (hker (Function.surjInv hπ x - Function.surjInv hπ y)).mpr
      (by rw [map_sub]; exact sub_eq_zero.mpr e')
    rw [map_sub, hps, hps] at h0
    exact sub_eq_zero.mp h0
  · obtain ⟨a, rfl⟩ := hf z
    exact ⟨π a, key _ _ (hps _)⟩
  · show f (Function.surjInv hπ (σB g b)) = ρ g (f (Function.surjInv hπ b))
    rw [← hfe]
    exact key _ _ (by rw [hps, hπe, hps])

theorem volI_H_6_5_aux {M : Type} [AddCommGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ x : M, x + x = 0) (m : M) (hm : ∀ t ∈ borel, ρ t m = m)
    (hgen : AddSubgroup.closure (Set.range fun g : Γ => ρ g m) = ⊤)
    (hl : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) = 4) :
    (∃ f : Core × St →+ M, Function.Surjective f ∧
        ∀ (g : Γ) (x : Core × St), f (prodRep ρCore ρSt g x) = ρ g (f x)) ∧
      (IsoMod ρ ρCore ∨ IsoMod ρ ρSt ∨ IsoMod ρ ρV ∨ IsoMod ρ (prodRep ρV ρSt) ∨
        IsoMod ρ (prodRep ρCore ρSt)) := by
  have hrel := line_rel ρ h2 hm hl
  have hker : ∀ c, psi c = 0 → flagMap ρ m hm h2 c = 0 := fun c hc => by
    have hc' : c ∈ lineMap.range := ker_psi_eq ▸ (AddMonoidHom.mem_ker.mpr hc)
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hc'
    exact flagMap_lineMap ρ m hm h2 hrel a
  obtain ⟨f, hfF, hfe⟩ := exists_factor ρ (flagMap ρ m hm h2) (flagMap_act ρ m hm h2) hker
  have hfs : Function.Surjective f := by
    have hle : AddSubgroup.closure (Set.range fun g : Γ => ρ g m) ≤ f.range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      refine AddMonoidHom.mem_range.mpr ⟨psi (Pi.single (g : Γ ⧸ borel) 1), ?_⟩
      rw [hfF, flagMap_single, orbPt_mk]
    rw [hgen] at hle
    exact AddMonoidHom.range_eq_top.mp (eq_top_iff.mpr hle)
  refine ⟨⟨f, hfs, hfe⟩, ?_⟩
  have hW : ∀ g : Γ, ∀ x ∈ f.ker, prodRep ρCore ρSt g x ∈ f.ker := fun g x hx => by
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [hfe, hx, map_zero]
  obtain ⟨W₁, W₂, hWe, h1, h2'⟩ := prod_sub f.ker hW
  have hk : ∀ x, f x = 0 ↔ x.1 ∈ W₁ ∧ x.2 ∈ W₂ := fun x => by
    rw [← AddMonoidHom.mem_ker, hWe, AddSubgroup.mem_prod]
  rcases h1 with e1 | e1 | e1 <;> rcases h2' with e2 | e2 <;> subst e1 e2
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨f, ⟨(injective_iff_map_eq_zero f).mpr
      fun x hx => ?_, hfs⟩, hfe⟩)))
    have h0 := (hk x).mp hx
    rw [AddSubgroup.mem_bot, AddSubgroup.mem_bot] at h0
    exact Prod.ext h0.1 h0.2
  ·
    refine Or.inl (isoMod_of_ker (σA := prodRep ρCore ρSt) (AddMonoidHom.fst Core St)
      Prod.fst_surjective (fun g a => rfl) f hfs hfe fun a => ?_)
    rw [hk, AddSubgroup.mem_bot]
    exact ⟨fun h => ⟨h, AddSubgroup.mem_top _⟩, fun h => h.1⟩
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inl (isoMod_of_ker
      (σA := prodRep ρCore ρSt) (kappa.prodMap (AddMonoidHom.id St)) (fun y => ?_)
      (fun g a => Prod.ext (kappa_smul g a.1) rfl) f hfs hfe fun a => ?_))))
    · obtain ⟨c, hc⟩ := kappa_surjective y.1
      exact ⟨(c, y.2), Prod.ext hc rfl⟩
    · rw [hk, AddSubgroup.mem_bot, AddMonoidHom.mem_ker]
      exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
        fun h => Prod.ext h.1 h.2⟩
  ·
    refine Or.inr (Or.inr (Or.inl (isoMod_of_ker (σA := prodRep ρCore ρSt)
      (kappa.comp (AddMonoidHom.fst Core St)) (fun v => ?_) (fun g a => kappa_smul g a.1) f hfs
      hfe fun a => ?_)))
    · obtain ⟨c, hc⟩ := kappa_surjective v
      exact ⟨(c, 0), hc⟩
    · rw [hk, AddMonoidHom.mem_ker]
      exact ⟨fun h => ⟨h, AddSubgroup.mem_top _⟩, fun h => h.1⟩
  ·
    refine Or.inr (Or.inl (isoMod_of_ker (σA := prodRep ρCore ρSt) (AddMonoidHom.snd Core St)
      Prod.snd_surjective (fun g a => rfl) f hfs hfe fun a => ?_))
    rw [hk, AddSubgroup.mem_bot]
    exact ⟨fun h => ⟨AddSubgroup.mem_top _, h⟩, fun h => h.2⟩
  ·
    exfalso
    have hM : ∀ y : M, y = 0 := fun y => by
      obtain ⟨x, rfl⟩ := hfs y
      exact (hk x).mpr ⟨AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩
    have hsub : Subsingleton ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) :=
      ⟨fun a b => Subtype.ext ((hM a).trans (hM b).symm)⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega

theorem volI_H_6_5 : VolI_H_6_5 := by
  intro M _ _ ρ h2 _hfaith m hm hgen hl
  let _ : AddCommGroup M := addCommGroupOfAddSelf h2
  exact volI_H_6_5_aux ρ h2 m hm hgen hl

end CFSG.Quasithin.H6
