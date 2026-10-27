module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartAutomizer
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideOrth

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

theorem inside_three_univ : ExcRaw.inside 3 Finset.univ = ⊤ := by
  have hb : ∀ l j : Fin (ExcRaw.dim 3),
      ExcRaw.coroot 3 (Fin.castLE (by decide) l) j = if l = j then 1 else 0 := by
    decide +kernel
  refine eq_top_iff.mpr fun v _ => ?_
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
  have hl : (fun j => if l = j then (1 : ZMod 3) else 0) =
      ExcRaw.coroot 3 (Fin.castLE (by decide) l) :=
    funext fun j => (hb l j).symm
  rw [hl]
  exact Submodule.subset_span ⟨_, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩

private theorem ie6_card_ge_of_indep {n : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod 3) M]
    [Finite M] (W : Submodule (ZMod 3) M) (v : Fin n → M) (hv : ∀ l, v l ∈ W)
    (hind : ∀ a : Fin n → ZMod 3, ∑ l, a l • v l = 0 → a = 0) : 3 ^ n ≤ Nat.card ↥W := by
  let f : (Fin n → ZMod 3) → ↥W := fun a =>
    ⟨∑ l, a l • v l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hv l)⟩
  have hf : Function.Injective f := by
    intro a a' h
    have h' : ∑ l, (a - a') l • v l = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrArg Subtype.val h)
    exact sub_eq_zero.mp (hind _ h')
  have hcard : Nat.card (Fin n → ZMod 3) = 3 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← hcard]
  exact Nat.card_le_card_of_injective f hf

theorem card_inside_two_univ : 3 ^ 5 ≤ Nat.card ↥(ExcRaw.inside 2 Finset.univ) := by
  let b : Fin 5 → ExcRaw.Root 2 := Fin.castLE (by decide)
  refine ie6_card_ge_of_indep _ (fun l => ExcRaw.coroot 2 (b l))
    (fun l => Submodule.subset_span ⟨_, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩) ?_
  decide +kernel

@[expose] def orthCode (m : Fin 6) (k : ExcRaw.Root m) : Finset (ExcRaw.Root m) :=
  Finset.univ.filter fun i => ExcRaw.pairing m k i = 0 ∧ ExcRaw.pairing m i k = 0

theorem not_adj_of_mem_orthCode {m : Fin 6} {k i : ExcRaw.Root m} (hi : i ∈ orthCode m k) :
    ¬ ExcRaw.Adj m k i := by
  simp only [orthCode, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [ExcRaw.Adj, hi.1, hi.2, ne_eq, not_true_eq_false, or_self, not_false_eq_true]

private def ie6OrthTab : List (List ℕ) :=
  [[1, 3, 4, 5], [0, 2, 4, 21], [1, 4, 5, 13], [0, 5, 8, 9], [0, 1, 2, 7], [0, 1, 2, 3],
    [0, 1, 2, 10], [0, 4, 11, 12], [0, 3, 4, 14], [3, 4, 8, 13], [0, 6, 8, 9], [0, 3, 6, 17],
    [3, 6, 11, 16], [2, 3, 6, 11], [6, 8, 9, 10], [5, 7, 13, 14], [2, 5, 7, 17], [3, 5, 8, 9],
    [2, 3, 5, 8], [0, 5, 7, 14], [2, 6, 8, 10], [1, 4, 7, 12], [2, 4, 7, 11], [4, 7, 11, 12],
    [2, 3, 4, 8], [1, 6, 9, 10], [1, 2, 6, 10], [0, 1, 3, 6], [1, 3, 5, 9], [1, 2, 3, 5],
    [0, 1, 5, 7], [0, 2, 4, 8], [0, 2, 3, 4], [0, 1, 3, 4], [1, 2, 4, 7], [1, 4, 5, 9]]

private def ie6OrthIdx (m : Fin 6) (h : 0 < ExcRaw.nroots m) (k : ExcRaw.Root m) (l : ℕ) :
    ExcRaw.Root m :=
  ⟨((ie6OrthTab.getD k.val []).getD l 0) % ExcRaw.nroots m, Nat.mod_lt _ h⟩

private def ie6OrthVec (m : Fin 6) (h : 0 < ExcRaw.nroots m) (k : ExcRaw.Root m) (l : Fin 5) :
    ExcRaw.V m :=
  if l.val < 4 then ExcRaw.coroot m (ie6OrthIdx m h k l.val) else ExcRaw.coroot m k

private theorem ie6_orth_check_two : ∀ k : ExcRaw.Root 2,
    (∀ l : Fin 4, ie6OrthIdx 2 (by decide) k l.val ∈ orthCode 2 k) ∧
      ∀ a : Fin 5 → ZMod 3, ∑ l, a l • ie6OrthVec 2 (by decide) k l = 0 → a = 0 := by
  decide +kernel

private theorem ie6_orth_check_three : ∀ k : ExcRaw.Root 3,
    (∀ l : Fin 4, ie6OrthIdx 3 (by decide) k l.val ∈ orthCode 3 k) ∧
      ∀ a : Fin 5 → ZMod 3, ∑ l, a l • ie6OrthVec 3 (by decide) k l = 0 → a = 0 := by
  decide +kernel

theorem card_inside_orthCode_sup_ge {m : Fin 6} (hm : m = 2 ∨ m = 3) (k : ExcRaw.Root m) :
    3 ^ 5 ≤ Nat.card ↥(ExcRaw.inside m (orthCode m k) ⊔
      Submodule.span (ZMod 3) {ExcRaw.coroot m k}) := by
  have hpos : 0 < ExcRaw.nroots m := by rcases hm with rfl | rfl <;> decide
  have hchk : (∀ l : Fin 4, ie6OrthIdx m hpos k l.val ∈ orthCode m k) ∧
      ∀ a : Fin 5 → ZMod 3, ∑ l, a l • ie6OrthVec m hpos k l = 0 → a = 0 := by
    rcases hm with rfl | rfl
    · exact ie6_orth_check_two k
    · exact ie6_orth_check_three k
  refine ie6_card_ge_of_indep _ (ie6OrthVec m hpos k) (fun l => ?_) hchk.2
  unfold ie6OrthVec
  split_ifs with hl
  · exact Submodule.mem_sup_left (Submodule.subset_span
      ⟨_, Finset.mem_coe.mpr (hchk.1 ⟨l.val, hl⟩), rfl⟩)
  · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem ggLinImage_Γ_le_inside_three
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup Tag.E6 L p} {T₀ : Subgroup (ModGL Tag.E6 L)} (d : ExcCoordDatum S T₀ 3) :
    ggLinImage (p := 3) d.coord S.Γ ≤ ExcRaw.inside 3 Finset.univ := by
  rw [inside_three_univ]
  exact le_top

theorem card_ggLinImage_Γ_le
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup Tag.E6 L p} {T₀ : Subgroup (ModGL Tag.E6 L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) (hcard : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5) :
    Nat.card ↥(ggLinImage (p := 3) d.coord S.Γ) ≤ 3 ^ 5 := by
  have hfin : Finite ↥(fullThreeTorus S ⊓ S.Γ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [card_ggLinImage, ← hcard]
  exact Subgroup.card_le_of_le (inf_le_inf_right _ d.le_fullThreeTorus)


theorem inside_univ_le_ggLinImage_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {T₀ : Subgroup (ModGL Tag.E6 L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) :
    ExcRaw.inside m Finset.univ ≤ ggLinImage (p := 3) d.coord S.Γ := by
  rw [ExcRaw.inside, Submodule.span_le]
  rintro _ ⟨i, -, rfl⟩
  rw [← d.coord_coroot i]
  exact (ofMul_mem_ggLinImage d.coord S.Γ _).mpr
    (corootTuple_mem_Γ_of_rho_neg S hS.1 hS.2.2 (d.isRoot i) d.ζ_pow_three)

theorem ggLinImage_Γ_eq_inside_two {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {T₀ : Subgroup (ModGL Tag.E6 L)}
    (d : ExcCoordDatum S T₀ 2) (hcard : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5) :
    ggLinImage (p := 3) d.coord S.Γ = ExcRaw.inside 2 Finset.univ := by
  refine (Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (inside_univ_le_ggLinImage_Γ S hS d) ?_)).symm
  exact (card_ggLinImage_Γ_le d hcard).trans card_inside_two_univ

theorem ggLinImage_codeComponent_univ_le_inside {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S)
    (hcard : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5) {T₀ : Subgroup (ModGL Tag.E6 L)}
    {m : Fin 6} (hm : m = 2 ∨ m = 3) (d : ExcCoordDatum S T₀ m) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ Finset.univ) ≤
      ExcRaw.inside m Finset.univ := by
  refine (ggLinImage_mono d.coord (codeComponent_le_Γ S d.γ _)).trans ?_
  rcases hm with rfl | rfl
  · exact (ggLinImage_Γ_eq_inside_two S hS d hcard).le
  · exact ggLinImage_Γ_le_inside_three d

theorem ggLinImage_codeComponent_orthCode_le_inside {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S)
    (hcard : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5) {T₀ : Subgroup (ModGL Tag.E6 L)}
    {m : Fin 6} (hm : m = 2 ∨ m = 3) (d : ExcCoordDatum S T₀ m) (k : ExcRaw.Root m) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ (orthCode m k)) ≤
      ExcRaw.inside m (orthCode m k) := by
  refine ggLinImage_codeComponent_le_inside_of_orth (Or.inr (Or.inl rfl)) S d _
    (fun i hi => not_adj_of_mem_orthCode hi) ?_
  have hW : ExcRaw.inside m (orthCode m k) ⊔ Submodule.span (ZMod 3) {ExcRaw.coroot m k} ≤
      ExcRaw.inside m Finset.univ :=
    sup_le (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_univ _))))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.subset_span ⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩))
  have hcW := card_inside_orthCode_sup_ge hm k
  rcases hm with rfl | rfl
  · exact (Submodule.toAddSubgroup_injective (AddSubgroup.eq_of_le_of_card_ge
      (hW.trans (inside_univ_le_ggLinImage_Γ S hS d))
      ((card_ggLinImage_Γ_le d hcard).trans hcW))).ge
  · have htop : ExcRaw.inside 3 (orthCode 3 k) ⊔ Submodule.span (ZMod 3) {ExcRaw.coroot 3 k} =
        ⊤ := by
      rw [← inside_three_univ]
      refine Submodule.toAddSubgroup_injective (AddSubgroup.eq_of_le_of_card_ge hW ?_)
      refine le_trans ?_ hcW
      calc Nat.card ↥(ExcRaw.inside 3 Finset.univ) ≤ Nat.card (ExcRaw.V 3) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = 3 ^ 5 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
            rfl
    rw [htop]
    exact le_top

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
