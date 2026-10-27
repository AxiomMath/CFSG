module

public import CFSG.Quasithin.MS93.ML3Syl
public import CFSG.Quasithin.MS93.ML3Ext

public section

namespace CFSG.Quasithin.MS93

open Matrix

variable {F : Type} [Field F]

theorem coe_one_SL3 : ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  rfl

@[expose] def fixN (A : Subgroup (SL3 F)) : Submodule F (Fin 3 → F) where
  carrier := {x | ∀ g ∈ A, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x}
  add_mem' := fun {x y} hx hy g hg => by rw [Matrix.mulVec_add, hx g hg, hy g hg]
  zero_mem' := fun g _ => Matrix.mulVec_zero _
  smul_mem' := fun c x hx g hg => by rw [Matrix.mulVec_smul, hx g hg]

theorem mem_fixN {A : Subgroup (SL3 F)} {x : Fin 3 → F} :
    x ∈ fixN A ↔ ∀ g ∈ A, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x :=
  Iff.rfl

@[expose] def commN (A : Subgroup (SL3 F)) : Submodule F (Fin 3 → F) :=
  Submodule.span F
    {y | ∃ g ∈ A, ∃ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = y}

theorem sub_mem_commN {A : Subgroup (SL3 F)} {g : SL3 F} (hg : g ∈ A) (x : Fin 3 → F) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ commN A :=
  Submodule.subset_span ⟨g, hg, x, rfl⟩

theorem commN_eq_closure (A : Subgroup (SL3 F)) :
    (commN A).toAddSubgroup = AddSubgroup.closure
      {y | ∃ g ∈ A, ∃ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = y} := by
  apply le_antisymm
  · intro y hy
    refine Submodule.span_induction (p := fun y _ => y ∈ AddSubgroup.closure _) ?_ ?_ ?_ ?_ hy
    · exact fun y hy => AddSubgroup.subset_closure hy
    · exact AddSubgroup.zero_mem _
    · exact fun _ _ _ _ h1 h2 => AddSubgroup.add_mem _ h1 h2
    · intro c y _ h
      refine AddSubgroup.closure_induction (p := fun y _ => c • y ∈ AddSubgroup.closure _)
        ?_ ?_ ?_ ?_ h
      · rintro _ ⟨g, hg, x, rfl⟩
        refine AddSubgroup.subset_closure ⟨g, hg, c • x, ?_⟩
        rw [Matrix.mulVec_smul, smul_sub]
      · rw [smul_zero]; exact AddSubgroup.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
      · intro a _ ha; rw [smul_neg]; exact AddSubgroup.neg_mem _ ha
  · rw [AddSubgroup.closure_le]
    exact Submodule.subset_span

theorem commN_mono {A B : Subgroup (SL3 F)} (h : A ≤ B) : commN A ≤ commN B :=
  Submodule.span_mono fun _ ⟨g, hg, x, hx⟩ => ⟨g, h hg, x, hx⟩

theorem fixN_anti {A B : Subgroup (SL3 F)} (h : A ≤ B) : fixN B ≤ fixN A :=
  fun _ hx g hg => hx g (h hg)

@[expose] def pt0 : Submodule F (Fin 3 → F) where
  carrier := {x | x 1 = 0 ∧ x 2 = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c x hx => ⟨by simp [hx.1], by simp [hx.2]⟩

@[expose] def ln01 : Submodule F (Fin 3 → F) where
  carrier := {x | x 2 = 0}
  add_mem' := fun {x y} hx hy => by simp [show x 2 = 0 from hx, show y 2 = 0 from hy]
  zero_mem' := rfl
  smul_mem' := fun c x hx => by simp [show x 2 = 0 from hx]

theorem mem_pt0 {x : Fin 3 → F} : x ∈ pt0 ↔ x 1 = 0 ∧ x 2 = 0 := Iff.rfl

theorem mem_ln01 {x : Fin 3 → F} : x ∈ ln01 ↔ x 2 = 0 := Iff.rfl

theorem pt0_le_ln01 : (pt0 : Submodule F (Fin 3 → F)) ≤ ln01 := fun _ hx => hx.2

theorem fixN_sup (A B : Subgroup (SL3 F)) : fixN (A ⊔ B) = fixN A ⊓ fixN B := by
  apply le_antisymm (le_inf (fixN_anti le_sup_left) (fixN_anti le_sup_right))
  intro x ⟨hA, hB⟩
  let S : Subgroup (SL3 F) :=
    { carrier := {g | ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x}
      mul_mem' := fun {g h} hg hh => by
        show ((g * h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x
        rw [coe_mul_SL3, ← Matrix.mulVec_mulVec,
          show ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x from hh]
        exact hg
      one_mem' := by
        show ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x
        simp
      inv_mem' := fun {g} hg => by
        show ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x
        have hg' : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := hg
        conv_lhs => rw [← hg']
        rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel]
        simp }
  have hle : A ⊔ B ≤ S := sup_le (fun g hg => hA g hg) (fun g hg => hB g hg)
  exact fun g hg => hle hg

theorem commN_sup (A B : Subgroup (SL3 F)) : commN (A ⊔ B) = commN A ⊔ commN B := by
  apply le_antisymm _ (sup_le (commN_mono le_sup_left) (commN_mono le_sup_right))
  set S := commN A ⊔ commN B with hS
  let T : Subgroup (SL3 F) :=
    { carrier := {g | ∀ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ S}
      mul_mem' := fun {g h} hg hh x => by
        show ((g * h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ S
        rw [coe_mul_SL3, ← Matrix.mulVec_mulVec]
        have := S.add_mem (hg (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) (hh x)
        rwa [sub_add_sub_cancel] at this
      one_mem' := fun x => by simp
      inv_mem' := fun {g} hg x => by
        show ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ S
        have := S.neg_mem (hg (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x))
        rwa [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel,
          coe_one_SL3, Matrix.one_mulVec, neg_sub] at this }
  have hle : A ⊔ B ≤ T := sup_le
    (fun g hg x => Submodule.mem_sup_left (sub_mem_commN hg x))
    (fun g hg x => Submodule.mem_sup_right (sub_mem_commN hg x))
  rw [commN, Submodule.span_le]
  rintro _ ⟨g, hg, x, rfl⟩
  exact hle hg x

@[expose] def coordZero (j : Fin 3) : Submodule F (Fin 3 → F) where
  carrier := {x | x j = 0}
  add_mem' := fun {x y} hx hy => by simp [show x j = 0 from hx, show y j = 0 from hy]
  zero_mem' := rfl
  smul_mem' := fun c x hx => by simp [show x j = 0 from hx]

@[expose] def coordLine (i : Fin 3) : Submodule F (Fin 3 → F) where
  carrier := {x | ∀ k, k ≠ i → x k = 0}
  add_mem' := fun {x y} hx hy k hk => by simp [hx k hk, hy k hk]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c x hx k hk => by simp [hx k hk]

theorem fixN_rootGroup {i j : Fin 3} (h : i ≠ j) :
    fixN (rootGroup i j : Subgroup (SL3 F)) = coordZero j := by
  ext x
  constructor
  · intro hx
    have h1 := hx (rootElt i j 1) (rootElt_mem_rootGroup _ _ _)
    rw [rootElt_mulVec h, add_eq_left] at h1
    have := congrFun h1 i
    show x j = 0
    simpa using this
  · intro hx
    rintro _ ⟨c, rfl⟩
    rw [rootElt_mulVec h, show x j = 0 from hx, mul_zero, Pi.single_zero, add_zero]

theorem commN_rootGroup {i j : Fin 3} (h : i ≠ j) :
    commN (rootGroup i j : Subgroup (SL3 F)) = coordLine i := by
  apply le_antisymm
  · rw [commN, Submodule.span_le]
    rintro _ ⟨_, ⟨c, rfl⟩, x, rfl⟩ k hk
    rw [rootElt_mulVec h, add_sub_cancel_left, Pi.single_eq_of_ne hk]
  · intro y hy
    have hy' : y = Pi.single i (y i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Pi.single_eq_of_ne hk, hy k hk]
    have := sub_mem_commN (rootElt_mem_rootGroup i j (y i)) (Pi.single j 1 : Fin 3 → F)
    rw [rootElt_mulVec h, add_sub_cancel_left, Pi.single_eq_same, mul_one] at this
    rwa [hy']

theorem fixN_qLn : fixN (qLn : Subgroup (SL3 F)) = ln01 := by
  rw [qLn, fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide), inf_idem]
  rfl

theorem commN_qLn : commN (qLn : Subgroup (SL3 F)) = ln01 := by
  rw [qLn, commN_sup, commN_rootGroup (by decide), commN_rootGroup (by decide)]
  apply le_antisymm
  · refine sup_le (fun x hx => hx 2 (by decide)) (fun x hx => hx 2 (by decide))
  · intro x hx
    have hx2 : x 2 = 0 := hx
    rw [Submodule.mem_sup]
    refine ⟨Pi.single 0 (x 0), fun k hk => Pi.single_eq_of_ne hk _, Pi.single 1 (x 1),
      fun k hk => Pi.single_eq_of_ne hk _, ?_⟩
    funext k
    fin_cases k <;> simp [hx2]

theorem fixN_qPt : fixN (qPt : Subgroup (SL3 F)) = pt0 := by
  rw [qPt, fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide)]
  rfl

theorem commN_qPt : commN (qPt : Subgroup (SL3 F)) = pt0 := by
  rw [qPt, commN_sup, commN_rootGroup (by decide), commN_rootGroup (by decide), sup_idem]
  ext x
  exact ⟨fun hx => ⟨hx 1 (by decide), hx 2 (by decide)⟩, fun hx k hk => by
    fin_cases k
    · exact absurd rfl hk
    · exact hx.1
    · exact hx.2⟩

theorem fixN_sStar : fixN (sStar : Subgroup (SL3 F)) = pt0 := by
  rw [sStar, fixN_sup, fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide),
    fixN_rootGroup (by decide), inf_assoc, inf_idem]
  rfl

theorem commN_sStar : commN (sStar : Subgroup (SL3 F)) = ln01 := by
  rw [sStar, commN_sup, show rootGroup 0 1 ⊔ rootGroup 0 2 = (qPt : Subgroup (SL3 F)) from rfl,
    commN_qPt, commN_rootGroup (by decide)]
  apply le_antisymm
  · exact sup_le pt0_le_ln01 (fun x hx => hx 2 (by decide))
  · rw [← commN_qLn, qLn, commN_sup, commN_rootGroup (by decide), commN_rootGroup (by decide)]
    refine sup_le (le_sup_of_le_left ?_) le_sup_right
    intro x hx
    exact ⟨hx 1 (by decide), hx 2 (by decide)⟩

theorem commN_le_ln01_of_le_sStar {A : Subgroup (SL3 F)} (h : A ≤ sStar) : commN A ≤ ln01 :=
  (commN_mono h).trans commN_sStar.le

theorem pt0_le_fixN_of_le_sStar {A : Subgroup (SL3 F)} (h : A ≤ sStar) : pt0 ≤ fixN A :=
  fixN_sStar.symm.le.trans (fixN_anti h)

theorem eq_one_of_mulVec_eq_self {g : SL3 F}
    (h : ∀ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : g = 1 := by
  apply Subtype.ext
  change ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  exact Matrix.ext_of_mulVec_single fun i => by rw [h, coe_one_SL3, Matrix.one_mulVec]

theorem commN_ne_bot {A : Subgroup (SL3 F)} (hA : A ≠ ⊥) : commN A ≠ ⊥ := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ≠ x := by
    by_contra h
    push Not at h
    exact hg1' (eq_one_of_mulVec_eq_self h)
  intro hbot
  have := sub_mem_commN hg x
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
  exact hx this

theorem card_le_of_ne_bot [Finite F] {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊥) :
    Nat.card F ≤ Nat.card S := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  let f : F → S := fun c => ⟨c • y, S.smul_mem c hy⟩
  have hf : Function.Injective f := fun c d h => by
    have h' : c • y = d • y := congrArg Subtype.val h
    exact smul_left_injective F hy0 h'
  exact Nat.card_le_card_of_injective f hf

theorem card_le_commN [Finite F] {A : Subgroup (SL3 F)} (hA : A ≠ ⊥) :
    Nat.card F ≤ Nat.card (commN A) :=
  card_le_of_ne_bot (commN_ne_bot hA)

@[expose] def dualMat (g : SL3 F) : Matrix (Fin 3) (Fin 3) F :=
  (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ

theorem card_ln01 [Finite F] : Nat.card (ln01 : Submodule F (Fin 3 → F)) = Nat.card F ^ 2 := by
  let e : F × F ≃ (ln01 : Submodule F (Fin 3 → F)) :=
    { toFun := fun p => ⟨![p.1, p.2, 0], rfl⟩
      invFun := fun x => ((x : Fin 3 → F) 0, (x : Fin 3 → F) 1)
      left_inv := fun p => rfl
      right_inv := fun x => by
        apply Subtype.ext
        funext k
        fin_cases k
        · rfl
        · rfl
        · exact x.2.symm }
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem finrank_ln01 [Finite F] : Module.finrank F (ln01 : Submodule F (Fin 3 → F)) = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := F) (V := (ln01 : Submodule F (Fin 3 → F)))
  rw [card_ln01] at h
  exact (Nat.pow_right_injective (Finite.one_lt_card (α := F)) h).symm

theorem fixN_ptLevi :
    fixN (rootGroup 0 1 ⊔ rootGroup 0 2 ⊔ rootGroup 1 2 ⊔ rootGroup 2 1 : Subgroup (SL3 F)) =
      pt0 := by
  rw [fixN_sup, fixN_sup, fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide),
    fixN_rootGroup (by decide), fixN_rootGroup (by decide)]
  ext x
  simp only [Submodule.mem_inf]
  exact ⟨fun h => ⟨h.1.1.1, h.1.1.2⟩, fun h => ⟨⟨⟨h.1, h.2⟩, h.2⟩, h.1⟩⟩

private theorem single_mem_of {S : Submodule F (Fin 3 → F)} {k : Fin 3} {a : F} (ha : a ≠ 0)
    (h : Pi.single k a ∈ S) (c : F) : Pi.single k c ∈ S := by
  have := S.smul_mem (c / a) h
  rwa [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ c ha] at this

private theorem root_sub_mem {S : Submodule F (Fin 3 → F)} {x : Fin 3 → F} {i j : Fin 3}
    (hij : i ≠ j)
    (hS : ((rootElt i j (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S) (hx : x ∈ S) :
    Pi.single i (x j) ∈ S := by
  have := S.sub_mem hS hx
  rwa [rootElt_mulVec hij, add_sub_cancel_left, one_mul] at this

theorem sStar_invariant_cases (S : Submodule F (Fin 3 → F))
    (hS : ∀ g ∈ (sStar : Subgroup (SL3 F)), ∀ x ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S) :
    S = ⊥ ∨ S = pt0 ∨ S = ln01 ∨ S = ⊤ := by
  have h01 : rootElt 0 1 (1 : F) ∈ (sStar : Subgroup (SL3 F)) :=
    mem_sStar_iff.mpr ⟨1, 0, 0, (rootElt01_eq_uniTri 1).symm⟩
  have h02 : rootElt 0 2 (1 : F) ∈ (sStar : Subgroup (SL3 F)) :=
    mem_sStar_iff.mpr ⟨0, 1, 0, (rootElt02_eq_uniTri 1).symm⟩
  have h12 : rootElt 1 2 (1 : F) ∈ (sStar : Subgroup (SL3 F)) :=
    mem_sStar_iff.mpr ⟨0, 0, 1, (rootElt12_eq_uniTri 1).symm⟩
  have hdecomp : ∀ x : Fin 3 → F,
      x = Pi.single 0 (x 0) + Pi.single 1 (x 1) + Pi.single 2 (x 2) := fun x => by
    funext k
    fin_cases k <;> simp
  by_cases hA : ∃ x ∈ S, x 2 ≠ 0
  · obtain ⟨x, hx, hx2⟩ := hA
    have s0 := single_mem_of hx2 (root_sub_mem (i := 0) (j := 2) (by decide) (hS _ h02 x hx) hx)
    have s1 := single_mem_of hx2 (root_sub_mem (i := 1) (j := 2) (by decide) (hS _ h12 x hx) hx)
    have s2 : Pi.single 2 (x 2) ∈ S := by
      have e : Pi.single 2 (x 2) = x - Pi.single 0 (x 0) - Pi.single 1 (x 1) := by
        funext k
        fin_cases k <;> simp
      rw [e]
      exact S.sub_mem (S.sub_mem hx (s0 (x 0))) (s1 (x 1))
    have s2' := single_mem_of hx2 s2
    refine Or.inr (Or.inr (Or.inr (eq_top_iff.mpr fun y _ => ?_)))
    rw [hdecomp y]
    exact S.add_mem (S.add_mem (s0 _) (s1 _)) (s2' _)
  push Not at hA
  have hSl : S ≤ ln01 := fun x hx => hA x hx
  by_cases hB : ∃ x ∈ S, x 1 ≠ 0
  · obtain ⟨x, hx, hx1⟩ := hB
    have s0 := single_mem_of hx1 (root_sub_mem (i := 0) (j := 1) (by decide) (hS _ h01 x hx) hx)
    have s1 : Pi.single 1 (x 1) ∈ S := by
      have e : Pi.single 1 (x 1) = x - Pi.single 0 (x 0) := by
        funext k
        fin_cases k <;> simp [hA x hx]
      rw [e]
      exact S.sub_mem hx (s0 (x 0))
    have s1' := single_mem_of hx1 s1
    refine Or.inr (Or.inr (Or.inl (le_antisymm hSl fun y hy => ?_)))
    rw [hdecomp y, show y 2 = 0 from hy, Pi.single_zero, add_zero]
    exact S.add_mem (s0 _) (s1' _)
  push Not at hB
  have hSp : S ≤ pt0 := fun x hx => ⟨hB x hx, hA x hx⟩
  by_cases hC : S = ⊥
  · exact Or.inl hC
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
    have ex : x = Pi.single 0 (x 0) := by
      funext k
      fin_cases k <;> simp [hB x hx, hA x hx]
    have hx0' : x 0 ≠ 0 := by
      intro h
      apply hx0
      rw [ex, h, Pi.single_zero]
    have s0 : Pi.single 0 (x 0) ∈ S := ex ▸ hx
    have s0' := single_mem_of hx0' s0
    refine Or.inr (Or.inl (le_antisymm hSp fun y hy => ?_))
    rw [hdecomp y, show y 1 = 0 from hy.1, show y 2 = 0 from hy.2]
    simpa using s0' (y 0)

theorem dualMat_rootElt_mulVec {i j : Fin 3} (h : i ≠ j) (c : F) (y : Fin 3 → F) :
    dualMat (rootElt i j c) *ᵥ y = y + Pi.single j (-c * y i) := by
  rw [dualMat, ← rootElt_neg, coe_rootElt h, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem not_equiv_dual :
    ¬ ∃ f : (Fin 3 → F) →+ (Fin 3 → F), Function.Injective f ∧
      ∀ (g : SL3 F) (x : Fin 3 → F),
        f (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = dualMat g *ᵥ f x := by
  rintro ⟨f, hf, hfeq⟩
  have hfix : ∀ i j : Fin 3, i ≠ j → j ≠ 0 →
      dualMat (rootElt i j (1 : F)) *ᵥ f ![1, 0, 0] = f ![1, 0, 0] := fun i j hij hj => by
    rw [← hfeq, rootElt_mulVec hij]
    congr 1
    fin_cases j
    · exact absurd rfl hj
    all_goals simp
  have hc : ∀ i j : Fin 3, i ≠ j → j ≠ 0 → f ![1, 0, 0] i = 0 := fun i j hij hj => by
    have h1 := hfix i j hij hj
    rw [dualMat_rootElt_mulVec hij, add_eq_left] at h1
    have := congrFun h1 j
    simpa using this
  have hzero : f ![1, 0, 0] = 0 := by
    funext k
    fin_cases k
    · exact hc 0 1 (by decide) (by decide)
    · exact hc 1 2 (by decide) (by decide)
    · exact hc 2 1 (by decide) (by decide)
  have := hf (hzero.trans (map_zero f).symm)
  have h0 := congrFun this 0
  simp at h0

end CFSG.Quasithin.MS93
