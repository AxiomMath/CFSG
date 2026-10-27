module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawFixWeyl
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawFixWeylOneData
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcCheck

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.FixWeylOne

open CFSG.Decide.F3

@[expose] def mk4 {α : Type} (f : ℕ → α) : List α := [f 0, f 1, f 2, f 3]

@[expose] def dot4 (a b : List ℕ) : ℕ :=
  a.getD 0 0 * b.getD 0 0 + a.getD 1 0 * b.getD 1 0 + a.getD 2 0 * b.getD 2 0 +
    a.getD 3 0 * b.getD 3 0

@[expose] def rootN (j : ℕ) (v : List ℕ) : ℕ := dot4 (fTab.getD j []) v

@[expose] def reflN (j : ℕ) (v : List ℕ) : List ℕ :=
  mk4 fun t => (v.getD t 0 + 2 * (rootN j v * (hTab.getD j []).getD t 0)) % 3

@[expose] def reflE (j : ℕ) (M : List (List ℕ)) : List (List ℕ) :=
  mk4 fun k => reflN j (M.getD k [])

@[expose] def applyN (M : List (List ℕ)) (v : List ℕ) : List ℕ :=
  mk4 fun t => (v.getD 0 0 * (M.getD 0 []).getD t 0 + v.getD 1 0 * (M.getD 1 []).getD t 0 +
    v.getD 2 0 * (M.getD 2 []).getD t 0 + v.getD 3 0 * (M.getD 3 []).getD t 0) % 3

@[expose] def applyW (w : List ℕ) (v : List ℕ) : List ℕ := w.foldr reflN v

@[expose] def decV (c : ℕ) : List ℕ := mk4 fun t => c / 3 ^ t % 3

@[expose] def decE (e : ℕ) : List (List ℕ) := mk4 fun k => decV (e / 81 ^ k % 81)

@[expose] def bas : List (List ℕ) := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def recAt (n : ℕ) : List ℕ := (wTab.getD (n / 32) []).getD (n % 32) []

@[expose] def elemAt (n : ℕ) : List (List ℕ) := decE ((recAt n).getD 0 0)

@[expose] def idxAt (n s : ℕ) : ℕ := (recAt n).getD (s + 1) 0

@[expose] def closedAt (n : ℕ) : Bool :=
  (List.range 4).all fun s =>
    decide (idxAt n s < 1152) && reflE (gens.getD s 0) (elemAt n) == elemAt (idxAt n s)

@[expose] def closedOK : Bool := elemAt 0 == bas && (List.range 1152).all closedAt

@[expose] def genWordOK (j : ℕ) : Bool :=
  (genWords.getD j []).all (· < 4) &&
    bas.all fun e => applyW ((genWords.getD j []).map (gens.getD · 0)) e == reflN j e

@[expose] def genWordsOK : Bool := (List.range 24).all genWordOK

@[expose] def wordOf : List ℕ → List ℕ
  | j :: _ :: l => j :: wordOf l
  | _ => []

@[expose] def subE (c : List ℕ) (k : ℕ) : List ℕ :=
  mk4 fun t => c.getD t 0 + if t = k then 2 else 0

@[expose] def gammaOK (M : List (List ℕ)) (j γ : ℕ) : Bool :=
  decide (j < 24) && (List.range 4).all fun k =>
    (fTab.getD j []).getD k 0 == dot4 (decV γ) (subE (M.getD k []) k) % 3

@[expose] def certAOK (M : List (List ℕ)) : List ℕ → Bool
  | j :: γ :: l => gammaOK M j γ && certAOK M l
  | [] => true
  | [_] => false

@[expose] def caseAOK (M : List (List ℕ)) (c : List ℕ) : Bool :=
  certAOK M c && (List.range 4).all fun k => applyW (wordOf c) (bas.getD k []) == M.getD k []

@[expose] def isDig (l : List ℕ) : Bool := l.length == 4 && l.all (· < 3)

@[expose] def splitOK (M : List (List ℕ)) (u : List ℕ) (mask : ℕ) (x₁ x₂ : List ℕ) : Bool :=
  (List.range 24).all (fun i => !mask.testBit i || (List.range 24).all fun j =>
    rootN j u % 3 != 0 || !(adjTab.getD i 0).testBit j || mask.testBit j) &&
  isDig x₁ && (List.range 24).all (fun i => !mask.testBit i || rootN i x₁ % 3 == 0) &&
    applyN M x₁ != x₁ &&
  isDig x₂ && (List.range 24).all (fun i => rootN i u % 3 != 0 || mask.testBit i ||
    rootN i x₂ % 3 == 0) && applyN M x₂ != x₂

@[expose] def caseBOK (n : ℕ) (M : List (List ℕ)) : Bool :=
  (allVecs 4).all fun u => u == [0, 0, 0, 0] || applyN M u != u ||
    bTab.any fun r => r.getD 0 0 == n && (r.drop 1).take 4 == u &&
      splitOK M u (r.getD 5 0) ((r.drop 6).take 4) ((r.drop 10).take 4)

@[expose] def certOK (n : ℕ) : Bool :=
  if (recAt n).getD 5 0 == 99 then caseBOK n (elemAt n)
  else caseAOK (elemAt n) ((recAt n).drop 5)

@[expose] def allOK : Bool := closedOK && genWordsOK && (List.range 1152).all certOK

@[expose] def toV (l : List ℕ) : V 1 := vecOfList (dim 1) l

theorem toV_apply (l : List ℕ) (k : Fin (dim 1)) : toV l k = (l.getD k 0 : ZMod 3) := rfl

@[expose] def IsCols (g : V 1 ≃ₗ[ZMod 3] V 1) (M : List (List ℕ)) : Prop :=
  ∀ k : Fin (dim 1), g (Pi.single k 1) = toV (M.getD k [])

@[expose] def rootOf (j : ℕ) : Root 1 := ⟨j % nroots 1, Nat.mod_lt _ (by decide)⟩

theorem rootOf_val {j : ℕ} (hj : j < 24) : (rootOf j : ℕ) = j := Nat.mod_eq_of_lt hj

theorem rootOf_coe (i : Root 1) : rootOf i = i := Fin.ext (rootOf_val i.isLt)

theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

theorem getD_mk4 {α : Type} (f : ℕ → α) (d : α) {k : ℕ} (hk : k < 4) :
    (mk4 f).getD k d = f k := by
  interval_cases k <;> rfl

theorem dotD_dim_one (a b : List ℕ) : Check.dotD (dim 1) a b = dot4 a b := by
  show Check.dotD 4 a b = _
  simp [Check.dotD, dot4]

theorem fTab_eq : fTab = (tabF 1).map (List.map Check.mod3) := by decide +kernel

theorem hTab_eq : hTab = (tabH 1).map (List.map Check.mod3) := by decide +kernel

theorem getD_fTab (j : ℕ) : fTab.getD j [] = ((tabF 1).getD j []).map Check.mod3 := by
  rw [fTab_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (tabF 1)[j]? <;> rfl

theorem getD_hTab (j : ℕ) : hTab.getD j [] = ((tabH 1).getD j []).map Check.mod3 := by
  rw [hTab_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (tabH 1)[j]? <;> rfl

theorem root_toV (i : Root 1) (l : List ℕ) : root 1 i (toV l) = (rootN i l : ZMod 3) := by
  rw [← Check.dualOf_tabF, toV, Check.dualOf_vecOfList, rootN, getD_fTab, dotD_dim_one]

theorem root_toV_eq_zero_iff (i : Root 1) (l : List ℕ) :
    root 1 i (toV l) = 0 ↔ rootN i l % 3 = 0 := by
  rw [root_toV]
  constructor
  · intro h
    rw [← ZMod.val_natCast, h, ZMod.val_zero]
  · intro h
    rw [← ZMod.natCast_mod, h, Nat.cast_zero]

theorem toV_hTab (i : Root 1) : toV (hTab.getD i []) = coroot 1 i := by
  rw [toV, getD_hTab]
  exact Check.vecOfList_tabH i

theorem toV_reflN {j : ℕ} (hj : j < 24) (v : List ℕ) :
    toV (reflN j v) = reflection 1 (rootOf j) (toV v) := by
  funext k
  have hr := root_toV (rootOf j) v
  have hc := toV_hTab (rootOf j)
  rw [rootOf_val hj] at hr hc
  rw [reflection_apply, ← hc, hr]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toV_apply, reflN, getD_mk4 _ _ k.isLt]
  push_cast [ZMod.natCast_mod]
  linear_combination ((rootN j v : ZMod 3) * ((hTab.getD j []).getD k 0 : ZMod 3)) * three_eq_zero

theorem toV_bas : ∀ k : Fin (dim 1), toV (bas.getD k []) = Pi.single k 1 := by
  decide +kernel

theorem bas_getD_mem : ∀ k : Fin (dim 1), bas.getD k [] ∈ bas := by
  decide +kernel

theorem dot4_bas (r : List ℕ) {k : ℕ} (hk : k < 4) : dot4 r (bas.getD k []) = r.getD k 0 := by
  interval_cases k <;> simp [dot4, bas]

theorem root_single (i : Root 1) (k : Fin (dim 1)) :
    root 1 i (Pi.single k 1) = ((fTab.getD i []).getD k 0 : ZMod 3) := by
  rw [← toV_bas, root_toV, rootN, dot4_bas _ k.isLt]

theorem isCols_reflE {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M) {j : ℕ}
    (hj : j < 24) : IsCols (reflection 1 (rootOf j) * g) (reflE j M) := fun k => by
  rw [LinearEquiv.mul_apply, hM k, ← toV_reflN hj, reflE, getD_mk4 _ _ k.isLt]

@[expose] def genR (s : ℕ) : V 1 ≃ₗ[ZMod 3] V 1 := reflection 1 (rootOf (gens.getD s 0))

theorem gens_lt (s : ℕ) : gens.getD s 0 < 24 := by
  unfold gens
  rcases s with _ | _ | _ | _ | s <;> simp

theorem exists_isCols_of_mem_closure (h : closedOK = true) {g : V 1 ≃ₗ[ZMod 3] V 1}
    (hg : g ∈ Subgroup.closure {x | ∃ s < 4, x = genR s}) :
    ∃ n < 1152, IsCols g (elemAt n) := by
  simp only [closedOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, hcl⟩ := h
  have step : ∀ s < 4, ∀ y : V 1 ≃ₗ[ZMod 3] V 1, (∃ n < 1152, IsCols y (elemAt n)) →
      ∃ n < 1152, IsCols (genR s * y) (elemAt n) := by
    rintro s hs y ⟨n, hn, hy⟩
    have hn' := hcl n hn
    simp only [closedAt, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hn'
    obtain ⟨hlt, heq⟩ := hn' s hs
    refine ⟨idxAt n s, hlt, ?_⟩
    rw [← heq]
    exact isCols_reflE hy (gens_lt s)
  refine Subgroup.closure_induction_left (p := fun g _ => ∃ n < 1152, IsCols g (elemAt n))
    ⟨0, by decide, fun k => by rw [h0, toV_bas]; rfl⟩ ?_ ?_ hg
  · rintro _ ⟨s, hs, rfl⟩ y _ ih
    exact step s hs y ih
  · rintro _ ⟨s, hs, rfl⟩ y _ ih
    rw [show (genR s)⁻¹ = genR s from Module.reflection_inv (root_coroot 1 _)]
    exact step s hs y ih

theorem toV_applyW {w : List ℕ} (hw : ∀ j ∈ w, j < 24) (v : List ℕ) :
    toV (applyW w v) = ((w.map rootOf).map (reflection 1)).prod (toV v) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply]
    rw [← ih fun i hi => hw i (List.mem_cons_of_mem _ hi), ← toV_reflN (hw j (by simp))]
    rfl

theorem ambientNormalizer_le_closure (h : genWordsOK = true) :
    ambientNormalizer 1 ≤ Subgroup.closure {x | ∃ s < 4, x = genR s} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  simp only [genWordsOK, List.all_eq_true, List.mem_range] at h
  have hi := h i i.isLt
  simp only [genWordOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
  obtain ⟨hlt, hw⟩ := hi
  have hw24 : ∀ j ∈ (genWords.getD i []).map (gens.getD · 0), j < 24 := by
    intro j hj
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hj
    exact gens_lt s
  have heq : reflection 1 i =
      ((((genWords.getD i []).map (gens.getD · 0)).map rootOf).map (reflection 1)).prod := by
    refine (Pi.basisFun (ZMod 3) (Fin (dim 1))).ext' fun k => ?_
    rw [Pi.basisFun_apply, ← toV_bas, ← toV_applyW hw24, hw _ (bas_getD_mem k),
      toV_reflN i.isLt, rootOf_coe]
  rw [SetLike.mem_coe, heq]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact Subgroup.subset_closure ⟨s, hlt s hs, rfl⟩

theorem toV_subE (c : List ℕ) (k : Fin (dim 1)) : toV (subE c k) = toV c - Pi.single k 1 := by
  funext t
  simp only [Pi.sub_apply, toV_apply, subE, getD_mk4 _ _ t.isLt, Pi.single_apply]
  by_cases h : t = k
  · subst h
    simp only [if_true]
    push_cast
    linear_combination three_eq_zero
  · rw [if_neg fun e => h (Fin.ext e), if_neg h, add_zero]
    exact (sub_zero _).symm

theorem gammaOK_lt {M : List (List ℕ)} {j γ : ℕ} (h : gammaOK M j γ = true) : j < 24 := by
  simp only [gammaOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem root_eq_zero_of_gammaOK {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M)
    {j γ : ℕ} (h : gammaOK M j γ = true) {v : V 1} (hv : g v = v) :
    root 1 (rootOf j) v = 0 := by
  simp only [gammaOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨hj, hk⟩ := h
  have hfun : root 1 (rootOf j) + Check.dualOf 1 (decV γ) =
      (Check.dualOf 1 (decV γ)).comp g.toLinearMap := by
    refine (Pi.basisFun (ZMod 3) (Fin (dim 1))).ext fun k => ?_
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, hM k,
      root_single, rootOf_val hj, hk k k.isLt, ZMod.natCast_mod,
      ← sub_add_cancel (toV (M.getD k [])) (Pi.single k 1), ← toV_subE, map_add, toV,
      Check.dualOf_vecOfList, dotD_dim_one]
  have h := LinearMap.congr_fun hfun v
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hv] at h
  linear_combination h

theorem wordOf_spec {M : List (List ℕ)} : ∀ {c : List ℕ}, certAOK M c = true →
    ∀ j ∈ wordOf c, ∃ γ, gammaOK M j γ = true
  | [], _ => by simp [wordOf]
  | [_], h => by simp [certAOK] at h
  | j :: γ :: l, h => by
    simp only [certAOK, Bool.and_eq_true] at h
    intro i hi
    simp only [wordOf, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨γ, h.1⟩
    · exact wordOf_spec h.2 i hi

theorem fixWeylCert_of_caseAOK {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M)
    {c : List ℕ} (h : caseAOK M c = true) : FixWeylCert 1 g := by
  simp only [caseAOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hc, hw⟩ := h
  have hspec := wordOf_spec hc
  have h24 : ∀ j ∈ wordOf c, j < 24 := fun j hj => by
    obtain ⟨γ, hγ⟩ := hspec j hj
    exact gammaOK_lt hγ
  refine Or.inl ⟨(wordOf c).map rootOf, ?_, ?_⟩
  · refine (Pi.basisFun (ZMod 3) (Fin (dim 1))).ext' fun k => ?_
    rw [Pi.basisFun_apply, hM k, ← toV_bas, ← toV_applyW h24, hw k k.isLt]
  · intro i hi v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    obtain ⟨γ, hγ⟩ := hspec j hj
    exact root_eq_zero_of_gammaOK hM hγ hv

theorem toV_injective {l₁ l₂ : List ℕ} (h₁ : isDig l₁ = true) (h₂ : isDig l₂ = true)
    (h : toV l₁ = toV l₂) : l₁ = l₂ := by
  simp only [isDig, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h₁ h₂
  refine List.ext_getElem (h₁.1.trans h₂.1.symm) fun k hk₁ hk₂ => ?_
  have hk4 : k < 4 := h₁.1 ▸ hk₁
  have hk := congrFun h ⟨k, hk4⟩
  simp only [toV_apply, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₁,
    List.getElem?_eq_getElem hk₂, Option.getD_some, ZMod.natCast_eq_natCast_iff'] at hk
  rwa [Nat.mod_eq_of_lt (h₁.2 _ (List.getElem_mem hk₁)),
    Nat.mod_eq_of_lt (h₂.2 _ (List.getElem_mem hk₂))] at hk

theorem isDig_applyN (M : List (List ℕ)) (v : List ℕ) : isDig (applyN M v) = true := by
  simp [isDig, applyN, mk4, Nat.mod_lt]

theorem isDig_of_mem_allVecs {l : List ℕ} (h : l ∈ allVecs 4) : isDig l = true := by
  obtain ⟨hl, ha⟩ := mem_allVecs.1 h
  simpa [isDig, hl, List.all_eq_true] using ha

theorem exists_mem_allVecs (u : V 1) : ∃ l ∈ allVecs 4, toV l = u := by
  refine ⟨List.ofFn fun k : Fin (dim 1) => (u k).val, mem_allVecs.2 ⟨List.length_ofFn, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
    exact ZMod.val_lt _
  · funext k
    simp [toV_apply, List.getD_eq_getElem?_getD]

theorem toV_zero : toV [0, 0, 0, 0] = 0 := by
  decide +kernel

theorem toV_applyN {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M)
    (v : List ℕ) : g (toV v) = toV (applyN M v) := by
  have hM' : ∀ k, g (Pi.single k 1) = toV (M.getD k []) := hM
  have hv : toV v = ∑ k : Fin (dim 1), (v.getD k 0 : ZMod 3) • Pi.single k 1 := by
    funext t
    simp [toV_apply, Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, hM']
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toV_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (v.getD k 0 : ZMod 3) * ((M.getD k []).getD t 0 : ZMod 3))
    (dim 1), show Finset.range (dim 1) = Finset.range 4 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, applyN, getD_mk4 _ _ t.isLt]
  push_cast [ZMod.natCast_mod]
  ring

theorem adjTab_testBit : ∀ i j : Root 1, Adj 1 i j → (adjTab.getD i 0).testBit j = true := by
  unfold Adj
  decide +kernel

theorem splitAt_of_splitOK {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M)
    {u : List ℕ} {mask : ℕ} {x₁ x₂ : List ℕ} (h : splitOK M u mask x₁ x₂ = true) :
    SplitAt 1 g (toV u) := by
  simp only [splitOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hcl, hd₁⟩, hx₁⟩, hm₁⟩, hd₂⟩, hx₂⟩, hm₂⟩ := h
  refine ⟨Finset.univ.filter fun i : Root 1 => mask.testBit i = true, ?_, ⟨toV x₁, ?_, ?_⟩,
    toV x₂, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hcl i i.isLt with hf | hall
    · simp [hi] at hf
    · rcases hall j j.isLt with (hr | ha) | hm
      · exact absurd ((root_toV_eq_zero_iff j u).1 hj) hr
      · rw [adjTab_testBit i j hij] at ha
        exact absurd ha (by decide)
      · exact hm
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hx₁ i i.isLt with hf | hr
    · simp [hi] at hf
    · exact (root_toV_eq_zero_iff i x₁).2 hr
  · rw [toV_applyN hM]
    exact fun e => hm₁ (toV_injective (isDig_applyN M x₁) hd₁ e)
  · intro i hi hi₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁
    rcases hx₂ i i.isLt with (hr | hm) | hr
    · exact absurd ((root_toV_eq_zero_iff i u).1 hi) hr
    · exact absurd hm hi₁
    · exact (root_toV_eq_zero_iff i x₂).2 hr
  · rw [toV_applyN hM]
    exact fun e => hm₂ (toV_injective (isDig_applyN M x₂) hd₂ e)

theorem fixWeylCert_of_caseBOK {g : V 1 ≃ₗ[ZMod 3] V 1} {M : List (List ℕ)} (hM : IsCols g M)
    {n : ℕ} (h : caseBOK n M = true) : FixWeylCert 1 g := by
  refine Or.inr fun u hu hu0 => ?_
  obtain ⟨l, hl, rfl⟩ := exists_mem_allVecs u
  simp only [caseBOK, List.all_eq_true] at h
  have h' := h l hl
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true,
    Bool.and_eq_true] at h'
  rcases h' with (h0 | hfix) | ⟨r, -, -, hr⟩
  · exact absurd (h0 ▸ toV_zero) hu0
  · exact absurd (toV_injective (isDig_applyN M l) (isDig_of_mem_allVecs hl)
      ((toV_applyN hM l).symm.trans hu)) hfix
  · exact splitAt_of_splitOK hM hr

theorem fixWeylCert_of_certOK {n : ℕ} (h : certOK n = true) {g : V 1 ≃ₗ[ZMod 3] V 1}
    (hg : IsCols g (elemAt n)) : FixWeylCert 1 g := by
  unfold certOK at h
  split at h
  · exact fixWeylCert_of_caseBOK hg h
  · exact fixWeylCert_of_caseAOK hg h

theorem fixWeylCert_of_allOK (h : allOK = true) {g : V 1 ≃ₗ[ZMod 3] V 1}
    (hg : g ∈ ambientNormalizer 1) : FixWeylCert 1 g := by
  simp only [allOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hcl, hw⟩, hc⟩ := h
  obtain ⟨n, hn, hM⟩ := exists_isCols_of_mem_closure hcl (ambientNormalizer_le_closure hw hg)
  exact fixWeylCert_of_certOK (hc n hn) hM

end CFSG.StandardType.GGQ2Frame.ExcRaw.FixWeylOne
