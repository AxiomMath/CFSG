module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Ch3E213M.G41.Refl

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OutcomeLocal (sumZero sumZeroEquiv onesLine heartRep
  heartRep_apply_mk permCoord_apply permCoord_swap coe_sumZeroEquiv mem_onesLine)

local notation "V₀" => Fin 4 → ZMod 2
local notation "GL₀" => LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)} {b : Fin 4 → Fin 4 → k}

theorem mem_sum6 {x : Fin 6 → ZMod 2} :
    x ∈ sumZero 6 ↔ x 0 + x 1 + x 2 + x 3 + x 4 + x 5 = 0 := by
  change ∑ i, x i = 0 ↔ _
  rw [Fin.sum_univ_six]

@[expose] def pairVec (i j : Fin 6) : Fin 6 → ZMod 2 :=
  fun l => if l = i ∨ l = j then 1 else 0

theorem heart_pair : ∀ y : Fin 6 → ZMod 2, y 0 + y 1 + y 2 + y 3 + y 4 + y 5 = 0 →
    (∀ c : ZMod 2, y ≠ fun _ => c) →
    ∃ i j : Fin 6, i ≠ j ∧ ∃ c : ZMod 2, ∀ l, y l = pairVec i j l + c := by
  decide

theorem pairVec_sum : ∀ i j : Fin 6, i ≠ j → pairVec i j 0 + pairVec i j 1 + pairVec i j 2 +
    pairVec i j 3 + pairVec i j 4 + pairVec i j 5 = 0 := by
  decide

theorem single_add_single : ∀ i j : Fin 6, i ≠ j →
    (Pi.single i 1 + Pi.single j 1 : Fin 6 → ZMod 2) = pairVec i j := by
  decide

theorem exists_third : ∀ i j : Fin 6, ∃ l : Fin 6, l ≠ i ∧ l ≠ j := by
  decide

theorem swap_pairVec_ne : ∀ i j l : Fin 6, i ≠ j → l ≠ i → l ≠ j → ∀ c : ZMod 2,
    (fun m => pairVec i l (Equiv.swap i j m) - pairVec i l m) ≠ fun _ => c := by
  decide

theorem heartRep_swap_ne_one {i j : Fin 6} (hij : i ≠ j) : heartRep 6 (Equiv.swap i j) ≠ 1 := by
  intro h1
  obtain ⟨l, hil, hjl⟩ := exists_third i j
  let w' : sumZero 6 := ⟨pairVec i l, mem_sum6.mpr (pairVec_sum i l (Ne.symm hil))⟩
  have hfix := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6) =>
    (g : (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6))
      (Submodule.Quotient.mk w')) h1
  change Submodule.Quotient.mk (sumZeroEquiv (Equiv.swap i j) w') = Submodule.Quotient.mk w'
    at hfix
  rw [Submodule.Quotient.eq, mem_onesLine] at hfix
  obtain ⟨c, hc⟩ := hfix
  refine swap_pairVec_ne i j l hij hil hjl c (funext fun m => ?_)
  have hm := congrFun hc m
  rw [Submodule.coe_sub, Pi.sub_apply, coe_sumZeroEquiv, permCoord_apply, Equiv.swap_inv] at hm
  exact hm

theorem all_of_sym6 [Finite k] (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) {β : V₀ ≃ₗ[ZMod 2] sumZero 6 ⧸ onesLine 6}
    (hβ : (grp G₀ b).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (heartRep 6).range) (v : V₀) (hv : v ≠ 0) : emb b v ∈ normC G₀ := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (onesLine 6) (β v)
  have hyc : ∀ c : ZMod 2, (y : Fin 6 → ZMod 2) ≠ fun _ => c := by
    intro c hc
    apply hv
    apply β.injective
    rw [map_zero, ← hy, Submodule.Quotient.mk_eq_zero]
    exact mem_onesLine.mpr ⟨c, hc⟩
  obtain ⟨i, j, hij, c, hc⟩ := heart_pair y (mem_sum6.mp y.2) hyc
  let w : sumZero 6 := ⟨pairVec i j, mem_sum6.mpr (pairVec_sum i j hij)⟩
  have hwv : Submodule.Quotient.mk w = β v := by
    rw [← hy, Submodule.Quotient.eq]
    refine mem_onesLine.mpr ⟨c, funext fun l => ?_⟩
    rw [Submodule.coe_sub, Pi.sub_apply, hc l]
    change pairVec i j l - (pairVec i j l + c) = c
    linear_combination (-c) * h2
  obtain ⟨h, hhG, hh⟩ : ∃ h ∈ grp G₀ b,
      LinearMap.GeneralLinearGroup.congrLinearEquiv β h = heartRep 6 (Equiv.swap i j) := by
    have hmem : heartRep 6 (Equiv.swap i j) ∈
        (grp G₀ b).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom := by
      rw [hβ]
      exact ⟨_, rfl⟩
    obtain ⟨h, hhG, hh⟩ := hmem
    exact ⟨h, hhG, hh⟩
  have hact : ∀ x, β (((h : GL₀) : V₀ →ₗ[ZMod 2] V₀) x) =
      ((heartRep 6 (Equiv.swap i j) : LinearMap.GeneralLinearGroup (ZMod 2) _) :
        (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) (β x) := by
    intro x
    rw [← hh]
    change _ = β (((h : GL₀) : V₀ →ₗ[ZMod 2] V₀) (β.symm (β x)))
    rw [LinearEquiv.symm_apply_apply]
  have hswap : ∀ z : sumZero 6 ⧸ onesLine 6, ∃ c : ZMod 2,
      ((heartRep 6 (Equiv.swap i j) : LinearMap.GeneralLinearGroup (ZMod 2) _) :
        (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) z =
        z + c • Submodule.Quotient.mk w := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨(z : Fin 6 → ZMod 2) i + (z : Fin 6 → ZMod 2) j, ?_⟩
      rw [heartRep_apply_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      rw [coe_sumZeroEquiv, permCoord_swap, single_add_single i j hij]
      rfl
  refine mem_normC_of_lift hF hb hli (grp_le_liftSub hF hb hli hhG)
    (fun h1 => heartRep_swap_ne_one hij (by rw [← hh, h1, map_one])) hv fun x => ?_
  obtain ⟨c', hc'⟩ := hswap (β x)
  refine ⟨c', β.injective ?_⟩
  rw [hact, hc', map_add, map_smul, hwv]

theorem f2_dichotomy [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b) :
    (∀ v : V₀, v ≠ 0 → emb b v ∈ normC G₀) ∨
      ∃ Q : QuadraticForm (ZMod 2) V₀,
        (∀ x y, QuadraticMap.polar Q x y = f0 b x y) ∧ ∀ r ∈ normC G₀, Q (pre b r) = 1 := by
  rcases mcl_outcomes hirr hF hb hli with h | ⟨f, hnd, halt, h⟩ | ⟨Q, hnd, h⟩ | ⟨β, h⟩ | ⟨β, h⟩
  · exact Or.inl (all_of_top hF hb hli h)
  · exact Or.inl (all_of_sp hF hb hli hnd halt h)
  · exact Or.inr ⟨Q, quad_of_orth hF hb hli hnd h⟩
  · exact Or.inr (quad_of_sym5 hF hb hli h)
  · exact Or.inl (all_of_sym6 hF hb hli h)

@[expose] def InF (b : Fin 4 → Fin 4 → k) (y : Fin 4 → k) : Prop :=
  ∃ x, emb b x = y

theorem InF.add {y z : Fin 4 → k} (hy : InF b y) (hz : InF b z) : InF b (y + z) := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨x', rfl⟩ := hz
  exact ⟨x + x', emb_add x x'⟩

theorem InF.smul {y : Fin 4 → k} (hy : InF b y) {c : k} (hc : c = 0 ∨ c = 1) : InF b (c • y) := by
  rcases hc with rfl | rfl
  · exact ⟨0, by rw [emb_zero, zero_smul]⟩
  · rwa [one_smul]

theorem InF.perp {x y m : Fin 4 → k} (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hx : InF b x) (hy : InF b y) (hm : InF b m) : InF b (G41.perpPart x y m) := by
  have hval : ∀ {u v : Fin 4 → k}, InF b u → InF b v → spBil u v = 0 ∨ spBil u v = 1 := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact bil_emb_eq_zero_or_one hF hb u v
  have h := eq_perpPart x y m
  rw [show G41.perpPart x y m = m + (spBil m y • x + spBil m x • y) by
    funext i
    have hi := congrFun h i
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination -hi - (spBil m y * x i + spBil m x * y i) * h2]
  exact hm.add ((hx.smul (hval hm hy)).add (hy.smul (hval hm hx)))

theorem exists_sympBasis (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) :
    ∃ e : Fin 4 → Fin 4 → k, (∀ s t, spBil (e s) (e t) = minorJ k s t) ∧ ∀ j, InF b (e j) := by
  classical
  have hval : ∀ {u v : Fin 4 → k}, InF b u → InF b v → spBil u v = 0 ∨ spBil u v = 1 := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact bil_emb_eq_zero_or_one hF hb u v
  have hbF : ∀ j, InF b (b j) := fun j => ⟨Pi.single j 1, emb_single j⟩
  have hnz : ∀ {u : Fin 4 → k}, u ≠ 0 → ∃ j, spBil u (b j) ≠ 0 := fun {u} hu => by
    by_contra hall
    push Not at hall
    exact hu (eq_of_bil_basis hli fun j => by rw [hall j, LinearMap.map_zero₂])
  obtain ⟨j₃, hj₃⟩ := hnz (hb 0).1
  have h03 : spBil (b 0) (b j₃) = 1 := (hval (hbF 0) (hbF j₃)).resolve_left hj₃
  obtain ⟨p, hp⟩ : ∃ p : Fin 4 → Fin 4 → k, ∀ l, p l = perpPart (b 0) (b j₃) (b l) :=
    ⟨_, fun _ => rfl⟩
  have hpF : ∀ l, InF b (p l) := fun l => hp l ▸ InF.perp hF hb (hbF 0) (hbF j₃) (hbF l)
  have hp0 : ∀ l, spBil (p l) (b 0) = 0 := fun l => hp l ▸ (perpPart_perp h03 (b l)).1
  have hp3 : ∀ l, spBil (p l) (b j₃) = 0 := fun l => hp l ▸ (perpPart_perp h03 (b l)).2
  have hpb : ∀ {u : Fin 4 → k}, spBil u (b 0) = 0 → spBil u (b j₃) = 0 → ∀ l,
      spBil u (b l) = spBil u (p l) := fun {u} hu0 hu3 l => by
    conv_lhs => rw [eq_perpPart (b 0) (b j₃) (b l), ← hp l]
    rw [map_add, map_add, map_smul, map_smul, hu0, hu3, smul_zero, smul_zero, zero_add, zero_add]
  obtain ⟨l₁, hl₁⟩ : ∃ l, p l ≠ 0 := by
    by_contra hall
    push Not at hall
    have hle : Submodule.span k (Set.range b) ≤ Submodule.span k {b 0, b j₃} := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      rw [eq_perpPart (b 0) (b j₃) (b l), ← hp l, hall l, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [span_range_eq_top hli] at hle
    have h4 := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun] at h4
    have h2 := finrank_span_finset_le_card (R := k) ({b 0, b j₃} : Finset (Fin 4 → k))
    rw [Finset.coe_insert, Finset.coe_singleton] at h2
    change Module.finrank k (Submodule.span k {b 0, b j₃}) ≤ _ at h2
    have h2' := Finset.card_insert_le (b 0) ({b j₃} : Finset (Fin 4 → k))
    rw [Finset.card_singleton] at h2'
    omega
  obtain ⟨l₂, hl₂⟩ := hnz hl₁
  rw [hpb (hp0 l₁) (hp3 l₁)] at hl₂
  have h12 : spBil (p l₁) (p l₂) = 1 := (hval (hpF l₁) (hpF l₂)).resolve_left hl₂
  refine ⟨![b 0, p l₁, p l₂, b j₃], fun s t => ?_, fun j => ?_⟩
  · have hs : ∀ u v : Fin 4 → k, spBil u v = spBil v u := bil_symm
    fin_cases s <;> fin_cases t <;>
      simp [minorJ_apply, bil_self, h03, h12, hp0, hp3, hs (b j₃) (b 0), hs (p l₂) (p l₁),
        hs (b 0) (p _), hs (b j₃) (p _)]
  · fin_cases j
    exacts [hbF 0, hpF l₁, hpF l₂, hbF j₃]

theorem InF.sum4 {c : Fin 4 → k} (hc : ∀ j, c j = 0 ∨ c j = 1) {e : Fin 4 → Fin 4 → k}
    (he : ∀ j, InF b (e j)) : InF b (∑ j, c j • e j) := by
  rw [Fin.sum_univ_four]
  exact ((((he 0).smul (hc 0)).add ((he 1).smul (hc 1))).add ((he 2).smul (hc 2))).add
    ((he 3).smul (hc 3))

theorem eq_zero_or_one_of_mem_fix {x : k} (hx : x ∈ fixField k 1) : x = 0 ∨ x = 1 := by
  rw [mem_fixField, pow_one] at hx
  have h : x * (x - 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem mem_fix_of {x : k} (hx : x = 0 ∨ x = 1) : x ∈ fixField k 1 := by
  rw [mem_fixField]
  rcases hx with rfl | rfl <;> simp

theorem spW_of_all [Finite k] (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) (hall : ∀ v : V₀, v ≠ 0 → emb b v ∈ normC G₀) : G41SpW G₀ := by
  obtain ⟨e, he, heF⟩ := exists_sympBasis hF hb hli
  have hval : ∀ {u v : Fin 4 → k}, InF b u → InF b v → spBil u v = 0 ∨ spBil u v = 1 := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact bil_emb_eq_zero_or_one hF hb u v
  have hnorm : ∀ {y : Fin 4 → k}, InF b y → y ≠ 0 → y ∈ normC G₀ := by
    rintro _ ⟨x, rfl⟩ hy
    exact hall x fun h => hy (by rw [h, emb_zero])
  have hne : ∀ j, e j ≠ 0 := by
    intro j h0
    have h1 := he j (Fin.rev j)
    have h3 : (j : ℕ) + (4 - ((j : ℕ) + 1)) = 3 := by omega
    rw [h0, LinearMap.map_zero₂, minorJ_apply, Fin.val_rev] at h1
    simp only [h3, ↓reduceIte] at h1
    exact zero_ne_one h1
  refine ⟨fixField k 1, ofBasis e he, le_antisymm (fun g hg => ?_) ?_⟩
  · refine ⟨(ofBasis e he)⁻¹ * g * ofBasis e he, fun i j => ?_, ?_⟩
    · rw [← act_single_apply, natAct_mul, natAct_mul, act_ofBasis_single,
        coord_eq_bil (natAct (ofBasis e he)⁻¹ (natAct g (e j))) i, bil_act_inv,
        act_ofBasis_single]
      have hgej : InF b (natAct g (e j)) :=
        exists_emb_eq hF hb hli (act_mem_normC (hnorm (heF j) (hne j)) hg)
      exact mem_fix_of (hval hgej (heF _))
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro _ ⟨g₀, hg₀, rfl⟩
    have hcl := subfieldSp_le_closure (fixField k 1) hg₀
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj (ofBasis e he)).toMonoidHom hcl
    rw [MonoidHom.map_closure] at hmap
    refine (Subgroup.closure_le G₀).mpr ?_ hmap
    rintro _ ⟨_, ⟨v, c, rfl⟩, rfl⟩
    change ofBasis e he * trv (fun i => (v i : k)) (c : k) * (ofBasis e he)⁻¹ ∈ G₀
    rw [conj_trv, act_ofBasis]
    have hvF : InF b (∑ j, (v j : k) • e j) :=
      InF.sum4 (fun j => eq_zero_or_one_of_mem_fix (v j).2) heF
    by_cases h0 : ∑ j, (v j : k) • e j = 0
    · rw [h0, trv_zero_left]
      exact G₀.one_mem
    · rcases eq_zero_or_one_of_mem_fix c.2 with hc | hc
      · rw [hc, trv_zero]
        exact G₀.one_mem
      · rw [hc]
        exact (hnorm hvF h0).2

@[expose] noncomputable def basisB (hli : LinearIndependent k b) :
    Module.Basis (Fin 4) k (Fin 4 → k) :=
  Module.Basis.mk hli (le_of_eq (span_range_eq_top hli).symm)

omit [CharP k 2] in
theorem basisB_apply (hli : LinearIndependent k b) (j : Fin 4) : basisB hli j = b j :=
  Module.Basis.mk_apply _ _ j

@[expose] noncomputable def extMat (b : Fin 4 → Fin 4 → k) (Q : QuadraticForm (ZMod 2) V₀) :
    Matrix (Fin 4) (Fin 4) k :=
  Matrix.of fun i j =>
    if i < j then spBil (b i) (b j) else if i = j then c2 (Q (Pi.single i 1)) else 0

@[expose] noncomputable def extQ (hli : LinearIndependent k b) (Q : QuadraticForm (ZMod 2) V₀) :
    QuadraticForm k (Fin 4 → k) :=
  (Matrix.toBilin (basisB hli) (extMat b Q)).toQuadraticMap

theorem toBilin_extMat (hli : LinearIndependent k b) (Q : QuadraticForm (ZMod 2) V₀)
    (i j : Fin 4) : Matrix.toBilin (basisB hli) (extMat b Q) (b i) (b j) = extMat b Q i j := by
  rw [← basisB_apply hli i, ← basisB_apply hli j, ← LinearMap.BilinForm.toMatrix_apply,
    LinearMap.BilinForm.toMatrix_toBilin]

theorem polar_extQ (hli : LinearIndependent k b) (Q : QuadraticForm (ZMod 2) V₀)
    (x y : Fin 4 → k) : QuadraticMap.polar (extQ hli Q) x y = spBil x y := by
  have h : Matrix.toBilin (basisB hli) (extMat b Q) +
      (Matrix.toBilin (basisB hli) (extMat b Q)).flip = spBil := by
    refine LinearMap.BilinForm.ext_basis (basisB hli) fun i j => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.BilinForm.flip_apply, basisB_apply,
      basisB_apply, toBilin_extMat, toBilin_extMat]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [extMat, hij, not_lt.mpr hij.le, hij.ne']
    · simp only [extMat, Matrix.of_apply, lt_irrefl, ↓reduceIte, bil_self]
      exact CharTwo.add_self_eq_zero _
    · simp [extMat, hij, not_lt.mpr hij.le, hij.ne', bil_symm (b i) (b j)]
  rw [extQ, LinearMap.BilinMap.polar_toQuadraticMap, ← h, LinearMap.add_apply,
    LinearMap.add_apply, LinearMap.BilinForm.flip_apply]

theorem extQ_emb (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    (Q : QuadraticForm (ZMod 2) V₀) (hpol : ∀ x y, QuadraticMap.polar Q x y = f0 b x y)
    (x : V₀) : extQ hli Q (emb b x) = c2 (Q x) := by
  let D : V₀ →+ k := AddMonoidHom.mk' (fun x => extQ hli Q (emb b x) - c2 (Q x)) fun x y => by
    have h1 : extQ hli Q (emb b x + emb b y) =
        extQ hli Q (emb b x) + extQ hli Q (emb b y) + spBil (emb b x) (emb b y) := by
      rw [← polar_extQ hli Q]
      unfold QuadraticMap.polar
      ring
    have h2 : Q (x + y) = Q x + Q y + f0 b x y := by
      rw [← hpol]
      unfold QuadraticMap.polar
      ring
    change extQ hli Q (emb b (x + y)) - c2 (Q (x + y)) =
      (extQ hli Q (emb b x) - c2 (Q x)) + (extQ hli Q (emb b y) - c2 (Q y))
    rw [emb_add, h1, h2, map_add, map_add, bil_emb hF hb]
    ring
  have hD : D x = 0 := by
    rw [← Finset.univ_sum_single x, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases zmod2_cases (x j) with h | h
    · rw [h, Pi.single_zero, map_zero]
    · rw [h]
      change extQ hli Q (emb b (Pi.single j 1)) - c2 (Q (Pi.single j 1)) = 0
      rw [emb_single, extQ, LinearMap.BilinMap.toQuadraticMap_apply, toBilin_extMat]
      simp [extMat]
  exact sub_eq_zero.mp hD

theorem orthW_of_quad (hspan : Submodule.span k (normC G₀) = ⊤) (hF : F2Vals G₀)
    (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b) (Q : QuadraticForm (ZMod 2) V₀)
    (hpol : ∀ x y, QuadraticMap.polar Q x y = f0 b x y)
    (hQ : ∀ r ∈ normC G₀, Q (pre b r) = 1) : G41OrthW G₀ :=
  orthW_of_forall hspan (extQ hli Q) (polar_extQ hli Q) fun r hr => by
    rw [← emb_pre hF hb hli hr, extQ_emb hF hb hli Q hpol, hQ r hr, map_one]

end CFSG.Quasithin.Ch3E213M.G41.Refl

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem factSp4TransvRefl_of_big (hBig : FactSp4ReflBig) : FactSp4TransvRefl := by
  intro k _ _ _ G₀ hirr hD hone
  by_cases hbig : ∃ r s : Fin 4 → k, trv r 1 ∈ G₀ ∧ trv s 1 ∈ G₀ ∧ spBil r s ≠ 0 ∧ spBil r s ≠ 1
  · exact Or.inr (hBig k G₀ hirr hD hone hbig)
  · have hF : Refl.F2Vals G₀ := fun r hr s hs => by
      by_contra h
      push Not at h
      exact hbig ⟨r, s, hr.2, hs.2, h.1, h.2⟩
    have hspan := Refl.span_normC hirr hD
    obtain ⟨b, hb, hli⟩ := Refl.exists_basis hspan
    rcases Refl.f2_dichotomy hirr hF hb hli with hall | ⟨Q, hpol, hQ⟩
    · exact Or.inl (Refl.spW_of_all hF hb hli hall)
    · exact Or.inr (Refl.orthW_of_quad hspan hF hb hli Q hpol hQ)

end CFSG.Quasithin.Ch3E213M.G41
