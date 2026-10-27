module

public import CFSG.Quasithin.Background.SmithB45J2Zorn
public import CFSG.Quasithin.Background.SmithB45J2RowModel
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Model CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour CFSG.Open CFSG.Quasithin.H
open scoped Matrix

section Proj

variable {F : Type} [Field F]

@[expose] def qProj (x : quasithinZorn F) : Fin 6 → F :=
  ![x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2]

@[expose] def qIncl (w : Fin 6 → F) : quasithinZorn F :=
  (0, ![w 0, w 1, w 2], ![w 3, w 4, w 5], 0)

theorem qProj_qIncl (w : Fin 6 → F) : qProj (qIncl w) = w := by
  funext i
  fin_cases i <;> rfl

@[expose] def qProjL : quasithinZorn F →ₗ[F] (Fin 6 → F) where
  toFun := qProj
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl

@[expose] def qInclL : (Fin 6 → F) →ₗ[F] quasithinZorn F where
  toFun := qIncl
  map_add' x y := by
    refine Prod.ext (by simp [qIncl]) (Prod.ext ?_ (Prod.ext ?_ (by simp [qIncl]))) <;>
      funext i <;> fin_cases i <;> rfl
  map_smul' c x := by
    refine Prod.ext (by simp [qIncl]) (Prod.ext ?_ (Prod.ext ?_ (by simp [qIncl]))) <;>
      funext i <;> fin_cases i <;> rfl

theorem qProj_zornOne : qProj (zornOne : quasithinZorn F) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem eq_qIncl_add [CharP F 2] {x : quasithinZorn F} (hx : x.1 + x.2.2.2 = 0) :
    x = qIncl (qProj x) + x.1 • zornOne := by
  have hs : x.2.2.2 = x.1 := by
    have := eq_neg_of_add_eq_zero_right hx
    rw [this, CharTwo.neg_eq]
  obtain ⟨r, u, v, s⟩ := x
  simp only at hs
  subst hs
  refine Prod.ext (by simp [qIncl, zornOne]) (Prod.ext ?_ (Prod.ext ?_ (by simp [qIncl, zornOne])))
  · funext i
    fin_cases i <;> simp [qIncl, qProj, zornOne]
  · funext i
    fin_cases i <;> simp [qIncl, qProj, zornOne]

@[expose] def qLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) : (Fin 6 → F) →ₗ[F] (Fin 6 → F) :=
  qProjL ∘ₗ (g : quasithinZorn F →ₗ[F] quasithinZorn F) ∘ₗ qInclL

theorem qLin_apply (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) (w : Fin 6 → F) :
    qLin g w = qProj (g (qIncl w)) := rfl

theorem trace_qIncl (w : Fin 6 → F) : (qIncl w).1 + (qIncl w).2.2.2 = 0 := by
  simp [qIncl]

variable [CharP F 2]

theorem qProj_apply {g : quasithinZorn F ≃ₗ[F] quasithinZorn F} (hg : g ∈ quasithinG2 F)
    {x : quasithinZorn F} (hx : x.1 + x.2.2.2 = 0) : qProj (g x) = qLin g (qProj x) := by
  conv_lhs => rw [eq_qIncl_add hx]
  have h1 : g zornOne = zornOne := (mem_quasithinG2_isZornAuto hg).map_one
  rw [map_add, map_smul, h1]
  change qProjL (g (qIncl (qProj x)) + x.1 • zornOne) = _
  rw [map_add, map_smul]
  change qLin g (qProj x) + x.1 • qProj zornOne = _
  rw [qProj_zornOne, smul_zero, add_zero]

theorem qLin_mul {g h : quasithinZorn F ≃ₗ[F] quasithinZorn F} (hg : g ∈ quasithinG2 F)
    (hh : h ∈ quasithinG2 F) : qLin (g * h) = qLin g ∘ₗ qLin h := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, qLin_apply, qLin_apply, qLin_apply]
  have htr := (mem_quasithinG2_isZornAuto hh).trace_zero (trace_qIncl w)
  exact qProj_apply hg htr

omit [CharP F 2] in
theorem qLin_one : qLin (1 : quasithinZorn F ≃ₗ[F] quasithinZorn F) = LinearMap.id :=
  LinearMap.ext fun w => qProj_qIncl w

theorem qLin_comp_inv (g : ↥(quasithinG2 F)) :
    qLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∘ₗ
      qLin ((g⁻¹ : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) = LinearMap.id := by
  rw [← qLin_mul g.2 (g⁻¹).2]
  have e : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) *
      ((g⁻¹ : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  rw [e, qLin_one]

theorem qLin_inv_comp (g : ↥(quasithinG2 F)) :
    qLin ((g⁻¹ : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∘ₗ
      qLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) = LinearMap.id := by
  rw [← qLin_mul (g⁻¹).2 g.2]
  have e : ((g⁻¹ : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) *
      (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  rw [e, qLin_one]

@[expose] noncomputable def qHom : ↥(quasithinG2 F) →* Matrix.GeneralLinearGroup (Fin 6) F where
  toFun g := ⟨LinearMap.toMatrix' (qLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F)),
    LinearMap.toMatrix' (qLin ((g⁻¹ : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F)),
    by rw [← LinearMap.toMatrix'_comp, qLin_comp_inv, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, qLin_inv_comp, LinearMap.toMatrix'_id]⟩
  map_one' := Units.ext (by
    change LinearMap.toMatrix' (qLin (1 : quasithinZorn F ≃ₗ[F] quasithinZorn F)) = 1
    rw [qLin_one, LinearMap.toMatrix'_id])
  map_mul' g h := Units.ext (by
    change LinearMap.toMatrix'
        (qLin ((g * h : ↥(quasithinG2 F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F)) =
      LinearMap.toMatrix' (qLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F)) *
        LinearMap.toMatrix' (qLin (h : quasithinZorn F ≃ₗ[F] quasithinZorn F))
    rw [Subgroup.coe_mul, qLin_mul g.2 h.2, LinearMap.toMatrix'_comp])

theorem qHom_mulVec (g : ↥(quasithinG2 F)) (w : Fin 6 → F) :
    ((qHom g : Matrix.GeneralLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ w = qLin g w :=
  LinearMap.toMatrix'_mulVec _ _

end Proj

@[expose] noncomputable def qHomJ : ↥j2Γ₀ →* GL6 :=
  qHom.comp (Subgroup.inclusion j2Γ₀_le_quasithinG2)

theorem j2EquivA_mem : j2EquivA ∈ j2Γ₀ := by
  rw [j2Γ₀_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem j2EquivB_mem : j2EquivB ∈ j2Γ₀ := by
  rw [j2Γ₀_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem qLin_A_bool : (List.finRange 6).all (fun i => (List.finRange 6).all fun j =>
    qProj (j2EquivA (qIncl (Pi.single j (1 : FieldFour)))) i == a6.toMat i j) = true := by
  decide +kernel

theorem qLin_B_bool : (List.finRange 6).all (fun i => (List.finRange 6).all fun j =>
    qProj (j2EquivB (qIncl (Pi.single j (1 : FieldFour)))) i == b6.toMat i j) = true := by
  decide +kernel

theorem qLin_A_check (i j : Fin 6) :
    qProj (j2EquivA (qIncl (Pi.single j (1 : FieldFour)))) i = a6.toMat i j := by
  have h := qLin_A_bool
  simp only [List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq] at h
  exact h i j

theorem qLin_B_check (i j : Fin 6) :
    qProj (j2EquivB (qIncl (Pi.single j (1 : FieldFour)))) i = b6.toMat i j := by
  have h := qLin_B_bool
  simp only [List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq] at h
  exact h i j

theorem qHomJ_A : qHomJ ⟨j2EquivA, j2EquivA_mem⟩ = gA := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change LinearMap.toMatrix' (qLin j2EquivA) i j = a6.toMat i j
  rw [LinearMap.toMatrix'_apply, qLin_apply]
  exact qLin_A_check i j

theorem qHomJ_B : qHomJ ⟨j2EquivB, j2EquivB_mem⟩ = gB := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change LinearMap.toMatrix' (qLin j2EquivB) i j = b6.toMat i j
  rw [LinearMap.toMatrix'_apply, qLin_apply]
  exact qLin_B_check i j

theorem range_qHomJ : qHomJ.range = Γ₆ := by
  have htop : (⊤ : Subgroup ↥j2Γ₀) = Subgroup.closure
      {⟨j2EquivA, j2EquivA_mem⟩, ⟨j2EquivB, j2EquivB_mem⟩} := by
    symm
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' := hx
    rw [j2Γ₀_eq] at hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz =>
      have hy' : y ∈ j2Γ₀ := by rw [j2Γ₀_eq]; exact hy
      have hz' : z ∈ j2Γ₀ := by rw [j2Γ₀_eq]; exact hz
      exact Subgroup.mul_mem _ (ihy hy') (ihz hz')
    | inv y hy ihy =>
      have hy' : y ∈ j2Γ₀ := by rw [j2Γ₀_eq]; exact hy
      exact Subgroup.inv_mem _ (ihy hy')
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, Γ₆]
  congr 1
  ext g
  simp only [Set.image_insert_eq, Set.image_singleton, qHomJ_A, qHomJ_B]

theorem qHomJ_mem (γ : ↥j2Γ₀) : qHomJ γ ∈ Γ₆ := by
  rw [← range_qHomJ]
  exact ⟨γ, rfl⟩

section Realize

variable {V : Type} [CommGroup V]

@[expose] noncomputable def qQuot : ↥(zornO0 FieldFour) ⧸ (zornR FieldFour).subgroupOf
    (zornO0 FieldFour) →* W6 :=
  QuotientGroup.lift _
    { toFun := fun m => Multiplicative.ofAdd (qProj (Multiplicative.toAdd (m : Multiplicative
        (quasithinZorn FieldFour))))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl
      map_mul' := fun m n => by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl }
    (by
      rintro ⟨m, hm⟩ hR
      obtain ⟨c, hc⟩ := hR
      have hc' : Multiplicative.toAdd m = (c, 0, 0, c) := hc
      apply Multiplicative.toAdd.injective
      change qProj (Multiplicative.toAdd m) = 0
      rw [hc']
      funext i
      fin_cases i <;> rfl)

theorem qQuot_mk (m : ↥(zornO0 FieldFour)) :
    qQuot (QuotientGroup.mk m) = Multiplicative.ofAdd (qProj (Multiplicative.toAdd
      (m : Multiplicative (quasithinZorn FieldFour)))) := rfl

theorem qQuot_bijective : Function.Bijective qQuot := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H m =>
      rw [qQuot_mk] at hq
      have h1 : qProj (Multiplicative.toAdd (m : Multiplicative (quasithinZorn FieldFour))) = 0 :=
        congrArg Multiplicative.toAdd hq
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      obtain ⟨x, hx⟩ := m
      set y := Multiplicative.toAdd x with hy
      have htr : y.1 + y.2.2.2 = 0 := hx
      have hdec := eq_qIncl_add htr
      refine ⟨y.1, ?_⟩
      change Multiplicative.toAdd x = _
      rw [← hy, hdec]
      rw [h1]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [qIncl, zornOne]
      · funext i
        fin_cases i <;> simp [qIncl, zornOne]
      · funext i
        fin_cases i <;> simp [qIncl, zornOne]
      · simp [qIncl, zornOne]
  · intro w
    refine ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (qIncl (Multiplicative.toAdd w)),
      trace_qIncl _⟩, ?_⟩
    rw [qQuot_mk]
    exact congrArg Multiplicative.ofAdd (qProj_qIncl _)

theorem exists_equiv_of_zornQ {L : Subgroup (MulAut V)} {π : ↥j2Γ₀ →* ↥L}
    (h : (FFModel.zornQ j2Γ₀).RealizesVia L ⊤ ⊥ π) :
    ∃ e : V ≃* W6, ∀ (γ : ↥j2Γ₀) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = matHom (qHomJ γ) (e v) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : V ≃* W6 := Subgroup.topEquiv.symm.trans
    ((MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans (MulEquiv.ofBijective qQuot qQuot_bijective))
  refine ⟨e, fun γ v => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, trivial⟩)
  have hm' : (FFModel.zornQ j2Γ₀).act γ m.1 ∈ (FFModel.zornQ j2Γ₀).sec :=
    zornAct_mem_O0 _ j2Γ₀_le_quasithinG2 γ m.2
  have h1 : β ⟨((π γ : ↥L) : MulAut V) v, trivial⟩ = QuotientGroup.mk ⟨_, hm'⟩ :=
    hβe γ ⟨v, trivial⟩ m trivial hm' hm.symm
  have hev : e v = qQuot (β ⟨v, trivial⟩) := rfl
  have hepv : e (((π γ : ↥L) : MulAut V) v) =
      qQuot (β ⟨((π γ : ↥L) : MulAut V) v, trivial⟩) := rfl
  rw [hepv, h1, hev, ← hm]
  change Multiplicative.ofAdd (qProj (Multiplicative.toAdd ((FFModel.zornQ j2Γ₀).act γ m.1))) =
    matHom (qHomJ γ) (Multiplicative.ofAdd (qProj (Multiplicative.toAdd m.1)))
  apply Multiplicative.toAdd.injective
  rw [toAdd_matHom, toAdd_ofAdd, toAdd_ofAdd, qHomJ, MonoidHom.comp_apply, qHom_mulVec]
  have htr : (Multiplicative.toAdd m.1).1 + (Multiplicative.toAdd m.1).2.2.2 = 0 := m.2
  exact qProj_apply (j2Γ₀_le_quasithinG2 γ.2) htr

theorem map_congr_eq_L6 {L : Subgroup (MulAut V)} {π : ↥j2Γ₀ →* ↥L} (hπ : Function.Surjective π)
    (e : V ≃* W6) (he : ∀ (γ : ↥j2Γ₀) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = matHom (qHomJ γ) (e v)) :
    L.map (MulAut.congr e).toMonoidHom = L6 := by
  have key : ∀ γ : ↥j2Γ₀, MulAut.congr e ((π γ : ↥L) : MulAut V) = matHom (qHomJ γ) := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, he]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
    refine ⟨⟨qHomJ γ, qHomJ_mem γ⟩, ?_⟩
    change matHom (qHomJ γ) = _
    rw [← key γ, hγ]
    rfl
  · rintro ⟨⟨δ, hδ⟩, rfl⟩
    rw [← range_qHomJ] at hδ
    obtain ⟨γ, rfl⟩ := hδ
    exact ⟨_, (π γ).2, key γ⟩

end Realize

end CFSG.Quasithin.J2Row
