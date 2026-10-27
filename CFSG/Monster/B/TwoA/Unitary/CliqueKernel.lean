module

public import CFSG.Monster.B.TwoA.Unitary.CliqueBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import all CFSG.Fischer.F4
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix

@[expose] noncomputable def stabL (W : Submodule F4 V) : Subgroup ProjSU where
  carrier := {x | ∀ p, projAct x p ∈ planePts W ↔ p ∈ planePts W}
  mul_mem' {x y} hx hy p := by rw [map_mul, Equiv.Perm.mul_apply, hx, hy]
  one_mem' p := by rw [map_one, Equiv.Perm.one_apply]
  inv_mem' {x} hx p := by rw [← hx, map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem mem_stabL {W : Submodule F4 V} {x : ProjSU} :
    x ∈ stabL W ↔ ∀ p, projAct x p ∈ planePts W ↔ p ∈ planePts W := Iff.rfl

@[expose] noncomputable def kerL (W : Submodule F4 V) : Subgroup ProjSU where
  carrier := {x | ∀ p ∈ planePts W, projAct x p = p}
  mul_mem' {x y} hx hy p hp := by rw [map_mul, Equiv.Perm.mul_apply, hy p hp, hx p hp]
  one_mem' p _ := by rw [map_one, Equiv.Perm.one_apply]
  inv_mem' {x} hx p hp := by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hx p hp]

theorem mem_kerL {W : Submodule F4 V} {x : ProjSU} :
    x ∈ kerL W ↔ ∀ p ∈ planePts W, projAct x p = p := Iff.rfl

@[expose] noncomputable def restrL (W : Submodule F4 V) : stabL W →* Equiv.Perm (planePts W) where
  toFun x := (projAct (x : ProjSU)).subtypePerm fun p => x.2 p
  map_one' := Equiv.ext fun p => Subtype.ext (by
    change projAct (1 : ProjSU) p = p
    rw [map_one, Equiv.Perm.one_apply])
  map_mul' x y := Equiv.ext fun p => Subtype.ext (by
    change projAct ((x : ProjSU) * y) p = projAct (x : ProjSU) (projAct (y : ProjSU) p)
    rw [map_mul, Equiv.Perm.mul_apply])

theorem restrL_apply (W : Submodule F4 V) (x : stabL W) (p : planePts W) :
    ((restrL W x p : planePts W) : IsoPt) = projAct (x : ProjSU) p := rfl

theorem kerL_le_stabL (W : Submodule F4 V) : kerL W ≤ stabL W := by
  intro x hx p
  constructor
  · intro hp
    have h := hx _ hp
    rwa [(projAct x).injective h] at hp
  · intro hp
    rw [hx p hp]
    exact hp

theorem restrL_eq_one_iff (W : Submodule F4 V) (x : stabL W) :
    restrL W x = 1 ↔ (x : ProjSU) ∈ kerL W := by
  constructor
  · intro h p hp
    have := congrArg (fun σ : Equiv.Perm (planePts W) => ((σ ⟨p, hp⟩ : planePts W) : IsoPt)) h
    exact this
  · intro h
    exact Equiv.ext fun p => Subtype.ext (h p p.2)

theorem smul_pt_eq_of_mulVec {g : SU frobeniusF4 6} {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0)
    (h : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v) :
    g • pt v hv0 hv = pt v hv0 hv := by
  rw [smul_pt, pt_eq_pt_iff]
  exact ⟨1, by rw [one_smul, smul_def, h]⟩

theorem planePts_W0_eq (p : IsoPt) (hp : p ∈ planePts W0) :
    ∃ (w : Fin 3 → F4) (hw : lift3 w ≠ 0), p = pt (lift3 w) hw (herm_lift3 w w) := by
  refine ⟨hypA p.1.rep, ?_, ?_⟩
  · rw [← eq_lift3_of_mem_W0 hp]
    exact rep_ne_zero p
  · conv_lhs => rw [← pt_rep p]
    exact (pt_eq_pt_iff _ _ _ _).2 ⟨1, by rw [one_smul, ← eq_lift3_of_mem_W0 hp]⟩

theorem mk_unipSU_mem_kerL_W0 (C : Matrix (Fin 3) (Fin 3) F4) (hC : IsHerm C) :
    ((unipSU C hC : SU frobeniusF4 6) : ProjSU) ∈ kerL W0 := by
  intro p hp
  obtain ⟨w, hw, rfl⟩ := planePts_W0_eq p hp
  rw [projAct_mk]
  exact smul_pt_eq_of_mulVec _ _ (by rw [coe_unipSU, unipMat_mulVec_lift3])

theorem scalarHom_mul_eq (c : F4ˣ) (g : SU frobeniusF4 6) :
    ((scalarHom c * g : SU frobeniusF4 6) : ProjSU) = (g : ProjSU) := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (mem_scalars.2 ⟨c, rfl⟩), one_mul]

theorem mem_kerL_W0_iff (x : ProjSU) :
    x ∈ kerL W0 ↔ ∃ (C : Matrix (Fin 3) (Fin 3) F4) (hC : IsHerm C),
      x = ((unipSU C hC : SU frobeniusF4 6) : ProjSU) := by
  constructor
  · intro hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hfix : ∀ w : Fin 3 → F4, w ≠ 0 → ∃ c : F4,
          ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ lift3 w = c • lift3 w := by
        intro w hw
        have hw0 : lift3 w ≠ 0 := fun h => hw (lift3_eq_zero_iff.1 h)
        have h := hx _ ((pt_mem_planePts hw0 (herm_lift3 w w)).2 (lift3_mem_W0 w))
        rw [projAct_mk, smul_pt, pt_eq_pt_iff] at h
        obtain ⟨c, hc⟩ := h
        exact ⟨c, by rw [← smul_def, hc]⟩
      obtain ⟨c, C, hc0, hC, hM⟩ := exists_eq_smul_unipMat (isIsometry_of_mem g) hfix
      refine ⟨C, hC, ?_⟩
      have hg : g = scalarHom (Units.mk0 c hc0) * unipSU C hC := SU_ext (by
        rw [coe_SU_mul, coe_scalarHom, coe_unipSU, Units.val_mk0, hM, Matrix.scalar_apply,
          smul_eq_diagonal_mul])
      rw [hg, scalarHom_mul_eq]
  · rintro ⟨C, hC, rfl⟩
    exact mk_unipSU_mem_kerL_W0 C hC

theorem neg_eq_self_F4 : ∀ a : F4, -a = a := by decide

@[expose] def hermSub : AddSubgroup (Matrix (Fin 3) (Fin 3) F4) where
  carrier := {C | IsHerm C}
  add_mem' := IsHerm.add
  zero_mem' := isHerm_zero
  neg_mem' {C} hC := by
    have e : -C = C := by
      ext i j
      exact neg_eq_self_F4 _
    change IsHerm (-C)
    rw [e]
    exact hC

@[expose] def hermOf (d o : Fin 3 → F4) : Matrix (Fin 3) (Fin 3) F4 :=
  !![d 0, o 0, o 1; bar (o 0), d 1, o 2; bar (o 1), bar (o 2), d 2]

theorem isHerm_hermOf {d : Fin 3 → F4} (hd : ∀ i, bar (d i) = d i) (o : Fin 3 → F4) :
    IsHerm (hermOf d o) := by
  rw [isHerm_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, hd, bar_bar]

theorem hermOf_diag_off {C : Matrix (Fin 3) (Fin 3) F4} (hC : IsHerm C) :
    hermOf (fun i => C i i) ![C 0 1, C 0 2, C 1 2] = C := by
  rw [isHerm_iff] at hC
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, hC]

@[expose] noncomputable def hermEquiv :
    {d : Fin 3 → F4 // ∀ i, bar (d i) = d i} × (Fin 3 → F4) ≃ hermSub where
  toFun x := ⟨hermOf x.1.1 x.2, isHerm_hermOf x.1.2 x.2⟩
  invFun C := (⟨fun i => C.1 i i, fun i => (isHerm_iff.1 C.2) i i⟩, ![C.1 0 1, C.1 0 2, C.1 1 2])
  left_inv x := by
    obtain ⟨⟨d, hd⟩, o⟩ := x
    refine Prod.ext (Subtype.ext ?_) ?_
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv C := Subtype.ext (hermOf_diag_off C.2)

theorem card_diag_F2 : Fintype.card {d : Fin 3 → F4 // ∀ i, bar (d i) = d i} = 8 := by
  decide

theorem card_hermSub : Nat.card hermSub = 2 ^ 9 := by
  rw [← Nat.card_congr hermEquiv, Nat.card_eq_fintype_card, Fintype.card_prod, card_diag_F2,
    Fintype.card_fun, F4.card, Fintype.card_fin]
  norm_num

@[expose] noncomputable def unipHom : Multiplicative hermSub →* ProjSU where
  toFun C := ((unipSU C.toAdd.1 C.toAdd.2 : SU frobeniusF4 6) : ProjSU)
  map_one' := by
    change ((unipSU 0 isHerm_zero : SU frobeniusF4 6) : ProjSU) = 1
    rw [unipSU_zero, QuotientGroup.mk_one]
  map_mul' C C' := by
    change ((unipSU (C.toAdd.1 + C'.toAdd.1) _ : SU frobeniusF4 6) : ProjSU) = _
    rw [← unipSU_mul C.toAdd.2 C'.toAdd.2, QuotientGroup.mk_mul]

theorem unipHom_apply (C : Multiplicative hermSub) :
    unipHom C = ((unipSU C.toAdd.1 C.toAdd.2 : SU frobeniusF4 6) : ProjSU) := rfl

theorem toBlocks₁₂_hyp_scalar (a : F4) : (hyp (Matrix.scalar (Fin 6) a)).toBlocks₁₂ = 0 := by
  ext i j
  simp [hyp, toBlocks₁₂, Matrix.scalar_apply]

theorem unipHom_injective : Function.Injective unipHom := by
  rw [injective_iff_map_eq_one]
  intro C hC
  rw [unipHom_apply, QuotientGroup.eq_one_iff, mem_scalars] at hC
  obtain ⟨a, ha⟩ := hC
  have ha' : unipMat (C.toAdd : Matrix (Fin 3) (Fin 3) F4) = Matrix.scalar (Fin 6) a := ha
  have h := congrArg (fun M => (hyp M).toBlocks₁₂) ha'
  simp only [hyp_unipMat, toBlocks_fromBlocks₁₂, toBlocks₁₂_hyp_scalar] at h
  change C = Multiplicative.ofAdd 0
  rw [← ofAdd_toAdd C]
  congr 1
  exact Subtype.ext h

theorem range_unipHom : unipHom.range = kerL W0 := by
  ext x
  rw [mem_kerL_W0_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C.toAdd.1, C.toAdd.2, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨C, hC⟩, rfl⟩

theorem card_kerL_W0 : Nat.card (kerL W0) = 2 ^ 9 := by
  rw [← range_unipHom, ← Nat.card_congr (MonoidHom.ofInjective unipHom_injective).toEquiv]
  exact card_hermSub

theorem isElementaryAbelian_two_of {G : Type*} [Group G] (H : Subgroup G)
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hs : ∀ x ∈ H, x ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 H := CFSG.IsElementaryAbelian.of_forall hc hs

theorem kerL_W0_comm : ∀ x ∈ kerL W0, ∀ y ∈ kerL W0, x * y = y * x := by
  rw [← range_unipHom]
  rintro _ ⟨C, rfl⟩ _ ⟨C', rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem kerL_W0_sq : ∀ x ∈ kerL W0, x ^ 2 = 1 := by
  rw [← range_unipHom]
  rintro _ ⟨C, rfl⟩
  rw [← map_pow]
  have h : C ^ 2 = 1 := by
    rw [pow_two]
    change Multiplicative.ofAdd (C.toAdd + C.toAdd) = Multiplicative.ofAdd 0
    congr 1
    exact Subtype.ext (add_self_matrix _)
  rw [h, map_one]

theorem isElementaryAbelian_kerL_W0 : CFSG.IsElementaryAbelian 2 (kerL W0) :=
  isElementaryAbelian_two_of _ kerL_W0_comm kerL_W0_sq

abbrev e3 (i : Fin 3) : Fin 3 → F4 := Pi.single i 1

@[expose] def diagList (i : Fin 3) (c : F4) : List (Fin 3 → F4) := if c = 0 then [] else [e3 i]

@[expose] def offList (i j : Fin 3) (c : F4) : List (Fin 3 → F4) :=
  if c = 0 then [] else [e3 i + bar c • e3 j, e3 i, e3 j]

@[expose] def listOf (d o : Fin 3 → F4) : List (Fin 3 → F4) :=
  diagList 0 (d 0) ++ diagList 1 (d 1) ++ diagList 2 (d 2) ++ offList 0 1 (o 0) ++
    offList 0 2 (o 1) ++ offList 1 2 (o 2)

theorem listOf_spec : ∀ d o : Fin 3 → F4, (∀ i, bar (d i) = d i) →
    (∀ w ∈ listOf d o, w ≠ 0) ∧ hermOf d o = ((listOf d o).map rk).sum := by
  decide +kernel

theorem isHerm_listSum (l : List (Fin 3 → F4)) : IsHerm ((l.map rk).sum) := by
  induction l with
  | nil => exact isHerm_zero
  | cons w l ih =>
    rw [List.map_cons, List.sum_cons]
    exact (isHerm_rk w).add ih

theorem transvec_lift3 (w : Fin 3 → F4) :
    transvec (lift3 w) (herm_lift3 w w) = unipSU (rk w) (isHerm_rk w) :=
  SU_ext (by rw [coe_transvec, coe_unipSU, transvecMat_lift3])

theorem tPt_lift3 (w : Fin 3 → F4) (hw : lift3 w ≠ 0) :
    tPt (pt (lift3 w) hw (herm_lift3 w w)) =
      ((unipSU (rk w) (isHerm_rk w) : SU frobeniusF4 6) : ProjSU) := by
  rw [tPt_pt, transvec_lift3]

theorem mk_unipSU_listSum_mem (X : Submodule F4 V) (l : List (Fin 3 → F4))
    (hl : ∀ w ∈ l, w ≠ 0) (hX : ∀ w ∈ l, lift3 w ∈ X) (h : IsHerm ((l.map rk).sum)) :
    ((unipSU _ h : SU frobeniusF4 6) : ProjSU) ∈ Subgroup.closure (tPt '' planePts X) := by
  induction l with
  | nil =>
    have e : unipSU (([] : List (Fin 3 → F4)).map rk).sum h = 1 := unipSU_zero
    rw [e, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  | cons w l ih =>
    have hw : w ≠ 0 := hl w (List.mem_cons_self ..)
    have hw0 : lift3 w ≠ 0 := fun h0 => hw (lift3_eq_zero_iff.1 h0)
    have e : unipSU ((w :: l).map rk).sum h =
        unipSU (rk w) (isHerm_rk w) * unipSU ((l.map rk).sum) (isHerm_listSum l) := by
      rw [unipSU_mul]
      congr 1
    rw [e, QuotientGroup.mk_mul]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, ?_, tPt_lift3 w hw0⟩)
      (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hX x (List.mem_cons_of_mem _ hx)) _)
    exact (pt_mem_planePts hw0 _).2 (hX w (List.mem_cons_self ..))

theorem kerL_W0_eq_closure : kerL W0 = Subgroup.closure (tPt '' planePts W0) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨C, hC, rfl⟩ := (mem_kerL_W0_iff x).1 hx
    have hd : ∀ i, bar ((fun i => C i i) i) = (fun i => C i i) i := fun i => isHerm_iff.1 hC i i
    obtain ⟨hl, hsum⟩ := listOf_spec (fun i => C i i) ![C 0 1, C 0 2, C 1 2] hd
    rw [hermOf_diag_off hC] at hsum
    have e : unipSU C hC = unipSU _ (isHerm_listSum (listOf (fun i => C i i)
        ![C 0 1, C 0 2, C 1 2])) := by
      congr 1
    rw [e]
    exact mk_unipSU_listSum_mem W0 _ hl (fun w _ => lift3_mem_W0 w) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨w, hw, rfl⟩ := planePts_W0_eq p hp
    rw [tPt_lift3]
    exact mk_unipSU_mem_kerL_W0 _ _

end CFSG.Monster.B.TwoA.Unitary.Clique
