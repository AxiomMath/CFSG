module

public import CFSG.Monster.B.TwoA.Amalgam.LocalLabel
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeCore
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct)

theorem inv_mul_mul_mem_rootClass
    (g : stdGroup) {x : stdGroup} (hx : x ∈ rootClass) :
    g⁻¹ * x * g ∈ rootClass :=
  IsConj.trans hx (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)

theorem mul_mul_inv_mem_rootClass
    (g : stdGroup) {x : stdGroup} (hx : x ∈ rootClass) :
    g * x * g⁻¹ ∈ rootClass :=
  IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩)

@[expose] def rootClassConj
    (g : stdGroup) : rootClass ≃ rootClass where
  toFun x := ⟨g⁻¹ * x * g, inv_mul_mul_mem_rootClass g x.2⟩
  invFun x := ⟨g * x * g⁻¹, mul_mul_inv_mem_rootClass g x.2⟩
  left_inv x := Subtype.ext (by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
    mul_one])
  right_inv x := Subtype.ext (by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
    mul_one])

theorem coe_rootClassConj
    (g : stdGroup) (x : rootClass) :
    (rootClassConj g x : stdGroup) = g⁻¹ * x * g :=
  rfl

theorem inl_rootClassConj
    (g : stdGroup) (x : rootClass) :
    (SemidirectProduct.inl (rootClassConj g x : stdGroup) : GStar) =
      (SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inl (x : stdGroup) *
        SemidirectProduct.inl g := by
  rw [coe_rootClassConj, map_mul, map_mul, map_inv]

@[expose] def conjRho
    {u : CVert} (g : stdGroup) (ρ : vStab u →* GStar) : vStab u →* GStar where
  toFun y := (SemidirectProduct.inl g)⁻¹ * ρ y * SemidirectProduct.inl g
  map_one' := by rw [map_one, mul_one, inv_mul_cancel]
  map_mul' a b := by simp only [map_mul, mul_assoc, mul_inv_cancel_left]

theorem conjRho_apply
    {u : CVert} (g : stdGroup) (ρ : vStab u →* GStar) (y : vStab u) :
    conjRho g ρ y = (SemidirectProduct.inl g)⁻¹ * ρ y * SemidirectProduct.inl g :=
  rfl

abbrev labelLocalHom
    (v : CVert) : LocalHom v where
  stab := vStab v
  mem_stab _ := Iff.rfl
  iv := (native_local_label_root v).choose_spec.choose
  rho := (native_local_label_root v).choose
  adj_iff := (native_local_label_root v).choose_spec.choose_spec.2.2.2.2.2.1
  act y a _ := (native_local_label_root v).choose_spec.choose_spec.2.2.2.2.1 y a
  surj := (native_local_label_root v).choose_spec.choose_spec.1
  ker := (native_local_label_root v).choose_spec.choose_spec.2.2.1
  orderOf_clabel := (native_local_label_root v).choose_spec.choose_spec.2.2.2.1
  rho_clabel := (native_local_label_root v).choose_spec.choose_spec.2.2.2.2.2.2.2

theorem labelLocalHom_rho_eq_one_iff
    (v : CVert) (y : vStab v) :
    (labelLocalHom v).rho y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v) :=
  (native_local_label_root v).choose_spec.choose_spec.2.1 y

theorem labelLocalHom_compat
    (v : CVert) (y : vStab v) (z : cgraph.neighborSet v) :
    SemidirectProduct.inl ((labelLocalHom v).iv (stabAct y z) : stdGroup) =
      ((labelLocalHom v).rho y)⁻¹ * SemidirectProduct.inl ((labelLocalHom v).iv z : stdGroup) *
        (labelLocalHom v).rho y :=
  (native_local_label_root v).choose_spec.choose_spec.2.2.2.2.1 y z

theorem labelLocalHom_label
    (v : CVert) (z : cgraph.neighborSet v) (y : vStab v)
    (hy : ((y : Shat) : Dfull) = clabel z) :
    (labelLocalHom v).rho y = SemidirectProduct.inl ((labelLocalHom v).iv z : stdGroup) :=
  (native_local_label_root v).choose_spec.choose_spec.2.2.2.2.2.2.2 z y hy

theorem cvMul_eq_of_clabel
    {z x : CVert} (hx : x ∈ cgraph.neighborSet z) {y : Shat}
    (hy : (y : Dfull) = clabel z) : cvMul x y = x :=
  (((native_local_label_root z).choose_spec.choose_spec.2.2.1 y).2
    (hy ▸ Subgroup.mem_zpowers _)).2 x hx

section Conj

variable (u : CVert) (g : stdGroup)

abbrev ivConj :
    cgraph.neighborSet u ≃ rootClass := (labelLocalHom u).iv.trans (rootClassConj g)

theorem conj_conj_eq {M : Type*} [Group M] (a b c : M) :
    a⁻¹ * (b⁻¹ * c * b) * a = (a⁻¹ * b * a)⁻¹ * (a⁻¹ * c * a) * (a⁻¹ * b * a) := by
  group

theorem conj_conj_inv_eq {M : Type*} [Group M] (a c : M) : a⁻¹ * (a * c * a⁻¹) * a = c := by
  group

theorem conjRho_surjective :
    Function.Surjective (conjRho g (labelLocalHom u).rho) := by
  intro γ
  obtain ⟨y, hy⟩ := (labelLocalHom u).surj
    (SemidirectProduct.inl g * γ * (SemidirectProduct.inl g)⁻¹)
  exact ⟨y, (congrArg (fun r => (SemidirectProduct.inl g)⁻¹ * r * SemidirectProduct.inl g)
    hy).trans (conj_conj_inv_eq _ _)⟩

theorem conjRho_eq_one_iff
    (y : vStab u) :
    conjRho g (labelLocalHom u).rho y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u) :=
  (conj_inv_eq_one_iff _ _).trans (labelLocalHom_rho_eq_one_iff u y)

theorem ivConj_stabAct
    (y : vStab u) (z : cgraph.neighborSet u) :
    SemidirectProduct.inl (ivConj u g (stabAct y z) : stdGroup) =
      (conjRho g (labelLocalHom u).rho y)⁻¹ * SemidirectProduct.inl (ivConj u g z : stdGroup) *
        conjRho g (labelLocalHom u).rho y :=
  (inl_rootClassConj g _).trans ((congrArg (fun r => (SemidirectProduct.inl g)⁻¹ * r *
    SemidirectProduct.inl g) (labelLocalHom_compat u y z)).trans
    ((conj_conj_eq _ _ _).trans (congrArg (fun r => (conjRho g (labelLocalHom u).rho y)⁻¹ * r *
      conjRho g (labelLocalHom u).rho y) (inl_rootClassConj g _).symm)))

theorem adj_iff_commute_ivConj
    {z z' : cgraph.neighborSet u} (hne : z ≠ z') :
    cgraph.Adj z z' ↔ Commute (ivConj u g z : stdGroup) (ivConj u g z') :=
  ((labelLocalHom u).adj_iff z z' hne).trans (commute_conj_inv_iff g _ _).symm

theorem conjRho_eq_of_clabel
    (z : cgraph.neighborSet u) (y : vStab u)
    (hy : ((y : Shat) : Dfull) = clabel z) :
    conjRho g (labelLocalHom u).rho y = SemidirectProduct.inl (ivConj u g z : stdGroup) :=
  (congrArg (fun r => (SemidirectProduct.inl g)⁻¹ * r * SemidirectProduct.inl g)
    (labelLocalHom_label u z y hy)).trans (inl_rootClassConj g _).symm

end Conj

theorem inl_rootPt_projAct
    (p q : IsoPt) :
    (SemidirectProduct.inl (E6.StdF4.rootPt (projAct (tPt p) q)) : GStar) =
      (SemidirectProduct.inl (E6.StdF4.rootPt p))⁻¹ *
        SemidirectProduct.inl (E6.StdF4.rootPt q) * SemidirectProduct.inl (E6.StdF4.rootPt p) := by
  have hsq : (tPt p)⁻¹ = tPt p := by
    have h := CFSG.Monster.B.Classical.UnitarySix.tPt_sq p
    rw [sq] at h
    exact inv_eq_of_mul_eq_one_right h
  have e : E6.StdF4.rootPt (projAct (tPt p) q) =
      (E6.StdF4.rootPt p)⁻¹ * E6.StdF4.rootPt q * E6.StdF4.rootPt p := by
    show leviG (leviPSU.symm (tPt (projAct (tPt p) q))) =
      (leviG (leviPSU.symm (tPt p)))⁻¹ * leviG (leviPSU.symm (tPt q)) *
        leviG (leviPSU.symm (tPt p))
    rw [CFSG.Monster.B.Classical.UnitarySix.tPt_projAct, ← map_inv, ← map_inv, hsq, map_mul,
      map_mul, map_mul, map_mul]
  rw [e, map_mul, map_mul, map_inv]

section Slice

variable {v w u : CVert} (hvu : v ∈ cgraph.neighborSet u) (hwu : w ∈ cgraph.neighborSet u)
  {g : stdGroup}

include hvu in
theorem ivConj_eq_rootInv
    (hgv : g * rootInv * g⁻¹ = (labelLocalHom u).iv ⟨v, hvu⟩) :
    (ivConj u g ⟨v, hvu⟩ : stdGroup) = rootInv :=
  (congrArg (fun r => g⁻¹ * r * g) hgv.symm).trans (conj_conj_inv_eq g rootInv)

include hwu in
theorem ivConj_eq_tMinus
    (hgw : g * tMinus * g⁻¹ = (labelLocalHom u).iv ⟨w, hwu⟩) :
    (ivConj u g ⟨w, hwu⟩ : stdGroup) = tMinus :=
  (congrArg (fun r => g⁻¹ * r * g) hgw.symm).trans (conj_conj_inv_eq g tMinus)

theorem mem_stab3_iff (y : Shat) :
    y ∈ vStab v ⊓ vStab w ⊓ vStab u ↔ cvMul v y = v ∧ cvMul w y = w ∧ cvMul u y = u := by
  simp only [Subgroup.mem_inf, mem_vStab, and_assoc]

theorem range_conjRho_stab3
    (hcent : Subgroup.centralizer
        ({(labelLocalHom u).pt ⟨v, hvu⟩, (labelLocalHom u).pt ⟨w, hwu⟩} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom)
    (hcn : commonNbrs ((labelLocalHom u).iv ⟨v, hvu⟩) ((labelLocalHom u).iv ⟨w, hwu⟩) =
      (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus) :
    ((conjRho g (labelLocalHom u).rho).comp
      (Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab w ⊓ vStab u ≤ vStab u))).range =
      E6.StdF4.leviStar := by
  obtain ⟨φ, hφsurj, -, hφ, -⟩ :=
    exists_leviHom (labelLocalHom u) (vStab v ⊓ vStab w ⊓ vStab u) mem_stab3_iff hcent hcn
  ext γ
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.comp_apply, conjRho_apply]
    have h := hφ y
    exact h ▸ (CFSG.Monster.B.E6.StdF4.leviStarEquiv.symm (φ y)).2
  · intro hγ
    obtain ⟨y, hy⟩ := hφsurj (CFSG.Monster.B.E6.StdF4.leviStarEquiv ⟨γ, hγ⟩)
    refine ⟨y, ?_⟩
    rw [MonoidHom.comp_apply, conjRho_apply]
    have h := hφ y
    rw [hy, MulEquiv.symm_apply_apply] at h
    exact h.symm

theorem exists_transvection_labels
    (hcn : commonNbrs ((labelLocalHom u).iv ⟨v, hvu⟩) ((labelLocalHom u).iv ⟨w, hwu⟩) =
      (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus) :
    ∃ τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt,
      (∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
        ((y : Shat) : Dfull) = clabel z →
          conjRho g (labelLocalHom u).rho y =
            SemidirectProduct.inl (leviG (leviPSU.symm (tPt (τ z))))) ∧
      ∀ (z z' : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
        ((y : Shat) : Dfull) = clabel z →
          ∃ h : cvMul (z' : CVert) (y : Shat) ∈
              cgraph.neighborSet u ∩ cgraph.commonNeighbors v w,
            τ ⟨_, h⟩ = projAct (tPt (τ z)) (τ z') := by
  obtain ⟨f, hfbij, hf, -⟩ := exists_isoPt_map (labelLocalHom u) hcn
  have key : ∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
      ((y : Shat) : Dfull) = clabel z →
        conjRho g (labelLocalHom u).rho y =
          SemidirectProduct.inl (E6.StdF4.rootPt (f z)) := by
    intro z y hy
    exact (conjRho_eq_of_clabel u g ⟨z, z.2.1⟩ y hy).trans
      (congrArg (fun r => (SemidirectProduct.inl r : GStar)) (hf z).symm)
  refine ⟨Equiv.ofBijective f hfbij, key, fun z z' y hy => ?_⟩
  have hz := (cgraph.mem_commonNeighbors).1 z.2.2
  have hyv : cvMul v (y : Shat) = v := cvMul_eq_of_clabel hz.1.symm hy
  have hyw : cvMul w (y : Shat) = w := cvMul_eq_of_clabel hz.2.symm hy
  have hz' := (cgraph.mem_commonNeighbors).1 z'.2.2
  have hmem : cvMul (z' : CVert) (y : Shat) ∈
      cgraph.neighborSet u ∩ cgraph.commonNeighbors v w := by
    refine ⟨cvMul_mem_neighborSet y.2 z'.2.1, (cgraph.mem_commonNeighbors).2 ⟨?_, ?_⟩⟩
    · have h := (cgraph_adj_cvMul v z' y).2 hz'.1
      rwa [hyv] at h
    · have h := (cgraph_adj_cvMul w z' y).2 hz'.2
      rwa [hyw] at h
  refine ⟨hmem, ?_⟩
  have h1 := ivConj_stabAct u g y ⟨z', z'.2.1⟩
  have h2 : (ivConj u g (stabAct y ⟨z', z'.2.1⟩) : stdGroup) =
      E6.StdF4.rootPt (f ⟨_, hmem⟩) := (hf ⟨_, hmem⟩).symm
  have h3 : (ivConj u g ⟨z', z'.2.1⟩ : stdGroup) = E6.StdF4.rootPt (f z') := (hf z').symm
  rw [h2, h3, key z y hy] at h1
  exact E6.StdF4.rootPt_injective (E6.StdF4.inl_injective
    (h1.trans (inl_rootPt_projAct (f z) (f z')).symm))

end Slice

theorem local_unitary_transvection_of
    {v w u : CVert} (hvu : v ∈ cgraph.neighborSet u)
    (hwu : w ∈ cgraph.neighborSet u) {g : stdGroup}
    (hgv : g * rootInv * g⁻¹ = (labelLocalHom u).iv ⟨v, hvu⟩)
    (hgw : g * tMinus * g⁻¹ = (labelLocalHom u).iv ⟨w, hwu⟩)
    (hcent : Subgroup.centralizer
        ({(labelLocalHom u).pt ⟨v, hvu⟩, (labelLocalHom u).pt ⟨w, hwu⟩} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom)
    (hcn : commonNbrs ((labelLocalHom u).iv ⟨v, hvu⟩) ((labelLocalHom u).iv ⟨w, hwu⟩) =
      (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus) :
    ∃ (ρ : vStab u →* GStar) (iu : cgraph.neighborSet u ≃ rootClass),
      Function.Surjective ρ ∧
      (∀ y : vStab u, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      (∀ (y : vStab u) (z : cgraph.neighborSet u),
        SemidirectProduct.inl (iu (stabAct y z) : stdGroup) =
          (ρ y)⁻¹ * SemidirectProduct.inl (iu z : stdGroup) * ρ y) ∧
      (∀ z z' : cgraph.neighborSet u, z ≠ z' →
        (cgraph.Adj z z' ↔ Commute (iu z : stdGroup) (iu z'))) ∧
      (∀ (z : cgraph.neighborSet u) (y : vStab u), ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (iu z : stdGroup)) ∧
      (∀ hvu : v ∈ cgraph.neighborSet u, (iu ⟨v, hvu⟩ : stdGroup) = rootInv) ∧
      (∀ hwu : w ∈ cgraph.neighborSet u, (iu ⟨w, hwu⟩ : stdGroup) = tMinus) ∧
      (ρ.comp (Subgroup.inclusion (inf_le_right :
        vStab v ⊓ vStab w ⊓ vStab u ≤ vStab u))).range = E6.StdF4.leviStar ∧
      (∀ y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat),
        ρ (Subgroup.inclusion inf_le_right y) = 1 ↔
          ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      ∃ τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt,
        (∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
          ((y : Shat) : Dfull) = clabel z →
            ρ y = SemidirectProduct.inl (leviG (leviPSU.symm (tPt (τ z))))) ∧
        ∀ (z z' : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
          ((y : Shat) : Dfull) = clabel z →
            ∃ h : cvMul (z' : CVert) (y : Shat) ∈
                cgraph.neighborSet u ∩ cgraph.commonNeighbors v w,
              τ ⟨_, h⟩ = projAct (tPt (τ z)) (τ z') :=
  ⟨conjRho g (labelLocalHom u).rho, ivConj u g, conjRho_surjective u g,
    conjRho_eq_one_iff u g, ivConj_stabAct u g, fun _ _ hne => adj_iff_commute_ivConj u g hne,
    conjRho_eq_of_clabel u g, fun h => ivConj_eq_rootInv h hgv, fun h => ivConj_eq_tMinus h hgw,
    range_conjRho_stab3 hvu hwu hcent hcn, fun _ => conjRho_eq_one_iff u g _,
    exists_transvection_labels hvu hwu hcn⟩

theorem native_local_unitary_transvection_map
    {v w u : CVert} (hw : w ∈ sphereThree v)
    (hu : u ∈ cgraph.commonNeighbors v w) :
    ∃ (ρ : vStab u →* GStar) (iu : cgraph.neighborSet u ≃ rootClass),
      Function.Surjective ρ ∧
      (∀ y : vStab u, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      (∀ (y : vStab u) (z : cgraph.neighborSet u),
        SemidirectProduct.inl (iu (stabAct y z) : stdGroup) =
          (ρ y)⁻¹ * SemidirectProduct.inl (iu z : stdGroup) * ρ y) ∧
      (∀ z z' : cgraph.neighborSet u, z ≠ z' →
        (cgraph.Adj z z' ↔ Commute (iu z : stdGroup) (iu z'))) ∧
      (∀ (z : cgraph.neighborSet u) (y : vStab u), ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (iu z : stdGroup)) ∧
      (∀ hvu : v ∈ cgraph.neighborSet u, (iu ⟨v, hvu⟩ : stdGroup) = rootInv) ∧
      (∀ hwu : w ∈ cgraph.neighborSet u, (iu ⟨w, hwu⟩ : stdGroup) = tMinus) ∧
      (ρ.comp (Subgroup.inclusion (inf_le_right :
        vStab v ⊓ vStab w ⊓ vStab u ≤ vStab u))).range = E6.StdF4.leviStar ∧
      (∀ y : (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat),
        ρ (Subgroup.inclusion inf_le_right y) = 1 ↔
          ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      ∃ τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt,
        (∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
          ((y : Shat) : Dfull) = clabel z →
            ρ y = SemidirectProduct.inl (leviG (leviPSU.symm (tPt (τ z))))) ∧
        ∀ (z z' : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
          ((y : Shat) : Dfull) = clabel z →
            ∃ h : cvMul (z' : CVert) (y : Shat) ∈
                cgraph.neighborSet u ∩ cgraph.commonNeighbors v w,
              τ ⟨_, h⟩ = projAct (tPt (τ z)) (τ z') := by
  have hvu : v ∈ cgraph.neighborSet u := ((cgraph.mem_commonNeighbors).1 hu).1.symm
  have hwu : w ∈ cgraph.neighborSet u := ((cgraph.mem_commonNeighbors).1 hu).2.symm
  have hd := cgraph_dist_eq_two_iff.1 hw.1
  have hne : (⟨v, hvu⟩ : cgraph.neighborSet u) ≠ ⟨w, hwu⟩ := fun h =>
    hd.1 (congrArg Subtype.val h)
  have hop :=
    exists_opposite (labelLocalHom u) (orderOf_pt_mul_pt_eq_three labelLocalHom hne hd.2.1 hw.2)
  exact local_unitary_transvection_of hvu hwu hop.choose_spec.1 hop.choose_spec.2.1
    hop.choose_spec.2.2.1 hop.choose_spec.2.2.2

end CFSG.Monster.B.TwoA.Amalgam
