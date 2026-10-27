module

public import CFSG.Monster.B.E6.FixedE6Descent
public import CFSG.Monster.B.E6.StdF4Points
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.Monster.B.E6.FixedE6Root

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.StdF4

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def rootOpV (a : V) : Module.End K V := 1 + ad K a + formTensor K a

theorem rootOpV_apply (a u : V) : rootOpV a u = u + bracket K a u + form K a u • a := by
  simp only [rootOpV, LinearMap.add_apply, Module.End.one_apply, ad_apply, formTensor_apply]

theorem form_bracket_add_smul_self
    (a u : V) :
    form K (bracket K a u + form K a u • a) u = form K a u ^ 2 := by
  rw [map_add, LinearMap.add_apply, form_bracket, bracket_self, map_zero, zero_add, map_smul,
    LinearMap.smul_apply, smul_eq_mul, sq]

theorem eq_of_sq_eq_sq_K {x y : K} (h : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (x - y) ^ 2 = 0 := by
    linear_combination h + (y ^ 2 - x * y) * (CharTwo.two_eq_zero (R := K))
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

theorem rootOpV_injective :
    Function.Injective rootOpV := by
  intro a c h
  have key : ∀ u, form K a u = form K c u := fun u => by
    have hu := LinearMap.congr_fun h u
    rw [rootOpV_apply, rootOpV_apply, add_assoc, add_assoc, add_right_inj] at hu
    exact eq_of_sq_eq_sq_K (by rw [← form_bracket_add_smul_self, ← form_bracket_add_smul_self, hu])
  refine sub_eq_zero.1 (form_separatingLeft (R := K) _ fun u => ?_)
  rw [map_sub, LinearMap.sub_apply, key, sub_self]

@[expose] def a0 : V := rootVec Tag.E6 K theta

theorem a0_eq_single :
    a0 = Finsupp.single (Sum.inr ⟨theta, isRoot_theta⟩) 1 :=
  CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single isRoot_theta

theorem gEnd_injective :
    Function.Injective gEnd := fun _ _ e => Subtype.ext (Units.ext e)

theorem gEnd_rootInv :
    gEnd rootInv = rootOpV a0 := by
  change ((pinnedX Tag.E6 K theta 1 : ModGL Tag.E6 K) : Module.End K V) = _
  rw [pinnedX_eq isRoot_theta, one_smul, one_pow, one_smul]
  rfl

theorem gEnd_mul_rootOpV_mul
    (g : stdGroup) (a : V) :
    gEnd g * rootOpV a * gEnd g⁻¹ = rootOpV (gEnd g a) := by
  have hg := stdGroup_mem_adjointGroup g
  have h := conj_rootOp (g := (g : ModGL Tag.E6 K)) (fun u v => adjointGroup_bracket hg u v)
    (fun u v => adjointGroup_form hg u v) a 1
  simp only [one_smul, one_pow] at h
  exact h

theorem gEnd_conj
    (g x : stdGroup) : gEnd (g * x * g⁻¹) = gEnd g * gEnd x * gEnd g⁻¹ := rfl

theorem gEnd_rootMap
    (g : stdGroup) : gEnd (rootMap g) = rootOpV (gEnd g a0) := by
  rw [rootMap, gEnd_conj, gEnd_rootInv, gEnd_mul_rootOpV_mul]

theorem gEnd_gEnd_inv
    (g : stdGroup) (u : V) : gEnd g (gEnd g⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← gEnd_mul, mul_inv_cancel, gEnd_one_apply]

theorem gEnd_inv_gEnd
    (g : stdGroup) (u : V) : gEnd g⁻¹ (gEnd g u) = u := by
  rw [← Module.End.mul_apply, ← gEnd_mul, inv_mul_cancel, gEnd_one_apply]

theorem fixedMap_a0 : fixedMap a0 = a0 := by
  rw [a0_eq_single, fixedMap_single, one_pow, labelRho_inr]
  exact congrArg (fun l => Finsupp.single l (1 : K))
    (congrArg Sum.inr (Subtype.ext permLattice_e6HighestRoot))

theorem a0_mem_fixedL : a0 ∈ fixedL := fixedMap_a0

@[expose] def a0L : fixedL := ⟨a0, a0_mem_fixedL⟩

@[simp] theorem coe_a0L : (a0L : V) = a0 := rfl

theorem sqV_a0 : sqV a0 = a0 := by
  rw [a0_eq_single, sqV, Finsupp.mapRange_single, map_one]

theorem sigmaPow_a0
    (b : betaGroup) : sigmaPow b a0 = a0 := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · exact sigmaPow_of_eq_one h a0
  · rw [sigmaPow_of_eq_betaG h, sqV_a0]

@[expose] def gL
    (g : stdGroup) : Module.End (ZMod 2) fixedL :=
  ((gEnd g).restrictScalars (ZMod 2)).restrict fun _ hu => stdGroup_mem_fixedL g hu

@[simp] theorem coe_gL_apply
    (g : stdGroup) (u : fixedL) : (gL g u : V) = gEnd g u := rfl

theorem actStar_inl_eq_gL
    (g : stdGroup) (u : fixedL) :
    actStar (SemidirectProduct.inl g) u = gL g u :=
  Subtype.ext (actStar_inl g u)

theorem gL_mul_apply
    (g h : stdGroup) (u : fixedL) : gL (g * h) u = gL g (gL h u) := rfl

theorem gL_one_apply
    (u : fixedL) : gL 1 u = u := rfl

theorem gEnd_a0_eq_iff
    (g : stdGroup) : gEnd g a0 = a0 ↔ g ∈ PJ := by
  rw [Subgroup.mem_subgroupOf, ← mem_centralizer_rootInv_iff]
  constructor
  · intro h
    have e : gEnd (rootMap g) = gEnd rootInv := by rw [gEnd_rootMap, h, gEnd_rootInv]
    exact gEnd_injective e
  · intro h
    refine rootOpV_injective ?_
    rw [← gEnd_rootMap, ← gEnd_rootInv]
    exact congrArg gEnd h

theorem actStar_inl_a0L_eq_iff
    (g : stdGroup) :
    actStar (SemidirectProduct.inl g) a0L = a0L ↔ g ∈ PJ := by
  rw [actStar_inl_eq_gL, ← Subtype.coe_inj, coe_gL_apply, coe_a0L]
  exact gEnd_a0_eq_iff g

theorem coe_actStar_a0L
    (γ : GStar) : (actStar γ a0L : V) = gEnd γ.left a0 := by
  rw [coe_actStar_apply, coe_a0L, sigmaPow_a0]

theorem actStar_a0L_eq_iff
    (γ : GStar) : actStar γ a0L = a0L ↔ γ ∈ parStar firstJ := by
  rw [mem_parStar, ← Subtype.coe_inj, coe_actStar_a0L, coe_a0L]
  exact gEnd_a0_eq_iff γ.left

theorem stabilizer_a0L :
    (MulAction.stabilizer (Equiv.Perm fixedL) a0L).comap
      (actStar.comp SemidirectProduct.inl) = PJ := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.comp_apply,
    Equiv.Perm.smul_def]
  exact actStar_inl_a0L_eq_iff g

theorem stabilizer_star_a0L :
    (MulAction.stabilizer (Equiv.Perm fixedL) a0L).comap actStar = parStar firstJ := by
  ext γ
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact actStar_a0L_eq_iff γ

open _root_.Classical in
@[expose] def rootVecOf
    (q : stdGroup) : fixedL :=
  if h : ∃ g, rootMap g = q then gL h.choose a0L else 0

theorem rootVecOf_rootMap
    (g : stdGroup) : rootVecOf (rootMap g) = gL g a0L := by
  have h : ∃ g', rootMap g' = rootMap g := ⟨g, rfl⟩
  rw [rootVecOf, dite_eq_left h]
  refine Subtype.ext (rootOpV_injective ?_)
  rw [coe_gL_apply, coe_gL_apply, coe_a0L, ← gEnd_rootMap, ← gEnd_rootMap, h.choose_spec]

theorem rootVecOf_conj_rootInv
    (g : stdGroup) :
    rootVecOf (g * rootInv * g⁻¹) = actStar (SemidirectProduct.inl g) a0L :=
  (rootVecOf_rootMap g).trans (actStar_inl_eq_gL g a0L).symm

theorem rootVecOf_rootInv :
    rootVecOf rootInv = a0L := by
  rw [← rootMap_one, rootVecOf_rootMap, gL_one_apply]

theorem gEnd_eq_rootOpV
    {q : stdGroup} (hq : q ∈ rootClass) :
    gEnd q = rootOpV (rootVecOf q) := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff q).1 hq
  rw [gEnd_rootMap, rootVecOf_rootMap, coe_gL_apply, coe_a0L]

theorem rootVecOf_eq_of_gEnd
    {q : stdGroup} (hq : q ∈ rootClass) {a : fixedL}
    (h : gEnd q = rootOpV a) : rootVecOf q = a :=
  Subtype.ext (rootOpV_injective ((gEnd_eq_rootOpV hq).symm.trans h))

theorem rootVecOf_conj
    {q : stdGroup} (hq : q ∈ rootClass) (g : stdGroup) :
    rootVecOf (g * q * g⁻¹) = gL g (rootVecOf q) := by
  obtain ⟨h, rfl⟩ := (mem_rootClass_iff q).1 hq
  rw [← rootMap_mul, rootVecOf_rootMap, rootVecOf_rootMap, gL_mul_apply]

theorem conj_mem_rootClass
    {q : stdGroup} (hq : q ∈ rootClass) (g : stdGroup) :
    g * q * g⁻¹ ∈ rootClass :=
  hq.trans (isConj_iff.2 ⟨g, rfl⟩)

abbrev rootOrbit :
    Set fixedL :=
  Set.range fun g : stdGroup => actStar (SemidirectProduct.inl g) a0L

theorem bijOn_rootVecOf :
    Set.BijOn rootVecOf rootClass rootOrbit := by
  refine ⟨fun q hq => ?_, fun q hq q' hq' e => ?_, fun u hu => ?_⟩
  · obtain ⟨g, rfl⟩ := (mem_rootClass_iff q).1 hq
    exact ⟨g, (actStar_inl_eq_gL g a0L).trans (rootVecOf_rootMap g).symm⟩
  · exact gEnd_injective (by rw [gEnd_eq_rootOpV hq, gEnd_eq_rootOpV hq', e])
  · obtain ⟨g, rfl⟩ := hu
    exact ⟨rootMap g, (mem_rootClass_iff _).2 ⟨g, rfl⟩,
      (rootVecOf_rootMap g).trans (actStar_inl_eq_gL g a0L).symm⟩

theorem range_actStar_a0L :
    (Set.range fun γ : GStar => actStar γ a0L) = rootOrbit := by
  ext u
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ.left, Subtype.ext ?_⟩
    simp only
    rw [actStar_inl, coe_actStar_a0L, coe_a0L]
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩

theorem rootVecOf_conj_star
    (γ : GStar) {q q' : stdGroup} (hq : q ∈ rootClass)
    (hq' : SemidirectProduct.inl q' = γ * SemidirectProduct.inl q * γ⁻¹) :
    q' ∈ rootClass ∧ rootVecOf q' = actStar γ (rootVecOf q) := by
  obtain ⟨h, rfl⟩ := (mem_rootClass_iff q).1 hq
  rw [conj_inl, apply_rootMap_of_mem_betaGroup, ← rootMap_mul] at hq'
  obtain rfl := inl_injective hq'
  refine ⟨(mem_rootClass_iff _).2 ⟨_, rfl⟩, Subtype.ext ?_⟩
  rw [rootVecOf_rootMap, rootVecOf_rootMap, coe_gL_apply, coe_actStar_apply, coe_gL_apply,
    coe_a0L, sigmaPow_gEnd, sigmaPow_a0]
  rfl

@[expose] def adL (a : fixedL) : Module.End (ZMod 2) fixedL where
  toFun := bracketL a
  map_add' u v := Subtype.ext (map_add (bracket K (a : V)) (u : V) (v : V))
  map_smul' c u := Subtype.ext (by
    change bracket K (a : V) (c • (u : V)) = c • bracket K (a : V) u
    rw [← algebraMap_smul K c (u : V), map_smul, algebraMap_smul])

@[simp] theorem adL_apply (a u : fixedL) : adL a u = bracketL a u := rfl

@[expose] def formTensorL (a : fixedL) : Module.End (ZMod 2) fixedL := (formL a).smulRight a

theorem formTensorL_apply (a u : fixedL) : formTensorL a u = formL a u • a := rfl

theorem form_smul_eq_formL_smul (u v : fixedL) (w : V) : form K u v • w = formL u v • w := by
  rw [← algebraMap_formL, algebraMap_smul]

theorem gL_eq_of_mem_rootClass
    {q : stdGroup} (hq : q ∈ rootClass) :
    gL q = 1 + adL (rootVecOf q) + formTensorL (rootVecOf q) := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  rw [coe_gL_apply, gEnd_eq_rootOpV hq, rootOpV_apply, LinearMap.add_apply, LinearMap.add_apply,
    Module.End.one_apply, Submodule.coe_add, Submodule.coe_add, adL_apply, formTensorL_apply,
    Submodule.coe_smul, form_smul_eq_formL_smul]
  rfl

theorem actStar_inl_of_mem_rootClass
    {q : stdGroup} (hq : q ∈ rootClass) (u : fixedL) :
    actStar (SemidirectProduct.inl q) u =
      u + bracketL (rootVecOf q) u + formL (rootVecOf q) u • rootVecOf q := by
  rw [actStar_inl_eq_gL, gL_eq_of_mem_rootClass hq]
  rfl

theorem formL_gL
    (g : stdGroup) (u v : fixedL) : formL (gL g u) (gL g v) = formL u v := by
  rw [formL_apply, formL_apply, coe_gL_apply, coe_gL_apply,
    adjointGroup_form (stdGroup_mem_adjointGroup g)]

theorem bracketL_gL
    (g : stdGroup) (u v : fixedL) :
    bracketL (gL g u) (gL g v) = gL g (bracketL u v) :=
  Subtype.ext (adjointGroup_bracket (stdGroup_mem_adjointGroup g) u v).symm

theorem gL_injective
    (g : stdGroup) : Function.Injective (gL g) := fun u v h => by
  have e := congrArg (fun w : fixedL => gEnd g⁻¹ w) h
  simp only [coe_gL_apply, gEnd_inv_gEnd] at e
  exact Subtype.ext e

theorem repPoint_mem_rootClass
    (i : Fin 5) : repPoint i ∈ rootClass :=
  (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem rootInv_mem_rootClass :
    rootInv ∈ rootClass := IsConj.refl rootInv

theorem mul_self_of_mem_rootClass
    {q : stdGroup} (hq : q ∈ rootClass) : q * q = 1 := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff q).1 hq
  exact rootMap_mul_self g

theorem coe_rootVecOf_repPoint
    (i : Fin 5) :
    (rootVecOf (repPoint i) : V) = rootVec Tag.E6 K (repRootL i) := by
  refine rootOpV_injective ?_
  rw [← gEnd_eq_rootOpV (repPoint_mem_rootClass i)]
  change ((repPoint i : ModGL Tag.E6 K) : Module.End K V) = _
  rw [coe_repPoint, pinnedX_eq (isRoot_repRootL i), one_smul, one_pow, one_smul]
  rfl

theorem exists_conj_pair
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass) (h₂ : q₂ ∈ rootClass) :
    ∃ (k : stdGroup) (i : Fin 5), q₁ = k * rootInv * k⁻¹ ∧ q₂ = k * repPoint i * k⁻¹ := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff q₁).1 h₁
  obtain ⟨h, rfl⟩ := (mem_rootClass_iff q₂).1 h₂
  obtain ⟨i, hi⟩ := exists_repLevel (g⁻¹ * h)
  have hmem : rootMap (g⁻¹ * h) ∈ conjOrbit PJ (repPoint i) := by
    rw [repPoint, conjOrbit_PJ_rootMap, lev_repPoint, ← hi]
    exact rootMap_mem_levPoints _
  obtain ⟨p, hp, e⟩ := hmem
  have hpt : p * rootInv * p⁻¹ = rootInv := (mem_centralizer_rootInv_iff p).2 hp
  refine ⟨g * p, i, ?_, ?_⟩
  · calc rootMap g = g * (p * rootInv * p⁻¹) * g⁻¹ := by rw [hpt]; rfl
      _ = g * p * rootInv * (g * p)⁻¹ := by group
  · calc rootMap h = g * rootMap (g⁻¹ * h) * g⁻¹ := by rw [← rootMap_mul, mul_inv_cancel_left]
      _ = g * (p * repPoint i * p⁻¹) * g⁻¹ := by rw [e]
      _ = g * p * repPoint i * (g * p)⁻¹ := by group

theorem orderOf_conj_pair
    (k : stdGroup) (i : Fin 5) :
    orderOf (k * rootInv * k⁻¹ * (k * repPoint i * k⁻¹)) = repOrder i := by
  have e : k * rootInv * k⁻¹ * (k * repPoint i * k⁻¹) = MulAut.conj k (rootInv * repPoint i) := by
    rw [MulAut.conj_apply]
    group
  rw [e, MulEquiv.orderOf_eq, orderOf_rootInv_mul_repPoint]

theorem commute_conj_pair_iff
    (k : stdGroup) (i : Fin 5) :
    Commute (k * rootInv * k⁻¹) (k * repPoint i * k⁻¹) ↔ repOrder i ∣ 2 := by
  rw [commute_iff_sq_eq_one (mul_self_of_mem_rootClass (conj_mem_rootClass rootInv_mem_rootClass k))
    (mul_self_of_mem_rootClass (conj_mem_rootClass (repPoint_mem_rootClass i) k)),
    ← orderOf_dvd_iff_pow_eq_one, orderOf_conj_pair]

theorem not_isRoot_of_theta_lt
    {α : Fin Tag.E6.rank → ℤ} (j : Fin Tag.E6.rank)
    (h : theta j < α j) : ¬IsRoot Tag.E6 α :=
  fun hα => absurd (le_e6HighestRoot hα j) (not_le.2 h)

theorem repRootL_ne_neg_theta {i : Fin 5} (hi : i ≠ 4) : repRootL i ≠ -theta := by
  fin_cases i <;> first | exact absurd rfl hi | decide

theorem form_a0_repRoot
    (i : Fin 5) :
    form K a0 (rootVec Tag.E6 K (repRootL i)) = if i = 4 then 1 else 0 := by
  by_cases hi : i = 4
  · subst hi
    rw [ite_eq_left rfl, a0, repRootL_four]
    exact form_rootVec_neg isRoot_theta (repRootL_four ▸ isRoot_repRootL 4)
  · rw [ite_eq_right hi, a0]
    exact form_rootVec_rootVec (repRootL_ne_neg_theta hi)

theorem hVec_sum_theta_ne_zero : ∑ j, ((theta j : ℤ) : K) • hVec Tag.E6 K j ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : V => v (Sum.inl ⟨0, by decide⟩)) h
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, hVec,
    Finsupp.single_apply, Sum.inl.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finsupp.coe_zero, Pi.zero_apply] at h0
  have h1 : ((theta ⟨0, by decide⟩ : ℤ) : K) = 1 := by
    rw [show theta ⟨0, by decide⟩ = 1 by decide, Int.cast_one]
  exact one_ne_zero (h1.symm.trans h0)

theorem bracket_a0_repRoot_eq_zero_iff
    (i : Fin 5) :
    bracket K a0 (rootVec Tag.E6 K (repRootL i)) = 0 ↔ repOrder i ∣ 2 := by
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [repRootL_zero, ← a0, bracket_self]
    exact ⟨fun _ => by decide, fun _ => rfl⟩
  · refine ⟨fun _ => by decide, fun _ => ?_⟩
    exact bracket_rootVec_rootVec_of_not isRoot_theta (isRoot_repRootL 1)
      (repRootL_ne_neg_theta (by decide)) (not_isRoot_of_theta_lt ⟨0, by decide⟩ (by decide))
  · refine ⟨fun _ => by decide, fun _ => ?_⟩
    exact bracket_rootVec_rootVec_of_not isRoot_theta (isRoot_repRootL 2)
      (repRootL_ne_neg_theta (by decide)) (not_isRoot_of_theta_lt ⟨3, by decide⟩ (by decide))
  · refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
    change bracket K a0 (rootVec Tag.E6 K (repRootL 3)) ≠ 0
    rw [a0, bracket_rootVec_rootVec isRoot_theta (isRoot_repRootL 3)
      (repRootL_ne_neg_theta (by decide)), theta_add_repRootL_three,
      CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single isRoot_e2]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  · refine ⟨fun h => absurd h ?_, fun h => absurd h (by decide)⟩
    change bracket K a0 (rootVec Tag.E6 K (repRootL 4)) ≠ 0
    rw [a0, repRootL_four, bracket_rootVec_neg isRoot_theta (repRootL_four ▸ isRoot_repRootL 4)]
    exact hVec_sum_theta_ne_zero

theorem repPoint_zero :
    repPoint 0 = rootInv := (rootMap_eq_rootInv_iff _).2 (lev_repPoint 0)

theorem rootVecOf_conj_pair
    (k : stdGroup) (i : Fin 5) :
    rootVecOf (k * rootInv * k⁻¹) = gL k a0L ∧
      rootVecOf (k * repPoint i * k⁻¹) = gL k (rootVecOf (repPoint i)) := by
  refine ⟨?_, rootVecOf_conj (repPoint_mem_rootClass i) k⟩
  rw [rootVecOf_conj rootInv_mem_rootClass k, rootVecOf_rootInv]

theorem formL_a0L_repPoint
    (i : Fin 5) :
    formL a0L (rootVecOf (repPoint i)) = if i = 4 then 1 else 0 := by
  have h := algebraMap_formL a0L (rootVecOf (repPoint i))
  rw [coe_a0L, coe_rootVecOf_repPoint, form_a0_repRoot] at h
  refine (algebraMap (ZMod 2) K).injective ?_
  rw [h]
  split_ifs <;> simp

theorem bracketL_a0L_repPoint_eq_zero_iff
    (i : Fin 5) :
    bracketL a0L (rootVecOf (repPoint i)) = 0 ↔ repOrder i ∣ 2 := by
  rw [← bracket_a0_repRoot_eq_zero_iff, ← coe_rootVecOf_repPoint, ← Subtype.coe_inj]
  rfl

theorem formL_bracketL_of_commute
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass) (h₂ : q₂ ∈ rootClass)
    (hc : Commute q₁ q₂) :
    formL (rootVecOf q₁) (rootVecOf q₂) = 0 ∧ bracketL (rootVecOf q₁) (rootVecOf q₂) = 0 := by
  obtain ⟨k, i, rfl, rfl⟩ := exists_conj_pair h₁ h₂
  have hi := (commute_conj_pair_iff k i).1 hc
  obtain ⟨e₁, e₂⟩ := rootVecOf_conj_pair k i
  rw [e₁, e₂, formL_gL, bracketL_gL, formL_a0L_repPoint,
    (bracketL_a0L_repPoint_eq_zero_iff i).2 hi, map_zero]
  have hi4 : i ≠ 4 := by
    rintro rfl
    exact absurd hi (by decide)
  exact ⟨ite_eq_right hi4, rfl⟩

theorem rootVecOf_mul_mul
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass) (h₂ : q₂ ∈ rootClass) :
    rootVecOf (q₁ * q₂ * q₁) = rootVecOf q₂ + bracketL (rootVecOf q₁) (rootVecOf q₂) +
      formL (rootVecOf q₁) (rootVecOf q₂) • rootVecOf q₁ := by
  have hinv : q₁⁻¹ = q₁ := inv_eq_of_mul_eq_one_right (mul_self_of_mem_rootClass h₁)
  have e := rootVecOf_conj h₂ q₁
  rw [hinv, gL_eq_of_mem_rootClass h₁] at e
  rw [e]
  rfl

theorem add_add_self_zmod (x y : fixedL) : x + y + y = x := by
  rw [add_assoc, ← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]

theorem formL_bracketL_of_orderOf_eq_three
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass)
    (h₂ : q₂ ∈ rootClass) (h3 : orderOf (q₁ * q₂) = 3) :
    formL (rootVecOf q₁) (rootVecOf q₂) = 1 ∧
      bracketL (rootVecOf q₁) (rootVecOf q₂) =
        rootVecOf q₁ + rootVecOf q₂ + rootVecOf (q₁ * q₂ * q₁) := by
  have hform : formL (rootVecOf q₁) (rootVecOf q₂) = 1 := by
    obtain ⟨k, i, rfl, rfl⟩ := exists_conj_pair h₁ h₂
    rw [orderOf_conj_pair] at h3
    obtain ⟨e₁, e₂⟩ := rootVecOf_conj_pair k i
    rw [e₁, e₂, formL_gL, formL_a0L_repPoint]
    have hi4 : i = 4 := by
      fin_cases i <;> first | rfl | exact absurd h3 (by decide)
    exact ite_eq_left hi4
  refine ⟨hform, ?_⟩
  rw [rootVecOf_mul_mul h₁ h₂, hform, one_smul]
  set a₁ := rootVecOf q₁
  set a₂ := rootVecOf q₂
  set c := bracketL a₁ a₂
  calc c = c + a₂ + a₂ + a₁ + a₁ := by rw [add_add_self_zmod, add_add_self_zmod]
    _ = a₁ + a₂ + (a₂ + c + a₁) := by abel

theorem fixed_E6_root_involution_vector_bijection :
    theta = e6HighestRoot ∧ a0 = rootVec Tag.E6 K theta ∧ a0 ∈ fixedL ∧ (a0L : V) = a0 ∧
    (rootInv : ModGL Tag.E6 K) = pinnedX Tag.E6 K theta 1 ∧
    gEnd rootInv = 1 + ad K a0 + formTensor K a0 ∧
    (MulAction.stabilizer (Equiv.Perm fixedL) a0L).comap
      (actStar.comp SemidirectProduct.inl) = PJ ∧
    (MulAction.stabilizer (Equiv.Perm fixedL) a0L).comap actStar = parStar firstJ ∧
    (∀ g : stdGroup, rootVecOf (g * rootInv * g⁻¹) = actStar (SemidirectProduct.inl g) a0L) ∧
    Set.BijOn rootVecOf {q : stdGroup | IsConj rootInv q}
      (Set.range fun g : stdGroup => actStar (SemidirectProduct.inl g) a0L) ∧
    (Set.range fun γ : GStar => actStar γ a0L) =
      Set.range (fun g : stdGroup => actStar (SemidirectProduct.inl g) a0L) ∧
    (∀ (γ : GStar) (q : stdGroup), γ * SemidirectProduct.inl q * γ⁻¹ =
      SemidirectProduct.inl (γ.left * (γ.right : MulAut stdGroup) q * γ.left⁻¹)) ∧
    (∀ (γ : GStar) (q q' : stdGroup), IsConj rootInv q →
      SemidirectProduct.inl q' = γ * SemidirectProduct.inl q * γ⁻¹ →
        IsConj rootInv q' ∧ rootVecOf q' = actStar γ (rootVecOf q)) ∧
    (∀ (g : stdGroup) (u : fixedL), actStar (SemidirectProduct.inl g) u = gL g u) ∧
    (∀ q : stdGroup, IsConj rootInv q →
      gL q = 1 + adL (rootVecOf q) + formTensorL (rootVecOf q)) ∧
    (∀ a u : fixedL, adL a u = bracketL a u ∧ formTensorL a u = formL a u • a) ∧
    (∀ q : stdGroup, IsConj rootInv q → ∀ u : fixedL, actStar (SemidirectProduct.inl q) u =
      u + bracketL (rootVecOf q) u + formL (rootVecOf q) u • rootVecOf q) ∧
    (∀ q : stdGroup, IsConj rootInv q →
      gEnd q = 1 + ad K (rootVecOf q : V) + formTensor K (rootVecOf q : V)) ∧
    (∀ q₁ q₂ : stdGroup, IsConj rootInv q₁ → IsConj rootInv q₂ → Commute q₁ q₂ →
      formL (rootVecOf q₁) (rootVecOf q₂) = 0 ∧ bracketL (rootVecOf q₁) (rootVecOf q₂) = 0) ∧
    ∀ q₁ q₂ : stdGroup, IsConj rootInv q₁ → IsConj rootInv q₂ → orderOf (q₁ * q₂) = 3 →
      formL (rootVecOf q₁) (rootVecOf q₂) = 1 ∧
        bracketL (rootVecOf q₁) (rootVecOf q₂) =
          rootVecOf q₁ + rootVecOf q₂ + rootVecOf (q₁ * q₂ * q₁) :=
  ⟨rfl, rfl, a0_mem_fixedL, rfl, rfl, gEnd_rootInv, stabilizer_a0L, stabilizer_star_a0L,
    rootVecOf_conj_rootInv, bijOn_rootVecOf,
    range_actStar_a0L, conj_inl, fun γ _ _ hq hq' => rootVecOf_conj_star γ hq hq',
    actStar_inl_eq_gL,
    fun _ hq => gL_eq_of_mem_rootClass hq, fun _ _ => ⟨rfl, rfl⟩,
    fun _ hq => actStar_inl_of_mem_rootClass hq, fun _ hq => gEnd_eq_rootOpV hq,
    fun _ _ h₁ h₂ hc => formL_bracketL_of_commute h₁ h₂ hc,
    fun _ _ h₁ h₂ h3 => formL_bracketL_of_orderOf_eq_three h₁ h₂ h3⟩

end CFSG.Monster.B.E6.FixedE6Root
