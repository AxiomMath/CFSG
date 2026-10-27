module

public import CFSG.Sporadic.Th.Max3.Involutions
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Recog.AltNine

public section

open scoped commutatorElement
namespace CFSG.Sporadic.Th.Recog
open CFSG.Sporadic.Th.Max3

abbrev V8 := Fin 8 → ZMod 2

local instance (priority := high) instAddCommGroupZMod2 : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

section
abbrev QZ : Type := ↥Q ⧸ Subgroup.center ↥Q
@[expose] noncomputable def conjQHom (m : ↥M) : ↥Q →* ↥Q where
  toFun q := ⟨(m : J) * q * (m : J)⁻¹, AltQuot.conj_mem_Q_of_mem_M m.2 q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q r := Subtype.ext (by simp [mul_assoc])
theorem conjQHom_apply (m : ↥M) (q : ↥Q) :
    conjQHom m q = ⟨(m : J) * q * (m : J)⁻¹, AltQuot.conj_mem_Q_of_mem_M m.2 q.2⟩ := Subtype.ext rfl
theorem conjQHom_one_apply (q : ↥Q) : conjQHom (1 : ↥M) q = q := by
  rw [conjQHom_apply]
  apply Subtype.ext
  simp
theorem conjQHom_mul_apply (a b : ↥M) (q : ↥Q) :
    conjQHom (a * b) q = conjQHom a (conjQHom b q) := by
  rw [conjQHom_apply, conjQHom_apply, conjQHom_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  group
theorem conjQHom_inv (m : ↥M) (q : ↥Q) :
    conjQHom m (conjQHom m⁻¹ q) = q := by
  rw [conjQHom_apply, conjQHom_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group
theorem conjQHom_inv' (m : ↥M) (q : ↥Q) :
    conjQHom m⁻¹ (conjQHom m q) = q := by
  rw [conjQHom_apply, conjQHom_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group
@[expose] noncomputable def quotConjHom (m : ↥M) : QZ →* QZ :=
  QuotientGroup.map (Subgroup.center ↥Q) (Subgroup.center ↥Q) (conjQHom m) (by
    intro x hx
    rw [Subgroup.mem_comap]
    change x ∈ Subgroup.center ↥Q at hx
    change conjQHom m x ∈ Subgroup.center ↥Q
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have h := congrArg Subtype.val (hx ⟨(m : J)⁻¹ * (g : J) * (m : J),
      AltQuot.conj_mem_Q_of_mem_M (M.inv_mem m.2) g.2⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    apply Subtype.ext
    change (g : J) * ((m : J) * (x : J) * (m : J)⁻¹) =
      ((m : J) * (x : J) * (m : J)⁻¹) * (g : J)
    calc
      (g : J) * ((m : J) * (x : J) * (m : J)⁻¹)
          = (m : J) * (((m : J)⁻¹ * (g : J) * (m : J)) * (x : J)) * (m : J)⁻¹ := by group
      _ = (m : J) * ((x : J) * ((m : J)⁻¹ * (g : J) * (m : J))) * (m : J)⁻¹ := by rw [h]
      _ = ((m : J) * (x : J) * (m : J)⁻¹) * (g : J) := by group)
theorem quotConjHom_mk (m : ↥M) (q : ↥Q) :
    quotConjHom m (QuotientGroup.mk q : QZ) = QuotientGroup.mk (conjQHom m q) :=
  QuotientGroup.map_mk (Subgroup.center ↥Q) (Subgroup.center ↥Q) (conjQHom m) _ q
@[expose] noncomputable def quotConj (m : ↥M) : QZ ≃* QZ :=
  MulEquiv.mk
    { toFun := quotConjHom m
      invFun := quotConjHom m⁻¹
      left_inv := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H q => rw [quotConjHom_mk, quotConjHom_mk, conjQHom_inv']
      right_inv := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H q => rw [quotConjHom_mk, quotConjHom_mk, conjQHom_inv] }
    (map_mul (quotConjHom m))
theorem quotConj_mk (m : ↥M) (q : ↥Q) :
    quotConj m (QuotientGroup.mk q : QZ) = QuotientGroup.mk (conjQHom m q) :=
  quotConjHom_mk m q
@[expose] noncomputable def actQ : ↥M →* MulAut QZ where
  toFun := quotConj
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H q => rw [quotConj_mk, conjQHom_one_apply]; rfl
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H q =>
        rw [quotConj_mk, MulAut.mul_apply, quotConj_mk, quotConj_mk, conjQHom_mul_apply]
theorem actQ_mk (m : ↥M) (q : ↥Q) :
    actQ m (QuotientGroup.mk q : QZ) = QuotientGroup.mk (conjQHom m q) :=
  quotConj_mk m q

theorem comm_mem_center (a b : ↥Q) : ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
  rw [← isExtraspecialPGroup_Q.2.1, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem Q_le_actQ_ker : Q.subgroupOf M ≤ actQ.ker := by
  intro q hq
  have hm : (q : J) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [actQ_mk, MulAut.one_apply]
    apply QuotientGroup.eq.2
    have hEq : (conjQHom q g)⁻¹ * g = ⁅(⟨(q : J), hm⟩ : ↥Q), g⁻¹⁆ := by
      rw [conjQHom_apply, commutatorElement_def]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hEq]
    exact comm_mem_center _ _

@[expose] noncomputable def actMQ : AltQuot.MQ →* MulAut QZ :=
  QuotientGroup.lift (Q.subgroupOf M) actQ Q_le_actQ_ker

theorem actMQ_mk (m : ↥M) : actMQ (AltQuot.proj m) = actQ m :=
  QuotientGroup.lift_mk' (Q.subgroupOf M) Q_le_actQ_ker m

end

section Transport

open CFSG.Sporadic.Th.Max3.InvRep

@[expose] noncomputable def linOfAut (e : QZ ≃* QZ) : V8 ≃ₗ[ZMod 2] V8 :=
  let th : Multiplicative V8 ≃* QZ := theta
  let E : V8 ≃+ V8 := AddEquiv.toMultiplicative.symm (th.trans (e.trans th.symm))
  LinearEquiv.mk
    (LinearMap.mk E.toAddMonoidHom (by
      intro c x
      rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases c with rfl | rfl
      · simp
      · simp))
    E.symm E.left_inv E.right_inv

theorem theta_linOfAut (e : QZ ≃* QZ) (v : V8) :
    theta (Multiplicative.ofAdd (linOfAut e v)) = e (theta (Multiplicative.ofAdd v)) := by
  have h : Multiplicative.ofAdd (linOfAut e v) =
      theta.symm (e (theta (Multiplicative.ofAdd v))) := rfl
  rw [h, MulEquiv.apply_symm_apply]

theorem linOfAut_one : linOfAut (1 : QZ ≃* QZ) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply Multiplicative.ofAdd.injective
  apply theta.injective
  rw [theta_linOfAut]
  rfl

theorem linOfAut_mul (a b : QZ ≃* QZ) : linOfAut (a * b) = linOfAut a * linOfAut b := by
  apply LinearEquiv.ext
  intro v
  apply Multiplicative.ofAdd.injective
  apply theta.injective
  rw [theta_linOfAut (a * b) v, MulAut.mul_apply, LinearEquiv.mul_apply,
    theta_linOfAut a (linOfAut b v), theta_linOfAut b v]

@[expose] noncomputable def linOfAutHom : MulAut QZ →* (V8 ≃ₗ[ZMod 2] V8) where
  toFun := linOfAut
  map_one' := linOfAut_one
  map_mul' := linOfAut_mul

@[expose] noncomputable def rho8a : alternatingGroup (Fin 9) →* (V8 ≃ₗ[ZMod 2] V8) :=
  linOfAutHom.comp (MonoidHom.comp actMQ kappa.symm.toMonoidHom)

theorem rho8a_kap (m : ↥M) : rho8a (kap m) = linOfAut (actQ m) := by
  show linOfAut (actMQ (kappa.symm (kappa (AltQuot.proj m)))) = linOfAut (actQ m)
  rw [MulEquiv.symm_apply_apply, actMQ_mk]

theorem theta_rho8a_kap (m : ↥M) (g : ↥Q) (v : V8)
    (hv : theta (Multiplicative.ofAdd v) = QuotientGroup.mk g) :
    theta (Multiplicative.ofAdd (rho8a (kap m) v)) =
      QuotientGroup.mk ⟨(m : J) * g * (m : J)⁻¹,
        AltQuot.conj_mem_Q_of_mem_M m.2 g.2⟩ := by
  rw [rho8a_kap, theta_linOfAut, hv, actQ_mk, conjQHom_apply]

theorem kap_x_eq : kap (⟨x, x_mem_M⟩ : ↥M) = ⟨aPerm, aPerm_mem⟩ := by
  apply Subtype.ext
  simpa [genM, Gen.eval] using kap_genM (Gen.x)

theorem kap_y_eq : kap (⟨y, y_mem_M⟩ : ↥M) = ⟨bPerm, bPerm_mem⟩ := by
  apply Subtype.ext
  simpa [genM, Gen.eval] using kap_genM (Gen.y)

theorem rho8a_aPerm (v : V8) : rho8a ⟨aPerm, aPerm_mem⟩ v = B1.mulVec v := by
  apply Multiplicative.ofAdd.injective
  apply theta.injective
  rw [← kap_x_eq]
  rw [theta_rho8a_kap ⟨x, x_mem_M⟩ ⟨nf 0 v, nf_mem_Q 0 v⟩ v
    (theta_apply_nf 0 v)]
  rw [← theta_B1 v]

theorem rho8a_bPerm (v : V8) : rho8a ⟨bPerm, bPerm_mem⟩ v = B2.mulVec v := by
  apply Multiplicative.ofAdd.injective
  apply theta.injective
  rw [← kap_y_eq]
  rw [theta_rho8a_kap ⟨y, y_mem_M⟩ ⟨nf 0 v, nf_mem_Q 0 v⟩ v
    (theta_apply_nf 0 v)]
  rw [← theta_B2 v]

theorem closure_aPerm_bPerm :
    Subgroup.closure ({⟨aPerm, aPerm_mem⟩, ⟨bPerm, bPerm_mem⟩} :
      Set (alternatingGroup (Fin 9))) = ⊤ := by
  have hM : Subgroup.closure ({⟨x, x_mem_M⟩, ⟨y, y_mem_M⟩} : Set ↥M) = ⊤ := by
    have hsetM : (Subgroup.subtype M) '' ({⟨x, x_mem_M⟩, ⟨y, y_mem_M⟩} : Set ↥M) =
        ({x, y} : Set J) := by
      ext z
      simp [Subgroup.subtype]
    have htop : Subgroup.map (Subgroup.subtype M) (⊤ : Subgroup ↥M) = M := by
      ext x
      simp [Subgroup.mem_map]
    have hmap : Subgroup.map (Subgroup.subtype M)
        (Subgroup.closure ({⟨x, x_mem_M⟩, ⟨y, y_mem_M⟩} : Set ↥M)) =
        Subgroup.map (Subgroup.subtype M) (⊤ : Subgroup ↥M) := by
      rw [MonoidHom.map_closure, hsetM, htop]
      rfl
    exact Subgroup.map_injective (Subgroup.subtype_injective M) hmap
  have hproj : Subgroup.closure ({AltQuot.proj ⟨x, x_mem_M⟩, AltQuot.proj ⟨y, y_mem_M⟩} :
      Set AltQuot.MQ) = ⊤ := by
    have h := MonoidHom.map_closure AltQuot.proj
      ({⟨x, x_mem_M⟩, ⟨y, y_mem_M⟩} : Set ↥M)
    rw [hM, Subgroup.map_top_of_surjective _ AltQuot.proj_surjective] at h
    simpa using h.symm
  have hk := congrArg (Subgroup.map kappa.toMonoidHom) hproj
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ kappa.surjective] at hk
  have hset : kappa '' ({AltQuot.proj ⟨x, x_mem_M⟩, AltQuot.proj ⟨y, y_mem_M⟩} :
      Set AltQuot.MQ) = ({⟨aPerm, aPerm_mem⟩, ⟨bPerm, bPerm_mem⟩} :
        Set (alternatingGroup (Fin 9))) := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl | rfl, rfl⟩
      · left; exact Subtype.ext kappa_mk_x
      · right; exact Subtype.ext kappa_mk_y
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inl rfl, Subtype.ext kappa_mk_x⟩
      · exact ⟨_, Or.inr rfl, Subtype.ext kappa_mk_y⟩
  have hk' : Subgroup.closure (⇑kappa '' ({AltQuot.proj ⟨x, x_mem_M⟩, AltQuot.proj ⟨y, y_mem_M⟩} :
      Set AltQuot.MQ)) = ⊤ := by
    simpa only [MulEquiv.coe_toMonoidHom] using hk
  rw [hset] at hk'
  exact hk'

abbrev qf (v : V8) : ZMod 2 := CFSG.Certificates.ExtraspecialNF.qf c v

@[expose] def enc (v : V8) : ℕ := ∑ i : Fin 8, (v i).val * 2 ^ (i : ℕ)

@[expose] def e0 : V8 := Pi.single 0 1

@[expose] def e01 : V8 := Pi.single 0 1 + Pi.single 1 1

@[expose] def genPerm : Bool → alternatingGroup (Fin 9)
  | true => ⟨aPerm, aPerm_mem⟩
  | false => ⟨bPerm, bPerm_mem⟩

@[expose] def permWord : List Bool → alternatingGroup (Fin 9)
  | [] => 1
  | b :: w => permWord w * genPerm b

@[expose] def applyWord : List Bool → V8 → V8
  | [], v => v
  | b :: w, v => applyWord w (if b then B1.mulVec v else B2.mulVec v)

theorem applyWord_eq_rho8a (w : List Bool) (v : V8) :
    applyWord w v = rho8a (permWord w) v := by
  induction w generalizing v with
  | nil => rw [applyWord, permWord, map_one]; rfl
  | cons b w ih =>
      rw [applyWord, ih, permWord, map_mul, LinearEquiv.mul_apply]
      congr 1
      cases b
      · exact (rho8a_bPerm v).symm
      · exact (rho8a_aPerm v).symm

@[expose] def wordsSing : List (List Bool) := [[],
 [],
 [false],
 [],
 [false, false, false, false, false],
 [],
 [false, false, true, false, false, false, false],
 [false, false, false, false, true, false, false, true, false, false, true, false, false],
 [false, false, false, false, false, true],
 [false, false, true, false, false, false, false, true],
 [],
 [false, false, false, false, true, false, false, true, false, false, true, false, false, true],
 [false, false, false, false, true, false, false, true, false],
 [],
 [],
 [],
 [false, false, false, false],
 [false, false, true, false, false, false],
 [false, false, true, false, false, true, false, false, true, false, false],
 [],
 [],
 [false, false, false, false, true, false, false, true, false, false, true, false],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, true, false, false, false, false, false, true],
 [],
 [false, false, false, false, true, false, true, false, false, true, false],
 [],
 [],
 [],
 [false, false, true, false, true, false, true, false, true],
 [],
 [false, false, true, false, false, false, false, true, false, true, false, true],
 [false, false, false, false, false, true, false, true, false, true],
 [false, false, false, false, true, false, true, false, true, false, true],
 [false, false, false, false, true, false, true, false, false, true, false, true, false, false],
 [false, false, false, false, true, false, true, false, true, false, false],
 [],
 [],
 [false, false, true, false, true],
 [false, false, false, false, true, false, false, false, false, false],
 [false, false, true, false, false, false, true, false, false, false, false, false],
 [],
 [],
 [false, false, false, false, true, false, false, false, true, false, false, true, false, false],
 [],
 [false, false, false, false, true, false, false, true],
 [],
 [false, false, false, false, true, false, false, false, true, false, false],
 [false, false, false, false, true, false, true, false, false, false, true],
 [],
 [],
 [],
 [false, false, false, false, false, true, false, false, false],
 [false, false, true, false, false, false, true, false, true],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, true, false, false, false, false],
 [],
 [false, false, false, false, true],
 [false, false, true, false, false, true, false, false, true, false, false, true],
 [false, false, true, false, false, false, true],
 [],
 [],
 [false, false, false, false, true, false, true, false, false, false, false, false],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, false, true, false, false, true, false, true],
 [],
 [false, false, false, false, true, false, true, false, false, true, false, true],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, false, true, false, false, true, false],
 [false, false, false, false, true, false, true],
 [false, false, false, false, true, false],
 [],
 [false, false, false, false, true, false, true, false],
 [],
 [false, false, true, false, false, false, true, false, false, true, false, false, true],
 [false, false, false, false, true, false, true, false, false],
 [false, false, false, false, true, false, true, false, true],
 [false, false, true, false, false, false, true, false, false, true, false, false],
 [],
 [false, false, false, false, true, false, true, false, false, true],
 [false, false, true, false, false, false, false, true, false, false, false],
 [],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, false],
 [],
 [],
 [false, false, false, false, true, false, false, false, false, true, false, false],
 [false, false, true, false, false, false, true, false, false, true, false],
 [false, false, false, false, false, true, false, false, false, false, true],
 [],
 [],
 [false, false, true],
 [false, false, true, false, false, true, false, false, true, false],
 [false, false, false],
 [false, false, false, false, false, true, false, true, false, false],
 [false, false, true, false, false, false, false, true, false, true, false, true, false, true],
 [],
 [false, false, true, false, false],
 [],
 [false, false, true, false, false, false, false, true, false, false],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, false, true, false, false, false, false, true, false, false],
 [false, false, true, false, true, false, true],
 [],
 [],
 [],
 [false, false, true, false, false, false, false, true, false, true],
 [false, false, false, false, false, true, false, true],
 [],
 [false, false, false, false, true, false, false, true, false, false, true],
 [false, false, true, false, true, false, true, false],
 [false, false, true, false, false, false, false, true, false, true, false],
 [],
 [false, false, false, false, false, true, false, true, false],
 [],
 [false, false, false, false, false, true, false, true, false, false, false],
 [false, false, true, false],
 [false, false, true, false, false, false, true, false, false, false, false, false, true],
 [false, false, false, false, true, false, true, false, true, false],
 [false, false, false, false, true, false, true, false, true, false, false, true],
 [false, false, true, false, false, false, true, false, false, true, false, false, false],
 [],
 [],
 [false, false, false, false, true, false, true, false, false, true, false, true, false],
 [],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, false, true],
 [],
 [],
 [false, false, true, false, false, true, false, false, true, false, true],
 [false, false],
 [false, false, false, true],
 [false, false, false, false, true, false, true, false, false, false, true, false],
 [false, false, false, false, false, true, false, false, false, false],
 [false, false, false, false, true, false, false, false, true, false, false, false],
 [],
 [false, false, false, false, false, true, false, true, false, false, true],
 [],
 [false, false, true, false, false, false, false, true, false, true, false, true, false],
 [false, false, true, false, false, true],
 [],
 [false, false, false, false, true, false, false, true, false, false, false, false],
 [false, false, false, false, false, true, false, false, false, true, false, false],
 [false, false, false, false, true, false, false, false, false, true, false],
 [false, false, false, false, true, false, false, false, true, false, false, true, false, true],
 [false, false, false, false, true, false, false, false, true],
 [],
 [false, false, true, false, false, false, true, false, false, true],
 [false, false, false, false, true, false, false, false, true, false, false, true, false],
 [],
 [false, false, false, false, true, false, false, false],
 [false, false, true, false, false, false, true, false, false],
 [],
 [],
 [],
 [false, false, true, false, true, false, false],
 [false, false, false, false, false, true, false, false, false, true, false, true],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, true, false, true],
 [false, false, true, false, false, false, false, true, false, true, false, true, false, false],
 [],
 [false, false, true, false, false, true, false],
 [false, false, false, false, true, false, false, false, false],
 [],
 [false, false, true, false, false, false, true, false, false, false],
 [false, false, true, false, true, false, false, false],
 [false, false, true, false, false, false, true, false, false, false, false],
 [false, false, true, false, true, false, false, false, false, false],
 [false, false, true, false, true, false, false, false, false],
 [],
 [false, false, false, false, true, false, false],
 [false, false, false, false, true, false, false, false, true, false, false, true],
 [],
 [false, false, false, false, true, false, true, false, false, false],
 [false, false, true, false, false, false, true, false],
 [],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, false, true, false, false, false, true],
 [],
 [false, false, false, false, false, true, false, false, false, false, true, false],
 [],
 [],
 [],
 [],
 [false, false, true, false, false, false, true, false, true, false],
 [],
 [false, false, true, false, true, false],
 [],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, true, false, false, true, false, false],
 [false, false, true, false, false, false, false, true, false],
 [],
 [false, false, false, false, false, true, false],
 [false, false, false, false, true, false, false, true, false, false],
 [false, false, false, false, false, true, false, false, false, true, false],
 [],
 [],
 [],
 [false, false, false, false, true, false, false, false, false, true],
 [false, false, false, false, true, false, false, true, false, false, false],
 [],
 [false, false, false, false, false, true, false, false],
 [false, false, true, false, false, true, false, true, false],
 [],
 [false, false, true, false, false, false, false, true, false, true, false, true, false,
   false, true],
 [false, false, true, false, false, true, false, true],
 [false, false, true, false, false, false, true, false, false, false, false, true],
 [false, false, true, false, true, false, false, false, false, true],
 [false, false, true, false, true, false, false, false, false, false, true],
 [],
 [],
 [false, false, false, false, true, false, false, true, false, false, false, false, false, true],
 [false, false, false, false, true, false, false, true, false, false, false, false, false],
 [false, false, false, false, true, false, false, false, true, false],
 [false, false, true, false, true, false, true, false, false, true],
 [false, false, true, false, false, true, false, true, false, true, false],
 [],
 [false, false, false, false, false, true, false, true, false, false, false, false, true],
 [false, false, true, false, true, false, true, false, false],
 [],
 [false, false, true, false, false, false, false, true, false, true, false, false],
 [false, false, false, false, false, true, false, true, false, false, false, false],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, false, true, false, true, false]]

@[expose] def wordsNon : List (List Bool) := [[],
 [],
 [],
 [],
 [],
 [false, false, false, false, false],
 [],
 [],
 [],
 [],
 [false, false, false, false, false, true],
 [],
 [],
 [false, true, false, false, true, false, false, true],
 [false, true, false, false, true, false, false],
 [false, false, true, false, false, false, true, false, false, true, false],
 [],
 [],
 [],
 [false, true, false, true, false, true, false, false, false],
 [false, false, false, false],
 [],
 [false, true, false, false, false, false],
 [false, false, true, false, false, false, false],
 [false, false, true, false, false, false, false, true, false],
 [false, false, false, true, false, false, true],
 [],
 [false, false, false, true, false, true, false, false, true],
 [],
 [false, false, false, true, false, false, true, false, true, false, false],
 [false, false, true, false, false, true, false, false, false, true, false, false, false],
 [false, true, false, true, false, false, false, true, false, false],
 [],
 [false, true, false, true, false, true, false, true],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, false],
 [false, true, false, true],
 [],
 [],
 [],
 [false, false, false, false, true, false, true],
 [false, true, false, false, false, true, false, false],
 [],
 [false, true, false, true, false, false, true, false, false, false, false],
 [],
 [false, true, false, false, true, false],
 [],
 [],
 [false, false, true, false, false, false, true, false, false, false, false],
 [false, false, true, false, false, false, true, false, false, true],
 [false, false, true, false, false, true, false, false, false, false],
 [],
 [],
 [false, true, false, true, false, false],
 [false, false, false, true, false, false, false, true],
 [false, false, false, true, false],
 [false, true, false, false, true, false, true, false],
 [false, true, false, true, false, false, true, false],
 [],
 [false, false, false, true, false, true, false],
 [],
 [],
 [],
 [false, true, false, true, false, true, false, false, false, true],
 [false, false, false, true, false, false, false, true, false],
 [],
 [false, false, false, true, false, false],
 [false, false, false, true, false, true, false, false],
 [false, false, false, false, true],
 [false, true, false, false, false, false, true],
 [],
 [false, false, true, false, false, false, false, true],
 [],
 [false, false, true, false, false, true, false, false, false, true, false, false, false, false],
 [false, false, false, true, false, true, false, false, true, false],
 [false, true, false, true, false, false, false, true, false, false, false],
 [],
 [],
 [],
 [false, false, false, true, false, false, false, true, false, false],
 [],
 [false, false, true, false, false, true, false, false, false, true, false, false, true],
 [],
 [],
 [],
 [],
 [false, false, true, false, false, true, false, false, false, true, false, false],
 [],
 [],
 [false, true, false, true, false, false, false, true, false, true],
 [false, true, false, true, false, false, false, true, false],
 [false, false, false, true, false, false, true, false, true, false],
 [false, false, true, false, false, true, false, false, false, true, false],
 [],
 [false, false, true, false, false, false, false, false, true],
 [false, false, true, false, false, true, false],
 [],
 [],
 [],
 [false, false, false, true, false, false, false, false, true, false],
 [false, true],
 [],
 [],
 [],
 [],
 [],
 [false, true, false, true, false, true, false, false],
 [],
 [false, true, false, true, false, false, false, true],
 [],
 [false, true, false, true, false, false, true, false, false, true],
 [false, false, true, false, false, false, true, false],
 [false, false, false, true, false, false, true, false, true],
 [false, true, false, false, true, false, true, false, true, false],
 [false, false, true, false, false, true, false, false, false, false, true, false],
 [],
 [],
 [false, true, false, true, false, true],
 [false, true, false, false, false],
 [false, false, false],
 [],
 [],
 [false, false, true, false, false, false],
 [],
 [],
 [],
 [false, true, false, true, false, true, false],
 [],
 [false, true, false],
 [],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, false, true, false, false, true],
 [false, false, false, false, true, false],
 [],
 [false, true, false, false, false, false, true, false],
 [false, true, false, true, false, false, true, false, false, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, false, true, false, false, false, false, false],
 [],
 [false, true, false, false, false, false, false],
 [false],
 [],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, true, false, false, false, false, true, false, true],
 [],
 [false, false, false, false, true, false, false, false],
 [],
 [],
 [false, false, false, true, false, true, false, true, false, false],
 [],
 [],
 [],
 [],
 [],
 [false, false, false, true, false, false, false, false, true],
 [],
 [],
 [false, false, false, true, false, false, false, false],
 [],
 [],
 [false, true, false, true, false, false, true, false, false, false],
 [false, true, false, false, false, true, false],
 [false, true, false, false, false, true, false, true],
 [],
 [],
 [false, true, false, false, false, false, true, false, false],
 [false, false, false, false, true, false, false, true, false],
 [false, false, true, false, false, true, false, false, false, true],
 [],
 [],
 [false, false, true, false, false, true],
 [],
 [],
 [false, true, false, false, false, true, false, true, false],
 [],
 [],
 [],
 [],
 [],
 [false, false, true, false, true],
 [],
 [],
 [false, true, false, false, true, false, true],
 [],
 [],
 [false, false, false, true, false, false, false],
 [false, true, false, true, false, false, true],
 [false, false, false, true, false, true],
 [false, true, false, true, false, false, true, false, false, true, false],
 [false, false, true, false, false, true, false, false, false, false, true],
 [false, false, true, false, false, false, true, false, false],
 [],
 [false, true, false, false, true, false, true, false, true],
 [],
 [false, false, true, false, false, true, false, false],
 [false, false, false, true, false, true, false, true],
 [false, true, false, true, false, false, false],
 [false, true, false, true, false, false, true, false, false],
 [],
 [false, false, true, false, false, false, true, false, true],
 [],
 [false, true, false, false, false, true],
 [false, true, false, true, false],
 [false, false, false, true],
 [false, false, false, true, false, false, true, false],
 [false, false, false, true, false, false, true, false, true, false, false, false],
 [false, false, true, false, false, false, false, true, false, false],
 [],
 [],
 [false, false, true, false, false, false, true],
 [],
 [],
 [],
 [false, false, false, true, false, true, false, true, false],
 [false, false, true, false, false, false, true, false, false, false],
 [false, false, true, false, false, true, false, false, false],
 [],
 [],
 [false, true, false, false, false, true, false, true, false, true],
 [],
 [],
 [false, false, true, false, false],
 [],
 [],
 [],
 [],
 [],
 [false, false, true, false],
 [false, false, false, true, false, true, false, true, false, false, false],
 [],
 [],
 [],
 [],
 [],
 [false, true, false, false, true],
 [],
 [],
 [false, true, false, false],
 [],
 [],
 [false, true, false, true, false, true, false, false, false, false, false],
 [false, false],
 [false, false, true],
 []]

theorem wordsSing_spec (v : V8) (hv : v ≠ 0) (hq : qf v = 0) :
    applyWord (wordsSing.getD (enc v) []) e0 = v := by
  decide +kernel +revert

theorem wordsNon_spec (v : V8) (hv : v ≠ 0) (hq : qf v = 1) :
    applyWord (wordsNon.getD (enc v) []) e01 = v := by
  decide +kernel +revert

theorem exists_rho8a_eq {v w : V8} (hv : v ≠ 0) (hw : w ≠ 0) (h : qf v = qf w) :
    ∃ g : alternatingGroup (Fin 9), rho8a g v = w := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf v) with hq | hq
  · have hwq : qf w = 0 := h.symm.trans hq
    have hv' : rho8a (permWord (wordsSing.getD (enc v) [])) e0 = v := by
      rw [← applyWord_eq_rho8a]
      exact wordsSing_spec v hv hq
    have hw' : rho8a (permWord (wordsSing.getD (enc w) [])) e0 = w := by
      rw [← applyWord_eq_rho8a]
      exact wordsSing_spec w hw hwq
    refine ⟨permWord (wordsSing.getD (enc w) []) *
      (permWord (wordsSing.getD (enc v) []))⁻¹, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, map_inv]
    change rho8a (permWord (wordsSing.getD (enc w) []))
      ((rho8a (permWord (wordsSing.getD (enc v) []))).symm v) = w
    have hinv : (rho8a (permWord (wordsSing.getD (enc v) []))).symm v = e0 := by
      calc (rho8a (permWord (wordsSing.getD (enc v) []))).symm v =
          (rho8a (permWord (wordsSing.getD (enc v) []))).symm
            (rho8a (permWord (wordsSing.getD (enc v) [])) e0) := by rw [hv']
        _ = e0 := LinearEquiv.symm_apply_apply _ _
    rw [hinv, hw']
  · have hwq : qf w = 1 := h.symm.trans hq
    have hv' : rho8a (permWord (wordsNon.getD (enc v) [])) e01 = v := by
      rw [← applyWord_eq_rho8a]
      exact wordsNon_spec v hv hq
    have hw' : rho8a (permWord (wordsNon.getD (enc w) [])) e01 = w := by
      rw [← applyWord_eq_rho8a]
      exact wordsNon_spec w hw hwq
    refine ⟨permWord (wordsNon.getD (enc w) []) *
      (permWord (wordsNon.getD (enc v) []))⁻¹, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, map_inv]
    change rho8a (permWord (wordsNon.getD (enc w) []))
      ((rho8a (permWord (wordsNon.getD (enc v) []))).symm v) = w
    have hinv : (rho8a (permWord (wordsNon.getD (enc v) []))).symm v = e01 := by
      calc (rho8a (permWord (wordsNon.getD (enc v) []))).symm v =
          (rho8a (permWord (wordsNon.getD (enc v) []))).symm
            (rho8a (permWord (wordsNon.getD (enc v) [])) e01) := by rw [hv']
        _ = e01 := LinearEquiv.symm_apply_apply _ _
    rw [hinv, hw']

@[expose] def vx : V8 := ![1, 0, 0, 0, 0, 0, 0, 0]
@[expose] def vy : V8 := ![0, 1, 0, 0, 0, 0, 0, 0]
@[expose] def vz : V8 := ![0, 0, 1, 0, 0, 0, 0, 0]

theorem qf_zero : qf (0 : V8) = 0 := by decide +kernel
theorem qf_e0 : qf e0 = 0 := by decide +kernel
theorem qf_e01 : qf e01 = 1 := by decide +kernel
theorem e0_ne_zero : e0 ≠ 0 := by decide +kernel
theorem e01_ne_zero : e01 ≠ 0 := by decide +kernel

theorem not_indicator_singular (Q' : QuadraticForm (ZMod 2) V8)
    (hQ : ∀ v, Q' v = if v ≠ 0 ∧ qf v = 0 then (1 : ZMod 2) else 0) : False := by
  have h := QuadraticMap.polar_add_right Q' vx vy vz
  simp only [QuadraticMap.polar] at h
  rw [hQ, hQ, hQ, hQ, hQ, hQ, hQ] at h
  revert h
  decide +kernel

theorem not_indicator_nonzero (Q' : QuadraticForm (ZMod 2) V8)
    (hQ : ∀ v, Q' v = if v = 0 then (0 : ZMod 2) else 1) : False := by
  have h := QuadraticMap.polar_add_right Q' vx vy vz
  simp only [QuadraticMap.polar] at h
  rw [hQ, hQ, hQ, hQ, hQ, hQ, hQ] at h
  revert h
  decide +kernel

theorem eq_qf_of_invariant (Q' : QuadraticForm (ZMod 2) V8)
    (hinv : ∀ g v, Q' (rho8a g v) = Q' v)
    (hnd : ∀ v, v ≠ 0 → ∃ w, QuadraticMap.polar Q' v w ≠ 0) :
    ∀ v, Q' v = qf v := by
  have hval : ∀ v, Q' v = if v = 0 then 0 else if qf v = 0 then Q' e0 else Q' e01 := by
    intro v
    by_cases hv : v = 0
    · subst hv
      simp [QuadraticMap.map_zero]
    · by_cases hq : qf v = 0
      · obtain ⟨g, hg⟩ := exists_rho8a_eq (v := e0) (w := v) e0_ne_zero hv
          (qf_e0.trans hq.symm)
        have h1 : Q' v = Q' e0 := by rw [← hg, hinv]
        rw [h1]
        simp [hv, hq]
      · have hq1 : qf v = 1 := by
          rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf v) with h | h
          · exact absurd h hq
          · exact h
        obtain ⟨g, hg⟩ := exists_rho8a_eq (v := e01) (w := v) e01_ne_zero hv
          (qf_e01.trans hq1.symm)
        have h1 : Q' v = Q' e01 := by rw [← hg, hinv]
        rw [h1]
        simp [hv, hq]
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (Q' e0) with ha | ha <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (Q' e01) with hb | hb
  · exfalso
    have hzero : ∀ v, Q' v = 0 := by
      intro v
      rw [hval v]
      by_cases hv : v = 0 <;> by_cases hq : qf v = 0 <;>
        simp [hv, hq, ha, hb]
    obtain ⟨w, hw⟩ := hnd e0 e0_ne_zero
    simp only [QuadraticMap.polar, hzero] at hw
    exact hw rfl
  · intro v
    by_cases hv : v = 0
    · subst hv
      simp [QuadraticMap.map_zero, qf_zero]
    · by_cases hq : qf v = 0
      · rw [hval v]
        simp [hv, hq, ha]
      · have hq1 : qf v = 1 := by
          rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf v) with h | h
          · exact absurd h hq
          · exact h
        rw [hval v]
        simp [hv, hq, hb, hq1]
  · have hQ : ∀ v, Q' v = if v ≠ 0 ∧ qf v = 0 then (1 : ZMod 2) else 0 := by
      intro v
      rw [hval v]
      by_cases hv : v = 0
      · simp [hv]
      · by_cases hq : qf v = 0
        · simp [hv, hq, ha]
        · simp [hv, hq, hb]
    exact absurd (not_indicator_singular Q' hQ) (fun h => h)
  · have hQ : ∀ v, Q' v = if v = 0 then (0 : ZMod 2) else 1 := by
      intro v
      rw [hval v]
      by_cases hv : v = 0
      · simp [hv]
      · by_cases hq : qf v = 0
        · simp [hv, hq, ha]
        · simp [hv, hq, hb]
    exact absurd (not_indicator_nonzero Q' hQ) (fun h => h)

end Transport

@[expose] def ext9 (x : V8) : Fin 9 → ZMod 2 :=
  fun j => if h : (j : ℕ) < 8 then x ⟨j, h⟩ else ∑ i, x i
theorem ext9_castSucc (x : V8) (i : Fin 8) : ext9 x (Fin.castSucc i) = x i := by simp [ext9]
theorem ext9_last (x : V8) : ext9 x (Fin.last 8) = ∑ i, x i := by simp [ext9]
theorem ext9_add (x y : V8) : ext9 (x + y) = ext9 x + ext9 y := by
  funext j
  by_cases hj : (j : ℕ) < 8
  · simp [ext9, hj, Pi.add_apply]
  · simp [ext9, hj, Finset.sum_add_distrib]
theorem ext9_smul (c : ZMod 2) (x : V8) : ext9 (c • x) = c • ext9 x := by
  funext j
  by_cases hj : (j : ℕ) < 8
  · simp [ext9, hj, Pi.smul_apply]
  · simp [ext9, hj, Finset.mul_sum]
theorem sum_ext9 (x : V8) : ∑ j : Fin 9, ext9 x j = 0 := by decide +kernel +revert
theorem sum_ext9_comp (x : V8) (τ : Equiv.Perm (Fin 9)) :
    ∑ i : Fin 8, ext9 x (τ (Fin.castSucc i)) = ext9 x (τ (Fin.last 8)) := by
  have h := Fin.sum_univ_castSucc (fun j : Fin 9 => ext9 x (τ j))
  have htot : (∑ j : Fin 9, ext9 x (τ j)) = 0 := by
    rw [Equiv.sum_comp τ (fun j => ext9 x j)]
    exact sum_ext9 x
  rw [htot] at h
  have h2 : ∑ i : Fin 8, ext9 x (τ (Fin.castSucc i)) =
      - ext9 x (τ (Fin.last 8)) := eq_neg_of_add_eq_zero_left h.symm
  rw [h2, CharTwo.neg_eq]
@[expose] noncomputable def rho8pFun (σ : alternatingGroup (Fin 9)) (x : V8) : V8 :=
  fun i => ext9 x ((σ : Equiv.Perm (Fin 9))⁻¹ (Fin.castSucc i))
theorem ext9_rho8p_fun (σ : alternatingGroup (Fin 9)) (x : V8) :
    ext9 (rho8pFun σ x) = fun j => ext9 x ((σ : Equiv.Perm (Fin 9))⁻¹ j) := by
  funext j
  by_cases hj : (j : ℕ) < 8
  · have h : j = Fin.castSucc ⟨j, hj⟩ := Fin.ext rfl
    rw [h, ext9_castSucc]
    rfl
  · have hj8 : j = Fin.last 8 := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hj8, ext9_last]
    exact sum_ext9_comp x ((σ : Equiv.Perm (Fin 9))⁻¹)
theorem rho8pFun_left (σ : alternatingGroup (Fin 9)) (x : V8) :
    rho8pFun σ⁻¹ (rho8pFun σ x) = x := by
  funext i
  have h := congrFun (ext9_rho8p_fun σ x) ((σ : Equiv.Perm (Fin 9)) (Fin.castSucc i))
  simp only [rho8pFun, Subgroup.coe_inv, inv_inv] at h ⊢
  rw [h, show ((σ : Equiv.Perm (Fin 9)))⁻¹ = (σ : Equiv.Perm (Fin 9)).symm from rfl,
    Equiv.symm_apply_apply, ext9_castSucc]
theorem rho8pFun_right (σ : alternatingGroup (Fin 9)) (x : V8) :
    rho8pFun σ (rho8pFun σ⁻¹ x) = x := by
  funext i
  have h := congrFun (ext9_rho8p_fun σ⁻¹ x) ((σ : Equiv.Perm (Fin 9))⁻¹ (Fin.castSucc i))
  simp only [rho8pFun, Subgroup.coe_inv, inv_inv] at h ⊢
  rw [h, show ((σ : Equiv.Perm (Fin 9)))⁻¹ = (σ : Equiv.Perm (Fin 9)).symm from rfl,
    Equiv.apply_symm_apply, ext9_castSucc]
@[expose] noncomputable def rho8pMap (σ : alternatingGroup (Fin 9)) : V8 →ₗ[ZMod 2] V8 where
  toFun := rho8pFun σ
  map_add' x y := by
    funext i
    exact congrFun (ext9_add x y) _
  map_smul' c x := by
    funext i
    exact congrFun (ext9_smul c x) _
@[expose] noncomputable def rho8pLin (σ : alternatingGroup (Fin 9)) : V8 ≃ₗ[ZMod 2] V8 :=
  LinearEquiv.mk (rho8pMap σ) (rho8pFun σ⁻¹) (rho8pFun_left σ) (rho8pFun_right σ)
@[expose] noncomputable def rho8p : alternatingGroup (Fin 9) →* (V8 ≃ₗ[ZMod 2] V8) where
  toFun := rho8pLin
  map_one' := by
    ext x i
    simp [rho8pLin, rho8pMap, rho8pFun, ext9_castSucc]
  map_mul' σ τ := by
    ext x i
    simp only [rho8pLin, rho8pMap, rho8pFun, Equiv.Perm.mul_apply, Subgroup.coe_mul,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    exact (congrFun (ext9_rho8p_fun τ x) ((σ : Equiv.Perm (Fin 9))⁻¹ (Fin.castSucc i))).symm
theorem rho8p_apply (σ : alternatingGroup (Fin 9)) (x : V8) (i : Fin 8) :
    (rho8p σ x) i = ext9 x ((σ : Equiv.Perm (Fin 9))⁻¹ (Fin.castSucc i)) := rfl
theorem ext9_rho8p (σ : alternatingGroup (Fin 9)) (x : V8) :
    ext9 (rho8p σ x) = fun j => ext9 x ((σ : Equiv.Perm (Fin 9))⁻¹ j) :=
  ext9_rho8p_fun σ x

@[expose] def supp9 (x : V8) : Finset (Fin 9) := Finset.univ.filter fun j => ext9 x j = 1
theorem mem_supp9 (x : V8) (j : Fin 9) : j ∈ supp9 x ↔ ext9 x j = 1 := by
  simp [supp9]
theorem even_card_supp9 (x : V8) : Even (supp9 x).card := by
  decide +kernel +revert
theorem supp9_nonempty {x : V8} (hx : x ≠ 0) : (supp9 x).Nonempty := by
  decide +kernel +revert
theorem ext9_injective : Function.Injective ext9 := by
  intro x y h
  funext i
  have h' := congrFun h (Fin.castSucc i)
  simpa [ext9_castSucc] using h'
theorem ext9_eq_iff_mem (x : V8) (a b : Fin 9) :
    ext9 x a = ext9 x b ↔ (a ∈ supp9 x ↔ b ∈ supp9 x) := by
  constructor
  · intro h
    rw [mem_supp9, mem_supp9, h]
  · intro h
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (ext9 x a) with ha | ha <;>
      rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (ext9 x b) with hb | hb
    · rw [ha, hb]
    · simp [mem_supp9, ha, hb] at h
    · simp [mem_supp9, ha, hb] at h
    · rw [ha, hb]
theorem rho8p_eq_self_iff (σ : alternatingGroup (Fin 9)) (x : V8) :
    rho8p σ x = x ↔ ∀ j, ((σ : Equiv.Perm (Fin 9)) j ∈ supp9 x ↔ j ∈ supp9 x) := by
  rw [← ext9_injective.eq_iff, ext9_rho8p]
  constructor
  · intro h j
    have h' : ∀ j, ext9 x ((σ : Equiv.Perm (Fin 9))⁻¹ j) = ext9 x j := fun j => congrFun h j
    rw [← ext9_eq_iff_mem]
    have := h' ((σ : Equiv.Perm (Fin 9)) j)
    simpa using this.symm
  · intro h
    funext j
    rw [ext9_eq_iff_mem]
    have := h ((σ : Equiv.Perm (Fin 9))⁻¹ j)
    simpa using this.symm
@[expose] def A9FaithfulDimEight :
    Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V], Module.finrank (ZMod 2) V = 8 →
    ∀ ρ : alternatingGroup (Fin 9) →* (V ≃ₗ[ZMod 2] V), Function.Injective ρ →
      ∃ (σ : Equiv.Perm (Fin 9)) (e : V ≃ₗ[ZMod 2] V8),
        (∀ g v, e (ρ g v) = rho8a (conjA σ g) (e v)) ∨
          (∀ g v, e (ρ g v) = rho8p g (e v))

end CFSG.Sporadic.Th.Recog
