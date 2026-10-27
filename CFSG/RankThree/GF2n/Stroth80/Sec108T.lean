module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Rho
public import CFSG.RankThree.GF2n.Stroth80.Sec108Norm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem sup_Q_eq_of_bar_eq [(Q.subgroupOf M).Normal] {S T : Subgroup G} (hS : S ≤ M)
    (hT : T ≤ M) (h : bar M Q S = bar M Q T) : S ⊔ Q = T ⊔ Q := by
  have key : ∀ {A B : Subgroup G}, A ≤ M → bar M Q A = bar M Q B → A ≤ B ⊔ Q := by
    intro A B hAM hAB a ha
    have hpi : HS6.piM M Q a ∈ bar M Q B := by
      rw [← hAB]
      exact HS6.piM_mem_bar ha (hAM ha)
    obtain ⟨b, hbB, hbM, hb⟩ := (HS6.mem_bar (M := M) (Q := Q) (S := B) (y := HS6.piM M Q a)).mp hpi
    have hq : a⁻¹ * b ∈ Q := (HS6.piM_eq_iff (hAM ha) hbM).mp hb.symm
    have haeq : a = b * (a⁻¹ * b)⁻¹ := by group
    rw [haeq]
    exact (B ⊔ Q).mul_mem (Subgroup.mem_sup_left hbB) (Subgroup.mem_sup_right (Q.inv_mem hq))
  exact le_antisymm (sup_le (key hS h) le_sup_right) (sup_le (key hT h.symm) le_sup_right)

private theorem mem_normalizer_sup_of_mem_normalizer_bar [(Q.subgroupOf M).Normal]
    (hQM : Q ≤ M) {Y : Subgroup G} (hYM : Y ≤ M) {m : G} (hmM : m ∈ M)
    (hY : HS6.piM M Q m ∈ Subgroup.normalizer ((bar M Q Y : Subgroup (Mbar M Q)) : Set _)) :
    m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
  have hMnorm : M ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hQM
  have hQconj : conjSubgroup m Q = Q := conjSubgroup_eq_self_iff.mpr (hMnorm hmM)
  have hbar : bar M Q (conjSubgroup m Y) = bar M Q Y := by
    have h1 : conjSubgroup (HS6.piM M Q m) (bar M Q Y) = bar M Q Y :=
      conjSubgroup_eq_self_iff.mpr hY
    rwa [HS6.conj_bar hQM hmM] at h1
  have hconjM : conjSubgroup m Y ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hmM (hYM hy)) (M.inv_mem hmM)
  have hsup : conjSubgroup m Y ⊔ Q = Y ⊔ Q := sup_Q_eq_of_bar_eq hconjM hYM hbar
  have hconj : conjSubgroup m (Y ⊔ Q) = Y ⊔ Q := by
    rw [conjSubgroup_sup', hQconj, hsup]
  exact conjSubgroup_eq_self_iff.mp hconj

theorem NLY_le_bar_normalizer [(Q.subgroupOf M).Normal] {L : Subgroup G} (hQM : Q ≤ M)
    (hYM : Y ≤ M) :
    Sec108.NLY (bar M Q L) (bar M Q Y) ≤
      bar M Q (M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := by
  intro y hy
  obtain ⟨m, hmM, hpi⟩ := HS6.exists_piM y
  have hmY : m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_normalizer_bar hQM hYM hmM (by rw [hpi]; exact hy.2)
  rw [← hpi]
  exact HS6.piM_mem_bar ⟨hmM, hmY⟩ hmM

private noncomputable def Sec108Data.chosenT (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    AM.M₀.E ≃+ AM.M₀.E :=
  (AM.glob.act m (Subgroup.mem_inf.mp m.2).1).choose_spec.choose_spec.choose

section T

variable (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)

noncomputable def Sec108Data.frameVec (v : Fin 3 → AM.K) : AM.M₀.E :=
  ∑ i, ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ v) i • (D.bV AM i : AM.M₀.E)

noncomputable def Sec108Data.frameCoord (e : AM.M₀.E) : Fin 3 → AM.K :=
  haveI := Classical.dec (e ∈ AM.Vsp hc t)
  if h : e ∈ AM.Vsp hc t then
    (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ
      fun i => (D.bV AM).repr ⟨e, h⟩ i
  else 0

private noncomputable def Sec108Data.frameMat : Matrix (Fin 3) (Fin 3) AM.K :=
  (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)

private noncomputable def Sec108Data.frameMatInv : Matrix (Fin 3) (Fin 3) AM.K :=
  (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
    Matrix (Fin 3) (Fin 3) AM.K)

private theorem Sec108Data.frameMat_mul_inv : D.frameMat AM * D.frameMatInv AM = 1 := by
  rw [Sec108Data.frameMat, Sec108Data.frameMatInv, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem Sec108Data.frameMat_inv_mul : D.frameMatInv AM * D.frameMat AM = 1 := by
  rw [Sec108Data.frameMat, Sec108Data.frameMatInv, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem Sec108Data.frameVec_eq (v : Fin 3 → AM.K) :
    D.frameVec AM v = ∑ i, (D.frameMat AM *ᵥ v) i • (D.bV AM i : AM.M₀.E) := rfl

private theorem Sec108Data.frameCoord_of_mem {e : AM.M₀.E} (he : e ∈ AM.Vsp hc t) :
    D.frameCoord AM e =
      (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) *ᵥ fun i => (D.bV AM).repr ⟨e, he⟩ i := by
  simp [Sec108Data.frameCoord, he]

private theorem Sec108Data.frameCoord_eq {e : AM.M₀.E} (he : e ∈ AM.Vsp hc t) :
    D.frameCoord AM e = D.frameMatInv AM *ᵥ (D.bV AM).repr ⟨e, he⟩ := by
  rw [D.frameCoord_of_mem AM he, Sec108Data.frameMatInv]

private theorem Sec108Data.frameVec_add (v w : Fin 3 → AM.K) :
    D.frameVec AM (v + w) = D.frameVec AM v + D.frameVec AM w := by
  rw [D.frameVec_eq, D.frameVec_eq, D.frameVec_eq]
  simp only [Matrix.mulVec_add, Pi.add_apply, Finset.sum_add_distrib, add_smul]

private theorem Sec108Data.frameVec_smul (c : AM.K) (v : Fin 3 → AM.K) :
    D.frameVec AM (c • v) = c • D.frameVec AM v := by
  rw [D.frameVec_eq, D.frameVec_eq]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

private theorem Sec108Data.frameVec_mem_Vsp (v : Fin 3 → AM.K) :
    D.frameVec AM v ∈ AM.Vsp hc t := by
  rw [D.frameVec_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (D.bV AM i).2

private theorem Sec108Data.frameCoord_add {e f : AM.M₀.E} (he : e ∈ AM.Vsp hc t)
    (hf : f ∈ AM.Vsp hc t) :
    D.frameCoord AM (e + f) = D.frameCoord AM e + D.frameCoord AM f := by
  have hef := (AM.Vsp hc t).add_mem he hf
  rw [D.frameCoord_eq AM hef, D.frameCoord_eq AM he, D.frameCoord_eq AM hf]
  rw [show (⟨e + f, hef⟩ : ↥(AM.Vsp hc t)) = ⟨e, he⟩ + ⟨f, hf⟩ from rfl, map_add]
  change D.frameMatInv AM *ᵥ ((D.bV AM).repr ⟨e, he⟩ + (D.bV AM).repr ⟨f, hf⟩) =
    D.frameMatInv AM *ᵥ (D.bV AM).repr ⟨e, he⟩ +
      D.frameMatInv AM *ᵥ (D.bV AM).repr ⟨f, hf⟩
  rw [Matrix.mulVec_add]

private theorem Sec108Data.frameCoord_smul (c : AM.K) {e : AM.M₀.E}
    (he : e ∈ AM.Vsp hc t) :
    D.frameCoord AM (c • e) = c • D.frameCoord AM e := by
  have hce := (AM.Vsp hc t).smul_mem c he
  rw [D.frameCoord_eq AM hce, D.frameCoord_eq AM he]
  rw [show (⟨c • e, hce⟩ : ↥(AM.Vsp hc t)) = c • ⟨e, he⟩ from rfl, map_smul]
  change D.frameMatInv AM *ᵥ (c • (D.bV AM).repr ⟨e, he⟩) =
    c • D.frameMatInv AM *ᵥ (D.bV AM).repr ⟨e, he⟩
  rw [Matrix.mulVec_smul]

private theorem Sec108Data.frameCoord_zero : D.frameCoord AM (0 : AM.M₀.E) = 0 := by
  rw [D.frameCoord_eq AM (AM.Vsp hc t).zero_mem]
  have h0 : (D.bV AM).repr ⟨0, (AM.Vsp hc t).zero_mem⟩ = 0 := map_zero _
  rw [h0]
  change D.frameMatInv AM *ᵥ (0 : Fin 3 → AM.K) = 0
  rw [Matrix.mulVec_zero]

private theorem Sec108Data.frameCoord_sum_bV (w : Fin 3 → AM.K) :
    D.frameCoord AM (∑ i, w i • (D.bV AM i : AM.M₀.E)) = D.frameMatInv AM *ᵥ w := by
  have hmem : (∑ i, w i • (D.bV AM i : AM.M₀.E)) ∈ AM.Vsp hc t :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (D.bV AM i).2
  rw [D.frameCoord_eq AM hmem]
  congr 1
  ext i
  have h1 : (⟨∑ j, w j • (D.bV AM j : AM.M₀.E), hmem⟩ : ↥(AM.Vsp hc t)) =
      ∑ j, w j • D.bV AM j := rfl
  refine (congrArg (fun x : ↥(AM.Vsp hc t) => (D.bV AM).repr x i) h1).trans ?_
  simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]

private theorem Sec108Data.frameCoord_frameVec (v : Fin 3 → AM.K) :
    D.frameCoord AM (D.frameVec AM v) = v := by
  rw [D.frameVec_eq, D.frameCoord_sum_bV, Matrix.mulVec_mulVec,
    D.frameMat_inv_mul, Matrix.one_mulVec]

private theorem Sec108Data.frameVec_frameCoord {e : AM.M₀.E} (he : e ∈ AM.Vsp hc t) :
    D.frameVec AM (D.frameCoord AM e) = e := by
  rw [D.frameCoord_eq AM he, D.frameVec_eq, Matrix.mulVec_mulVec, D.frameMat_mul_inv,
    Matrix.one_mulVec]
  have h := congrArg Subtype.val ((D.bV AM).sum_repr ⟨e, he⟩)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Subtype.coe_mk] using h

private theorem Sec108Data.frameVec_e0_mem_Bsp :
    D.frameVec AM (Sec108.e₀ AM.K) ∈ D.Bsp AM := by
  simpa [Sec108Data.frameVec] using D.frameB_mem_Bsp AM

private theorem Sec108Data.frameVec_e0_ne_zero :
    D.frameVec AM (Sec108.e₀ AM.K) ≠ 0 := by
  intro h0
  have h1 := D.frameCoord_frameVec AM (Sec108.e₀ AM.K)
  rw [h0, D.frameCoord_zero] at h1
  have h2 : (0 : AM.K) = 1 := by simpa [Sec108.e₀] using congrFun h1 0
  exact (zero_ne_one : (0 : AM.K) ≠ 1) h2

noncomputable def Sec108Data.semiFun
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (v : Fin 3 → AM.K) :
    Fin 3 → AM.K :=
  D.frameCoord AM
    ((AM.glob.act m (Subgroup.mem_inf.mp m.2).1).choose_spec.choose_spec.choose
      (D.frameVec AM v))

private theorem Sec108Data.semiFun_eq_chosen
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (v : Fin 3 → AM.K) :
    D.semiFun AM m v =
      D.frameCoord AM (D.chosenT AM m (D.frameVec AM v)) := rfl

private theorem Sec108Data.chosenT_apply_pi
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) {x : G} (hx : x ∈ Q) :
    D.chosenT AM m (AM.M₀.π x) = AM.M₀.π (m * x * m⁻¹) :=
  ((AM.glob.act m (Subgroup.mem_inf.mp m.2).1).choose_spec.choose_spec.choose_spec.2.1
    x hx).symm

private theorem Sec108Data.chosenT_smul
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (c : AM.K)
    (e : AM.M₀.E) :
    D.chosenT AM m (c • e) =
      (AM.glob.act m (Subgroup.mem_inf.mp m.2).1).choose c • D.chosenT AM m e :=
  (AM.glob.act m (Subgroup.mem_inf.mp m.2).1).choose_spec.choose_spec.choose_spec.1 c e

private theorem Sec108Data.chosenT_mem_Vsp
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) {e : AM.M₀.E}
    (he : e ∈ AM.Vsp hc t) : D.chosenT AM m e ∈ AM.Vsp hc t := by
  obtain ⟨x, hxV, hxQ, hxe⟩ := mem_imgSub.mp he
  rw [← hxe, D.chosenT_apply_pi AM m hxQ]
  have hV := D.conj_Vt_of_mem_normalizer_root (Subgroup.mem_inf.mp m.2).1
    (Subgroup.mem_inf.mp m.2).2
  have hmxV : (m : G) * x * (m : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hV) x).mp hxV
  exact mem_imgSub.mpr (AM.M₀.pi_mem_img hmxV (hc.Vt_le_Q t hmxV))

theorem Sec108Data.semiFun_add (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (v w : Fin 3 → AM.K) :
    D.semiFun AM m (v + w) = D.semiFun AM m v + D.semiFun AM m w := by
  rw [D.semiFun_eq_chosen AM m (v + w), D.semiFun_eq_chosen AM m v,
    D.semiFun_eq_chosen AM m w, D.frameVec_add, map_add]
  exact D.frameCoord_add AM (D.chosenT_mem_Vsp AM m (D.frameVec_mem_Vsp AM v))
    (D.chosenT_mem_Vsp AM m (D.frameVec_mem_Vsp AM w))

noncomputable def Sec108Data.semiEnd
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    AddMonoid.End (Fin 3 → AM.K) :=
  (AddMonoid.End.equiv (Fin 3 → AM.K)).symm
    (AddMonoidHom.mk' (D.semiFun AM m) (D.semiFun_add AM m))

private theorem Sec108Data.semiEnd_apply
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (v : Fin 3 → AM.K) :
    (AddMonoid.End.equiv (Fin 3 → AM.K) (D.semiEnd AM m)) v = D.semiFun AM m v := rfl

private theorem Sec108Data.chosenT_one_eq_refl :
    D.chosenT AM 1 = AddEquiv.refl AM.M₀.E := by
  refine AddEquiv.ext fun e => ?_
  obtain ⟨x, hxQ, rfl⟩ := AM.M₀.π_surj e
  rw [D.chosenT_apply_pi AM 1 hxQ]
  simp

private theorem Sec108Data.chosenT_mem_Q_eq_refl
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (hm : (m : G) ∈ Q) :
    D.chosenT AM m = AddEquiv.refl AM.M₀.E := by
  refine AddEquiv.ext fun e => ?_
  obtain ⟨x, hxQ, rfl⟩ := AM.M₀.π_surj e
  rw [D.chosenT_apply_pi AM m hxQ]
  simp only [AddEquiv.refl_apply]
  change AM.M₀.π ((m : G) * x * (m : G)⁻¹) = AM.M₀.π x
  have hcomm : ⁅(m : G), x⁆ ∈ Z := by
    have h : ⁅(m : G), x⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hm hxQ
    rwa [hc.hyp.special.1] at h
  have hmx : (m : G) * x * (m : G)⁻¹ = ⁅(m : G), x⁆ * x := by
    rw [commutatorElement_def]; group
  conv_lhs => rw [hmx]
  rw [AM.M₀.π_mul _ (hc.hyp.Z_normal.1 hcomm) x hxQ,
    (AM.M₀.π_ker _ (hc.hyp.Z_normal.1 hcomm)).mpr hcomm, zero_add]

private theorem Sec108Data.chosenT_mul_apply
    (m m' : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (e : AM.M₀.E) :
    D.chosenT AM (m * m') e = D.chosenT AM m (D.chosenT AM m' e) := by
  obtain ⟨x, hxQ, rfl⟩ := AM.M₀.π_surj e
  have hm'M := (Subgroup.mem_inf.mp m'.2).1
  have hmx'Q : (m' : G) * x * (m' : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm'M) x).mp hxQ
  rw [D.chosenT_apply_pi AM (m * m') hxQ, D.chosenT_apply_pi AM m' hxQ]
  change AM.M₀.π (((m : G) * (m' : G)) * x * (((m : G) * (m' : G))⁻¹)) =
    D.chosenT AM m (AM.M₀.π ((m' : G) * x * (m' : G)⁻¹))
  rw [D.chosenT_apply_pi AM m hmx'Q]
  congr 1
  simp only [Subgroup.coe_inv]
  group

theorem Sec108Data.semiEnd_one : D.semiEnd AM 1 = 1 := by
  apply (AddMonoid.End.equiv (Fin 3 → AM.K)).injective
  apply AddMonoidHom.ext
  intro v
  rw [D.semiEnd_apply, D.semiFun_eq_chosen AM 1 v, D.chosenT_one_eq_refl]
  simp [D.frameCoord_frameVec]

theorem Sec108Data.semiEnd_mul
    (m m' : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    D.semiEnd AM (m * m') = D.semiEnd AM m * D.semiEnd AM m' := by
  apply (AddMonoid.End.equiv (Fin 3 → AM.K)).injective
  apply AddMonoidHom.ext
  intro v
  rw [show (AddMonoid.End.equiv (Fin 3 → AM.K) (D.semiEnd AM m * D.semiEnd AM m')) =
      (AddMonoid.End.equiv (Fin 3 → AM.K) (D.semiEnd AM m)).comp
        (AddMonoid.End.equiv (Fin 3 → AM.K) (D.semiEnd AM m')) from rfl,
    AddMonoidHom.comp_apply, D.semiEnd_apply, D.semiEnd_apply, D.semiEnd_apply]
  calc D.semiFun AM (m * m') v
      = D.frameCoord AM (D.chosenT AM (m * m') (D.frameVec AM v)) :=
          D.semiFun_eq_chosen AM (m * m') v
    _ = D.frameCoord AM (D.chosenT AM m (D.chosenT AM m' (D.frameVec AM v))) := by
          rw [D.chosenT_mul_apply]
    _ = D.frameCoord AM (D.chosenT AM m (D.frameVec AM (D.semiFun AM m' v))) := by
          rw [show D.frameVec AM (D.semiFun AM m' v) =
              D.chosenT AM m' (D.frameVec AM v) from by
            rw [D.semiFun_eq_chosen AM m' v,
              D.frameVec_frameCoord AM (D.chosenT_mem_Vsp AM m' (D.frameVec_mem_Vsp AM v))]]
    _ = D.semiFun AM m (D.semiFun AM m' v) := (D.semiFun_eq_chosen AM m _).symm

noncomputable def Sec108Data.semiT₀ :
    ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) →*
      AddMonoid.End (Fin 3 → AM.K) where
  toFun := D.semiEnd AM
  map_one' := D.semiEnd_one AM
  map_mul' := D.semiEnd_mul AM

private theorem Sec108Data.semiT₀_apply
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (v : Fin 3 → AM.K) :
    (AddMonoid.End.equiv (Fin 3 → AM.K) (D.semiT₀ AM m)) v = D.semiFun AM m v := rfl

theorem Sec108Data.semiT₀_eq_one
    (m : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) (hm : (m : G) ∈ Q) :
    D.semiT₀ AM m = 1 := by
  apply (AddMonoid.End.equiv (Fin 3 → AM.K)).injective
  apply AddMonoidHom.ext
  intro v
  rw [D.semiT₀_apply, D.semiFun_eq_chosen AM m v, D.chosenT_mem_Q_eq_refl AM m hm]
  simp [D.frameCoord_frameVec]

variable [(Q.subgroupOf M).Normal]

noncomputable def Sec108Data.semiT :
    ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)) →* AddMonoid.End (Fin 3 → AM.K) :=
  (barLift (D.semiT₀ AM) (D.semiT₀_eq_one AM)).comp
    (Subgroup.inclusion (NLY_le_bar_normalizer hc.hyp.Q_normal.1 (D.root_le_LB.trans hc.LB_le_M)))

theorem Sec108Data.semiT_piM {m : G}
    (hm : m ∈ M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (h : HS6.piM M Q m ∈ Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)) (v : Fin 3 → AM.K) :
    D.semiT AM ⟨HS6.piM M Q m, h⟩ v = D.semiFun AM ⟨m, hm⟩ v := by
  have hincl : Subgroup.inclusion
      (NLY_le_bar_normalizer hc.hyp.Q_normal.1 (D.root_le_LB.trans hc.LB_le_M))
      ⟨HS6.piM M Q m, h⟩ =
      ⟨HS6.piM M Q m,
        NLY_le_bar_normalizer hc.hyp.Q_normal.1 (D.root_le_LB.trans hc.LB_le_M) h⟩ := rfl
  rw [show D.semiT AM ⟨HS6.piM M Q m, h⟩ v = barLift (D.semiT₀ AM) (D.semiT₀_eq_one AM)
      (Subgroup.inclusion _ ⟨HS6.piM M Q m, h⟩) v from rfl, hincl,
    barLift_piM (D.semiT₀ AM) (D.semiT₀_eq_one AM) ⟨m, hm⟩ hm.1 _]
  exact D.semiT₀_apply AM ⟨m, hm⟩ v

private theorem Sec108Data.semiT_eq_semiFun (g : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)))
    {m : G} (hmS : m ∈ M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hpi : HS6.piM M Q m = (g : Mbar M Q)) (v : Fin 3 → AM.K) :
    D.semiT AM g v = D.semiFun AM ⟨m, hmS⟩ v := by
  have hh : HS6.piM M Q m ∈ Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y) := by
    rw [hpi]; exact g.2
  rw [show g = ⟨HS6.piM M Q m, hh⟩ from Subtype.ext hpi.symm]
  exact D.semiT_piM AM hmS hh v

theorem Sec108Data.semiT_semilinear (g : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y))) :
    ∃ σ : AM.K ≃+* AM.K, ∀ (c : AM.K) (v : Fin 3 → AM.K),
      D.semiT AM g (c • v) = σ c • D.semiT AM g v := by
  have hbar : (g : Mbar M Q) ∈ bar M Q (M ⊓ Subgroup.normalizer
      ((Y ⊔ Q : Subgroup G) : Set G)) :=
    NLY_le_bar_normalizer hc.hyp.Q_normal.1 (D.root_le_LB.trans hc.LB_le_M) g.2
  obtain ⟨m, hmS, -, hpi⟩ := (HS6.mem_bar (M := M) (Q := Q) (S := M ⊓ Subgroup.normalizer
    ((Y ⊔ Q : Subgroup G) : Set G)) (y := (g : Mbar M Q))).mp hbar
  refine ⟨(AM.glob.act m (Subgroup.mem_inf.mp hmS).1).choose, fun c v => ?_⟩
  rw [D.semiT_eq_semiFun AM g hmS hpi (c • v), D.semiT_eq_semiFun AM g hmS hpi v]
  calc D.semiFun AM ⟨m, hmS⟩ (c • v)
      = D.frameCoord AM (D.chosenT AM ⟨m, hmS⟩ (D.frameVec AM (c • v))) :=
          D.semiFun_eq_chosen AM ⟨m, hmS⟩ (c • v)
    _ = D.frameCoord AM (D.chosenT AM ⟨m, hmS⟩ (c • D.frameVec AM v)) := by
          rw [D.frameVec_smul]
    _ = D.frameCoord AM ((AM.glob.act m (Subgroup.mem_inf.mp hmS).1).choose c •
          D.chosenT AM ⟨m, hmS⟩ (D.frameVec AM v)) := by rw [D.chosenT_smul]
    _ = (AM.glob.act m (Subgroup.mem_inf.mp hmS).1).choose c •
          D.frameCoord AM (D.chosenT AM ⟨m, hmS⟩ (D.frameVec AM v)) := by
          rw [D.frameCoord_smul AM _ (D.chosenT_mem_Vsp AM ⟨m, hmS⟩ (D.frameVec_mem_Vsp AM v))]
    _ = (AM.glob.act m (Subgroup.mem_inf.mp hmS).1).choose c •
          D.semiFun AM ⟨m, hmS⟩ v := by rw [D.semiFun_eq_chosen]

private theorem Sec108Data.chosenT_mem_Bsp (m : ↥(M ⊓ Subgroup.normalizer
    ((Y ⊔ Q : Subgroup G) : Set G)))
    (hmBZ : (m : G) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G))
    {e : AM.M₀.E} (he : e ∈ D.Bsp AM) : D.chosenT AM m e ∈ D.Bsp AM := by
  obtain ⟨b, hbB, hbQ, hbe⟩ := AM.M₀.mem_img.mp ((D.mem_Bsp AM).mp he)
  rw [← hbe, D.chosenT_apply_pi AM m hbQ]
  have hmb : (m : G) * b * (m : G)⁻¹ ∈ B ⊔ Z :=
    (Subgroup.mem_normalizer_iff.mp hmBZ b).mp (Subgroup.mem_sup_left hbB)
  obtain ⟨b', hb'B, z, hzZ, hb'z⟩ := exists_mul_of_mem_sup_of_commute
    (fun b hb z hz => (Smith81.Z_central hc.hyp hz (hc.le hb)).symm) hmb
  refine (D.mem_Bsp AM).mpr (AM.M₀.mem_img.mpr ⟨b', hb'B, hc.le hb'B, ?_⟩)
  have hzQ : z ∈ Q := hc.hyp.Z_normal.1 hzZ
  simp only [Subgroup.coe_inv] at hb'z ⊢
  rw [hb'z, AM.M₀.π_mul _ (hc.le hb'B) _ hzQ,
    (AM.M₀.π_ker _ hzQ).mpr hzZ, add_zero]

private theorem Sec108Data.chosenT_eq_phi_of_mem_Rt (r : ↥(Rt M (LB M Q B) t))
    (e : AM.M₀.E) :
    D.chosenT AM ⟨r, ⟨hc.Rt_le_M t r.2, D.Rt_le_normalizer_root r.2⟩⟩ e =
      AM.φ ⟨r, D.Rt_le_H0 r.2⟩ e := by
  obtain ⟨x, hxQ, rfl⟩ := AM.M₀.π_surj e
  rw [D.chosenT_apply_pi AM ⟨r, ⟨hc.Rt_le_M t r.2, D.Rt_le_normalizer_root r.2⟩⟩ hxQ]
  simpa using AM.φ_π ⟨r, D.Rt_le_H0 r.2⟩ x hxQ

private theorem Sec108Data.phi_frameVec_eq_sum (r : ↥(Rt M (LB M Q B) t))
    (v : Fin 3 → AM.K) :
    AM.φ ⟨r, D.Rt_le_H0 r.2⟩ (D.frameVec AM v) =
      ∑ i, (D.matV AM ⟨r, D.Rt_le_H0 r.2⟩ *ᵥ (D.frameMat AM *ᵥ v)) i •
        (D.bV AM i : AM.M₀.E) := by
  have hmV : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨r, D.Rt_le_H0 r.2⟩ e ∈ AM.Vsp hc t := by
    intro e he
    obtain ⟨x, hxV, hxQ, hxe⟩ := mem_imgSub.mp he
    have hmxV : (r : G) * x * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt D.good.1.mem_LB r.2) x).mp hxV
    rw [← hxe, ← AM.φ_π ⟨r, D.Rt_le_H0 r.2⟩ x hxQ]
    exact mem_imgSub.mpr (AM.M₀.pi_mem_img hmxV (hc.Vt_le_Q t hmxV))
  have h1 : AM.φ ⟨r, D.Rt_le_H0 r.2⟩ (D.frameVec AM v) =
      ∑ j, (D.frameMat AM *ᵥ v) j •
        (∑ i, D.matV AM ⟨r, D.Rt_le_H0 r.2⟩ i j • (D.bV AM i : AM.M₀.E)) := by
    rw [D.frameVec_eq]
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [D.phi_bV_eq_sum AM hmV j]
  rw [h1]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

private theorem Sec108Data.frameCoord_phi_eq_rhoMat (r : ↥(Rt M (LB M Q B) t))
    (v : Fin 3 → AM.K) :
    D.frameCoord AM (AM.φ ⟨r, D.Rt_le_H0 r.2⟩ (D.frameVec AM v)) =
      (D.rhoMat AM r : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ v := by
  rw [D.phi_frameVec_eq_sum AM r v, D.frameCoord_sum_bV, Sec108Data.rhoMat]
  rw [← Sec108Data.frameMatInv, ← Sec108Data.frameMat]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem Sec108Data.rho_eq_rhoMat (g : ↥(bar M Q (Rt M (LB M Q B) t))) {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) (hpi : HS6.piM M Q r = (g : Mbar M Q)) :
    ((D.rho AM g : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) =
      D.rhoMat AM ⟨r, hrR⟩ := by
  have hh : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t) := by
    rw [hpi]; exact g.2
  rw [show g = ⟨HS6.piM M Q r, hh⟩ from Subtype.ext hpi.symm]
  exact D.rho_piM AM hrR hh

theorem Sec108Data.semiT_line (g : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y))) :
    ∃ c : AM.K, D.semiT AM g (Sec108.e₀ AM.K) = c • Sec108.e₀ AM.K := by
  have hYM : Y ≤ M := D.root_le_LB.trans hc.LB_le_M
  have hQn : ∀ x ∈ Q, ∀ k ∈ M, k * x * k⁻¹ ∈ Q := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hk) x).mp hx
  obtain ⟨m, hmM, hpi, hmL⟩ := HS6.exists_lift_normalizer hc.hyp.Q_normal.1 hQn
    (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M g.2.1
  have hmY : m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_normalizer_bar hc.hyp.Q_normal.1 hYM hmM (by rw [hpi]; exact g.2.2)
  have hmS : m ∈ M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := ⟨hmM, hmY⟩
  have hmBZ : m ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_11_1a hc D.hyp.width (by norm_num) hmM).mpr (conjSubgroup_eq_self_iff.mp hmL)
  rw [D.semiT_eq_semiFun AM g hmS hpi (Sec108.e₀ AM.K), D.semiFun_eq_chosen AM ⟨m, hmS⟩]
  have hBsp : D.frameVec AM (Sec108.e₀ AM.K) ∈ D.Bsp AM := D.frameVec_e0_mem_Bsp AM
  have hne : D.frameVec AM (Sec108.e₀ AM.K) ≠ 0 := D.frameVec_e0_ne_zero AM
  have hspan : D.Bsp AM = AM.K ∙ D.frameVec AM (Sec108.e₀ AM.K) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (D.finrank_Bsp AM) hBsp hne
  have hmem : D.chosenT AM ⟨m, hmS⟩ (D.frameVec AM (Sec108.e₀ AM.K)) ∈ D.Bsp AM :=
    D.chosenT_mem_Bsp AM ⟨m, hmS⟩ hmBZ hBsp
  obtain ⟨c, hscale⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hmem)
  refine ⟨c, ?_⟩
  rw [← hscale, D.frameCoord_smul AM _ (D.Bsp_le_Vsp AM hBsp), D.frameCoord_frameVec]

theorem Sec108Data.semiT_rho (g : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)))
    (hg : (g : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t)) (v : Fin 3 → AM.K) :
    D.semiT AM g v =
      ((D.rho AM ⟨g, hg⟩ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ v := by
  obtain ⟨r, hrR, hrM, hpi⟩ :=
    (HS6.mem_bar (M := M) (Q := Q) (S := Rt M (LB M Q B) t) (y := (g : Mbar M Q))).mp hg
  have hrS : r ∈ M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    ⟨hrM, D.Rt_le_normalizer_root hrR⟩
  rw [D.semiT_eq_semiFun AM g hrS hpi v, D.semiFun_eq_chosen AM ⟨r, hrS⟩,
    D.chosenT_eq_phi_of_mem_Rt AM ⟨r, hrR⟩, D.frameCoord_phi_eq_rhoMat AM ⟨r, hrR⟩]
  rw [D.rho_eq_rhoMat AM ⟨g, hg⟩ hrR hpi]

end T

end CFSG.RankThree.GF2n.Stroth80
