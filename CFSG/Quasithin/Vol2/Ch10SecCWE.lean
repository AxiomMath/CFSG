module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.G2SL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.G16

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.QuasithinUnique
open scoped MatrixGroups Pointwise

section SL2

variable {F : Type*} [Field F]

theorem inv_lower_left (k : SL(2, F)) : (k⁻¹).1 1 0 = -k.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

theorem conj_mem_Rg {k t : SL(2, F)} (hk : k.1 1 0 = 0) (ht : t ∈ Rg F) :
    k * t * k⁻¹ ∈ Rg F := by
  obtain ⟨c, rfl⟩ := mem_Rg.1 ht
  have hdet := det_eq_one' k
  have hk' : (k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hk
  rw [hk', mul_zero, sub_zero] at hdet
  refine mem_Rg.2 ⟨(k : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * c, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hk', e12_coe] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

theorem e21_one_lower_left :
    (e21 (1 : F)).1 1 0 ≠ 0 ∧ ((e21 (1 : F))⁻¹).1 1 0 ≠ 0 := by
  rw [inv_lower_left]
  simp

end SL2

section Standard

variable {U : Type} [CommGroup U] {F : Type} [Field F]

theorem exists_mulEquiv_Rg [Finite F] [CharP F 2] {Gm R : Subgroup (MulAut U)}
    (hR : IsSylowTwoOf R Gm)
    (e : ↥Gm ≃* SL(2, F)) :
    ∃ e' : ↥Gm ≃* SL(2, F), ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup SL(2, F) := (R.subgroupOf Gm).map e.toMonoidHom with hP
  have hP2 : IsPGroup 2 P :=
    (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm).map e.toMonoidHom
  have hPi : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_map_of_bijective e.bijective]
    exact hR.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) (Rg_isPGroup.toSylow Rg_index_odd)
    (hP2.toSylow hPi)
  have hgP : ∀ y : SL(2, F), y ∈ P ↔ g⁻¹ * y * g ∈ Rg F := by
    intro y
    have h1 : y ∈ ((g • Rg_isPGroup.toSylow Rg_index_odd : Sylow 2 SL(2, F)) :
        Subgroup SL(2, F)) ↔ y ∈ P := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [← h1, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  refine ⟨e.trans (MulAut.conj g⁻¹ : SL(2, F) ≃* SL(2, F)), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, ← hgP, hP, Subgroup.mem_map_equiv,
    MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

variable {Gm R : Subgroup (MulAut U)} {e' : ↥Gm ≃* SL(2, F)}

theorem eq_top_of_R_conj [CharP F 2] (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F)
    (S : Subgroup ↥Gm)
    (h1 : ∀ y : ↥Gm, (y : MulAut U) ∈ R → y ∈ S)
    (h2 : ∀ y : ↥Gm, (y : MulAut U) ∈ R → e'.symm (e21 1) * y * (e'.symm (e21 1))⁻¹ ∈ S) :
    S = ⊤ := by
  have hRS : Rg F ≤ S.map e'.toMonoidHom := fun t ht => by
    rw [Subgroup.mem_map_equiv]
    exact h1 _ ((he' _).2 (by rwa [MulEquiv.apply_symm_apply]))
  have hRS' : (Rg F).map (MulAut.conj (e21 (1 : F))⁻¹⁻¹).toMonoidHom ≤
      S.map e'.toMonoidHom := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_map_equiv]
    have h := h2 (e'.symm t) ((he' _).2 (by rwa [MulEquiv.apply_symm_apply]))
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
  have htop := Rg_sup_conj_eq_top (e21 (1 : F))⁻¹ e21_one_lower_left.2
  rw [eq_top_iff]
  intro x _
  have hx : e' x ∈ S.map e'.toMonoidHom := (sup_le hRS hRS') (htop ▸ Subgroup.mem_top (e' x))
  rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hx

theorem symm_mem_R (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F) {t : SL(2, F)}
    (ht : t ∈ Rg F) : ((e'.symm t : ↥Gm) : MulAut U) ∈ R :=
  (he' _).2 (by rwa [MulEquiv.apply_symm_apply])

theorem mul_self_eq_one [CharP F 2] (hRG : R ≤ Gm)
    (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F) {r : MulAut U} (hr : r ∈ R) :
    r * r = 1 := by
  obtain ⟨b, hb⟩ := mem_Rg.1 ((he' ⟨r, hRG hr⟩).1 hr)
  have h : e' (⟨r, hRG hr⟩ * ⟨r, hRG hr⟩) = 1 := by rw [map_mul, ← hb, e12_mul_self]
  have h' : (⟨r, hRG hr⟩ * ⟨r, hRG hr⟩ : ↥Gm) = 1 := e'.injective (by rw [h, map_one])
  exact congrArg Subtype.val h'

theorem mem_stabSub_of_forall {D : Subgroup U} {g : MulAut U} (h1 : ∀ d ∈ D, g d ∈ D)
    (h2 : ∀ d ∈ D, g⁻¹ d ∈ D) : g ∈ stabSub D := fun u => by
  refine ⟨fun hu => ?_, h1 u⟩
  have h := h2 _ hu
  rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h

theorem mul_inv_mem_fixV [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hRG : R ≤ Gm)
    (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F)
    (hC : ∀ r ∈ R, r ≠ 1 → fixV (Subgroup.zpowers r) = fixV R) {r : MulAut U} (hr : r ∈ R)
    (u : U) : r u * u⁻¹ ∈ fixV R := by
  by_cases h1 : r = 1
  · rw [h1, MulAut.one_apply, mul_inv_cancel]
    exact (fixV R).one_mem
  rw [← hC r hr h1]
  have hinv : ∀ v : U, v⁻¹ = v := fun v => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hU]
  have hrr : r (r u) = u := by
    have h := congrArg (fun φ : MulAut U => φ u) (mul_self_eq_one hRG he' hr)
    simpa using h
  have hfix : r (r u * u⁻¹) = r u * u⁻¹ := by
    rw [map_mul, map_inv, hrr, ← hinv (r u * u⁻¹), mul_inv_rev, inv_inv]
  have hst : Subgroup.zpowers r ≤ MulAction.stabilizer (MulAut U) (r u * u⁻¹) :=
    Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hfix)
  intro y hy
  have h := hst hy
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h

theorem apply_mem_fixV_of_lower_left_eq_zero (hRG : R ≤ Gm)
    (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F) {k : SL(2, F)} (hk : k.1 1 0 = 0)
    {u : U} (hu : u ∈ fixV R) : ((e'.symm k : ↥Gm) : MulAut U) u ∈ fixV R := by
  intro r hr
  have hk' : (k⁻¹).1 1 0 = 0 := by rw [inv_lower_left, hk, neg_zero]
  have hconj : (((e'.symm k)⁻¹ * ⟨r, hRG hr⟩ * e'.symm k : ↥Gm) : MulAut U) ∈ R := by
    rw [he', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h := conj_mem_Rg hk' ((he' ⟨r, hRG hr⟩).1 hr)
    rwa [inv_inv] at h
  have h := hu _ hconj
  have e1 : r (((e'.symm k : ↥Gm) : MulAut U) u) = ((e'.symm k : ↥Gm) : MulAut U)
      ((((e'.symm k)⁻¹ * ⟨r, hRG hr⟩ * e'.symm k : ↥Gm) : MulAut U) u) := by
    simp [MulAut.mul_apply]
  rw [e1, h]

theorem mem_fixV_of_mul_inv_mem [CharP F 2] (hRG : R ≤ Gm)
    (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F) {u u' : U} (hu : u ∈ fixV R)
    (hu' : u' ∈ fixV R) (h : u * (((e'.symm (e21 1) : ↥Gm) : MulAut U) u')⁻¹ ∈ fixV Gm) :
    u ∈ fixV Gm := by
  set x : ↥Gm := e'.symm (e21 1) with hx
  set v := (x : MulAut U) u' with hv
  have hZR : fixV Gm ≤ fixV R := fun z hz r hr => hz r (hRG hr)
  have hvR : v ∈ fixV R := by
    have e1 : v = (u * v⁻¹)⁻¹ * u := by group
    rw [e1]
    exact mul_mem (inv_mem (hZR h)) hu
  let S : Subgroup ↥Gm := (MulAction.stabilizer (MulAut U) v).subgroupOf Gm
  have hmemS : ∀ y : ↥Gm, y ∈ S ↔ (y : MulAut U) v = v := fun y => by
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hS : S = ⊤ := by
    refine eq_top_of_R_conj he' S (fun y hy => (hmemS y).2 (hvR _ hy)) fun y hy => ?_
    rw [hmemS, ← hx]
    have e1 : ((x * y * x⁻¹ : ↥Gm) : MulAut U) v = (x : MulAut U) ((y : MulAut U) u') := by
      simp [hv, MulAut.mul_apply]
    rw [e1, hu' _ hy]
  have hvG : v ∈ fixV Gm := fun g hg => (hmemS ⟨g, hg⟩).1 (hS ▸ Subgroup.mem_top _)
  have e2 : u = (u * v⁻¹) * v := by group
  rw [e2]
  exact mul_mem h hvG

theorem exists_eq_mul_apply [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hRG : R ≤ Gm)
    (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F)
    (hC : ∀ r ∈ R, r ≠ 1 → fixV (Subgroup.zpowers r) = fixV R)
    (hgen : (⨆ g ∈ Gm, (fixV R).map (g : MulAut U).toMonoidHom) = ⊤) (u : U) :
    ∃ a ∈ fixV R, ∃ b ∈ fixV R, u = a * ((e'.symm (e21 1) : ↥Gm) : MulAut U) b := by
  set x : ↥Gm := e'.symm (e21 1) with hx
  set D : Subgroup U := fixV R ⊔ (fixV R).map (x : MulAut U).toMonoidHom with hD
  have hcomm : ∀ {r : MulAut U}, r ∈ R → ∀ v : U, r v * v⁻¹ ∈ fixV R :=
    fun hr v => mul_inv_mem_fixV hU hRG he' hC hr v
  have hRD : ∀ r ∈ R, ∀ d ∈ D, r d ∈ D := by
    intro r hr d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hd
    have e1 : r (a * b) = (a * (r b * b⁻¹)) * b := by
      rw [map_mul, ha r hr]
      group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem ha (hcomm hr b))) (Subgroup.mem_sup_right hb)
  have hRD' : ∀ r ∈ R, ∀ d ∈ D, ((x : MulAut U) * r * (x : MulAut U)⁻¹) d ∈ D := by
    intro r hr d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hd
    obtain ⟨a', ha', rfl⟩ := hb
    set c := r ((x : MulAut U)⁻¹ a) * ((x : MulAut U)⁻¹ a)⁻¹ with hc
    have e1 : ((x : MulAut U) * r * (x : MulAut U)⁻¹) (a * (x : MulAut U) a') =
        a * ((x : MulAut U) c * (x : MulAut U) a') := by
      have h3 : r a' = a' := ha' r hr
      simp only [MulAut.mul_apply, map_mul, hc, map_inv, MulAut.inv_apply,
        MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, h3]
      rw [mul_comm _ a⁻¹, mul_assoc a⁻¹, mul_inv_cancel_left]
    change ((x : MulAut U) * r * (x : MulAut U)⁻¹) (a * (x : MulAut U) a') ∈ D
    rw [e1]
    refine mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (mul_mem ?_ ⟨a', ha', rfl⟩))
    exact ⟨c, hcomm hr _, rfl⟩
  let S : Subgroup ↥Gm := (stabSub D).subgroupOf Gm
  have hS : S = ⊤ := by
    refine eq_top_of_R_conj he' S (fun y hy => ?_) fun y hy => ?_
    · exact Subgroup.mem_subgroupOf.2
        (mem_stabSub_of_forall (hRD _ hy) (hRD _ (inv_mem hy)))
    · rw [← hx, Subgroup.mem_subgroupOf]
      have hinv : ((x * y * x⁻¹ : ↥Gm) : MulAut U)⁻¹ =
          (x : MulAut U) * (y : MulAut U)⁻¹ * (x : MulAut U)⁻¹ := by
        simp [mul_assoc]
      refine mem_stabSub_of_forall (fun d hd => ?_) fun d hd => ?_
      · exact hRD' _ hy d hd
      · rw [hinv]
        exact hRD' _ (inv_mem hy) d hd
  have hGD : ∀ g ∈ Gm, ∀ d ∈ D, g d ∈ D := fun g hg d hd =>
    ((Subgroup.mem_subgroupOf.1 (hS ▸ Subgroup.mem_top (⟨g, hg⟩ : ↥Gm)) : g ∈ stabSub D) d).2 hd
  have hle : (⨆ g ∈ Gm, (fixV R).map (g : MulAut U).toMonoidHom) ≤ D :=
    iSup₂_le fun g hg => by
      rintro _ ⟨a, ha, rfl⟩
      exact hGD g hg a (Subgroup.mem_sup_left ha)
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hle (hgen ▸ Subgroup.mem_top u))
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨a, ha, b', hb', hab.symm⟩

end Standard

end CFSG.Quasithin.Vol2.Ch10.G16
