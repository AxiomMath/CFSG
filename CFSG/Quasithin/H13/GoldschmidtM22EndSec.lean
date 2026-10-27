module

public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Quasithin

variable {G : Type} [Group G]

section Basic

variable {U W : Subgroup G}

theorem normal_subgroupOf_of_comm (h : IsElemAbelianMod U W) : (W.subgroupOf U).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 := (h g g.2 n n.2).1
  have e : ((g * n * g⁻¹ : ↥U) : G) = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact W.mul_mem h1 hn

end Basic

variable (U W : Subgroup G)

abbrev Sec : Type := ↥U ⧸ W.subgroupOf U

variable [hUW : Fact (IsElemAbelianMod U W)]

instance : (W.subgroupOf U).Normal := normal_subgroupOf_of_comm hUW.out

noncomputable instance instCommGroupSec : CommGroup (Sec U W) :=
  { (inferInstance : Group (Sec U W)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h1 := (hUW.out (y⁻¹ : ↥U) (y⁻¹).2 (x⁻¹ : ↥U) (x⁻¹).2).1
      have e : (((x * y)⁻¹ * (y * x) : ↥U) : G) = (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ *
          (x : G)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
      rw [e]
      exact h1 }

omit hUW in
@[expose] def Sec.mk (u : ↥U) : Sec U W := (QuotientGroup.mk u : Sec U W)

theorem Sec.mk_eq_one_iff (u : ↥U) : Sec.mk U W u = 1 ↔ (u : G) ∈ W := by
  rw [Sec.mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit hUW in
theorem Sec.mk_surjective : Function.Surjective (Sec.mk U W) := fun q => by
  induction q using QuotientGroup.induction_on with | H x => exact ⟨x, rfl⟩

theorem Sec.mk_mul (u v : ↥U) : Sec.mk U W (u * v) = Sec.mk U W u * Sec.mk U W v :=
  QuotientGroup.mk_mul _ _ _

theorem Sec.sq_eq_one (q : Sec U W) : q ^ 2 = 1 := by
  induction q using QuotientGroup.induction_on with | H x => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact (hUW.out x x.2 x x.2).2

@[expose] noncomputable def conjU (g : G) (hU : g ∈ Subgroup.normalizer (U : Set G)) : MulAut ↥U :=
  conjAct U ⟨g, hU⟩

omit hUW in
theorem coe_conjU (g : G) (hU : g ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    ((conjU U g hU u : ↥U) : G) = g * u * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion le_rfl ⟨g, hU⟩) u

omit hUW in
theorem map_conjU_subgroupOf (g : G) (hU : g ∈ Subgroup.normalizer (U : Set G))
    (hW : g ∈ Subgroup.normalizer (W : Set G)) :
    (W.subgroupOf U).map (conjU U g hU).toMonoidHom = W.subgroupOf U := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [coe_conjU]
    exact (Subgroup.mem_normalizer_iff.mp hW y).mp hy
  · intro hx
    have hU' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem hU
    have hW' : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := inv_mem hW
    refine ⟨conjU U g⁻¹ hU' x, ?_, ?_⟩
    · rw [coe_conjU]
      exact (Subgroup.mem_normalizer_iff.mp hW' x).mp hx
    · apply Subtype.ext
      rw [coe_conjU, coe_conjU]
      group

@[expose] noncomputable def secAut (g : G) (hU : g ∈ Subgroup.normalizer (U : Set G))
    (hW : g ∈ Subgroup.normalizer (W : Set G)) : MulAut (Sec U W) :=
  QuotientGroup.congr (W.subgroupOf U) (W.subgroupOf U) (conjU U g hU)
    (map_conjU_subgroupOf U W g hU hW)

theorem secAut_mk (g : G) (hU : g ∈ Subgroup.normalizer (U : Set G))
    (hW : g ∈ Subgroup.normalizer (W : Set G)) (u : ↥U) :
    secAut U W g hU hW (Sec.mk U W u) = Sec.mk U W (conjU U g hU u) :=
  QuotientGroup.congr_mk (W.subgroupOf U) (W.subgroupOf U) (conjU U g hU)
    (map_conjU_subgroupOf U W g hU hW) u

@[expose] noncomputable def secHom (X : Subgroup G) (hU : X ≤ Subgroup.normalizer (U : Set G))
    (hW : X ≤ Subgroup.normalizer (W : Set G)) : ↥X →* MulAut (Sec U W) where
  toFun x := secAut U W x (hU x.2) (hW x.2)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with | H x => ?_
    change secAut U W ((1 : ↥X) : G) (hU (1 : ↥X).2) (hW (1 : ↥X).2) (Sec.mk U W x) =
      Sec.mk U W x
    rw [secAut_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjU]
    simp
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with | H x => ?_
    change secAut U W ((a * b : ↥X) : G) (hU (a * b).2) (hW (a * b).2) (Sec.mk U W x) =
      secAut U W (a : G) (hU a.2) (hW a.2) (secAut U W (b : G) (hU b.2) (hW b.2) (Sec.mk U W x))
    rw [secAut_mk, secAut_mk, secAut_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjU, coe_conjU, coe_conjU]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem secHom_mk (X : Subgroup G) (hU : X ≤ Subgroup.normalizer (U : Set G))
    (hW : X ≤ Subgroup.normalizer (W : Set G)) (x : ↥X) (u : ↥U) :
    secHom U W X hU hW x (Sec.mk U W u) = Sec.mk U W (conjU U x (hU x.2) u) :=
  secAut_mk U W x (hU x.2) (hW x.2) u

theorem secHom_eq_one_iff (X : Subgroup G) (hU : X ≤ Subgroup.normalizer (U : Set G))
    (hW : X ≤ Subgroup.normalizer (W : Set G)) (x : ↥X) :
    secHom U W X hU hW x = 1 ↔ (x : G) ∈ centralizerMod W X U := by
  rw [mem_centralizerMod]
  constructor
  · intro h
    refine ⟨x.2, hW x.2, fun u hu => ?_⟩
    have h1 := congrArg (fun φ : MulAut (Sec U W) => φ (Sec.mk U W ⟨u, hu⟩)) h
    simp only [secHom_mk, MulAut.one_apply] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [coe_conjU, div_eq_mul_inv] using h2
  · rintro ⟨-, -, h⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with | H u => ?_
    change secHom U W X hU hW x (Sec.mk U W u) = Sec.mk U W u
    rw [secHom_mk]
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [coe_conjU, div_eq_mul_inv] using h u u.2

end CFSG.Quasithin.H13.GM22
