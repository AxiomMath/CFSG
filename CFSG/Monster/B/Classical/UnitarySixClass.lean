module

public import CFSG.Monster.B.Classical.UnitarySixGraph
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def tPt (p : IsoPt) : ProjSU :=
  (transvec p.1.rep (isIsoPt_of p) : ProjSU)

theorem transvec_smul {v : V} (hv : herm v v = 0) {c : F4} (hc : c ≠ 0)
    (hcv : herm (c • v) (c • v) = 0) : transvec (c • v) hcv = transvec v hv :=
  SU_ext (by rw [coe_transvec, coe_transvec, transvecMat_smul hc])

theorem tPt_pt (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0) :
    tPt (pt v hv0 hv) = (transvec v hv : ProjSU) := by
  obtain ⟨a, ha⟩ := rep_pt hv0 hv
  rw [tPt]
  congr 1
  have h := transvec_smul hv a.ne_zero (by rw [herm_smul_left, herm_smul_right, hv]; simp)
  rw [← h]
  congr 1
  rw [← ha]
  rfl

@[expose] def rankOneClass : Set ProjSU :=
  {y | ∃ A : SU frobeniusF4 6, A ^ 2 = 1 ∧ invRank A = 1 ∧ (A : ProjSU) = y}

theorem tPt_mem_rankOneClass (p : IsoPt) : tPt p ∈ rankOneClass :=
  ⟨_, transvec_sq _ _, (invRank_eq_one_iff _ (transvec_sq _ _)).2
    ⟨_, isIsoPt_of p, rep_ne_zero p, rfl⟩, rfl⟩

theorem range_tPt : Set.range tPt = rankOneClass := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact tPt_mem_rankOneClass p
  · rintro ⟨A, hA, h1, rfl⟩
    obtain ⟨v, hv, hv0, rfl⟩ := (invRank_eq_one_iff A hA).1 h1
    exact ⟨pt v hv0 hv, tPt_pt v hv0 hv⟩

theorem transvec_not_mem_scalars {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    transvec v hv ∉ scalars := by
  intro h
  obtain ⟨a, ha⟩ := mem_scalars.1 h
  have h1 := (invRank_eq_one_iff _ (transvec_sq v hv)).2 ⟨v, hv, hv0, rfl⟩
  rw [invRank, ha] at h1
  by_cases ha1 : a = 1
  · subst ha1
    rw [map_one, sub_self, Matrix.rank_zero] at h1
    exact zero_ne_one h1
  · have hunit : IsUnit (Matrix.scalar (Fin 6) a - 1 : Matrix (Fin 6) (Fin 6) F4) := by
      rw [show (Matrix.scalar (Fin 6) a - 1 : Matrix (Fin 6) (Fin 6) F4) =
          Matrix.scalar (Fin 6) (a - 1) by simp [map_sub]]
      exact (Matrix.isUnit_iff_isUnit_det _).2 (by
        rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const]
        exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha1)).pow 6)
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at h1
    omega

theorem tPt_sq (p : IsoPt) : tPt p ^ 2 = 1 := by
  rw [tPt, ← QuotientGroup.mk_pow, transvec_sq, QuotientGroup.mk_one]

theorem tPt_ne_one (p : IsoPt) : tPt p ≠ 1 := by
  rw [tPt, Ne, QuotientGroup.eq_one_iff]
  exact transvec_not_mem_scalars (rep_ne_zero p) (isIsoPt_of p)

theorem tPt_injective : Function.Injective tPt := by
  intro p q h
  obtain ⟨A, -, hu⟩ := exists_unique_involution_lift (tPt p) (tPt_sq p) (tPt_ne_one p)
  have hp := hu _ ⟨rfl, transvec_sq _ _⟩
  have hq := hu _ ⟨h.symm, transvec_sq _ _⟩
  have heq := hq.trans hp.symm
  rw [transvec_eq_transvec_iff _ _ (rep_ne_zero p)] at heq
  rw [← pt_rep p, ← pt_rep q, pt_eq_pt_iff]
  have hmem : p.1.rep ∈ F4 ∙ q.1.rep := heq ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc⟩

theorem tPt_projAct (x : ProjSU) (p : IsoPt) : tPt (projAct x p) = x * tPt p * x⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction p using IsoPt.ind with
    | h v hv0 hv =>
      rw [projAct_mk, smul_pt, tPt_pt, tPt_pt]
      obtain ⟨hv', hconj⟩ := conj_transvec g v hv
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hconj]
      rfl

theorem rankOneClass_eq_conj : rankOneClass = {y | IsConj (tPt (stdPt 0)) y} := by
  ext y
  rw [← range_tPt]
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := projAct_transitive (stdPt 0) p
    refine isConj_iff.2 ⟨x, ?_⟩
    rw [← tPt_projAct, hx]
  · intro h
    obtain ⟨x, rfl⟩ := isConj_iff.1 h
    exact ⟨projAct x (stdPt 0), tPt_projAct x _⟩

theorem orderOf_conj_eq {G : Type*} [Group G] (x y : G) : orderOf (x * y * x⁻¹) = orderOf y := by
  rw [← MulAut.conj_apply]
  exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y

theorem tPt_mul_projAct (x : ProjSU) (p q : IsoPt) :
    tPt (projAct x p) * tPt (projAct x q) = x * (tPt p * tPt q) * x⁻¹ := by
  rw [tPt_projAct, tPt_projAct]
  group

theorem std_sq_adj :
    (transvecMat (Pi.single 0 1) * transvecMat (Pi.single 1 1)) ^ 2 = 1 := by
  decide +kernel

theorem std_cube_nonadj :
    (transvecMat (Pi.single 0 1) * transvecMat (Pi.single 5 1)) ^ 3 = 1 := by
  decide +kernel

theorem std_ne_scalar_adj : ∀ a : F4,
    transvecMat (Pi.single 0 1) * transvecMat (Pi.single 1 1) ≠ Matrix.scalar (Fin 6) a := by
  decide +kernel

theorem std_ne_scalar_nonadj : ∀ a : F4,
    transvecMat (Pi.single 0 1) * transvecMat (Pi.single 5 1) ≠ Matrix.scalar (Fin 6) a := by
  decide +kernel

theorem std_commute :
    transvecMat (Pi.single 0 1) * transvecMat (Pi.single 1 1) =
      transvecMat (Pi.single 1 1) * transvecMat (Pi.single 0 1) := by
  decide +kernel

theorem tPt_stdPt (j : Fin 6) :
    tPt (stdPt j) = (transvec (Pi.single j 1) (herm_single_self j) : ProjSU) :=
  tPt_pt _ _ _

theorem orderOf_std_adj : orderOf (tPt (stdPt 0) * tPt (stdPt 1)) = 2 := by
  rw [tPt_stdPt, tPt_stdPt, ← QuotientGroup.mk_mul]
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine (mem_scalars.2 ⟨1, ?_⟩)
    rw [show ((((transvec (Pi.single 0 1) (herm_single_self 0) *
        transvec (Pi.single 1 1) (herm_single_self 1)) ^ 2 : SU frobeniusF4 6) :
          GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        (transvecMat (Pi.single 0 1) * transvecMat (Pi.single 1 1)) ^ 2 by
      rw [pow_two, pow_two, coe_SU_mul, coe_SU_mul, coe_transvec, coe_transvec]]
    rw [std_sq_adj, map_one]
  · rw [Ne, QuotientGroup.eq_one_iff, mem_scalars]
    rintro ⟨a, ha⟩
    rw [coe_SU_mul, coe_transvec, coe_transvec] at ha
    exact std_ne_scalar_adj a ha

theorem orderOf_std_nonadj : orderOf (tPt (stdPt 0) * tPt (stdPt 5)) = 3 := by
  rw [tPt_stdPt, tPt_stdPt, ← QuotientGroup.mk_mul]
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine (mem_scalars.2 ⟨1, ?_⟩)
    rw [show ((((transvec (Pi.single 0 1) (herm_single_self 0) *
        transvec (Pi.single 5 1) (herm_single_self 5)) ^ 3 : SU frobeniusF4 6) :
          GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        (transvecMat (Pi.single 0 1) * transvecMat (Pi.single 5 1)) ^ 3 by
      simp only [pow_succ, pow_zero, one_mul, coe_SU_mul, coe_transvec]]
    rw [std_cube_nonadj, map_one]
  · rw [Ne, QuotientGroup.eq_one_iff, mem_scalars]
    rintro ⟨a, ha⟩
    rw [coe_SU_mul, coe_transvec, coe_transvec] at ha
    exact std_ne_scalar_nonadj a ha

theorem orderOf_tPt_mul_adj {p q : IsoPt} (h : isoGraph.Adj p q) :
    orderOf (tPt p * tPt q) = 2 := by
  obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_adj p q h
  rw [← projAct_mk, ← projAct_mk, tPt_mul_projAct, orderOf_conj_eq, orderOf_std_adj]

theorem orderOf_tPt_mul_nonadj {p q : IsoPt} (hpq : p ≠ q) (h : ¬isoGraph.Adj p q) :
    orderOf (tPt p * tPt q) = 3 := by
  obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_nonadj p q hpq h
  rw [← projAct_mk, ← projAct_mk, tPt_mul_projAct, orderOf_conj_eq, orderOf_std_nonadj]

theorem commute_tPt_std : Commute (tPt (stdPt 0)) (tPt (stdPt 1)) := by
  rw [tPt_stdPt, tPt_stdPt]
  have h : transvec (Pi.single 0 1) (herm_single_self 0) *
      transvec (Pi.single 1 1) (herm_single_self 1) =
      transvec (Pi.single 1 1) (herm_single_self 1) *
        transvec (Pi.single 0 1) (herm_single_self 0) :=
    SU_ext (by rw [coe_SU_mul, coe_SU_mul, coe_transvec, coe_transvec, std_commute])
  change (_ : ProjSU) * _ = _ * _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem adj_iff_commute (p q : IsoPt) :
    isoGraph.Adj p q ↔ p ≠ q ∧ Commute (tPt p) (tPt q) := by
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_adj p q h
    rw [← projAct_mk, ← projAct_mk, tPt_projAct, tPt_projAct]
    exact (commute_tPt_std.conj _ :)
  · rintro ⟨hpq, hc⟩
    by_contra h
    have h3 := orderOf_tPt_mul_nonadj hpq h
    have h2 : (tPt p * tPt q) ^ 2 = 1 := by
      rw [hc.mul_pow, tPt_sq, tPt_sq, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    norm_num at this

end CFSG.Monster.B.Classical.UnitarySix
