module

public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiAlt
public import CFSG.CGT.Timmesfeld75.ListWCLinBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Ctx.comm_Vt_of_fix (hc : Ctx M Q Z B) (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G}
    (hd : d ∈ H0 M Z) (hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z := fun v hv =>
  (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨d, hd⟩) (hc.conj_mem_Q_of_mem_M hd.1).1
    (fun z hz => AM.φ_π ⟨d, hd⟩ z hz) (hc.Vt_le_Q t hv)).mpr
    (hfix _ (mem_imgSub.mpr (AM.M₀.pi_mem_img hv (hc.Vt_le_Q t hv))))

private def detOne (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Subgroup G where
  carrier := {x | ∃ hx : x ∈ Rt M (LB M Q B) t,
    (D.matV AM ⟨x, D.Rt_le_H0 hx⟩).det = 1}
  mul_mem' := by
    rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
    refine ⟨(Rt M (LB M Q B) t).mul_mem haR hbR, ?_⟩
    have hmul := D.matV_mul AM (m := ⟨a, D.Rt_le_H0 haR⟩) (m' := ⟨b, D.Rt_le_H0 hbR⟩)
      (fun e he => D.phi_mem_Vsp AM hbR he)
    have heq : (⟨a, D.Rt_le_H0 haR⟩ * ⟨b, D.Rt_le_H0 hbR⟩ : ↥(H0 M Z)) =
        ⟨a * b, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem haR hbR)⟩ := rfl
    rw [heq] at hmul
    rw [hmul, det_mul, ha, hb, one_mul]
  one_mem' := by
    refine ⟨(Rt M (LB M Q B) t).one_mem, ?_⟩
    show (D.matV AM (1 : ↥(H0 M Z))).det = 1
    rw [D.matV_one AM, det_one]
  inv_mem' := by
    rintro a ⟨haR, ha⟩
    have haR' : a⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem haR
    refine ⟨haR', ?_⟩
    have hmul := D.matV_mul AM (m := ⟨a, D.Rt_le_H0 haR⟩) (m' := ⟨a⁻¹, D.Rt_le_H0 haR'⟩)
      (fun e he => D.phi_mem_Vsp AM haR' he)
    have heq : (⟨a, D.Rt_le_H0 haR⟩ * ⟨a⁻¹, D.Rt_le_H0 haR'⟩ : ↥(H0 M Z)) =
        ⟨a * a⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem haR haR')⟩ := rfl
    have hone : (⟨a * a⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem haR haR')⟩ :
        ↥(H0 M Z)) = 1 := Subtype.ext (mul_inv_cancel a)
    rw [heq, hone, D.matV_one AM] at hmul
    have hdet := congrArg Matrix.det hmul
    rw [det_one, det_mul, ha, one_mul] at hdet
    exact hdet.symm

private theorem matV_eq_one_of_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {z : G} (hz : z ∈ Q) :
    D.matV AM ⟨z, hc.Q_le_H0 hz⟩ = 1 := by
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨z, hc.Q_le_H0 hz⟩ e = e := fun e _ => by
    rw [(AM.φ_ker _).mpr hz, LinearEquiv.coe_one, id_eq]
  exact (D.matV_eq_one_iff AM fun e he => by rw [hfix e he]; exact he).mpr hfix

private theorem det_matV_eq_one_of_sq_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {x : G} (hx : x ∈ Rt M (LB M Q B) t)
    (hx2 : x ^ 2 ∈ Q) : (D.matV AM ⟨x, D.Rt_le_H0 hx⟩).det = 1 := by
  have hpres : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨x, D.Rt_le_H0 hx⟩ e ∈ AM.Vsp hc t :=
    fun e he => D.phi_mem_Vsp AM hx he
  have hmul := D.matV_mul AM (m := ⟨x, D.Rt_le_H0 hx⟩) (m' := ⟨x, D.Rt_le_H0 hx⟩) hpres
  have heq : (⟨x, D.Rt_le_H0 hx⟩ * ⟨x, D.Rt_le_H0 hx⟩ : ↥(H0 M Z)) =
      ⟨x ^ 2, hc.Q_le_H0 hx2⟩ := Subtype.ext (pow_two x).symm
  rw [heq, matV_eq_one_of_mem_Q D AM hx2] at hmul
  have hsq : (D.matV AM ⟨x, D.Rt_le_H0 hx⟩).det ^ 2 = 1 := by
    rw [pow_two, ← det_mul, ← hmul, det_one]
  have hzero : ((D.matV AM ⟨x, D.Rt_le_H0 hx⟩).det - 1) ^ 2 = 0 := by
    rw [sub_pow_char, hsq, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hzero)

theorem Sec108Data.det_matV_eq_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    (D.matV AM ⟨r, D.Rt_le_H0 hr⟩).det = 1 := by
  have hle : Rt M (LB M Q B) t ≤ detOne D AM := by
    unfold Rt
    refine iSup₂_le fun m hm => ?_
    refine iSup_le fun htm x hx => ?_
    have hx2 : x ^ 2 ∈ Q := by
      rw [mem_conjSubgroup] at hx
      have hl2 : (m⁻¹ * x * m) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hx
      have hconj : m * (m⁻¹ * x * m) ^ 2 * m⁻¹ = x ^ 2 := by
        rw [pow_two, pow_two]
        group
      have h := (hc.conj_mem_Q_of_mem_M hm).1 _ hl2
      rwa [hconj] at h
    have hxR : x ∈ Rt M (LB M Q B) t := by
      have hle' : conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t := by
        unfold Rt
        exact le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl)
      exact hle' hx
    exact ⟨hxR, det_matV_eq_one_of_sq_mem_Q D AM hxR hx2⟩
  exact (hle hr).2

private theorem commutator_Rt_le (D : Sec108Data hc t Y) :
    ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤ Rt M (LB M Q B) t := by
  refine Subgroup.commutator_le.mpr fun r hr s hs => ?_
  rw [commutatorElement_def]
  exact (Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hr hs)
      ((Rt M (LB M Q B) t).inv_mem hr))
    ((Rt M (LB M Q B) t).inv_mem hs)

private noncomputable def matVHom (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ↥(Rt M (LB M Q B) t) →* Matrix.SpecialLinearGroup (Fin 3) AM.K where
  toFun r := ⟨D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩, D.det_matV_eq_one AM r.2⟩
  map_one' := Subtype.ext (D.matV_one AM)
  map_mul' r s := Subtype.ext (D.matV_mul AM (m := ⟨(r : G), D.Rt_le_H0 r.2⟩)
    (m' := ⟨(s : G), D.Rt_le_H0 s.2⟩) fun e he => D.phi_mem_Vsp AM s.2 he)

private theorem matVHom_coe (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (r : ↥(Rt M (LB M Q B) t)) :
    (matVHom D AM r : Matrix (Fin 3) (Fin 3) AM.K) =
      D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩ := rfl

private noncomputable def matVComm (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ↥⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ →* Matrix.SpecialLinearGroup (Fin 3) AM.K :=
  (matVHom D AM).comp (Subgroup.inclusion (commutator_Rt_le D))

private theorem matVComm_coe (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (c : ↥⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆) :
    (matVComm D AM c : Matrix (Fin 3) (Fin 3) AM.K) =
      D.matV AM ⟨(c : G), D.Rt_le_H0 (commutator_Rt_le D c.2)⟩ := by
  simp only [matVComm, MonoidHom.comp_apply, matVHom_coe, Subgroup.coe_inclusion]

theorem Sec108Data.exists_commutator_matV_eq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
    ∃ c ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆, ∃ hcH : c ∈ H0 M Z,
      D.matV AM ⟨c, hcH⟩ = (A : Matrix (Fin 3) (Fin 3) AM.K) := by
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) AM.K)) ≤
      (matVComm D AM).range := by
    rw [← CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := AM.K) (n := 3)
      (by norm_num)]
    refine Subgroup.commutator_le.mpr fun A _ A' _ => ?_
    obtain ⟨a, ⟨haR, -⟩, haH, hab⟩ := D.bV_spec AM A
    obtain ⟨b, ⟨hbR, -⟩, hbH, hbb⟩ := D.bV_spec AM A'
    have hmatA : matVHom D AM (⟨a, haR⟩ : ↥(Rt M (LB M Q B) t)) = A :=
      Subtype.ext (D.matV_eq_of_forall AM hab)
    have hmatB : matVHom D AM (⟨b, hbR⟩ : ↥(Rt M (LB M Q B) t)) = A' :=
      Subtype.ext (D.matV_eq_of_forall AM hbb)
    refine ⟨⟨⁅a, b⁆, Subgroup.commutator_mem_commutator haR hbR⟩, ?_⟩
    rw [← hmatA, ← hmatB]
    exact map_commutatorElement (matVHom D AM)
      (⟨a, haR⟩ : ↥(Rt M (LB M Q B) t)) (⟨b, hbR⟩ : ↥(Rt M (LB M Q B) t))
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (htop (Subgroup.mem_top A))
  refine ⟨(c : G), c.2, D.Rt_le_H0 (commutator_Rt_le D c.2), ?_⟩
  have hval := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) AM.K =>
    (x : Matrix (Fin 3) (Fin 3) AM.K)) hc
  rw [matVComm_coe] at hval
  simpa using hval

theorem Sec108Data.exists_commutator_mul_CN (D : Sec108Data hc t Y) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) :
    ∃ c ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆, c⁻¹ * r ∈ hc.CN t := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨c, hcComm, hcH, hcEq⟩ := D.exists_commutator_matV_eq AM
    ⟨D.matV AM ⟨r, D.Rt_le_H0 hr⟩, D.det_matV_eq_one AM hr⟩
  have hcR : c ∈ Rt M (LB M Q B) t := commutator_Rt_le D hcComm
  have hcr : c⁻¹ * r ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hcR) hr
  have hcrH : c⁻¹ * r ∈ H0 M Z := D.Rt_le_H0 hcr
  have hmat : D.matV AM ⟨c⁻¹ * r, hcrH⟩ = 1 := by
    have hcA : matVHom D AM (⟨c, hcR⟩ : ↥(Rt M (LB M Q B) t)) =
        matVHom D AM (⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) := by
      refine Subtype.ext ?_
      change D.matV AM ⟨c, D.Rt_le_H0 hcR⟩ = D.matV AM ⟨r, D.Rt_le_H0 hr⟩
      rw [hcEq]
    have h2 := map_mul (matVHom D AM) ((⟨c, hcR⟩ : ↥(Rt M (LB M Q B) t))⁻¹)
      (⟨r, hr⟩ : ↥(Rt M (LB M Q B) t))
    rw [map_inv, hcA, inv_mul_cancel] at h2
    exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) AM.K =>
      (x : Matrix (Fin 3) (Fin 3) AM.K)) h2
  have hfix := (D.matV_eq_one_iff AM fun e he => D.phi_mem_Vsp AM hcr he).mp hmat
  exact ⟨c, hcComm, Ctx.mem_CN.mpr ⟨hcr, Ctx.comm_Vt_of_fix hc AM hcrH hfix⟩⟩

private theorem commutator_le_CN (D : Sec108Data hc t Y) :
    ⁅hc.CN t, Rt M (LB M Q B) t⁆ ≤ hc.CN t := by
  refine Subgroup.commutator_le.mpr fun n hn r hr => ?_
  have h := (hc.CN t).mul_mem hn (D.conj_mem_CN hr ((hc.CN t).inv_mem hn))
  simpa only [commutatorElement_def, mul_assoc] using h

private theorem commutator_mem_CN (D : Sec108Data hc t Y) {n r : G} (hn : n ∈ hc.CN t)
    (hr : r ∈ Rt M (LB M Q B) t) : ⁅r, n⁆ ∈ hc.CN t := by
  have h := (hc.CN t).mul_mem (D.conj_mem_CN hr hn) ((hc.CN t).inv_mem hn)
  simpa only [commutatorElement_def, mul_assoc] using h

private theorem conj_mem_commutator (D : Sec108Data hc t Y) {r c : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hcm : c ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆) :
    r * c * r⁻¹ ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆ := by
  have hN : conjSubgroup r (hc.CN t) = hc.CN t :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_iff''.mpr fun h =>
      ⟨fun hh => by simpa only [inv_inv] using D.conj_mem_CN ((Rt M (LB M Q B) t).inv_mem hr) hh,
        fun hh => by
          have h1 := D.conj_mem_CN hr hh
          rwa [show r * (r⁻¹ * h * r) * r⁻¹ = h by group] at h1⟩)
  have hR : conjSubgroup r (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr)
  have hmap : conjSubgroup r ⁅hc.CN t, Rt M (LB M Q B) t⁆ =
      ⁅hc.CN t, Rt M (LB M Q B) t⁆ := by
    rw [show conjSubgroup r ⁅hc.CN t, Rt M (LB M Q B) t⁆ =
        Subgroup.map (MulAut.conj r).toMonoidHom ⁅hc.CN t, Rt M (LB M Q B) t⁆ from rfl,
      Subgroup.map_commutator]
    rw [show Subgroup.map (MulAut.conj r).toMonoidHom (hc.CN t) = conjSubgroup r (hc.CN t)
        from rfl,
      show Subgroup.map (MulAut.conj r).toMonoidHom (Rt M (LB M Q B) t) =
        conjSubgroup r (Rt M (LB M Q B) t) from rfl, hN, hR]
  rw [← hmap]
  exact mem_conjSubgroup.mpr
    (by rwa [show r⁻¹ * (r * c * r⁻¹) * r = c by group])

private noncomputable def commMat (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : AddSubgroup (Matrix (Fin 3) (Fin 3) AM.K) :=
  Subgroup.toAddSubgroup' ((D.phiHom AM).comp (Subgroup.inclusion (commutator_le_CN D))).range

private theorem mem_commMat_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {S : Matrix (Fin 3) (Fin 3) AM.K} :
    S ∈ commMat D AM ↔ ∃ c : G, ∃ hcm : c ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆,
      D.phiMat AM ⟨c, D.CN_le_H0 (commutator_le_CN D hcm)⟩ = S := by
  constructor
  · intro hS
    rw [commMat, Subgroup.mem_toAddSubgroup'] at hS
    obtain ⟨c, hcmem⟩ := MonoidHom.mem_range.mp hS
    refine ⟨(c : G), c.2, ?_⟩
    have h := congrArg Multiplicative.toAdd hcmem
    have hincl : (Subgroup.inclusion (commutator_le_CN D) c : ↥(hc.CN t)) =
        ⟨(c : G), commutator_le_CN D c.2⟩ := Subtype.ext rfl
    have h2 : Multiplicative.toAdd ((D.phiHom AM).comp
        (Subgroup.inclusion (commutator_le_CN D)) c) =
        D.phiMat AM ⟨(c : G), D.CN_le_H0 (commutator_le_CN D c.2)⟩ := by
      rw [MonoidHom.comp_apply, hincl]
      exact Sec108Data.phiHom_apply D AM ⟨(c : G), commutator_le_CN D c.2⟩
    rwa [h2] at h
  · rintro ⟨c, hcm, rfl⟩
    rw [commMat, Subgroup.mem_toAddSubgroup']
    refine MonoidHom.mem_range.mpr ⟨⟨c, hcm⟩, ?_⟩
    have h := Sec108Data.phiHom_apply D AM ⟨c, commutator_le_CN D hcm⟩
    have hincl : (Subgroup.inclusion (commutator_le_CN D) ⟨c, hcm⟩ : ↥(hc.CN t)) =
        ⟨c, commutator_le_CN D hcm⟩ := Subtype.ext rfl
    have h' : D.phiHom AM ⟨c, commutator_le_CN D hcm⟩ =
        Multiplicative.ofAdd (D.phiMat AM ⟨c, D.CN_le_H0 (commutator_le_CN D hcm)⟩) := by
      rw [← h]
      simp
    rw [MonoidHom.comp_apply, hincl]
    exact h'

private theorem commMat_invariant (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    {S : Matrix (Fin 3) (Fin 3) AM.K} (hS : S ∈ commMat D AM) :
    (A : Matrix (Fin 3) (Fin 3) AM.K) * S * (A : Matrix (Fin 3) (Fin 3) AM.K)ᵀ ∈
      commMat D AM := by
  obtain ⟨c, hcm, rfl⟩ := (mem_commMat_iff D AM).mp hS
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hrb⟩ := D.bV_spec AM A
  have hrT : ∀ e, AM.φ ⟨r, hrH⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨r, hrH⟩ e) := by
    refine Sec108Data.phi_comm_of_comm_mem AM ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hrt)]
    exact Q.one_mem
  have hconj := D.phiMat_conj AM (m := ⟨c, D.CN_le_H0 (commutator_le_CN D hcm)⟩) hrT hrb
    (fun e he => D.fix_Vsp_of_mem_CN AM (commutator_le_CN D hcm) he)
    (D.comm_t_of_mem_CN AM (commutator_le_CN D hcm))
  rw [← hconj]
  exact (mem_commMat_iff D AM).mpr ⟨r * c * r⁻¹, conj_mem_commutator D hrR hcm, rfl⟩

private theorem commMat_alt (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {S : Matrix (Fin 3) (Fin 3) AM.K}
    (hS : S ∈ commMat D AM) : Sᵀ = -S ∧ ∀ i, S i i = 0 := by
  obtain ⟨c, hcm, rfl⟩ := (mem_commMat_iff D AM).mp hS
  refine ⟨?_, fun i => D.phiMat_diag AM (commutator_le_CN D hcm) i⟩
  rw [D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM (commutator_le_CN D hcm) he)
    (D.comm_t_of_mem_CN AM (commutator_le_CN D hcm))]
  ext i j
  exact (CharTwo.neg_eq (D.phiMat AM ⟨c, D.CN_le_H0 (commutator_le_CN D hcm)⟩ i j)).symm

private theorem phiMat_conj_mul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n r : G} (hn : n ∈ hc.CN t)
    (hr : r ∈ Rt M (LB M Q B) t) :
    D.phiMat AM ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ =
      D.phiMat AM ⟨⁅r, n⁆, D.CN_le_H0 (commutator_mem_CN D hn hr)⟩ +
        D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ := by
  have hmul := D.phiMat_mul AM (m := ⟨⁅r, n⁆, D.CN_le_H0 (commutator_mem_CN D hn hr)⟩)
    (m' := ⟨n, D.CN_le_H0 hn⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM (commutator_mem_CN D hn hr) he)
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  have heq : (⟨⁅r, n⁆, D.CN_le_H0 (commutator_mem_CN D hn hr)⟩ *
      ⟨n, D.CN_le_H0 hn⟩ : ↥(H0 M Z)) =
      ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ := by
    refine Subtype.ext ?_
    show ⁅r, n⁆ * n = r * n * r⁻¹
    rw [commutatorElement_def]
    group
  rwa [heq] at hmul

private def stdFirst (K : Type) [Zero K] [One K] : Fin 3 → K := Pi.single 0 1

private def stdSecond (K : Type) [Zero K] [One K] : Fin 3 → K := Pi.single 1 1

private theorem dot_stdFirst_stdFirst {K : Type} [Field K] : stdFirst K ⬝ᵥ stdFirst K = 1 := by
  simp [stdFirst, dotProduct, Fin.sum_univ_three]

private theorem dot_stdSecond_stdFirst {K : Type} [Field K] : stdSecond K ⬝ᵥ stdFirst K = 0 := by
  simp [stdFirst, stdSecond, dotProduct, Fin.sum_univ_three]

private theorem det_one_add_vecMulVec_std {K : Type} [Field K] :
    (1 + Matrix.vecMulVec (stdFirst K) (stdSecond K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.CGT.Timmesfeld75.det_one_add_vecMulVec_of_dot (dot_stdSecond_stdFirst (K := K))

private theorem crossMatrix_transpose {K : Type} [Field K] (a : Fin 3 → K) :
    (CFSG.LinearAlgebra.crossMatrix a)ᵀ = -CFSG.LinearAlgebra.crossMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LinearAlgebra.crossMatrix]

private theorem crossMatrix_diag {K : Type} [Field K] (a : Fin 3 → K) :
    ∀ i, CFSG.LinearAlgebra.crossMatrix a i i = 0 := by
  intro i
  fin_cases i <;> simp [CFSG.LinearAlgebra.crossMatrix]

private theorem crossMatrix_stdFirst_symm {K : Type} [Field K] [CharP K 2] :
    (CFSG.LinearAlgebra.crossMatrix (stdFirst K))ᵀ =
      CFSG.LinearAlgebra.crossMatrix (stdFirst K) := by
  rw [crossMatrix_transpose]
  ext i j
  exact CharTwo.neg_eq (CFSG.LinearAlgebra.crossMatrix (stdFirst K) i j)

private theorem crossMatrix_stdSecond_ne_zero {K : Type} [Field K] :
    CFSG.LinearAlgebra.crossMatrix (stdSecond K) ≠ 0 := by
  intro h
  have h1 := congrFun ((CFSG.LinearAlgebra.crossMatrix_eq_zero_iff (stdSecond K)).mp h) 1
  simp [stdSecond] at h1

private theorem crossMatrix_stdFirst_sub_stdSecond_sub_stdFirst {K : Type} [Field K] [CharP K 2] :
    CFSG.LinearAlgebra.crossMatrix (stdFirst K - stdSecond K) -
        CFSG.LinearAlgebra.crossMatrix (stdFirst K) =
      CFSG.LinearAlgebra.crossMatrix (stdSecond K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LinearAlgebra.crossMatrix, stdFirst, stdSecond, CharTwo.neg_eq]

private theorem one_add_vecMulVec_std_mul_crossMatrix {K : Type} [Field K] :
    ((⟨1 + Matrix.vecMulVec (stdFirst K) (stdSecond K), det_one_add_vecMulVec_std⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      CFSG.LinearAlgebra.crossMatrix (stdFirst K) *
      ((⟨1 + Matrix.vecMulVec (stdFirst K) (stdSecond K), det_one_add_vecMulVec_std⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
    CFSG.LinearAlgebra.crossMatrix (stdFirst K - stdSecond K) := by
  rw [show ((⟨1 + Matrix.vecMulVec (stdFirst K) (stdSecond K), det_one_add_vecMulVec_std⟩ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (stdFirst K) (stdSecond K) from rfl]
  rw [CFSG.LinearAlgebra.one_add_vecMulVec_mul_crossMatrix, dot_stdFirst_stdFirst,
    dot_stdSecond_stdFirst]
  simp

private theorem exists_ne_zero_mem_commMat (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ S ∈ commMat D AM, S ≠ 0 := by
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hrb⟩ := D.bV_spec AM
    ⟨1 + Matrix.vecMulVec (stdFirst AM.K) (stdSecond AM.K), det_one_add_vecMulVec_std⟩
  obtain ⟨n0, hn0, hn0S⟩ := D.exists_phiMat_eq AM
    (CFSG.LinearAlgebra.crossMatrix (stdFirst AM.K)) (crossMatrix_stdFirst_symm (K := AM.K))
    (crossMatrix_diag _)
  have hrT : ∀ e, AM.φ ⟨r, hrH⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨r, hrH⟩ e) := by
    refine Sec108Data.phi_comm_of_comm_mem AM ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hrt)]
    exact Q.one_mem
  have hAcomp : ((⟨1 + Matrix.vecMulVec (stdFirst AM.K) (stdSecond AM.K),
        det_one_add_vecMulVec_std⟩ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) * D.phiMat AM ⟨n0, D.CN_le_H0 hn0⟩ *
        ((⟨1 + Matrix.vecMulVec (stdFirst AM.K) (stdSecond AM.K),
          det_one_add_vecMulVec_std⟩ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
          Matrix (Fin 3) (Fin 3) AM.K)ᵀ =
      CFSG.LinearAlgebra.crossMatrix (stdFirst AM.K - stdSecond AM.K) := by
    rw [hn0S]
    exact one_add_vecMulVec_std_mul_crossMatrix (K := AM.K)
  have hconj := D.phiMat_conj AM (m := ⟨n0, D.CN_le_H0 hn0⟩) hrT hrb
    (fun e he => D.fix_Vsp_of_mem_CN AM hn0 he) (D.comm_t_of_mem_CN AM hn0)
  have h1 : D.phiMat AM ⟨r * n0 * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hrR hn0)⟩ =
      CFSG.LinearAlgebra.crossMatrix (stdFirst AM.K - stdSecond AM.K) := by
    have harg : (⟨r * n0 * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hrR hn0)⟩ : ↥(H0 M Z)) =
        ⟨r, hrH⟩ * ⟨n0, D.CN_le_H0 hn0⟩ * ⟨r, hrH⟩⁻¹ := Subtype.ext rfl
    rw [harg, hconj, hAcomp]
  have h3 : D.phiMat AM ⟨⁅r, n0⁆, D.CN_le_H0 (commutator_mem_CN D hn0 hrR)⟩ =
      CFSG.LinearAlgebra.crossMatrix (stdSecond AM.K) := by
    have hcomm_eq : D.phiMat AM ⟨⁅r, n0⁆, D.CN_le_H0 (commutator_mem_CN D hn0 hrR)⟩ +
        D.phiMat AM ⟨n0, D.CN_le_H0 hn0⟩ =
          CFSG.LinearAlgebra.crossMatrix (stdFirst AM.K - stdSecond AM.K) := by
      rw [← phiMat_conj_mul D AM hn0 hrR, h1]
    have h4 : D.phiMat AM ⟨⁅r, n0⁆, D.CN_le_H0 (commutator_mem_CN D hn0 hrR)⟩ =
        CFSG.LinearAlgebra.crossMatrix (stdFirst AM.K - stdSecond AM.K) -
          D.phiMat AM ⟨n0, D.CN_le_H0 hn0⟩ := eq_sub_iff_add_eq.mpr hcomm_eq
    rw [h4, hn0S, crossMatrix_stdFirst_sub_stdSecond_sub_stdFirst]
  have hcr : ⁅r, n0⁆ ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆ := by
    simpa only [Subgroup.commutator_comm] using Subgroup.commutator_mem_commutator hrR hn0
  have hmem : CFSG.LinearAlgebra.crossMatrix (stdSecond AM.K) ∈ commMat D AM := by
    rw [← h3]
    exact (mem_commMat_iff D AM).mpr ⟨⁅r, n0⁆, hcr, rfl⟩
  exact ⟨CFSG.LinearAlgebra.crossMatrix (stdSecond AM.K), hmem,
    crossMatrix_stdSecond_ne_zero (K := AM.K)⟩

private theorem phiMat_inv (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {c : G} (hcN : c ∈ hc.CN t) :
    D.phiMat AM ⟨c⁻¹, D.CN_le_H0 ((hc.CN t).inv_mem hcN)⟩ =
      -D.phiMat AM ⟨c, D.CN_le_H0 hcN⟩ := by
  have hzero : D.phiMat AM (1 : ↥(H0 M Z)) = 0 :=
    (D.phiMat_eq_zero_iff AM (m := 1) (fun e _ => by rw [map_one]; rfl)
      (fun e => by rw [map_one]; rfl)).mpr (fun u _ => by rw [map_one]; rfl)
  have hmul := D.phiMat_mul AM (m := ⟨c, D.CN_le_H0 hcN⟩)
    (m' := ⟨c⁻¹, D.CN_le_H0 ((hc.CN t).inv_mem hcN)⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM hcN he)
    (fun e he => D.fix_Vsp_of_mem_CN AM ((hc.CN t).inv_mem hcN) he)
    (D.comm_t_of_mem_CN AM ((hc.CN t).inv_mem hcN))
  have heq : (⟨c, D.CN_le_H0 hcN⟩ *
      ⟨c⁻¹, D.CN_le_H0 ((hc.CN t).inv_mem hcN)⟩ : ↥(H0 M Z)) = 1 :=
    Subtype.ext (mul_inv_cancel c)
  rw [heq, hzero] at hmul
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hmul.symm

private theorem phiMat_inv_mul_eq_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {c n : G}
    (hcm : c ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆) (hn : n ∈ hc.CN t)
    (hcphi : D.phiMat AM ⟨c, D.CN_le_H0 (commutator_le_CN D hcm)⟩ =
      D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) :
    D.phiMat AM ⟨c⁻¹ * n, D.CN_le_H0 ((hc.CN t).mul_mem
      ((hc.CN t).inv_mem (commutator_le_CN D hcm)) hn)⟩ = 0 := by
  have hcN : c ∈ hc.CN t := commutator_le_CN D hcm
  have hcinv : c⁻¹ * n ∈ hc.CN t := (hc.CN t).mul_mem ((hc.CN t).inv_mem hcN) hn
  have hmul := D.phiMat_mul AM (m := ⟨c⁻¹, D.CN_le_H0 ((hc.CN t).inv_mem hcN)⟩)
    (m' := ⟨n, D.CN_le_H0 hn⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM ((hc.CN t).inv_mem hcN) he)
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  have heq : (⟨c⁻¹, D.CN_le_H0 ((hc.CN t).inv_mem hcN)⟩ * ⟨n, D.CN_le_H0 hn⟩ :
      ↥(H0 M Z)) = ⟨c⁻¹ * n, D.CN_le_H0 hcinv⟩ := rfl
  rw [heq] at hmul
  rw [hmul, phiMat_inv D AM hcN, hcphi]
  abel

theorem Sec108Data.exists_commutator_root (D : Sec108Data hc t Y) {n : G} (hn : n ∈ hc.CN t) :
    ∃ c ∈ ⁅hc.CN t, Rt M (LB M Q B) t⁆, ∃ y ∈ Y, (c * y)⁻¹ * n ∈ Q := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨S₀, hS₀, hS₀ne⟩ := exists_ne_zero_mem_commMat D AM
  obtain ⟨hS₀t, hS₀d⟩ := commMat_alt D AM hS₀
  have hSsym : (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)ᵀ = -(D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) := by
    rw [D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM hn he)
      (D.comm_t_of_mem_CN AM hn)]
    ext i j
    exact (CharTwo.neg_eq (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ i j)).symm
  have hSn : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ ∈ commMat D AM :=
    CFSG.LinearAlgebra.mem_of_specialLinear_invariant (commMat D AM)
      (fun A S hS => commMat_invariant D AM A hS) hS₀ hS₀t hS₀d hS₀ne hSsym
      (fun i => D.phiMat_diag AM hn i)
  obtain ⟨c, hcm, hcphi⟩ := (mem_commMat_iff D AM).mp hSn
  have hphi0 := phiMat_inv_mul_eq_zero D AM hcm hn hcphi
  have hcinv : c⁻¹ * n ∈ hc.CN t := (hc.CN t).mul_mem
    ((hc.CN t).inv_mem (commutator_le_CN D hcm)) hn
  obtain ⟨y, hy, hyQ⟩ := (D.phiMat_eq_zero_iff_root AM hcinv).mp hphi0
  refine ⟨c, hcm, y, hy, ?_⟩
  have e : (c * y)⁻¹ * n = y⁻¹ * (c⁻¹ * n) := by group
  rw [e]
  exact hyQ

end CFSG.RankThree.GF2n.Stroth80
