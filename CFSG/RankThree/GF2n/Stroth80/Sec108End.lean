module

public import CFSG.RankThree.GF2n.Stroth80.Sec108LB
public import CFSG.ClassicalGroups.SpecialLinear.LagrangianCommutant

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Sec108Data.phi_comm_of_comm_mem (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m m' : ↥(H0 M Z)} (h : ⁅(m : G), (m' : G)⁆ ∈ Q) (e : AM.M₀.E) :
    AM.φ m (AM.φ m' e) = AM.φ m' (AM.φ m e) := by
  have h1 : AM.φ ⁅m, m'⁆ = 1 := (AM.φ_ker ⁅m, m'⁆).mpr h
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 := congrArg (fun g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => g e) h1
  simpa only [LinearEquiv.mul_apply] using h2

theorem Sec108Data.nu_phi (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (e : AM.M₀.E) : D.nu AM (AM.φ m e) = AM.φ m (D.nu AM e) := by
  rw [D.nu_apply, D.nu_apply, map_sub, hm e]

theorem Sec108Data.map_range_nu (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    (LinearMap.range (D.nu AM)).map (AM.φ m : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.range (D.nu AM) := by
  have hcomp : (AM.φ m : AM.M₀.E →ₗ[AM.K] AM.M₀.E) ∘ₗ D.nu AM =
      D.nu AM ∘ₗ (AM.φ m : AM.M₀.E →ₗ[AM.K] AM.M₀.E) := by
    ext e
    exact (D.nu_phi AM hm e).symm
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

noncomputable def Sec108Data.resU (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z))
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    ↥(LinearMap.range (D.nu AM)) ≃ₗ[AM.K] ↥(LinearMap.range (D.nu AM)) :=
  (AM.φ m).ofSubmodules _ _ (D.map_range_nu AM hm)

theorem Sec108Data.coe_resU_apply (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (u : ↥(LinearMap.range (D.nu AM))) :
    ((D.resU AM m hm u : ↥(LinearMap.range (D.nu AM))) : AM.M₀.E) = AM.φ m u := by
  simp only [Sec108Data.resU, LinearEquiv.ofSubmodules_apply]

theorem Sec108Data.resU_Pform (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (u w : ↥(LinearMap.range (D.nu AM))) :
    D.Pform AM (D.resU AM m hm u) (D.resU AM m hm w) = D.Pform AM u w := by
  obtain ⟨e, he⟩ := u.2
  obtain ⟨f, hf⟩ := w.2
  have hu : D.resU AM m hm u = ⟨D.nu AM (AM.φ m e), LinearMap.mem_range_self _ _⟩ :=
    Subtype.ext (by
      show AM.φ m (u : AM.M₀.E) = D.nu AM (AM.φ m e)
      rw [← he, D.nu_phi AM hm])
  have hw : D.resU AM m hm w = ⟨D.nu AM (AM.φ m f), LinearMap.mem_range_self _ _⟩ :=
    Subtype.ext (by
      show AM.φ m (w : AM.M₀.E) = D.nu AM (AM.φ m f)
      rw [← hf, D.nu_phi AM hm])
  have hu' : u = ⟨D.nu AM e, LinearMap.mem_range_self _ _⟩ := Subtype.ext he.symm
  have hw' : w = ⟨D.nu AM f, LinearMap.mem_range_self _ _⟩ := Subtype.ext hf.symm
  rw [hu, hw, D.Pform_map AM hm e f, ← hu', ← hw']

theorem Sec108Data.phi_mem_Vsp (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m : ↥(H0 M Z)} (hmR : (m : G) ∈ Rt M (LB M Q B) t) {e : AM.M₀.E}
    (he : e ∈ AM.Vsp hc t) : AM.φ m e ∈ AM.Vsp hc t := by
  obtain ⟨v, hvV, hvQ, rfl⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp he)
  rw [← AM.φ_π m v hvQ]
  exact mem_imgSub.mpr (AM.M₀.pi_mem_img
    ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt D.good.1.mem_LB hmR) v).mp hvV)
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hmR)) v).mp hvQ))

noncomputable def Sec108Data.VU (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Submodule AM.K ↥(LinearMap.range (D.nu AM)) :=
  (AM.Vsp hc t).comap (LinearMap.range (D.nu AM)).subtype

theorem Sec108Data.mem_VU (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {u : ↥(LinearMap.range (D.nu AM))} : u ∈ D.VU AM ↔ (u : AM.M₀.E) ∈ AM.Vsp hc t :=
  Iff.rfl

theorem Sec108Data.finrank_VU (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Module.finrank AM.K (D.VU AM) = 3 := by
  rw [Sec108Data.VU, (Submodule.comapSubtypeEquivOfLe (D.Vsp_le_range_nu AM)).finrank_eq,
    D.finrank_Vsp AM]

theorem Sec108Data.orthogonal_VU (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    (D.Pform AM).orthogonal (D.VU AM) = D.VU AM := by
  have hle : D.VU AM ≤ (D.Pform AM).orthogonal (D.VU AM) := fun v hv =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => D.Pform_Vsp AM w v hw hv
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal (D.Pform_nondegenerate AM), D.finrank_range_nu AM,
    D.finrank_VU AM]

private def gam (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Set (↥(LinearMap.range (D.nu AM)) ≃ₗ[AM.K] ↥(LinearMap.range (D.nu AM))) :=
  {g | ∃ (m : ↥(H0 M Z)) (_ : (m : G) ∈ Rt M (LB M Q B) t)
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)),
    g = D.resU AM m hm}

private theorem exists_basis (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ b : Module.Basis (Fin 3) AM.K ↥(D.VU AM),
      ∀ A : Matrix.SpecialLinearGroup (Fin 3) AM.K, ∃ g ∈ gam D AM,
        ∀ j, g (b j) = ∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) i j •
          (b i : ↥(LinearMap.range (D.nu AM))) := by
  obtain ⟨b₀, hb₀⟩ := SLMNat.exists_basis_statedSL D.h34 D.hspread D.hyp D.good.1 D.slm
    (by norm_num) AM.glob AM.φ AM.φ_π
  set b : Module.Basis (Fin 3) AM.K ↥(D.VU AM) :=
    b₀.map (Submodule.comapSubtypeEquivOfLe (D.Vsp_le_range_nu AM)).symm with hb
  have hbj : ∀ j, ((b j : ↥(LinearMap.range (D.nu AM))) : AM.M₀.E) = (b₀ j : AM.M₀.E) :=
    fun _ => rfl
  refine ⟨b, fun A => ?_⟩
  obtain ⟨r, hr, hrH0, hrb⟩ := hb₀ A
  have hm : ∀ e, AM.φ ⟨r, hrH0⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨r, hrH0⟩ e) := by
    refine Sec108Data.phi_comm_of_comm_mem AM ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hr.2)]
    exact Q.one_mem
  refine ⟨D.resU AM ⟨r, hrH0⟩ hm, ⟨⟨r, hrH0⟩, hr.1, hm, rfl⟩, fun j => ?_⟩
  apply Subtype.ext
  rw [Sec108Data.coe_resU_apply, hbj, hrb j, Submodule.coe_sum]
  simp only [Submodule.coe_smul, hbj]

private theorem exists_mem_LB_inf_CN (D : Sec108Data hc t Y) :
    ∃ x ∈ LB M Q B ⊓ hc.CN t, ¬ ∃ y ∈ Y, y⁻¹ * x ∈ Q := by
  by_contra h
  push Not at h
  have hle : LB M Q B ⊓ hc.CN t ≤ Q ⊔ Y := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h x hx
    have : x = y * (y⁻¹ * x) := by group
    rw [this, show y * (y⁻¹ * x) = (y * (y⁻¹ * x) * y⁻¹) * y by group]
    refine Subgroup.mul_mem_sup ?_ hy
    exact (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 ((smith_1_12 D.sit).1 hy).1) _).mp hyx
  have hprod := card_sup_mul_card_inf_of_normalizer (A := Q) (C := Y)
    (fun y hy => hc.hyp.Q_normal.2 ((smith_1_12 D.sit).1 hy).1)
  have hY : Nat.card Y = Nat.card Z := by
    obtain ⟨g, hg⟩ := D.sit.conj
    rw [hg, card_conjSubgroup]
  have h1 := Subgroup.card_le_of_le hle
  rw [D.card_LB_inf_CN] at h1
  have h2 : Nat.card ↥(Q ⊔ Y) ≤ Nat.card Q * Nat.card Z := by
    rw [← hY, ← hprod]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hq := hc.hyp.q4
  have hQ : 0 < Nat.card Q := Nat.card_pos
  have h3 : Nat.card Z ^ 3 * Nat.card Q ≤ Nat.card Z * Nat.card Q := by
    rw [mul_comm (Nat.card Z)]
    exact h1.trans h2
  have h4 : Nat.card Z ^ 3 ≤ Nat.card Z := Nat.le_of_mul_le_mul_right h3 hQ
  have h5 : Nat.card Z ^ 3 = Nat.card Z * Nat.card Z * Nat.card Z := by ring
  nlinarith

private theorem exists_N (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ g ∈ gam D AM, (∀ v ∈ D.VU AM, g v = v) ∧ ∃ u, g u ≠ u := by
  obtain ⟨x, hx, hxY⟩ := exists_mem_LB_inf_CN D
  have htLB := D.good.1.mem_LB
  have hm : ∀ e, AM.φ ⟨x, hc.LB_le_H0 hx.1⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨x, hc.LB_le_H0 hx.1⟩ e) :=
    Sec108Data.phi_comm_of_comm_mem AM
      (Subgroup.commutator_le.mp hc.commutator_LB_le_Q x hx.1 t htLB)
  refine ⟨D.resU AM ⟨x, hc.LB_le_H0 hx.1⟩ hm,
    ⟨⟨x, hc.LB_le_H0 hx.1⟩, le_Rt (M := M) (LB M Q B) htLB hx.1, hm, rfl⟩, ?_, ?_⟩
  · intro v hv
    apply Subtype.ext
    rw [Sec108Data.coe_resU_apply]
    obtain ⟨w, hwV, hwQ, hw⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp ((D.mem_VU AM).mp hv))
    rw [← hw]
    exact (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨x, hc.LB_le_H0 hx.1⟩)
      (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hx.1)).1
      (fun z hz => AM.φ_π ⟨x, hc.LB_le_H0 hx.1⟩ z hz) hwQ).mp
      ((Ctx.mem_CN.mp hx.2).2 w hwV)
  · have hnot := mt (D.fix_range_nu_iff AM ⟨x, hx.1⟩).mp hxY
    push Not at hnot
    obtain ⟨u, hu, hne⟩ := hnot
    exact ⟨⟨u, hu⟩, fun h => hne (congrArg Subtype.val h)⟩

theorem Sec108Data.eq_smul_of_commute (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (ψ : ↥(LinearMap.range (D.nu AM)) →ₗ[AM.K] ↥(LinearMap.range (D.nu AM)))
    (hψ : ∀ m : ↥(H0 M Z), (m : G) ∈ Rt M (LB M Q B) t →
      (∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) →
      ∀ u u' : ↥(LinearMap.range (D.nu AM)), (u' : AM.M₀.E) = AM.φ m u →
        (ψ u' : AM.M₀.E) = AM.φ m (ψ u)) :
    ∃ c : AM.K, ψ = c • LinearMap.id := by
  obtain ⟨b, hb⟩ := exists_basis D AM
  refine CFSG.ClassicalGroups.SpecialLinear.eq_smul_of_commute_of_lagrangian (n := 3) le_rfl
    (D.Pform AM) (D.Pform_nondegenerate AM) (D.VU AM) (D.orthogonal_VU AM) b
    (gam D AM) ?_ ?_ hb (exists_N D AM) ψ ?_
  · rintro g ⟨m, -, hm, rfl⟩ u w
    exact D.resU_Pform AM hm u w
  · rintro g ⟨m, hmR, hm, rfl⟩ v hv
    exact D.phi_mem_Vsp AM hmR hv
  · rintro g ⟨m, hmR, hm, rfl⟩ u
    exact Subtype.ext (hψ m hmR hm u _ (D.coe_resU_apply AM hm u))

theorem Sec108Data.exists_smul_of_commute (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z))
    (hcomm : ∀ m' : ↥(H0 M Z), (m' : G) ∈ Rt M (LB M Q B) t →
      (∀ e, AM.φ m' (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m' e)) →
      ∀ e, AM.φ m (AM.φ m' e) = AM.φ m' (AM.φ m e)) :
    ∃ c : AM.K, ∀ u ∈ LinearMap.range (D.nu AM), AM.φ m u = c • u := by
  have hmt : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e) :=
    hcomm ⟨t, D.t_mem_H0⟩ (le_Rt (M := M) (LB M Q B) D.good.1.mem_LB D.good.1.mem_LB)
      (fun _ => rfl)
  obtain ⟨c, hc'⟩ := D.eq_smul_of_commute AM (D.resU AM m hmt : _ →ₗ[AM.K] _)
    (fun m' hm'R hm' u u' hu' => by
      simp only [LinearEquiv.coe_coe, Sec108Data.coe_resU_apply]
      rw [hu', hcomm m' hm'R hm'])
  refine ⟨c, fun u hu => ?_⟩
  have h := congrArg Subtype.val (LinearMap.congr_fun hc' ⟨u, hu⟩)
  simpa [Sec108Data.coe_resU_apply] using h

theorem Sec108Data.eq_id_add_smul_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z))
    (hcomm : ∀ m' : ↥(H0 M Z), (m' : G) ∈ Rt M (LB M Q B) t →
      (∀ e, AM.φ m' (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m' e)) →
      ∀ e, AM.φ m (AM.φ m' e) = AM.φ m' (AM.φ m e))
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ m u = u) :
    ∃ c : AM.K, (AM.φ m : AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id + c • D.nu AM := by
  set g : AM.M₀.E →ₗ[AM.K] AM.M₀.E := (AM.φ m : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - LinearMap.id
    with hg
  have hgapp : ∀ e, g e = AM.φ m e - e := fun e => rfl
  have hrange : ∀ e, g e ∈ LinearMap.range (D.nu AM) := by
    intro e
    rw [← D.orthogonal_range_nu AM, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    show AM.M₀.B u (g e) = 0
    rw [hgapp, map_sub, ← quadModel_B_iso AM.M₀ (AM.φ m) (AM.φ_Qf m) u e, hU u hu, sub_self]
  let g' : AM.M₀.E →ₗ[AM.K] ↥(LinearMap.range (D.nu AM)) := g.codRestrict _ hrange
  have hker : LinearMap.ker (D.nu AM) ≤ LinearMap.ker g' := by
    intro e he
    rw [← D.range_nu_eq_ker AM] at he
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show g e = 0
    rw [hgapp, hU e he, sub_self]
  let ψ : ↥(LinearMap.range (D.nu AM)) →ₗ[AM.K] ↥(LinearMap.range (D.nu AM)) :=
    (LinearMap.ker (D.nu AM)).liftQ g' hker ∘ₗ
      ((LinearMap.quotKerEquivRange (D.nu AM)).symm : _ →ₗ[AM.K] _)
  have hψ : ∀ e, (ψ ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩ : AM.M₀.E) = g e := by
    intro e
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hmt : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e) :=
    hcomm ⟨t, D.t_mem_H0⟩ (le_Rt (M := M) (LB M Q B) D.good.1.mem_LB D.good.1.mem_LB)
      (fun _ => rfl)
  obtain ⟨c, hc'⟩ := D.eq_smul_of_commute AM ψ (by
    intro m' hm'R hm' u u' hu'
    obtain ⟨e, he⟩ := u.2
    have hu : u = ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩ := Subtype.ext he.symm
    have hu'' : u' = ⟨D.nu AM (AM.φ m' e), LinearMap.mem_range_self _ _⟩ :=
      Subtype.ext (by
        show (u' : AM.M₀.E) = D.nu AM (AM.φ m' e)
        rw [hu', ← he, D.nu_phi AM hm'])
    rw [hu, hu'', hψ, hψ, hgapp, hgapp, map_sub, hcomm m' hm'R hm' e])
  refine ⟨c, LinearMap.ext fun e => ?_⟩
  have h1 := hψ e
  rw [hc'] at h1
  have h2 : c • D.nu AM e = AM.φ m e - e := by
    simpa [hgapp] using h1
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, h2,
    LinearEquiv.coe_coe]
  abel

theorem Sec108Data.root_eq (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {y : G} (hy : y ∈ Y) :
    ∃ c : AM.K, (AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + c • D.nu AM := by
  refine D.eq_id_add_smul_nu AM _ (fun m' hm'R _ e => Sec108Data.phi_comm_of_comm_mem AM ?_ e)
    (fun u hu => D.root_fix_range_nu AM hy hu)
  rw [← commutatorElement_inv]
  exact Q.inv_mem (D.comm_Rt_root_mem _ hm'R y hy)

theorem Sec108Data.nu_ne_zero (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    D.nu AM ≠ 0 := by
  intro h
  have h6 := D.finrank_range_nu AM
  rw [h, LinearMap.range_zero, finrank_bot] at h6
  omega

theorem Sec108Data.exists_root_eq_smul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (c : AM.K) :
    ∃ (y : G) (hy : y ∈ Y),
      (AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
        LinearMap.id + c • D.nu AM := by
  choose f hf using fun y : ↥Y => D.root_eq AM y.2
  have hinj : Function.Injective f := by
    intro y₁ y₂ h
    have h12 : AM.φ ⟨y₁, hc.LB_le_H0 (D.root_le_LB y₁.2)⟩ =
        AM.φ ⟨y₂, hc.LB_le_H0 (D.root_le_LB y₂.2)⟩ :=
      LinearEquiv.toLinearMap_injective (by rw [hf, hf, h])
    have hq : (y₂ : G)⁻¹ * y₁ ∈ Q := by
      have h1 : AM.φ (⟨y₂, hc.LB_le_H0 (D.root_le_LB y₂.2)⟩⁻¹ *
          ⟨y₁, hc.LB_le_H0 (D.root_le_LB y₁.2)⟩) = 1 := by
        rw [map_mul, map_inv, h12, inv_mul_cancel]
      exact (AM.φ_ker _).mp h1
    have hmem : (y₂ : G)⁻¹ * y₁ ∈ Y ⊓ Q := ⟨Y.mul_mem (Y.inv_mem y₂.2) y₁.2, hq⟩
    rw [(smith_1_12 D.sit).2, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact (Subtype.ext hmem).symm
  have hcard : Nat.card AM.K ≤ Nat.card ↥Y := by
    obtain ⟨g, hg⟩ := D.sit.conj
    rw [AM.glob.card, hg, card_conjSubgroup]
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le hcard).2 c
  exact ⟨y, y.2, by rw [hf, hy]⟩

end CFSG.RankThree.GF2n.Stroth80
