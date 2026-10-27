module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.C3

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

omit [Finite G] in
theorem back_facts (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    vtype m = true ∧ vtype γ' = false ∧ γ' ≠ α' ∧ dist β γ' + 3 = bMin H M := by
  obtain ⟨hm, hγ, d1, d2⟩ := hb
  have hd := hp.dist_eq
  have hm' : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  refine ⟨hm', vtype_nbr_S3 hm' hγ, ?_, by omega⟩
  rintro rfl
  omega

theorem wb_le_stab (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Wb β ≤ stab γ' := by
  obtain ⟨-, -, -, h1⟩ := back_facts hp hb
  refine iSup₂_le fun ρ hρ => Vn_le_stab_dist hS ?_
  have h2 := dist_triangle rfl ρ β γ'
  omega

theorem conjSub_Zv_le (hA : F53Amalgam H M S) {x : G} (hx : x ∈ stab m) :
    conjSub x (Zv m) ≤ Zv m := by
  intro y hy
  have hy' : x⁻¹ * y * x ∈ Zv m := mem_conjSub.mp hy
  have hn := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA m hx) (x⁻¹ * y * x)
  have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  rw [e] at hn
  exact hn.mp hy'

theorem conjSub_le_of_Qv (hS : Sit H M S) (hα' : vtype α' = false) (hm : m ∈ nbrs α')
    {R : Subgroup G} (hR : R ≤ Vn α') {x : G} (hxQ : x ∈ Qv α') (hxm : x ∈ stab m) :
    conjSub x (R ⊔ Zv m) ≤ R ⊔ Zv m := by
  rw [conjSub_sup]
  refine sup_le ?_ ((conjSub_Zv_le hS.glob.amalg hxm).trans le_sup_right)
  intro y hy
  have hr : x⁻¹ * y * x ∈ R := mem_conjSub.mp hy
  have hc : ⁅(x⁻¹ * y * x)⁻¹, x⁆ ∈ Zv α' := by
    have h := Subgroup.commutator_mem_commutator (hR (R.inv_mem hr)) hxQ
    rwa [comm_Vn_Qv hS hα'] at h
  have e : y = (x⁻¹ * y * x) * ⁅(x⁻¹ * y * x)⁻¹, x⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (R ⊔ Zv m).mul_mem (Subgroup.mem_sup_left hr)
    (Subgroup.mem_sup_right (Zv_le_Zv_of_nbr hS hα' hm hc))

theorem conjSub_le_of_Wb (hS : Sit H M S) {β : Geo H M} {R : Subgroup G} (hR : R ≤ Vn β) {x : G}
    (hxW : x ∈ Wb β) (hxm : x ∈ stab m) : conjSub x (R ⊔ Zv m) ≤ R ⊔ Zv m := by
  rw [conjSub_sup]
  refine sup_le ?_ ((conjSub_Zv_le hS.glob.amalg hxm).trans le_sup_right)
  intro y hy
  have hr : x⁻¹ * y * x ∈ R := mem_conjSub.mp hy
  have hc : ⁅x⁻¹ * y * x, x⁆ ∈ (⊥ : Subgroup G) := by
    have h := Subgroup.commutator_mem_commutator (hR hr) hxW
    rwa [comm_Vn_Wb hS] at h
  have h1 : ⁅x⁻¹ * y * x, x⁆ = 1 := Subgroup.mem_bot.mp hc
  have e : y = x⁻¹ * y * x := by
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = (x⁻¹ * y * x) * x * x⁻¹ := by rw [h2]
      _ = x⁻¹ * y * x := by group
  rw [e]
  exact Subgroup.mem_sup_left hr

theorem claim3_of (hS : Sit H M S) (hII : CaseII H M) (h3a : S35.II.Claim3a H M) :
    S35.II.Claim3 H M := by
  intro β α' m γ' hp hb w hw
  by_contra hwα
  obtain ⟨hmS3, hγS5, hγα, -⟩ := back_facts hp hb
  have hα'S5 := hp.vδ'
  have hmα : m ∈ nbrs α' := hb.1
  have hγm : γ' ∈ nbrs m := hb.2.1
  have hα'm : α' ∈ nbrs m := mem_nbrs_symm.mp hmα
  have hwγ : w ∈ stab γ' := wb_le_stab hS hp hb hw.1
  obtain ⟨q, hqQ, hqnQ⟩ : ∃ q ∈ Qv α', q ∉ Qv m := by
    by_contra h
    push Not at h
    exact Q_not_le hS hα'S5 hmα h
  have hqm : q ∈ stab m := Qv_le_stab hS hmα hqQ
  have hqα : q ∈ stab α' := pCoreOf_le 2 _ hqQ
  have hqγ : q ∉ stab γ' := fun h =>
    hqnQ (mem_Qv_of_fix_two hS hmS3 hα'm hγm (Ne.symm hγα) hqm hqα h)
  obtain ⟨σ, hσm, hσα, hσγ, hall⟩ := nbrs_S3_third hS hmS3 hα'm hγm (Ne.symm hγα)
  let gw : ↥(H ⊔ M) := ⟨w, stab_le m hw.2⟩
  let gq : ↥(H ⊔ M) := ⟨q, stab_le m hqm⟩
  have hgwγ : gw • γ' = γ' := smul_eq_of_mem_stab hwγ
  have hgwα : gw • α' = σ := by
    have hmem : gw • α' ∈ nbrs m := smul_mem_nbrs_of_stab hw.2 hα'm
    rcases hall _ hmem with h | h | h
    · exact absurd (mem_stab_of_smul_eq h) hwα
    · exact absurd (MulAction.injective gw (h.trans hgwγ.symm)) (Ne.symm hγα)
    · exact h
  have hgqα : gq • α' = α' := smul_eq_of_mem_stab hqα
  have hgqγ : gq • γ' = σ := by
    have hmem : gq • γ' ∈ nbrs m := smul_mem_nbrs_of_stab hqm hγm
    rcases hall _ hmem with h | h | h
    · exact absurd (MulAction.injective gq (h.trans hgqα.symm)) hγα
    · exact absurd (mem_stab_of_smul_eq h) hqγ
    · exact h
  have hgqσ : gq • σ = γ' := by
    have hmem : gq • σ ∈ nbrs m := smul_mem_nbrs_of_stab hqm hσm
    rcases hall _ hmem with h | h | h
    · exact absurd (MulAction.injective gq (h.trans hgqα.symm)) hσα
    · exact h
    · exact absurd (MulAction.injective gq (h.trans hgqγ.symm)) hσγ
  have hg : (gq * gw) • α' = γ' := by rw [mul_smul, hgwα, hgqσ]
  have hRV : ⁅Vn β, Vn α'⁆ ≤ Vn α' := (PD_comm_le hS hp).trans inf_le_right
  have hRβ : ⁅Vn β, Vn α'⁆ ≤ Vn β := (PD_comm_le hS hp).trans inf_le_left
  have hN : ⁅Vn β, Vn α'⁆ ⊔ Zv m ≤ Vn α' := sup_le hRV (Zv_le_Vn hmα)
  have h1 : conjSub ((gq * gw : ↥(H ⊔ M)) : G)⁻¹ (⁅Vn β, Vn α'⁆ ⊔ Zv m) ≤
      ⁅Vn β, Vn α'⁆ ⊔ Zv m := by
    have e : ((gq * gw : ↥(H ⊔ M)) : G)⁻¹ = w⁻¹ * q⁻¹ := by
      simp [gw, gq, mul_inv_rev]
    rw [e, conjSub_mul]
    exact (conjSub_mono _ (conjSub_le_of_Qv hS hα'S5 hmα hRV ((Qv α').inv_mem hqQ)
      ((stab m).inv_mem hqm))).trans
      (conjSub_le_of_Wb hS hRβ ((Wb β).inv_mem hw.1) ((stab m).inv_mem hw.2))
  have h2 : ⁅Vn β, Vn α'⁆ ⊔ Zv m ≤ Vn γ' := by
    have := (le_conjSub_iff (((gq * gw : ↥(H ⊔ M)) : G))).mpr (h1.trans hN)
    rwa [← Vn_smul, hg] at this
  have h3 : ⁅Vn β, Vn α'⁆ ≤ Zv m :=
    le_sup_left.trans ((le_inf hN h2).trans
      (hII α' m γ' hα'S5 hmα (mem_nbrs_symm.mp hγm) hγα).le)
  exact (h3a β α' m γ' hp hb).2 h3

end S35.C3

end F53.Stellmacher

end CFSG.Quasithin
