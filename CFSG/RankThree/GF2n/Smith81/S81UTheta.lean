module

public import CFSG.RankThree.GF2n.Smith81.S81NThmA

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

section Coinv
variable [Finite G] [CharP K 2]

@[expose] noncomputable def thetaF (M₀ : Tim79.QuadModel Q Z K γ) (x : G) (c : M₀.E) : K :=
  γ ⁅(M₀.π_surj c).choose, x⁆

theorem thetaF_pi (hs : Sit M Q Z X x) {q : G} (hq : q ∈ Q) :
    thetaF M₀ x (M₀.π q) = γ ⁅q, x⁆ := by
  obtain ⟨hQ', hπ'⟩ := (M₀.π_surj (M₀.π q)).choose_spec
  unfold thetaF
  rw [comm_eq_of_pi_eq hs hQ' hq hπ']

theorem thetaF_add (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    {c₁ c₂ : M₀.E} (h₁ : c₁ ∈ Cs Tx) (h₂ : c₂ ∈ Cs Tx) :
    thetaF M₀ x (c₁ + c₂) = thetaF M₀ x c₁ + thetaF M₀ x c₂ := by
  obtain ⟨q₁, hq₁, rfl⟩ := M₀.π_surj c₁
  obtain ⟨q₂, hq₂, rfl⟩ := M₀.π_surj c₂
  have hz₁ : ⁅q₁, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hq₁).mpr h₁
  have hz₂ : ⁅q₂, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hq₂).mpr h₂
  rw [thetaF_pi (M₀ := M₀) hs hq₁, thetaF_pi (M₀ := M₀) hs hq₂, ← M₀.π_mul q₁ hq₁ q₂ hq₂,
    thetaF_pi (M₀ := M₀) hs (Q.mul_mem hq₁ hq₂), comm_mul hs hq₁ hz₂, hD.reg.add _ hz₂ _ hz₁]
  exact add_comm _ _

theorem thetaF_zero (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) :
    thetaF M₀ x (0 : M₀.E) = 0 := by
  rw [← Tim79.QuadModel.pi_one M₀, thetaF_pi (M₀ := M₀) hs Q.one_mem, commutatorElement_one_left,
    hD.reg.one]

theorem thetaF_sub (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    {a b : M₀.E} (ha : a ∈ Cs Tx) (hb : b ∈ Cs Tx) :
    thetaF M₀ x (a - b) = thetaF M₀ x a - thetaF M₀ x b := by
  have h := thetaF_add hD hs Tx (Submodule.sub_mem _ ha hb) hb
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem thetaF_eq_zero_of_mem_Rs (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0) {r : M₀.E} (hr : r ∈ Rs Tx) :
    thetaF M₀ x r = 0 := by
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj r
  rw [thetaF_pi (M₀ := M₀) hs hy, (gamma_comm_of_mem_Rs hD hs Tx hy hr).2]
  exact hQf _ hr

theorem exists_twist (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    {u : G} (hu : u ∈ H0 M Z) (hux : ⁅u, x⁆ ∈ Q) :
    ∃ q₁ ∈ Q, ∀ w ∈ Q, M₀.π w ∈ Cs Tx →
      M₀.π (u * w * u⁻¹) ∈ Cs Tx ∧
      thetaF M₀ x (M₀.π (u * w * u⁻¹)) = thetaF M₀ x (M₀.π w) + M₀.B (M₀.π w) (M₀.π q₁) := by
  obtain ⟨huM, huC⟩ := Subgroup.mem_inf.mp hu
  have hcen : ∀ z ∈ Z, u * z * u⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp huC z hz, mul_inv_cancel_right]
  have hxu : ⁅x, u⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem hux
  have hq₁ : u⁻¹ * x * u * x⁻¹ ∈ Q := by
    have e : u⁻¹ * x * u * x⁻¹ = u⁻¹ * ⁅x, u⁆ * u⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_Q hs.hyp (M.inv_mem huM) hxu
  refine ⟨u⁻¹ * x * u * x⁻¹, hq₁, fun w hw hwC => ?_⟩
  have hwx : ⁅w, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hw).mpr hwC
  have hw1 : ⁅w, u⁻¹ * x * u * x⁻¹⁆ ∈ Z := comm_mem_Z hs.hyp hw hq₁
  have hcz : u⁻¹ * x * u * x⁻¹ * ⁅w, x⁆ * (u⁻¹ * x * u * x⁻¹)⁻¹ = ⁅w, x⁆ := by
    rw [← Z_central hs.hyp hwx hq₁, mul_inv_cancel_right]
  have ha : ⁅u * w * u⁻¹, x⁆ = u * ⁅w, u⁻¹ * x * u * x⁻¹ * x⁆ * u⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hb : ⁅w, u⁻¹ * x * u * x⁻¹ * x⁆ = ⁅w, u⁻¹ * x * u * x⁻¹⁆ *
      (u⁻¹ * x * u * x⁻¹ * ⁅w, x⁆ * (u⁻¹ * x * u * x⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hcc : ⁅u * w * u⁻¹, x⁆ = ⁅w, u⁻¹ * x * u * x⁻¹⁆ * ⁅w, x⁆ := by
    rw [ha, hb, hcz, hcen _ (Z.mul_mem hw1 hwx)]
  have hwu : u * w * u⁻¹ ∈ Q := conj_mem_Q hs.hyp huM hw
  have hZc : ⁅u * w * u⁻¹, x⁆ ∈ Z := by
    rw [hcc]
    exact Z.mul_mem hw1 hwx
  refine ⟨(comm_mem_Z_iff hs Tx hwu).mp hZc, ?_⟩
  rw [thetaF_pi (M₀ := M₀) hs hwu, hcc, hD.reg.add _ hw1 _ hwx, M₀.comm_eq w hw _ hq₁,
    ← thetaF_pi (M₀ := M₀) hs hw]
  exact add_comm _ _

theorem exists_linear_conj (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) {u : G}
    (hu : u ∈ H0 M Z) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, ∀ w ∈ Q, M₀.π (u * w * u⁻¹) = T (M₀.π w) := by
  obtain ⟨huM, huC⟩ := Subgroup.mem_inf.mp hu
  have hc : ∀ z ∈ Z, u * z * u⁻¹ = z := fun z hz => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp huC z hz).symm
  obtain ⟨T, hT, -, -⟩ := hD.linear_of_centralizes huM hc
  exact ⟨T, hT⟩

theorem theta_dichotomy_of_coinv (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0) (Vfam : Set G)
    (hV0 : ∀ u ∈ Vfam, u ∈ H0 M Z) (hVx : ∀ u ∈ Vfam, ⁅u, x⁆ ∈ Q)
    (hcov : ∀ c ∈ Cs Tx, c ∈ (Rs Tx).toAddSubgroup ⊔ AddSubgroup.closure
      {e | ∃ u ∈ Vfam, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧ e = M₀.π (u * w * u⁻¹) - M₀.π w}) :
    CaseI Q Z x ∨ CaseII Q Z x := by
  have h12 := smith_1_12 hs
  have hZQ : Z ≤ Q := hs.hyp.Z_normal.1
  have hlin : ∀ c ∈ Cs Tx, ∀ l : K, thetaF M₀ x (l • c) = l * thetaF M₀ x c := by
    let S₀ : AddSubgroup M₀.E :=
      { carrier := {c | c ∈ Cs Tx ∧ ∀ l : K, thetaF M₀ x (l • c) = l * thetaF M₀ x c}
        add_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨add_mem ha hb, fun l => ?_⟩
          rw [smul_add, thetaF_add hD hs Tx (Submodule.smul_mem _ l ha) (Submodule.smul_mem _ l hb),
            thetaF_add hD hs Tx ha hb, ha' l, hb' l, mul_add]
        zero_mem' := by
          refine ⟨zero_mem _, fun l => ?_⟩
          rw [smul_zero, thetaF_zero hD hs, mul_zero]
        neg_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨neg_mem ha, fun l => ?_⟩
          rw [smul_neg, ← zero_sub, thetaF_sub hD hs Tx (zero_mem _) (Submodule.smul_mem _ l ha),
            ← zero_sub, thetaF_sub hD hs Tx (zero_mem _) ha, thetaF_zero hD hs, ha' l]
          ring }
    have hR : (Rs Tx).toAddSubgroup ≤ S₀ := by
      intro r hr
      refine ⟨hr.elim fun e he => ?_, fun l => ?_⟩
      · exact Rs_le_Cs hs Tx hr
      · have h1 := thetaF_eq_zero_of_mem_Rs hD hs Tx hQf (Submodule.smul_mem (Rs Tx) l hr)
        rw [h1, thetaF_eq_zero_of_mem_Rs hD hs Tx hQf hr, mul_zero]
    have hgen : ∀ e ∈ {e | ∃ u ∈ Vfam, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧
        e = M₀.π (u * w * u⁻¹) - M₀.π w}, e ∈ S₀ := by
      rintro e ⟨u, hu, w, hw, hwC, rfl⟩
      obtain ⟨q₁, hq₁, htw⟩ := exists_twist hD hs Tx (hV0 u hu) (hVx u hu)
      obtain ⟨T, hT⟩ := exists_linear_conj hD hs (hV0 u hu)
      obtain ⟨hcC, hθc⟩ := htw w hw hwC
      refine ⟨sub_mem hcC hwC, fun l => ?_⟩
      obtain ⟨wl, hwl, hwlπ⟩ := M₀.π_surj (l • M₀.π w)
      have hwlC : M₀.π wl ∈ Cs Tx := by rw [hwlπ]; exact Submodule.smul_mem _ l hwC
      obtain ⟨hclC, hθcl⟩ := htw wl hwl hwlC
      have hπl : M₀.π (u * wl * u⁻¹) = l • M₀.π (u * w * u⁻¹) := by
        rw [hT wl hwl, hT w hw, hwlπ, map_smul]
      have hlcC : l • M₀.π (u * w * u⁻¹) ∈ Cs Tx := Submodule.smul_mem _ l hcC
      have hlwC : l • M₀.π w ∈ Cs Tx := Submodule.smul_mem _ l hwC
      rw [smul_sub, thetaF_sub hD hs Tx hlcC hlwC, thetaF_sub hD hs Tx hcC hwC, ← hπl, hθcl, hθc,
        hwlπ, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    intro c hc l
    have hmem := (sup_le hR ((AddSubgroup.closure_le S₀).2 hgen)) (hcov c hc)
    exact hmem.2 l
  by_cases hII : CaseII Q Z x
  · exact Or.inr hII
  left
  have hne : ∃ q ∈ Q, ⁅q, x⁆ ∈ Z ∧ ⁅q, x⁆ ≠ 1 := by
    by_contra hno
    apply hII
    intro q hq hqZ
    by_contra h1
    exact hno ⟨q, hq, hqZ, h1⟩
  obtain ⟨q₀, hq₀, hq₀Z, hq₀1⟩ := hne
  have hc₀ : M₀.π q₀ ∈ Cs Tx := (comm_mem_Z_iff hs Tx hq₀).mp hq₀Z
  have hθ₀ : thetaF M₀ x (M₀.π q₀) ≠ 0 := by
    rw [thetaF_pi hs hq₀]
    intro h0
    exact hq₀1 (hD.reg.inj _ hq₀Z h0)
  intro z hz
  obtain ⟨q', hq', hq'π⟩ := M₀.π_surj ((γ z * (thetaF M₀ x (M₀.π q₀))⁻¹) • M₀.π q₀)
  have hq'C : M₀.π q' ∈ Cs Tx := by
    rw [hq'π]; exact Submodule.smul_mem _ _ hc₀
  have hq'Z : ⁅q', x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hq').mpr hq'C
  refine ⟨q', hq', GM.eq_of_γ_eq hD hq'Z hz ?_⟩
  rw [← thetaF_pi (M₀ := M₀) hs hq', hq'π, hlin _ hc₀, mul_assoc, inv_mul_cancel₀ hθ₀, mul_one]

end Coinv


section Coinv2
variable [Finite G] [CharP K 2]

theorem exists_isom_conj (hD : GlobalModelData M Q Z γ M₀) {u : G} (hu : u ∈ H0 M Z) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ w ∈ Q, M₀.π (u * w * u⁻¹) = T (M₀.π w)) ∧
      ∀ e f, M₀.B (T e) (T f) = M₀.B e f := by
  obtain ⟨huM, huC⟩ := Subgroup.mem_inf.mp hu
  have hc : ∀ z ∈ Z, u * z * u⁻¹ = z := fun z hz => by
    have h1 := Subgroup.mem_centralizer_iff.mp huC z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  obtain ⟨T, hT, -, hB⟩ := hD.linear_of_centralizes huM hc
  exact ⟨T, hT, hB⟩

private theorem pi_conj_mem_Q_T8 {c y : G} (hc : c ∈ Q) (hy : y ∈ Q) :
    M₀.π (c * y * c⁻¹) = M₀.π y := by
  have hcy : ⁅c, y⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hc hy) (Q.inv_mem hc)) (Q.inv_mem hy)
  have e : c * y * c⁻¹ = ⁅c, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [e, M₀.π_mul _ hcy _ hy, (M₀.π_ker _ hcy).mpr (M₀.comm_mem c hc y hy), zero_add]

theorem conj_T_comm (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {u : G} (hu : u ∈ M)
    (hux : ⁅u, x⁆ ∈ Q) {T' : M₀.E ≃ₗ[K] M₀.E}
    (hT' : ∀ w ∈ Q, M₀.π (u * w * u⁻¹) = T' (M₀.π w)) (e : M₀.E) :
    Tx.T (T' e) = T' (Tx.T e) := by
  obtain ⟨w, hw, rfl⟩ := M₀.π_surj e
  have huw : u * w * u⁻¹ ∈ Q := conj_mem_Q hs.hyp hu hw
  have hxw : x * w * x⁻¹ ∈ Q := conj_mem_Q hs.hyp hs.memM hw
  have hxuw : x * (u * w * u⁻¹) * x⁻¹ ∈ Q := conj_mem_Q hs.hyp hs.memM huw
  have hL : Tx.T (T' (M₀.π w)) = M₀.π (x * (u * w * u⁻¹) * x⁻¹) := by
    rw [← hT' w hw, Tx.hπ _ huw]
  have hR : T' (Tx.T (M₀.π w)) = M₀.π (u * (x * w * x⁻¹) * u⁻¹) := by
    rw [← Tx.hπ w hw, hT' _ hxw]
  have key : u * (x * w * x⁻¹) * u⁻¹ = ⁅u, x⁆ * (x * (u * w * u⁻¹) * x⁻¹) * ⁅u, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hL, hR, key]
  exact (pi_conj_mem_Q_T8 (M₀ := M₀) hux hxuw).symm

theorem Phi_add (hs : Sit M Q Z X x) (Tx : XAct M₀ x) (e f : M₀.E) :
    M₀.B (Tx.T (e + f)) (e + f) = M₀.B (Tx.T e) e + M₀.B (Tx.T f) f := by
  have h1 := B_T_right hs Tx f e
  have h2 := Tim79.QuadModel.B_comm (M₀ := M₀) (Tx.T e) f
  have h3 : M₀.B (Tx.T e) f + M₀.B (Tx.T f) e = 0 := by
    rw [← h1, h2]
    ring
  simp only [map_add, LinearMap.add_apply]
  linear_combination h3

theorem qf_zero_of_coinv (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (Wfam : Set G) (hW0 : ∀ u ∈ Wfam, u ∈ H0 M Z) (hWx : ∀ u ∈ Wfam, ⁅u, x⁆ ∈ Q)
    (hcov : ∀ e : M₀.E, e ∈ AddSubgroup.closure
      {f | ∃ u ∈ Wfam, ∃ w ∈ Q, f = M₀.π (u * w * u⁻¹) - M₀.π w}) :
    ∀ r ∈ Rs Tx, M₀.Qf r = 0 := by
  let Φ : M₀.E →+ K := AddMonoidHom.mk' (fun e => M₀.B (Tx.T e) e) (Phi_add hs Tx)
  have hΦ : ∀ e, Φ e = M₀.B (Tx.T e) e := fun e => rfl
  have hgen : ∀ f ∈ {f | ∃ u ∈ Wfam, ∃ w ∈ Q, f = M₀.π (u * w * u⁻¹) - M₀.π w}, Φ f = 0 := by
    rintro f ⟨u, hu, w, hw, rfl⟩
    obtain ⟨T', hT', hB⟩ := exists_isom_conj hD (hW0 u hu)
    have hcomm := conj_T_comm hs Tx (Subgroup.mem_inf.mp (hW0 u hu)).1 (hWx u hu) hT'
    rw [map_sub, hΦ, hΦ, hT' w hw, hcomm, hB]
    exact sub_self _
  have hker : AddSubgroup.closure {f | ∃ u ∈ Wfam, ∃ w ∈ Q, f = M₀.π (u * w * u⁻¹) - M₀.π w} ≤
      Φ.ker := (AddSubgroup.closure_le Φ.ker).2 fun f hf => hgen f hf
  intro r hr
  obtain ⟨e, rfl⟩ := mem_Rs.mp hr
  rw [Qf_sub hs Tx e, ← hΦ]
  exact hker (hcov e)

private theorem conj_H0_fix' {c : G} (hc : c ∈ H0 M Z) {w : G} (hw : w ∈ Z) :
    c * w * c⁻¹ = w := by
  have h1 : w * c = c * w := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 w hw
  rw [← h1, mul_inv_cancel_right]

private theorem pi_conj_H0_eq' (hs : Sit M Q Z X x) {c : G} (hc : c ∈ H0 M Z) {d y : G}
    (hdQ : d ∈ Q) (hyQ : y ∈ Q) (h : M₀.π d = M₀.π y) :
    M₀.π (c * d * c⁻¹) = M₀.π (c * y * c⁻¹) := by
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hc).1
  have hcd : c * d * c⁻¹ ∈ Q := conj_mem_Q hs.hyp hcM hdQ
  have hcy : c * y * c⁻¹ ∈ Q := conj_mem_Q hs.hyp hcM hyQ
  have hw : d⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hdQ hyQ).mp h
  refine (Tim79.QuadModel.pi_eq_iff M₀ hcd hcy).mpr ?_
  have e : (c * d * c⁻¹)⁻¹ * (c * y * c⁻¹) = c * (d⁻¹ * y) * c⁻¹ := by group
  rw [e, conj_H0_fix' hc hw]
  exact hw

private theorem hfus_of_caseI' (hs : Sit M Q Z X x) (hI : CaseI Q Z x) :
    ∀ z ∈ Z, IsConj x (x * z) := by
  intro z hz
  obtain ⟨q, -, hqz⟩ := hI z hz
  have hxz : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hs.x_cent (smith_1_12 hs) z hz)
  refine isConj_iff.mpr ⟨q, ?_⟩
  calc q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
    _ = z * x := by rw [hqz]
    _ = x * z := hxz.symm

theorem e3l28_root_of_coinv (hs : Sit M Q Z X x) (hD : GlobalModelData M Q Z γ M₀)
    (Tx : XAct M₀ x) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0)
    (Vfam : Set G) (hV0 : ∀ u ∈ Vfam, u ∈ H0 M Z) (hVx : ∀ u ∈ Vfam, ⁅u, x⁆ ∈ Q)
    (hcov : ∀ c ∈ Cs Tx, c ∈ (Rs Tx).toAddSubgroup ⊔ AddSubgroup.closure
      {e | ∃ u ∈ Vfam, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧ e = M₀.π (u * w * u⁻¹) - M₀.π w})
    (Ufam : Set G) (hU0 : ∀ u ∈ Ufam, u ∈ H0 M Z) (hUx : ∀ u ∈ Ufam, ⁅u, x⁆ ∈ Q)
    (hUC : ∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx)
    (hUfix : ∀ e ∈ Cs Tx, (∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w = e → M₀.π (u * w * u⁻¹) = e) →
      e ∈ Rs Tx)
    (hP2 : ∀ S : AddSubgroup M₀.E, S ≠ ⊥ → (∀ s ∈ S, s ∈ Rs Tx) →
      (∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ S → M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ S) →
      ∃ e ∈ S, e ≠ 0 ∧ RootPt M₀ e)
    (hne : Q ⊓ QB X ≠ ⊥) : ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  rcases theta_dichotomy_of_coinv hD hs Tx hQf Vfam hV0 hVx hcov with hI | hII
  · by_cases hJ : Jx Q X x = ⊥
    · exact absurd (caseI_D_bot hD hs Tx hI hJ hQf Ufam hU0 hUx hUC hUfix) hne
    · exact smith28_of_fused hs hJ (hfus_of_caseI' hs hI)
  · obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hd0 : M₀.π d ≠ 0 := fun h0 => hd1' (D_eq_one_of_pi_eq_zero hs hd h0)
    have hS0 : piSub M₀ (Q ⊓ QB X) inf_le_left ≠ ⊥ := by
      intro hS
      have hmem : M₀.π d ∈ piSub M₀ (Q ⊓ QB X) inf_le_left :=
        mem_piSub.mpr ⟨d, hd, rfl⟩
      rw [hS, AddSubgroup.mem_bot] at hmem
      exact hd0 hmem
    have hSR : ∀ s ∈ piSub M₀ (Q ⊓ QB X) inf_le_left, s ∈ Rs Tx := by
      intro s hs'
      obtain ⟨d₀, hd₀, rfl⟩ := mem_piSub.mp hs'
      exact caseII_piD_le_R hD hs Tx hII hd₀
    have hstab : ∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ piSub M₀ (Q ⊓ QB X) inf_le_left →
        M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ piSub M₀ (Q ⊓ QB X) inf_le_left := by
      intro a b ha0 hb0 hax hbx y hyQ hyS
      obtain ⟨d₀, hd₀, hπy⟩ := mem_piSub.mp hyS
      obtain ⟨d', hd', hπ'⟩ := commInv_piD hD hs Tx hII ha0 hax hb0 hbx hd₀
      have hcH : ⁅a, b⁆ ∈ H0 M Z := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha0 hb0) (inv_mem ha0)) (inv_mem hb0)
      refine mem_piSub.mpr ⟨d', hd', ?_⟩
      rw [hπ']
      exact pi_conj_H0_eq' hs hcH (Subgroup.mem_inf.mp hd₀).1 hyQ hπy
    obtain ⟨e, heS, he0, hroot⟩ := hP2 _ hS0 hSR hstab
    obtain ⟨d', hd', rfl⟩ := mem_piSub.mp heS
    exact ⟨d', isConj_of_rootPt hD hs (Subgroup.mem_inf.mp hd').1 he0 hroot,
      (Subgroup.mem_inf.mp hd').1, (Subgroup.mem_inf.mp hd').2⟩

end Coinv2

end CFSG.RankThree.GF2n.Smith81.E3LCond
