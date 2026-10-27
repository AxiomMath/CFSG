module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1E
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DLC
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DLCF
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DRank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_comm_zpowers (g s : G) (S : Subgroup G) :
    conjSubgroup g ⁅S, Subgroup.zpowers s⁆ =
      ⁅conjSubgroup g S, Subgroup.zpowers (g * s * g⁻¹)⁆ := by
  unfold conjSubgroup
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  rfl

section Lemmas

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem mem_img_comm_iff {a : G} (ha : a ∈ H0 M Z) (e : M₀.E) :
    e ∈ M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) ↔ e ∈ V2 φ a := by
  have hQa : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha.1) x).mp hx
  have hQa' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem ha.1)) x).mp hx
    simpa using this
  exact mem_img_comm_zpowers_sup_iff M₀ S.glob.reg (actM φ a) hQa hQa'
    (fun x hx => S.pi_conj ha hx) e

end Setup95

end Lemmas

end HS9


theorem lc95_of_M1 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hM1 : Step95M1Statement 7) : Step95LCStatementFrom 7 := by
  intro G _ _ M Q Z B hc n t Z0 cfg hn h1 z hz h3 h5
  classical
  have hs : Sec9Hyp hc n t := cfg.hs
  have ht : t ∈ LB M Q B := hs.mem
  have hzM : z ∈ M := hz.mem
  have hzBZ := HS9.mem_normalizer_BZ95 h34 hs hzM hz.normL
  have hzLi : conjSubgroup z⁻¹ (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_eq_self_iff]
    exact (Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G)).inv_mem
      (conjSubgroup_eq_self_iff.mp hz.normL)
  have hzi : z⁻¹ ∈ M := M.inv_mem hzM
  obtain ⟨K, fK, finK, chK, γ, M₀, hglob⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφQf⟩ := exists_actionHom_H0 hc.hyp hglob
  obtain ⟨Y₁, Y₂, i1, i2, i3, i4, ⟨D⟩⟩ := hM1 G M Q Z B hc n t hs hn hglob φ hφπ hφQ
  obtain ⟨r0, hr0⟩ := hA G M Q Z B hc n t hs
  have hWV := (h91b G M Q Z B hc n t hs r0 hr0 _ _ rfl rfl).2
  let S : HS9.Setup95 hc t M₀ φ Y₁ Y₂ := ⟨hglob, hφπ, hφQ, hφQf, hWV, ht, D⟩
  have hq4 : 4 ≤ Nat.card K := by
    rw [hglob.card]
    exact hc.hyp.q4
  have hKgrp : ∀ m ∈ hc.CN t, (∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, x⁆ ∈ Z) →
      m ∈ LB M Q B := by
    intro m hm hmW
    have := S.mem_Z0_of_theta_eq_zero h34 h311a h311bComm h311bCard hs hr0 cfg.hZ0 hm
      ((S.theta_eq_zero_iff hm).mpr hmW)
    exact (Subgroup.mem_inf.mp (cfg.centre.1 this)).1
  obtain ⟨ρ, hρz, c, hcR, hEq, hρV, hρBZ⟩ := HS9.exists_point_pair95 hs hzM h5
  have hρR : z⁻¹ * ρ * z ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp hρz
  have hρM : ρ ∈ M := by
    have h2 := hc.Rt_le_M t hρR
    have e : ρ = z * (z⁻¹ * ρ * z) * z⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hzM h2) (M.inv_mem hzM)
  set r : G := z⁻¹ * ρ * z with hrdef
  have hrR : r ∈ Rt M (LB M Q B) t := hρR
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hrH : r ∈ H0 M Z := hc.Rt_le_H0 t hrR
  obtain ⟨s, hsZ0, hsV⟩ := HS9.exists_gen_Vt95 cfg.centre
  set s₂ : G := z⁻¹ * s * z with hs₂def
  have hs₂N1 : s₂ ∈ HS9.N1 hc t := mem_conjSubgroup.mp (HS9.centre_le_conj_N1_95 cfg hz hsZ0)
  obtain ⟨x, hxz, hxN⟩ : ∃ x ∈ conjSubgroup z (HS9.N1 hc t), x ∉ hc.CN t := by
    by_contra hcon
    push Not at hcon
    have hle : conjSubgroup z (HS9.N1 hc t) ≤ HS9.N1 hc t := fun y hy => by
      refine Subgroup.mem_inf.mpr ⟨?_, hcon y hy⟩
      have : y ∈ conjSubgroup z (LB M Q B) :=
        Subgroup.map_mono (inf_le_left : HS9.N1 hc t ≤ LB M Q B) hy
      rwa [hz.normL] at this
    have h4 := h3.1.1
    rw [sup_eq_left.mpr hle] at h4
    exact lt_irrefl _ h4
  have hx₀N1 : z⁻¹ * x * z ∈ HS9.N1 hc t := mem_conjSubgroup.mp hxz
  set x₀ : G := z⁻¹ * x * z with hx₀def
  set V' : Subgroup G := conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) with hV'def
  have hV'Q : V' ≤ Q := by
    have h1 : V' ≤ conjSubgroup z⁻¹ Q := Subgroup.map_mono (hc.Vt_le_Q t)
    rwa [hc.conj_Q_eq hzi] at h1
  have hV's : ⁅Q, Subgroup.zpowers s₂⁆ ⊔ Z = V' := by
    have h4 := congrArg (conjSubgroup z⁻¹) hsV
    rw [conjSubgroup_sup', HS9.conj_comm_zpowers, hc.conj_Q_eq hzi, hc.conj_Z_eq hzi] at h4
    simpa using h4
  have hV'x : ⁅V', Subgroup.zpowers x₀⁆ ⊔ Z = V' ⊓ Vt M (LB M Q B) B Z t := by
    have h5x := h5.2.2.2.2 x hxz hxN
    have h4 := congrArg (conjSubgroup z⁻¹) h5x
    rw [conjSubgroup_sup', HS9.conj_comm_zpowers, hc.conj_Z_eq hzi, conjSubgroup_inf,
      ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h4
    simpa using h4
  have hBV' : B ≤ V' ⊓ Vt M (LB M Q B) B Z t := by
    have h6 := HS9.B_le_inf_conj95 h34 hs hzi hzLi
    exact fun b hb => ⟨(h6 hb).2, (h6 hb).1⟩
  have hs₂H : s₂ ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t (Subgroup.mem_inf.mp hs₂N1).2)
  have hx₀H : x₀ ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t (Subgroup.mem_inf.mp hx₀N1).2)
  have hx₀x₀ : x₀ * x₀ ∈ Q := by
    have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_inf.mp hx₀N1).1
    rwa [pow_two] at this
  have himgV' : ∀ e, e ∈ M₀.img V' ↔ e ∈ HS9.V2 φ s₂ := fun e => by
    rw [← hV's]
    exact S.mem_img_comm_iff hs₂H e
  obtain ⟨u, huC, huBZ⟩ : ∃ u ∈ conjSubgroup ρ B, u ∉ B ⊔ Z := by
    by_contra hall
    push Not at hall
    exact hρBZ hall
  have huV := hρV huC
  have huQ : u ∈ Q := (hc.conj_of_mem hρM).le huC
  have hu₀V : z⁻¹ * u * z ∈ V' ⊓ Vt M (LB M Q B) B Z t := by
    refine Subgroup.mem_inf.mpr ⟨?_, mem_conjSubgroup.mp (Subgroup.mem_inf.mp huV).2⟩
    have h6 := HS9.conj_mem95 z⁻¹ (Subgroup.mem_inf.mp huV).1
    simpa using h6
  have hu₀Q : z⁻¹ * u * z ∈ Q := by
    have h6 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hzi) u).mp huQ
    simpa using h6
  set b : G := ρ⁻¹ * u * ρ with hbdef
  have hbB : b ∈ B := mem_conjSubgroup.mp huC
  have hzb : z⁻¹ * b * z ∈ B ⊔ Z := by
    have h6 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)).inv_mem hzBZ) b).mp
      (Subgroup.mem_sup_left hbB)
    simpa using h6
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun b' hb' =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb'))
  obtain ⟨b₃, hb₃B, ζ, hζZ, hbe⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hzb
  have hu₀e : z⁻¹ * u * z = r * (b₃ * ζ) * r⁻¹ := by
    rw [hbe, hrdef, hbdef]
    group
  have hb₃Q : b₃ ∈ Q := hc.le hb₃B
  have hζQ : ζ ∈ Q := hc.Z_le_Q hζZ
  have hbζQ : b₃ * ζ ∈ Q := Q.mul_mem hb₃Q hζQ
  have hπu₀ : M₀.π (z⁻¹ * u * z) = HS9.actM φ r (M₀.π b₃) := by
    rw [hu₀e, S.pi_conj hrH hbζQ, M₀.π_mul _ hb₃Q _ hζQ, (S.pi_eq_zero_iff hζQ).mpr hζZ,
      add_zero]
  have hp'B : M₀.π b₃ ∈ M₀.img B := M₀.pi_mem_img hb₃B hb₃Q
  have hp'0 : M₀.π b₃ ≠ 0 := by
    intro h0
    apply huBZ
    have hb₃Z : b₃ ∈ Z := (S.pi_eq_zero_iff hb₃Q).mp h0
    have hu₀Z : z⁻¹ * u * z ∈ Z := by
      rw [hu₀e]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) (b₃ * ζ)).mp
        (Z.mul_mem hb₃Z hζZ)
    have h6 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hzM) (z⁻¹ * u * z)).mp hu₀Z
    have e : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    rw [e] at h6
    exact Subgroup.mem_sup_right h6
  have hb : ∃ e ∈ HS9.V2 φ s₂, HS9.actM φ x₀ e - e = M₀.π b₃ := by
    have hmem : M₀.π b₃ ∈ M₀.img (⁅V', Subgroup.zpowers x₀⁆ ⊔ Z) := by
      rw [hV'x]
      exact M₀.img_mono hBV' hp'B
    obtain ⟨w, hw, hwe⟩ := S.exists_pre_of_mem_img_comm hV'Q hx₀H hx₀x₀ hmem
    exact ⟨w, (himgV' w).mp hw, hwe⟩
  have hc₀ : ∃ e ∈ HS9.V2 φ s₂, HS9.actM φ x₀ e - e = HS9.actM φ r (M₀.π b₃) := by
    have hmem : HS9.actM φ r (M₀.π b₃) ∈ M₀.img (⁅V', Subgroup.zpowers x₀⁆ ⊔ Z) := by
      rw [hV'x, ← hπu₀]
      exact M₀.pi_mem_img hu₀V hu₀Q
    obtain ⟨w, hw, hwe⟩ := S.exists_pre_of_mem_img_comm hV'Q hx₀H hx₀x₀ hmem
    exact ⟨w, (himgV' w).mp hw, hwe⟩
  have hne : ∀ κ : K, HS9.actM φ r (M₀.π b₃) ≠ κ • M₀.π b₃ := by
    intro κ hκ
    obtain ⟨p, hp0, hBp, hcp⟩ := S.desc.point
    have hκB : κ • M₀.π b₃ ∈ M₀.img B := by
      obtain ⟨lam, hlam⟩ := (hBp _).mp hp'B
      exact (hBp _).mpr ⟨κ * lam, by rw [hlam, smul_smul]⟩
    have hmem : M₀.π (z⁻¹ * u * z) ∈ M₀.img (B ⊔ Z) := by
      rw [hπu₀, hκ]
      exact M₀.img_mono le_sup_left hκB
    have hu₀BZ : z⁻¹ * u * z ∈ B ⊔ Z := (M₀.mem_img_iff le_sup_right hu₀Q).mp hmem
    apply huBZ
    have h6 := (Subgroup.mem_normalizer_iff.mp hzBZ (z⁻¹ * u * z)).mp hu₀BZ
    have e : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    rwa [e] at h6
  have hs₂r : s₂ ∈ LB M Q (conjSubgroup r B) := by
    have hsL : s ∈ LB M Q (conjSubgroup ρ B) :=
      HS9.Z0_le_LB_conj95 cfg.hZ0 cfg.centre hρM hcR hEq hsZ0
    rw [hc.LB_conj hρM, mem_conjSubgroup] at hsL
    rw [hc.LB_conj hrM, mem_conjSubgroup]
    have h6 := HS9.conj_mem95 z⁻¹ hsL
    rw [hzLi] at h6
    have e : r⁻¹ * s₂ * r = z⁻¹ * (ρ⁻¹ * s * ρ) * z⁻¹⁻¹ := by
      simp only [hrdef, hs₂def]
      group
    rw [e]
    exact h6
  obtain ⟨d, hdN1, hdL, e₂, he₂, hde⟩ :=
    S.core hq4 h34 hs hKgrp hs₂N1 hx₀N1 hrR hs₂r hp'B hp'0 hb hc₀ hne
  have hdH : d ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t (Subgroup.mem_inf.mp hdN1).2)
  refine ⟨ρ, hρz, hρV, hρBZ, z * d * z⁻¹, Subgroup.mem_inf.mpr ⟨HS9.conj_mem95 z hdN1, ?_⟩, ?_⟩
  · rw [hc.LB_conj hρM, mem_conjSubgroup]
    rw [hc.LB_conj hrM, mem_conjSubgroup] at hdL
    have h6 := HS9.conj_mem95 z hdL
    rw [hz.normL] at h6
    have e : ρ⁻¹ * (z * d * z⁻¹) * ρ = z * (r⁻¹ * d * r) * z⁻¹ := by
      simp only [hrdef]
      group
    rw [e]
    exact h6
  · intro hxc
    apply hde
    obtain ⟨v', hv'V', hv'Q, hv'e⟩ := (himgV' e₂).mpr he₂
    have hv : z * v' * z⁻¹ ∈ Vt M (LB M Q B) B Z t := by
      have h6 := mem_conjSubgroup.mp hv'V'
      simpa using h6
    have hcomm := (Ctx.mem_CN.mp hxc).2 _ hv
    have e : ⁅d, v'⁆ = z⁻¹ * ⁅z * d * z⁻¹, z * v' * z⁻¹⁆ * z⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hdv : ⁅d, v'⁆ ∈ Z := by
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hzi) _).mp hcomm
    have hq : M₀.π ⁅d, v'⁆ = 0 := (S.pi_eq_zero_iff (hc.Z_le_Q hdv)).mpr hdv
    rw [S.pi_comm hdH hv'Q, hv'e] at hq
    exact sub_eq_zero.mp hq

theorem wvMin95_of_M1 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hM1 : Step95M1Statement 7) : Step95WVMinStatementFrom 7 :=
  wvMin_of_lc95 h34 h91b hA (lc95_of_M1 h34 h91b hA h311a h311bComm h311bCard hM1)

end CFSG.RankThree.GF2n.Stroth80
