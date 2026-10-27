module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Count
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Dict
public import CFSG.RankThree.GF2n.Stroth80.Sec78HypFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj
public import CFSG.RankThree.GF2n.Stroth80.Sec7RootLemma

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_comm_V_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {l v : G} (hl : l ∈ LB M Q B)
    (hv : v ∈ Vt M (LB M Q B) B Z t) :
    ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hlM : l ∈ M := hc.LB_le_M hl
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  obtain ⟨T, hTπ, -, -⟩ := h.linear_of_centralizes hlM (hc.LB_centralizes_Z hl)
  have hflag := hc.LB_act_flag hs5.width hs5.n_gt hs5.noA2 h hB hl
    (T := (T : M₀.E →ₗ[K] M₀.E)) hTπ
  obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have huV : u ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht huB
  have hvW : v ∈ Wt Q (Vt M (LB M Q B) B Z t) := sec7ctr_Vt_le_Wt h34 hc hs5 hv
  have hcomm : v * u = u * v := (Subgroup.mem_centralizer_iff.mp hvW.2 u huV).symm
  have hy := hflag.2.2 (M₀.π v) (by
    rw [← hu]
    exact (M₀.comm_iff_B h.reg hvQ huQ).mp hcomm)
  have hlvQ : l * v * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hlM).1 v hvQ
  have hcQ : ⁅l, v⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hlvQ (Q.inv_mem hvQ)
  have hπc : M₀.π ⁅l, v⁆ = T (M₀.π v) - M₀.π v := by
    have e : ⁅l, v⁆ = (l * v * l⁻¹) * v⁻¹ := by rw [commutatorElement_def]
    rw [e, M₀.π_mul _ hlvQ _ (Q.inv_mem hvQ), Tim79.QuadModel.pi_inv M₀ hvQ, hTπ v hvQ,
      sub_eq_add_neg]
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hmem : ⁅l, v⁆ ∈ Q ⊓ QB B := (M₀.mem_img_iff hZX hcQ).mp (hπc ▸ hy)
  refine ⟨?_, hmem.2⟩
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hl
  have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hlR) v).mp hv
  rw [commutatorElement_def]
  exact (Vt M (LB M Q B) B Z t).mul_mem h1 ((Vt M (LB M Q B) B Z t).inv_mem hv)

theorem sec7_orbit_frame (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {β : G} (hβ : β ∈ Q ⊓ QB B)
    (hβV : β ∉ Vt M (LB M Q B) B Z t) {a : G} (ha : a ∈ B ⊔ Z) :
    ∃ y ∈ LB M Q B ⊓ hc.CN t, ∃ z ∈ Z, ⁅β, y⁆ = a * z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hcard := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hZQB
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨W, hW⟩ := hc.exists_submodule_inf_QB hs5.width hcard.2.2.2 h
  set Y₀ : Subgroup G := Vt M (LB M Q B) B Z t ⊓ QB B with hY₀
  have hZY₀ : Z ≤ Y₀ := le_inf hZV hZQB
  have hY₀Q : Y₀ ≤ Q ⊓ QB B := inf_le_inf_right _ (hc.Vt_le_Q t)
  have hY₀sc : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y₀ → c • e ∈ M₀.img Y₀ := by
    intro c e he
    obtain ⟨y, hyY, hyQ, rfl⟩ := he
    obtain ⟨v', hv'V, hv'Q, hv'⟩ := hc.smul_mem_img_Vt h t c (M₀.pi_mem_img hyY.1 hyQ)
    have hyW : M₀.π y ∈ W := (hW _).mpr (M₀.pi_mem_img (hY₀Q hyY) hyQ)
    have hv'W : M₀.π v' ∈ W := by
      rw [hv']
      exact W.smul_mem c hyW
    have hv'X : v' ∈ Q ⊓ QB B := (M₀.mem_img_iff hZX hv'Q).mp ((hW _).mp hv'W)
    exact ⟨v', ⟨hv'V, hv'X.2⟩, hv'Q, hv'⟩
  let S₀ : Submodule K M₀.E := imgSub M₀ Y₀ hY₀sc
  have hβQ : β ∈ Q := hβ.1
  let S₁ : Submodule K M₀.E := S₀ ⊔ Submodule.span K {M₀.π β}
  have hS₁W : S₁ ≤ W := by
    refine sup_le (fun e he => (hW e).mpr (M₀.img_mono hY₀Q he)) ?_
    refine Submodule.span_le.mpr ?_
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact (hW _).mpr (M₀.pi_mem_img hβ hβQ)
  let Y₁ : Subgroup G := HS9.preSub M₀ S₁.toAddSubgroup
  have hY₁sc : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y₁ → c • e ∈ M₀.img Y₁ := by
    intro c e he
    rw [HS9.img_preSub] at he ⊢
    exact S₁.smul_mem c he
  have hY₁X : Y₁ ≤ Q ⊓ QB B := by
    intro x hx
    exact (M₀.mem_img_iff hZX hx.1).mp ((hW _).mp (hS₁W hx.2))
  have hS₀S₁ : S₀ ≤ S₁ := le_sup_left
  have hBS₀ : ∀ x ∈ B, M₀.π x ∈ S₀ := fun x hx =>
    M₀.pi_mem_img ⟨hc.B_le_Vt ht hx, hc.B_le_QB hx⟩ (hc.le hx)
  have hBY₁ : B ≤ Y₁ := fun x hx => ⟨hc.le hx, hS₀S₁ (hBS₀ x hx)⟩
  obtain ⟨b, hbY, hb0, hBline, hel3, hel4, -⟩ := hc.elation_package hs5.width hs5.n_gt hs5.noA2
    hcard.2.2.1 hcard.2.2.2 h hBY₁ hY₁X hY₁sc
  have haB : a ∈ HS9.preSub M₀ (M₀.img B) := by
    have : B ⊔ Z ≤ HS9.preSub M₀ (M₀.img B) :=
      sup_le (fun x hx => ⟨hc.le hx, M₀.pi_mem_img hx (hc.le hx)⟩)
        (HS9.Z_le_preSub M₀ hc.Z_le_Q _)
    exact this ha
  obtain ⟨s, hsa⟩ := (hBline _).mp haB.2
  have haQ : a ∈ Q := haB.1
  let P : Submodule K M₀.E := imgSub M₀ Y₁ hY₁sc
  have hβY₁ : β ∈ Y₁ := ⟨hβQ, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
  have hπβP : M₀.π β ∈ P := mem_imgSub.mpr (M₀.pi_mem_img hβY₁ hβQ)
  let xβ : P := ⟨M₀.π β, hπβP⟩
  let P₀ : Submodule K P := Submodule.comap P.subtype S₀
  have hxβ : xβ ∉ P₀ := by
    intro hx
    have hx' : M₀.π β ∈ M₀.img Y₀ := hx
    exact hβV ((M₀.mem_img_iff hZY₀ hβQ).mp hx').1
  obtain ⟨f₀, hf₀x, hf₀P⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxβ inferInstance
  set f : Module.Dual K P := ((-s) / f₀ xβ) • f₀ with hf
  have hfx : f xβ = -s := by
    simp only [hf, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hfP : ∀ p ∈ P₀, f p = 0 := by
    intro p hp
    have hmem : f₀ p ∈ P₀.map f₀ := Submodule.mem_map_of_mem hp
    rw [hf₀P] at hmem
    simp only [hf, LinearMap.smul_apply, smul_eq_mul]
    rw [(Submodule.mem_bot K).mp hmem, mul_zero]
  have hbimg : b ∈ M₀.img B := (hBline b).mpr ⟨1, (one_smul K b).symm⟩
  have hbP : (⟨b, hbY⟩ : P) ∈ P₀ :=
    M₀.img_mono (le_inf (hc.B_le_Vt ht) hc.B_le_QB) hbimg
  have hfb : f ⟨b, hbY⟩ = 0 := hfP _ hbP
  obtain ⟨l, hl, hlS⟩ := hel4 f hfb
  have hlM : l ∈ M := hc.LB_le_M hl
  obtain ⟨T, hTπ, -, -⟩ := h.linear_of_centralizes hlM (hc.LB_centralizes_Z hl)
  have hSl := hlS T hTπ
  have hlQ : ∀ x ∈ Q, l * x * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hlM).1
  have hcentY : ∀ y ∈ Y₀, ⁅l, y⁆ ∈ Z := by
    intro y hy
    have hyQ : y ∈ Q := hc.Vt_le_Q t hy.1
    have hyY₁ : y ∈ Y₁ := ⟨hyQ, hS₀S₁ (M₀.pi_mem_img hy hyQ)⟩
    have hπyP : M₀.π y ∈ P := mem_imgSub.mpr (M₀.pi_mem_img hyY₁ hyQ)
    have hyP₀ : (⟨M₀.π y, hπyP⟩ : P) ∈ P₀ := M₀.pi_mem_img hy hyQ
    have h1 := hSl ⟨M₀.π y, hπyP⟩
    rw [hfP _ hyP₀, zero_smul, add_zero] at h1
    exact (M₀.comm_mem_iff hyQ (hlQ y hyQ)).mpr ((hTπ y hyQ).trans h1)
  have hlN : l ∈ hc.CN t := by
    refine mem_CN_of_comm_comm_mem_Z hA hPts hc hs hl (fun v hv => hcentY v ?_)
    have hle : ⁅Vt M (LB M Q B) B Z t, LB M Q B⁆ ≤ Y₀ := by
      rw [Subgroup.commutator_le]
      intro v hv l' hl'
      have h1 := sec7_comm_V_LB h34 hc hs h hBline hl' hv
      rw [← commutatorElement_inv l' v]
      exact Y₀.inv_mem h1
    exact hle hv
  refine ⟨l, ⟨hl, hlN⟩, ?_⟩
  have hβl : T (M₀.π β) = M₀.π β + (-s) • b := by
    have := hSl xβ
    rw [hfx] at this
    exact this
  have hlβQ : l * β * l⁻¹ ∈ Q := hlQ β hβQ
  have hcQ : ⁅β, l⁆ ∈ Q := by
    have e : ⁅β, l⁆ = β * (l * β * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hβQ (Q.inv_mem hlβQ)
  have hπ : M₀.π ⁅β, l⁆ = M₀.π a := by
    have e : ⁅β, l⁆ = β * (l * β * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, M₀.π_mul _ hβQ _ (Q.inv_mem hlβQ), Tim79.QuadModel.pi_inv M₀ hlβQ, hTπ β hβQ, hβl,
      hsa]
    module
  have hz : a⁻¹ * ⁅β, l⁆ ∈ Z := (M₀.pi_eq_iff haQ hcQ).mp hπ.symm
  exact ⟨a⁻¹ * ⁅β, l⁆, hz, by group⟩

@[expose] def Step72OrbitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ β ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup r B),
      β ∉ Vt M (LB M Q B) B Z t →
    ∀ a ∈ conjSubgroup r B ⊔ Z,
      ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ∃ z ∈ Z, ⁅β, y⁆ = a * z

theorem step72Orbit_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Step72OrbitStatement := by
  intro G _ _ M Q Z B hc n t hs r hr β hβ hβV a ha
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRt : Rt M (LB M Q B) (r * t * r⁻¹) = Rt M (LB M Q B) t := by
    rw [← conjSubgroup_Rt_eq hrM t]
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr.mem)
  have hVt : Vt M (LB M Q B) B Z (r * t * r⁻¹) = Vt M (LB M Q B) B Z t := by
    rw [← conjSubgroup_Vt_eq hrM (hc.conj_Z_eq hrM) t]
    exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr.mem)
  have hsL : r * t * r⁻¹ ∈ LB M Q (conjSubgroup r B) := by
    rw [hc.LB_conj hrM, mem_conjSubgroup, show r⁻¹ * (r * t * r⁻¹) * r = t by group]
    exact ht
  have hsQ : r * t * r⁻¹ ∉ Q := fun hsQ =>
    hs.toSec5.notQ ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) t).mpr hsQ)
  have hs' : Sec7Hyp (hc.conj_of_mem hrM) n (r * t * r⁻¹) :=
    sec7ctr_hyp_frame hc hs hrM hsL hsQ hRt hVt
  have hCN : (hc.conj_of_mem hrM).CN (r * t * r⁻¹) = hc.CN t :=
    (sec7ctr_CN_conj_frame hc hrM (r * t * r⁻¹)).trans (hc.CN_congr hRt hVt)
  have hVfr : Vt M (LB M Q (conjSubgroup r B)) (conjSubgroup r B) Z (r * t * r⁻¹) =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hrM, sec7ctr_Vt_conj_frame hrM, hVt]
  obtain ⟨y, hy, z, hz, hyz⟩ := sec7_orbit_frame h34 hA hPts (hc.conj_of_mem hrM) hs'
    (β := β) ⟨hβ.1.1, hβ.2⟩ (by rw [hVfr]; exact hβV) ha
  exact ⟨y, ⟨hy.1, by rw [← hCN]; exact hy.2⟩, z, hz, hyz⟩

end CFSG.RankThree.GF2n.Stroth80
