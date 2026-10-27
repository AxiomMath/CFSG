module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishSwap
public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishCountAbs
public import CFSG.RankThree.GF2n.Stroth80.Sec7CardBeta

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS93

theorem x_facts (hCentre : Step95CentreStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {s z : G} (hT : Sec9T1 M Q Z0 s z) :
    z * s * z⁻¹ ∈ M ∧ z * s * z⁻¹ ∈ H0 M Z ∧ (z * s * z⁻¹) ^ 2 ∈ Q ∧
      conjSubgroup (z * s * z⁻¹) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  have hsR : s ∈ Rt M (LB M Q B) t := ((hZ0 s).mp hT.s_mem).1
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hsL : s ∈ LB M Q B := (((hCentre G M Q Z B hc n t hs Z0 hZ0).1) hT.s_mem).1
  refine ⟨M.mul_mem (M.mul_mem hT.z_mem hsM) (M.inv_mem hT.z_mem),
    hc.conj_mem_H0 hT.z_mem (hc.Rt_le_H0 t hsR), ?_, conj_Vt_of_centre hCentre hs hZ0 hT⟩
  have e : (z * s * z⁻¹) ^ 2 = z * s ^ 2 * z⁻¹ := by
    simp only [pow_two]
    group
  rw [e]
  exact norm_Q hc hT.z_mem (hc.sq_mem_Q_of_mem_LB hsL)

theorem comm_mem_conj_Vt_of_mem_Q (hCentre : Step95CentreStatement) {hc : Ctx M Q Z B} {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s z : G} (hT : Sec9T1 M Q Z0 s z) {y : G}
    (hy : y ∈ Q) : ⁅z * s * z⁻¹, y⁆ ∈ conjSubgroup z (Vt M (LB M Q B) B Z t) := by
  rw [mem_conjSubgroup]
  have hq : z⁻¹ * y * z ∈ Q := by
    have := norm_Q hc (M.inv_mem hT.z_mem) hy
    simpa using this
  have hcomm : ⁅z⁻¹ * y * z, s⁆ ∈ (⁅Q, Subgroup.zpowers s⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers s)
  have e : z⁻¹ * ⁅z * s * z⁻¹, y⁆ * z = ⁅z⁻¹ * y * z, s⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, Vt_eq_comm_of_centre hCentre hs hZ0 hT]
  exact Subgroup.mem_sup_left ((⁅Q, Subgroup.zpowers s⁆ : Subgroup G).inv_mem hcomm)

theorem S_eq_of_le {hc : Ctx M Q Z B} {t : G} {B₁ B₂ : Subgroup G} (hc₁ : Ctx M Q Z B₁)
    (hc₂ : Ctx M Q Z B₂) (hle : B₁ ≤ Z ⊔ B₂) :
    (QB B₁ ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t =
      (QB B₂ ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  obtain ⟨p, hp, rfl⟩ := hc₂.exists_conj_of_le_ZB hc₁ hle
  rw [QB_conj]
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hc2Q : QB B₂ ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_right.trans inf_le_left
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy1, hy2⟩
    have hu : p⁻¹ * y * p ∈ QB B₂ := mem_conjSubgroup.mp hy1
    have huW : p⁻¹ * y * p ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have := conj_mem_Wt_of_mem_Q hc hVQ (Q.inv_mem hp) hy2
      simpa using this
    have hcz : ⁅p, p⁻¹ * y * p⁆ ∈ Z :=
      hc.hyp.toHyp79.comm_mem_V hp (huW.1)
    have e : y = ⁅p, p⁻¹ * y * p⁆ * (p⁻¹ * y * p) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ((QB B₂ ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t).mul_mem
      (Subgroup.mem_sup_right (hZV hcz)) (Subgroup.mem_sup_left ⟨hu, huW⟩)
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy1, hy2⟩
    have hcz : ⁅p, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hp hy2.1
    have hpy : p * y * p⁻¹ ∈ conjSubgroup p (QB B₂) ⊓ Wt Q (Vt M (LB M Q B) B Z t) :=
      ⟨conj_mem' p hy1, conj_mem_Wt_of_mem_Q hc hVQ hp hy2⟩
    have e : y = ⁅p, y⁆⁻¹ * (p * y * p⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ((conjSubgroup p (QB B₂) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_sup_right (hZV hcz)))
      (Subgroup.mem_sup_left hpy)

theorem conjSubgroup_eq_of_mem {S S' : Subgroup G} {x : G} (h₁ : ∀ y ∈ S, x * y * x⁻¹ ∈ S')
    (h₂ : ∀ y ∈ S', x⁻¹ * y * x ∈ S) : conjSubgroup x S = S' := by
  apply le_antisymm
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact h₁ u hu
  · intro y hy
    refine mem_conjSubgroup.mpr (h₂ y hy)

theorem conj_mem_Wt_of_normalizes (hc : Ctx M Q Z B) {t x y : G} (hxM : x ∈ M)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x⁻¹ * v * x ∈ Vt M (LB M Q B) B Z t)
    (hy : y ∈ Wt Q (Vt M (LB M Q B) B Z t)) : x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  refine ⟨norm_Q hc hxM hy.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hy.2 _ (hxV v hv)
  calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * y * x⁻¹) * v := by group

theorem conj_S_eq {hc : Ctx M Q Z B} {t r x : G} (hrM : r ∈ M) (hxM : x ∈ M)
    (hxV : conjSubgroup x (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t)
    (hsw₁ : conjSubgroup x B ≤ conjSubgroup r B ⊔ Z)
    (hsw₂ : conjSubgroup x (conjSubgroup r B) ≤ B ⊔ Z) :
    conjSubgroup x ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
        (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t ∧
      conjSubgroup x ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) =
        (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxV
  have hxV1 : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxVn v).mp hv
  have hxV2 : ∀ v ∈ Vt M (LB M Q B) B Z t, x⁻¹ * v * x ∈ Vt M (LB M Q B) B Z t := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxVn) v).mp hv
    simpa using this
  have hxW : conjSubgroup x (Wt Q (Vt M (LB M Q B) B Z t)) = Wt Q (Vt M (LB M Q B) B Z t) :=
    conjSubgroup_eq_of_mem (fun y hy => conj_mem_Wt_of_normalizes hc hxM hxV2 hy)
      (fun y hy => by
        have := conj_mem_Wt_of_normalizes (hc := hc) (t := t) (M.inv_mem hxM)
          (fun v hv => by simpa using hxV1 v hv) hy
        simpa using this)
  have hcx : Ctx M Q Z (conjSubgroup x B) := hc.conj_of_mem hxM
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hcxr : Ctx M Q Z (conjSubgroup x (conjSubgroup r B)) := by
    rw [← conjSubgroup_mul]
    exact hc.conj_of_mem (M.mul_mem hxM hrM)
  constructor
  · rw [conjSubgroup_sup', conjSubgroup_inf, ← QB_conj, hxW, hxV]
    exact S_eq_of_le (hc := hc) (t := t) hcx hcr (by rw [sup_comm]; exact hsw₁)
  · rw [conjSubgroup_sup', conjSubgroup_inf, ← QB_conj, hxW, hxV]
    exact S_eq_of_le (hc := hc) (t := t) hcxr hc (by rw [sup_comm]; exact hsw₂)

theorem count_core (hCentre : Step95CentreStatement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s z : G}
    (hT : Sec9T1 M Q Z0 s z) (hne : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∉ Z)
    (hsw₁ : conjSubgroup (z * s * z⁻¹) B ≤ conjSubgroup r B ⊔ Z)
    (hsw₂ : conjSubgroup (z * s * z⁻¹) (conjSubgroup r B) ≤ B ⊔ Z) : n ≤ 6 := by
  classical
  obtain ⟨hxM, hxH, hx2, hxVeq⟩ := x_facts hCentre hs hZ0 hT
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  obtain ⟨hSw1, hSw2⟩ := conj_S_eq (hc := hc) (t := t) hrM hxM hxVeq hsw₁ hsw₂
  have hcardV : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 5 := hs.card_V
  have hcardQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  have hdualG := hc.card_Wt_mul_card_Vt t
  obtain ⟨⟨hVSA, hSAW, hVSB, hSBW, hsup, hinf⟩, -⟩ := h91b G M Q Z B hc n t hs r hr
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl
  set x := z * s * z⁻¹ with hx
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  set SA := (QB (conjSubgroup r B) ⊓ W) ⊔ V with hSA
  set SB := (QB B ⊓ W) ⊔ V with hSB
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hWQ : W ≤ Q := inf_le_left
  have hZW : Z ≤ W := Z_le_Wt_of_le_Q hc hVQ
  have hxVn : x ∈ Subgroup.normalizer (V : Set G) := conjSubgroup_eq_self_iff.mp hxVeq
  have hxV1 : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxVn v).mp hv
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hxcentr : ∀ ζ ∈ Z, x * ζ * x⁻¹ = ζ := by
    intro ζ hζ
    have := Subgroup.mem_centralizer_iff.mp hxH.2 ζ hζ
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h.linear_of_centralizes hxM hxcentr
  have hreg := h.reg
  have hK : Nat.card K = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hTT : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨q, hq, rfl⟩ := M₀.π_surj e
    have hxq : x * q * x⁻¹ ∈ Q := norm_Q hc hxM hq
    rw [← hTπ q hq, ← hTπ _ hxq]
    have e2 : x * (x * q * x⁻¹) * x⁻¹ = x ^ 2 * q * (x ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev]
      group
    rw [e2]
    exact M₀.pi_conj_self hx2 hq
  have hnd : ∀ y : M₀.E, (∀ e, M₀.B e y = 0) → y = 0 := by
    intro y hy
    apply M₀.nondeg y
    intro f
    rw [M₀.B_comm y f, hy f, neg_zero]
  let V' : Submodule K M₀.E :=
    { carrier := (M₀.img V : Set M₀.E)
      add_mem' := fun {a b} ha hb => (M₀.img V).add_mem ha hb
      zero_mem' := (M₀.img V).zero_mem
      smul_mem' := fun c e he => hc.smul_mem_img_Vt h t c he }
  let W' : Submodule K M₀.E :=
    { carrier := {w | ∀ v ∈ V', M₀.B w v = 0}
      add_mem' := fun {a b} ha hb v hv => by
        rw [map_add, LinearMap.add_apply, ha v hv, hb v hv, add_zero]
      zero_mem' := fun v hv => by simp
      smul_mem' := fun c a ha v hv => by simp [ha v hv] }
  have hTV : ∀ v ∈ V', T v ∈ V' := by
    rintro v ⟨y, hyV, hyQ, rfl⟩
    show T (M₀.π y) ∈ M₀.img V
    rw [← hTπ y hyQ]
    exact M₀.pi_mem_img (hxV1 y hyV) (norm_Q hc hxM hyQ)
  have hnt : ∃ v ∈ V', T v ≠ v := by
    obtain ⟨v₀, hv₀, hv₀Z⟩ := hne
    refine ⟨M₀.π v₀, M₀.pi_mem_img hv₀ (hVQ hv₀), fun hTv => hv₀Z ?_⟩
    rw [← hTπ v₀ (hVQ hv₀)] at hTv
    have hxv : x * v₀ * x⁻¹ ∈ Q := norm_Q hc hxM (hVQ hv₀)
    have e : ⁅x, v₀⁆ = (x * v₀ * x⁻¹) * v₀⁻¹ := by
      simp only [commutatorElement_def, mul_assoc]
    have hcm : ⁅x, v₀⁆ ∈ Q := by
      rw [e]
      exact Q.mul_mem hxv (Q.inv_mem (hVQ hv₀))
    refine (M₀.π_ker _ hcm).mp ?_
    rw [e, M₀.π_mul _ hxv _ (Q.inv_mem (hVQ hv₀)), M₀.pi_inv (hVQ hv₀), hTv]
    exact add_neg_cancel _
  have hSAQ : SA ≤ Q := hSAW.trans hWQ
  have hSBQ : SB ≤ Q := hSBW.trans hWQ
  have hperp : ∀ y ∈ W, ∀ w ∈ V, M₀.B (M₀.π y) (M₀.π w) = 0 := by
    intro y hy w hw
    have hcomm : y * w = w * y := (Subgroup.mem_centralizer_iff.mp hy.2 w hw).symm
    exact (M₀.comm_iff_B hreg (hWQ hy) (hVQ hw)).mp hcomm
  have hAW : ∀ a ∈ M₀.img SA, a ∈ W' := by
    rintro a ⟨y, hySA, hyQ, rfl⟩ v ⟨w, hwV, hwQ, rfl⟩
    exact hperp y (hSAW hySA) w hwV
  have hBW : ∀ a ∈ M₀.img SB, a ∈ W' := by
    rintro a ⟨y, hySB, hyQ, rfl⟩ v ⟨w, hwV, hwQ, rfl⟩
    exact hperp y (hSBW hySB) w hwV
  have hSAnormB : SA ≤ Subgroup.normalizer (SB : Set G) := fun a ha =>
    mem_normalizer_of (fun b hb => by
      have e : a * b * a⁻¹ = ⁅a, b⁆ * b := by simp only [commutatorElement_def]; group
      rw [e]
      exact SB.mul_mem (hVSB (hZV (hc.hyp.toHyp79.comm_mem_V (hSAQ ha) (hSBQ hb)))) hb)
      (fun b hb => by
      have e : a⁻¹ * b * a = ⁅a⁻¹, b⁆ * b := by simp only [commutatorElement_def]; group
      rw [e]
      exact SB.mul_mem (hVSB (hZV (hc.hyp.toHyp79.comm_mem_V (Q.inv_mem (hSAQ ha))
        (hSBQ hb)))) hb)
  have hsum : ∀ w ∈ W', ∃ a ∈ M₀.img SA, ∃ b ∈ M₀.img SB, w = a + b := by
    intro w hw
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj w
    have hyW : y ∈ W := by
      refine ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have := hw (M₀.π v) (M₀.pi_mem_img hv (hVQ hv))
      exact ((M₀.comm_iff_B hreg hyQ (hVQ hv)).mpr this).symm
    rw [← hsup] at hyW
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hSAnormB hyW
    exact ⟨M₀.π a, M₀.pi_mem_img ha (hSAQ ha), M₀.π b, M₀.pi_mem_img hb (hSBQ hb),
      M₀.π_mul a (hSAQ ha) b (hSBQ hb)⟩
  have hinfE : ∀ e, e ∈ M₀.img SA → e ∈ M₀.img SB → e ∈ V' := by
    rintro e ⟨y₁, hy₁, hy₁Q, rfl⟩ ⟨y₂, hy₂, hy₂Q, h12⟩
    have hz : y₁⁻¹ * y₂ ∈ Z := (M₀.pi_eq_iff hy₁Q hy₂Q).mp h12.symm
    have hy₁B : y₁ ∈ SB := by
      have : y₁ = y₂ * (y₁⁻¹ * y₂)⁻¹ := by group
      rw [this]
      exact SB.mul_mem hy₂ (SB.inv_mem (hVSB (hZV hz)))
    have : y₁ ∈ V := by
      have hmem : y₁ ∈ SA ⊓ SB := ⟨hy₁, hy₁B⟩
      rwa [hinf] at hmem
    exact M₀.pi_mem_img this hy₁Q
  have hTA : ∀ a ∈ M₀.img SA, T a ∈ M₀.img SB := by
    rintro a ⟨y, hy, hyQ, rfl⟩
    rw [← hTπ y hyQ]
    refine M₀.pi_mem_img ?_ (norm_Q hc hxM hyQ)
    have := conj_mem' x hy
    rwa [hSw2] at this
  have hTB' : ∀ b ∈ M₀.img SB, T b ∈ M₀.img SA := by
    rintro a ⟨y, hy, hyQ, rfl⟩
    rw [← hTπ y hyQ]
    refine M₀.pi_mem_img ?_ (norm_Q hc hxM hyQ)
    have := conj_mem' x hy
    rwa [hSw1] at this
  have hWimg : ∀ w, w ∈ W' ↔ w ∈ M₀.img W := by
    intro w
    constructor
    · intro hw
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj w
      refine ⟨y, ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩, hyQ, rfl⟩
      have := hw (M₀.π v) (M₀.pi_mem_img hv (hVQ hv))
      exact ((M₀.comm_iff_B hreg hyQ (hVQ hv)).mpr this).symm
    · rintro ⟨y, hyW, hyQ, rfl⟩ v ⟨w, hwV, hwQ, rfl⟩
      exact hperp y hyW w hwV
  have hcardW' : Nat.card W' = Nat.card (M₀.img W) :=
    Nat.card_congr (Equiv.subtypeEquivRight hWimg)
  have hcardV' : Nat.card V' = Nat.card (M₀.img V) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have himgQ : M₀.img Q = ⊤ := by
    ext e
    simp only [AddSubgroup.mem_top, iff_true]
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
    exact M₀.pi_mem_img hy hy
  have hcQ := M₀.card_eq (S := Q) le_rfl hZQ
  have hcV := M₀.card_eq (S := V) hVQ hZV
  have hcW := M₀.card_eq (S := W) hWQ hZW
  rw [himgQ, AddSubgroup.card_top] at hcQ
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hdual : Nat.card W' * Nat.card V' = Nat.card M₀.E := by
    rw [hcardW', hcardV']
    have h1 := hdualG
    rw [hcW, hcV, hcQ] at h1
    have h2 : Nat.card Z * Nat.card Z * (Nat.card (M₀.img W) * Nat.card (M₀.img V)) =
        Nat.card Z * Nat.card Z * Nat.card M₀.E := by
      calc Nat.card Z * Nat.card Z * (Nat.card (M₀.img W) * Nat.card (M₀.img V))
          = Nat.card Z * Nat.card (M₀.img W) * (Nat.card Z * Nat.card (M₀.img V)) := by ring
        _ = Nat.card Z * Nat.card M₀.E * Nat.card Z := h1
        _ = Nat.card Z * Nat.card Z * Nat.card M₀.E := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hqpos hqpos) h2
  have habs := card_range_sub_id_sq_ge M₀.B hnd T.toLinearMap hTB hTT V' W'
    (fun w => Iff.rfl) hTV hnt (M₀.img SA) (M₀.img SB) (fun v hv => M₀.img_mono hVSA hv)
    (fun v hv => M₀.img_mono hVSB hv) hAW hBW hsum hinfE hTA hTB' hdual
  have hzV : conjSubgroup z V ≤ Q := by
    intro y hy
    have hy' : z⁻¹ * y * z ∈ V := mem_conjSubgroup.mp hy
    have := norm_Q hc hT.z_mem (hVQ hy')
    simpa [mul_assoc] using this
  have hZzV : Z ≤ conjSubgroup z V := by
    intro ζ hζ
    rw [mem_conjSubgroup]
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hT.z_mem)) ζ).mp hζ
    exact hZV (by simpa using this)
  have hcZ := M₀.card_eq (S := conjSubgroup z V) hzV hZzV
  have hcardzV : Nat.card (conjSubgroup z V) = Nat.card V := card_conjSubgroup z V
  have hrange : ∀ e ∈ LinearMap.range (T.toLinearMap - LinearMap.id),
      e ∈ M₀.img (conjSubgroup z V) := by
    rintro _ ⟨e₀, rfl⟩
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e₀
    have hxy : x * y * x⁻¹ ∈ Q := norm_Q hc hxM hyQ
    have hcm : ⁅x, y⁆ ∈ conjSubgroup z V := comm_mem_conj_Vt_of_mem_Q hCentre hs hZ0 hT hyQ
    have hcmQ : ⁅x, y⁆ ∈ Q := hzV hcm
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp only [commutatorElement_def, mul_assoc]
    have hπ : M₀.π ⁅x, y⁆ = T (M₀.π y) - M₀.π y := by
      rw [e, M₀.π_mul _ hxy _ (Q.inv_mem hyQ), M₀.pi_inv hyQ, ← hTπ y hyQ, sub_eq_add_neg]
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, ← hπ]
    exact M₀.pi_mem_img hcm hcmQ
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hcardR : Nat.card (LinearMap.range (T.toLinearMap - LinearMap.id)) ≤
      Nat.card (M₀.img (conjSubgroup z V)) := by
    refine Nat.card_le_card_of_injective
      (fun e : LinearMap.range (T.toLinearMap - LinearMap.id) =>
        (⟨e.1, hrange e.1 e.2⟩ : M₀.img (conjSubgroup z V))) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext h
  set q := Nat.card Z with hq
  have hqpos : 0 < q := Nat.card_pos
  have hEq : Nat.card M₀.E = q ^ (2 * n) := by
    have h1 : q * Nat.card M₀.E = q * q ^ (2 * n) := by
      rw [← hcQ, hcardQ, pow_succ']
    exact Nat.eq_of_mul_eq_mul_left hqpos h1
  have hVq : Nat.card (M₀.img V) = q ^ 4 := by
    have h1 : q * Nat.card (M₀.img V) = q * q ^ 4 := by
      rw [← hcV, hcardV, ← pow_succ']
    exact Nat.eq_of_mul_eq_mul_left hqpos h1
  have hzVq : Nat.card (M₀.img (conjSubgroup z V)) = q ^ 4 := by
    have h1 : q * Nat.card (M₀.img (conjSubgroup z V)) = q * q ^ 4 := by
      rw [← hcZ, hcardzV, hcardV, ← pow_succ']
    exact Nat.eq_of_mul_eq_mul_left hqpos h1
  have hRle : Nat.card (LinearMap.range (T.toLinearMap - LinearMap.id)) ≤ q ^ 4 :=
    hzVq ▸ hcardR
  rw [hK, hEq, hcardV'] at habs
  rw [hVq] at habs
  have h2 : q ^ 4 * q ^ (2 * n) ≤ (q ^ 4 * q ^ 4) ^ 2 :=
    habs.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hRle) 2)
  have h3 : q ^ (4 + 2 * n) ≤ q ^ 16 := by
    calc q ^ (4 + 2 * n) = q ^ 4 * q ^ (2 * n) := pow_add _ _ _
      _ ≤ (q ^ 4 * q ^ 4) ^ 2 := h2
      _ = q ^ 16 := by ring
  have h4 : 4 + 2 * n ≤ 16 := (Nat.pow_le_pow_iff_right (by omega)).mp h3
  omega

end HS93

end CFSG.RankThree.GF2n.Stroth80
