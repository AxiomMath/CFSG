module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec7Adm (hc : Ctx M Q Z B) (t y : G) : Prop where
  mem : y ∈ M
  comm_t : ⁅y, t⁆ ∈ Q
  vanish : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z
  wv : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t

theorem conj_centre_normalizes {Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) {y : G}
    (hy : ∀ z ∈ Z0, ⁅z, y⁆ ∈ Q) : y ∈ Subgroup.normalizer (Z0 : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun h hh => ?_
  have hh' : h ∈ Z0 := hh
  have e1 : y * h * y⁻¹ = ⁅h, y⁆⁻¹ * h := by
    rw [← commutatorElement_inv y h, commutatorElement_def]
    group
  show y * h * y⁻¹ ∈ Z0
  rw [e1]
  exact Z0.mul_mem (Z0.inv_mem (hQZ0 (hy h hh'))) hh'

theorem conjSubgroup_mem_H0 (hc : Ctx M Q Z B) {Z0 : Subgroup G} (hZ0H : Z0 ≤ H0 M Z) {g : G}
    (hg : g ∈ M) {y : G} (hy : y ∈ conjSubgroup g Z0) : y ∈ H0 M Z := by
  have h := hc.conj_mem_H0 hg (hZ0H (mem_conjSubgroup.mp hy))
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rwa [e] at h

theorem sec7Adm_of_conj (hSV : Sec7SVStatement) (hSW : Sec7SWStatement)
    (hV : Step71VanishStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hcl : Close71Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) {y : G} (hy : y ∈ conjSubgroup g Z0) :
    Sec7Adm hc t y := by
  have hs : Sec7Hyp hc n t := hcl.1
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hcomm : ∀ y' ∈ conjSubgroup g Z0, ⁅y', t⁆ ∈ Q := by
    intro y' hy'
    have := Q.inv_mem (hΓ t htZ0 y' hy')
    rwa [commutatorElement_inv] at this
  have hyM : ∀ y' ∈ conjSubgroup g Z0, y' ∈ M := by
    intro y' hy'
    have hz := hZ0M (mem_conjSubgroup.mp hy')
    have := M.mul_mem (M.mul_mem hg hz) (M.inv_mem hg)
    simpa [mul_assoc] using this
  have hxmem : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using htZ0
  have hxM : g * t * g⁻¹ ∈ M := hyM _ hxmem
  have hx : ConjMod M Q t (g * t * g⁻¹) := ⟨hxM, g, hg, by simpa using Q.one_mem⟩
  have hxt : ⁅g * t * g⁻¹, t⁆ ∈ Q := hcomm _ hxmem
  exact ⟨hyM y hy, hcomm y hy,
    hSV G M Q Z B hc n t hs Z0 hZ0 g hg (hV G M Q Z B hc n t hs hcl.2.1 _ hx hxt) y hy,
    hSW G M Q Z B hc n t hs Z0 hZ0 g hg (hcl.2.2 _ hx hxt) y hy⟩

theorem comm_mem_CN_of_adm (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {y : G}
    (hy : Sec7Adm hc t y) {r : G} (hr : r ∈ Rt M (LB M Q B) t) : ⁅r, y⁆ ∈ hc.CN t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hyN : y ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hy.mem hy.comm_t)
  have hrV : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hr
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  refine Ctx.mem_CN.mpr ⟨?_, fun v hv => ?_⟩
  · have h1 : y * r⁻¹ * y⁻¹ ∈ Rt M (LB M Q B) t :=
      (Subgroup.mem_normalizer_iff.mp hyN r⁻¹).mp ((Rt M (LB M Q B) t).inv_mem hr)
    have e : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hr h1
  · have hv' : r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrV) v).mp hv
      simpa using this
    have h1 : ⁅r * y * r⁻¹, v⁆ ∈ Z := by
      have e : ⁅r * y * r⁻¹, v⁆ = r * ⁅y, r⁻¹ * v * r⁆ * r⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hZn r hrM _ (hy.vanish _ hv')
    have h2 : ⁅y⁻¹, v⁆ ∈ Z := by
      have e : ⁅y⁻¹, v⁆ = y⁻¹ * ⁅y, v⁆⁻¹ * y := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := hZn y⁻¹ (M.inv_mem hy.mem) _ (Z.inv_mem (hy.vanish v hv))
      simpa using this
    have h3 : ⁅(r * y * r⁻¹) * y⁻¹, v⁆ = (r * y * r⁻¹) * ⁅y⁻¹, v⁆ * (r * y * r⁻¹)⁻¹ *
        ⁅r * y * r⁻¹, v⁆ := by
      simp only [commutatorElement_def]; group
    have hM' : r * y * r⁻¹ ∈ M := M.mul_mem (M.mul_mem hrM hy.mem) (M.inv_mem hrM)
    have e2 : ⁅r, y⁆ = (r * y * r⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e2, h3]
    exact Z.mul_mem (hZn _ hM' _ h2) h1

theorem commutator_adm_comm_R (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hcomm : ∀ y : G, Sec7Adm hc t y → ∀ k ∈ hc.CN t, ⁅k, y⁆ ∈ Z0) {y₁ y₂ : G}
    (h₁ : Sec7Adm hc t y₁) (h₁' : Sec7Adm hc t y₁⁻¹) (h₂ : Sec7Adm hc t y₂)
    (h₂' : Sec7Adm hc t y₂⁻¹) (hn₁ : y₁ ∈ Subgroup.normalizer (Z0 : Set G))
    (hn₂ : y₂ ∈ Subgroup.normalizer (Z0 : Set G)) :
    ∀ r ∈ Rt M (LB M Q B) t, ⁅⁅y₁, y₂⁆, r⁆ ∈ Z0 := by
  intro r hr
  have hnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hrn : r ∈ Subgroup.normalizer (Z0 : Set G) := hZ0.mem_normalizer hnorm hr
  have key := three_subgroup_mod Z0 y₂ y₁⁻¹ r
    (fun n hn => (Subgroup.mem_normalizer_iff.mp hn₂ n).mp hn)
    (fun n hn => by
      have := (Subgroup.mem_normalizer_iff.mp hn₁ n).mp hn
      simpa using this)
    (fun n hn => (Subgroup.mem_normalizer_iff.mp hrn n).mp hn)
    (by
      have e : ⁅y₁⁻¹, r⁻¹⁆⁻¹ = ⁅r⁻¹, y₁⁻¹⁆ := commutatorElement_inv _ _
      rw [e]
      exact hcomm y₂ h₂ _ (comm_mem_CN_of_adm hc hs h₁' ((Rt M (LB M Q B) t).inv_mem hr)))
    (by
      have hmem := comm_mem_CN_of_adm hc hs h₂' hr
      exact hcomm y₁⁻¹ h₁' _ ((hc.CN t).inv_mem hmem))
  have e : ⁅y₂, y₁⁻¹⁻¹⁆⁻¹ = ⁅y₁, y₂⁆ := by
    rw [inv_inv]
    exact commutatorElement_inv _ _
  rwa [e] at key

theorem commutator_R_comm_of_comm (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {w : G} (hwM : w ∈ M)
    (hw : ∀ r ∈ Rt M (LB M Q B) t, ⁅w, r⁆ ∈ Z0) :
    ∀ a ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆, ⁅w, a⁆ ∈ Q := by
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hQM (hRM hρ)) y).mp hy
  have hwn : w ∈ Subgroup.normalizer (Z0 : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hz' : z ∈ Z0 := hz
    have e : w * z * w⁻¹ = ⁅w, z⁆ * z := by rw [commutatorElement_def]; group
    show w * z * w⁻¹ ∈ Z0
    rw [e]
    exact Z0.mul_mem (hw z (hZ0.le hz')) hz'
  have hw' : ∀ r ∈ Rt M (LB M Q B) t, ⁅w⁻¹, r⁆ ∈ Z0 := by
    intro r hr
    have e : ⁅w⁻¹, r⁆ = w⁻¹ * ⁅w, r⁆⁻¹ * w := by simp only [commutatorElement_def]; group
    rw [e]
    have hn' : w⁻¹ ∈ Subgroup.normalizer (Z0 : Set G) := Subgroup.inv_mem _ hwn
    have := (Subgroup.mem_normalizer_iff.mp hn' _).mp (Z0.inv_mem (hw r hr))
    simpa using this
  have hle : ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤ CommQ hQM w := by
    rw [Subgroup.commutator_le]
    intro r₁ hr₁ r₂ hr₂
    refine mem_CommQ.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem (hRM hr₁) (hRM hr₂)) (M.inv_mem (hRM hr₁)))
        (M.inv_mem (hRM hr₂))
    · have key := three_subgroup_mod Q r₂ r₁⁻¹ w
        (fun n hn => hnorm r₂ hr₂ n hn)
        (fun n hn => by
          have := hnorm r₁ hr₁ n hn
          simpa using this)
        (fun n hn => (Subgroup.mem_normalizer_iff.mp (hQM hwM) n).mp hn)
        (by
          have e : ⁅r₁⁻¹, w⁻¹⁆⁻¹ = ⁅w⁻¹, r₁⁻¹⁆ := commutatorElement_inv _ _
          rw [e]
          exact hZ0.comm_mem (hw' _ ((Rt M (LB M Q B) t).inv_mem hr₁)) hr₂)
        (by
          have hmem := hw _ ((Rt M (LB M Q B) t).inv_mem hr₂)
          have := hZ0.comm_mem (Z0.inv_mem hmem) ((Rt M (LB M Q B) t).inv_mem hr₁)
          simpa using this)
      have e : ⁅r₂, r₁⁻¹⁻¹⁆⁻¹ = ⁅r₁, r₂⁆ := by
        rw [inv_inv]
        exact commutatorElement_inv _ _
      rwa [e] at key
  intro a ha
  have h1 := (mem_CommQ.mp (hle ha)).2
  have := Q.inv_mem h1
  rwa [commutatorElement_inv] at this

theorem Sec7Adm.conj_Wt (hc : Ctx M Q Z B) {t y : G} (hy : Sec7Adm hc t y) :
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), y * w * y⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), y⁻¹ * w * y ∈ Wt Q (Vt M (LB M Q B) B Z t)) := by
  have hyVn : y ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hy.mem hy.comm_t)
  have hyQn : y ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hy.mem
  refine ⟨fun w hw => conj_mem_Wt hyQn hyVn hw, fun w hw => ?_⟩
  have := conj_mem_Wt (Subgroup.inv_mem _ hyQn) (Subgroup.inv_mem _ hyVn) hw
  simpa using this

theorem close71E_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hK : Sec7CRWStatement)
    (hSch : Sec7SchurStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hV : Step71VanishStatement) : Close71EStatement := by
  intro G _ _ M Q Z B hc n t hcl Z0 hZ0
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hs : Sec7Hyp hc n t := hcl.1
  have hSV := sec7SV_of_parts h34 h310chi hZc hZV
  have hSW := sec7SW_of_parts h34 h310chi hZc hZV
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  have hZ0H : Z0 ≤ H0 M Z := fun z hz => hc.Rt_le_H0 t (hZ0.le hz)
  have hQn : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hcomm : ∀ y : G, Sec7Adm hc t y → ∀ k ∈ hc.CN t, ⁅k, y⁆ ∈ Z0 := fun y hy k hk =>
    comm_N_of_vanish h34 h310chi hK h52a hA hc hs hZ0 hy.mem hy.comm_t hy.vanish hy.wv k hk
  refine commutator_Egen_le hQZ0 ?_
  intro g₁ hg₁ hΓ₁ g₂ hg₂ hΓ₂ y₁ hy₁ y₂ hy₂
  have hadm : ∀ {g : G}, g ∈ M → (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y ∈ conjSubgroup g Z0, Sec7Adm hc t y := fun hg hΓ y hy =>
    sec7Adm_of_conj hSV hSW hV hc hcl hZ0 hg hΓ hy
  have hnz : ∀ {g : G}, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y ∈ conjSubgroup g Z0, y ∈ Subgroup.normalizer (Z0 : Set G) := fun hΓ y hy =>
    conj_centre_normalizes hQZ0 (fun z hz => hΓ z hz y hy)
  have hy₁' : y₁⁻¹ ∈ conjSubgroup g₁ Z0 := (conjSubgroup g₁ Z0).inv_mem hy₁
  have hy₂' : y₂⁻¹ ∈ conjSubgroup g₂ Z0 := (conjSubgroup g₂ Z0).inv_mem hy₂
  have h₁ := hadm hg₁ hΓ₁ y₁ hy₁
  have h₁' := hadm hg₁ hΓ₁ _ hy₁'
  have h₂ := hadm hg₂ hΓ₂ y₂ hy₂
  have h₂' := hadm hg₂ hΓ₂ _ hy₂'
  have hw3 := commutator_adm_comm_R hc hs hZ0 hcomm h₁ h₁' h₂ h₂' (hnz hΓ₁ y₁ hy₁)
    (hnz hΓ₂ y₂ hy₂)
  have hwM : ⁅y₁, y₂⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem h₁.mem h₂.mem) (M.inv_mem h₁.mem)) (M.inv_mem h₂.mem)
  have hwH : ⁅y₁, y₂⁆ ∈ H0 M Z := by
    have h1 := conjSubgroup_mem_H0 hc hZ0H hg₁ hy₁
    have h2 := conjSubgroup_mem_H0 hc hZ0H hg₂ hy₂
    rw [commutatorElement_def]
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).mul_mem h1 h2) ((H0 M Z).inv_mem h1))
      ((H0 M Z).inv_mem h2)
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  have hVW := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  obtain ⟨hy₁W, hy₁W'⟩ := h₁.conj_Wt hc
  obtain ⟨hy₂W, hy₂W'⟩ := h₂.conj_Wt hc
  refine hSch G M Q Z B hc n t hs Z0 hZ0 _ hwH
    (commutator_R_comm_of_comm hc hs hZ0 hwM hw3) ?_
  exact commutator_comm_mem_Z hQn hS.conj sec39_Z_le_Vt hVW hWQ h₁.mem h₂.mem hy₁W hy₁W'
    hy₂W hy₂W' h₁.vanish h₂.vanish h₁.wv h₂.wv

end CFSG.RankThree.GF2n.Stroth80
