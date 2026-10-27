module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommPerp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step76EightKStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
    ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g₂ * t * g₂⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ a ∈ Ut Q Z (g₁ * t * g₁⁻¹), ∀ b ∈ Ut Q Z (g₂ * t * g₂⁻¹), ⁅a, b⁆ = 1

@[expose] def Step76EightKTameWildStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g₁ * t * g₁⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g₂ * t * g₂⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ a ∈ Ut Q Z (g₁ * t * g₁⁻¹), ∀ b ∈ Ut Q Z (g₂ * t * g₂⁻¹), ⁅a, b⁆ = 1

@[expose] def Step76EightKWildWildStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g₁ * t * g₁⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g₂ * t * g₂⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ a ∈ Ut Q Z (g₁ * t * g₁⁻¹), ∀ b ∈ Ut Q Z (g₂ * t * g₂⁻¹), ⁅a, b⁆ = 1

@[expose] def Step76EightTameConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    ∃ r ∈ Rt M (LB M Q B) t, ∃ f ∈ LB M Q B, ConjMod M Q t f ∧
      Ut Q Z (g * t * g⁻¹) = conjSubgroup r (Ut Q Z f)

@[expose] def Step76EightKTameStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ f ∈ LB M Q B, ConjMod M Q t f →
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ a ∈ Ut Q Z f, ∀ b ∈ Ut Q Z (g * t * g⁻¹), ⁅a, b⁆ = 1

section Reduction

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step76EightKTameWild_of (hT : Step76EightTameConjStatement)
    (hK : Step76EightKTameStatement) : Step76EightKTameWildStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ htame g₂ hg₂ hΓ₂ hwild a ha b hb
  obtain ⟨r, hr, f, hfL, hfc, hUt⟩ := hT G M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ htame
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hrM' : r⁻¹ ∈ M := M.inv_mem hrM
  have hnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hrZ0 : r ∈ Subgroup.normalizer (Z0 : Set G) := hZ0.mem_normalizer hnorm hr
  have hrQ : ∀ y ∈ Q, r⁻¹ * y * r ∈ Q := fun y hy => by
    have := (hc.conj_mem_Q_of_mem_M hrM).2 y hy
    exact this
  have hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup (r⁻¹ * g₂) Z0, ⁅z, y⁆ ∈ Q := by
    intro z hz y hy
    have hy' : (r⁻¹ * g₂)⁻¹ * y * (r⁻¹ * g₂) ∈ Z0 := mem_conjSubgroup.mp hy
    have hy'' : g₂⁻¹ * (r * y * r⁻¹) * g₂ ∈ Z0 := by
      have e : g₂⁻¹ * (r * y * r⁻¹) * g₂ = (r⁻¹ * g₂)⁻¹ * y * (r⁻¹ * g₂) := by group
      rw [e]
      exact hy'
    have hy₂ : r * y * r⁻¹ ∈ conjSubgroup g₂ Z0 := mem_conjSubgroup.mpr hy''
    have hz' : r * z * r⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hrZ0 z).mp hz
    have h1 := hΓ₂ _ hz' _ hy₂
    have e : ⁅z, y⁆ = r⁻¹ * ⁅r * z * r⁻¹, r * y * r⁻¹⁆ * r := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hrQ _ h1
  have hW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun w hw => conj_mem_Wt (hc.hyp.Q_normal.2 hrM) (hc.Rt_normalizes_Vt ht hr) hw
  have hV : ∀ v ∈ Vt M (LB M Q B) B Z t, r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hc.Rt_normalizes_Vt ht hr)) v).mp
      hv
    simpa using this
  have hVr : ∀ v ∈ Vt M (LB M Q B) B Z t, r * v * r⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) v).mp hv
  have hwild' : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅(r⁻¹ * g₂) * t * (r⁻¹ * g₂)⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t := by
    obtain ⟨w₂, hw₂, hw₂V⟩ := hwild
    refine ⟨r⁻¹ * w₂ * r, ?_, fun hmem => hw₂V ?_⟩
    · have := conj_mem_Wt (hc.hyp.Q_normal.2 hrM') (hc.Rt_normalizes_Vt ht
        ((Rt M (LB M Q B) t).inv_mem hr)) hw₂
      simpa using this
    · have e : ⁅(r⁻¹ * g₂) * t * (r⁻¹ * g₂)⁻¹, r⁻¹ * w₂ * r⁆ =
          r⁻¹ * ⁅g₂ * t * g₂⁻¹, w₂⁆ * r := by
        simp only [commutatorElement_def]
        group
      rw [e] at hmem
      have := hVr _ hmem
      simpa [mul_assoc] using this
  have hUt' : Ut Q Z ((r⁻¹ * g₂) * t * (r⁻¹ * g₂)⁻¹) =
      conjSubgroup r⁻¹ (Ut Q Z (g₂ * t * g₂⁻¹)) := by
    rw [show (r⁻¹ * g₂) * t * (r⁻¹ * g₂)⁻¹ = r⁻¹ * (g₂ * t * g₂⁻¹) * r⁻¹⁻¹ by group]
    exact Ut_conj_of_normalizes (hc.conj_Q_eq hrM') (hc.conj_Z_eq hrM') _
  rw [hUt] at ha
  have ha' : r⁻¹ * a * r ∈ Ut Q Z f := mem_conjSubgroup.mp ha
  have hb' : r⁻¹ * b * r ∈ Ut Q Z ((r⁻¹ * g₂) * t * (r⁻¹ * g₂)⁻¹) := by
    rw [hUt']
    refine mem_conjSubgroup.mpr ?_
    rw [inv_inv, show r * (r⁻¹ * b * r) * r⁻¹ = b by group]
    exact hb
  have key := hK G M Q Z B hc n t hs hno h4 Z0 hZ0 f hfL hfc (r⁻¹ * g₂) (M.mul_mem hrM' hg₂) hΓ
    hwild' _ ha' _ hb'
  have e : ⁅a, b⁆ = r * ⁅r⁻¹ * a * r, r⁻¹ * b * r⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, key]
  group

end Reduction

theorem step76EightK_of_parts (h1 : Step76EightKTameWildStatement)
    (h2 : Step76EightKWildWildStatement) : Step76EightKStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ g₂ hg₂ hΓ₂ hw₂ a ha b hb
  by_cases hw₁ : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅g₁ * t * g₁⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t
  · exact h2 G M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ hw₁ g₂ hg₂ hΓ₂ hw₂ a ha b hb
  · push Not at hw₁
    exact h1 G M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ hw₁ g₂ hg₂ hΓ₂ hw₂ a ha b hb

section Assembly

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7Adm_of_conj_tame (hSV : Sec7SVStatement) (hSW : Sec7SWStatement)
    (hV : Step71VanishStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hno : ¬ Conc71abcd hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q)
    (htame : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t)
    {y : G} (hy : y ∈ conjSubgroup g Z0) : Sec7Adm hc t y := by
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
    hSV G M Q Z B hc n t hs Z0 hZ0 g hg (hV G M Q Z B hc n t hs hno _ hx hxt) y hy,
    hSW G M Q Z B hc n t hs Z0 hZ0 g hg htame y hy⟩

theorem Ut_le_Ut_conj_of_mem_conj_centre (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ M) {y : G}
    (hy : y ∈ conjSubgroup g Z0) : Ut Q Z y ≤ Ut Q Z (g * t * g⁻¹) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htQ : t ∉ Q := hs.toSec5.notQ
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Z0, y = g * z * g⁻¹ :=
    ⟨g⁻¹ * y * g, mem_conjSubgroup.mp hy, by group⟩
  rw [Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) z,
    Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) t]
  refine Subgroup.map_mono ?_
  by_cases hzQ : z ∈ Q
  · refine sup_le ?_ le_sup_right
    refine le_trans ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbQ : b ∈ Q := (Subgroup.zpowers_le.mpr hzQ) hb
    exact hc.hyp.toHyp79.comm_mem_V ha hbQ
  · exact (hZV G M Q Z B hc n t hs Z0 hZ0 z hz hzQ).trans_le (le_of_eq
      (hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 htQ).symm)

theorem sq_mem_Q_and_H0_of_mem_conj_centre (hZc : Sec7CentreMpStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ M) {y : G}
    (hy : y ∈ conjSubgroup g Z0) : y ^ 2 ∈ Q ∧ y ∈ H0 M Z := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Z0, y = g * z * g⁻¹ :=
    ⟨g⁻¹ * y * g, mem_conjSubgroup.mp hy, by group⟩
  have hzL : z ∈ LB M Q B := (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hZ0H : Z0 ≤ H0 M Z := fun z hz => hc.Rt_le_H0 t (hZ0.le hz)
  refine ⟨?_, conjSubgroup_mem_H0 hc hZ0H hg hy⟩
  rw [conj_pow]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) (z ^ 2)).mp
    (hc.sq_mem_Q_of_mem_LB hzL)

theorem step76Eight_of_K (hKst : Step76EightKStatement) (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hCRW : Sec7CRWStatement) (hSch : Sec7SchurStatement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) (hV : Step71VanishStatement) :
    Step76EEightStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hSV := sec7SV_of_parts h34 h310chi hZc hZV
  have hSW := sec7SW_of_parts h34 h310chi hZc hZV
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  have hZ0H : Z0 ≤ H0 M Z := fun z hz => hc.Rt_le_H0 t (hZ0.le hz)
  have hQn : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hcomm : ∀ y : G, Sec7Adm hc t y → ∀ k ∈ hc.CN t, ⁅k, y⁆ ∈ Z0 := fun y hy k hk =>
    comm_N_of_vanish h34 h310chi hCRW h52a hA hc hs hZ0 hy.mem hy.comm_t hy.vanish hy.wv k hk
  have hwild : ∀ {ga gb : G}, ga ∈ M → (∀ z ∈ Z0, ∀ y ∈ conjSubgroup ga Z0, ⁅z, y⁆ ∈ Q) →
      gb ∈ M → (∀ z ∈ Z0, ∀ y ∈ conjSubgroup gb Z0, ⁅z, y⁆ ∈ Q) →
      (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅gb * t * gb⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
      ∀ {ya yb : G}, ya ∈ conjSubgroup ga Z0 → yb ∈ conjSubgroup gb Z0 → ⁅ya, yb⁆ ∈ Q := by
    intro ga gb hga hΓa hgb hΓb hw ya yb hya hyb
    obtain ⟨hya2, hyaH⟩ := sq_mem_Q_and_H0_of_mem_conj_centre hZc hc hs hZ0 hga hya
    obtain ⟨hyb2, hybH⟩ := sq_mem_Q_and_H0_of_mem_conj_centre hZc hc hs hZ0 hgb hyb
    refine sec7_comm_mem_Q_of_perp h34 h310chi hZc hZV hZcard hc hs hZ0 hyaH hybH hya2 hyb2 ?_
    intro a ha b hb
    exact hKst G M Q Z B hc n t hs hno h4 Z0 hZ0 ga hga hΓa gb hgb hΓb hw a
      (Ut_le_Ut_conj_of_mem_conj_centre hZV hc hs hZ0 hga hya ha) b
      (Ut_le_Ut_conj_of_mem_conj_centre hZV hc hs hZ0 hgb hyb hb)
  refine commutator_Egen_le hQZ0 ?_
  intro g₁ hg₁ hΓ₁ g₂ hg₂ hΓ₂ y₁ hy₁ y₂ hy₂
  by_cases hw₂ : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅g₂ * t * g₂⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t
  · exact hQZ0 (hwild hg₁ hΓ₁ hg₂ hΓ₂ hw₂ hy₁ hy₂)
  by_cases hw₁ : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅g₁ * t * g₁⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t
  · have h := hwild hg₂ hΓ₂ hg₁ hΓ₁ hw₁ hy₂ hy₁
    rw [← commutatorElement_inv] at h
    exact hQZ0 (by simpa using Q.inv_mem h)
  push Not at hw₁ hw₂
  have hadm : ∀ {g : G}, g ∈ M → (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∀ y ∈ conjSubgroup g Z0, Sec7Adm hc t y := fun hg hΓ htame y hy =>
    sec7Adm_of_conj_tame hSV hSW hV hc hs hno hZ0 hg hΓ htame hy
  have hnz : ∀ {g : G}, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y ∈ conjSubgroup g Z0, y ∈ Subgroup.normalizer (Z0 : Set G) := fun hΓ y hy =>
    conj_centre_normalizes hQZ0 (fun z hz => hΓ z hz y hy)
  have hy₁' : y₁⁻¹ ∈ conjSubgroup g₁ Z0 := (conjSubgroup g₁ Z0).inv_mem hy₁
  have hy₂' : y₂⁻¹ ∈ conjSubgroup g₂ Z0 := (conjSubgroup g₂ Z0).inv_mem hy₂
  have h₁ := hadm hg₁ hΓ₁ hw₁ y₁ hy₁
  have h₁' := hadm hg₁ hΓ₁ hw₁ _ hy₁'
  have h₂ := hadm hg₂ hΓ₂ hw₂ y₂ hy₂
  have h₂' := hadm hg₂ hΓ₂ hw₂ _ hy₂'
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

end Assembly

end CFSG.RankThree.GF2n.Stroth80
