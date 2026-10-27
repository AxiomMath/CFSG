module

public import CFSG.RankThree.GF2n.Stroth80.Sec91
public import CFSG.RankThree.GF2n.Stroth80.Sec9Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_Rt_ne_LB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) : Rt M (LB M Q B) t ≠ LB M Q B := by
  intro hRL
  have hs5 := hs.toSec5
  have hp : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
  obtain ⟨K, fK, finK, hK, φ, hφr, -, -⟩ := hs.plus4
  have hpR : IsPGroup 2 ↥(Rt M (LB M Q B) t) := by rw [hRL]; exact hp
  have hpr : IsPGroup 2 ↥φ.range :=
    IsPGroup.of_surjective hpR φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  rw [hφr] at hpr
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  exact sec9_not_isPGroup_omegaPlusFour h4 hpr

theorem sec9_N51 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hNC : Sec9NCommStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t)
    (hr : Sec7A hc t r) :
    (∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b) ∧
    (∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B), ⁅s, x⁆ ∈ Q) ∧
    ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]; exact le_sup_right
  have hgen : Rt M (LB M Q B) t = hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup r B) := by
    refine le_antisymm ?_ (sup_le (sup_le (sec9_CN_le_Rt hc t) hLR) hL'R)
    calc Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B) := hr.gen
      _ ≤ hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup r B) :=
        sup_le_sup_right le_sup_right _
  exact hc.sec51_core h35 hs5.mem hr.mem
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
    (hNC G M Q Z B hc n t hs) hgen

theorem sec9_conj_Wt_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) :
    conjSubgroup ρ (Wt Q (Vt M (LB M Q B) B Z t)) = Wt Q (Vt M (LB M Q B) B Z t) := by
  rw [conjSubgroup_eq_self_iff]
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => sec9_conj_mem_Wt hc ht hρ hw,
    fun hw => ?_⟩
  have h1 := sec9_conj_mem_Wt hc ht ((Rt M (LB M Q B) t).inv_mem hρ) hw
  have e : ρ⁻¹ * (ρ * w * ρ⁻¹) * ρ⁻¹⁻¹ = w := by group
  rw [e] at h1
  exact h1

theorem sec9_conj_Vt_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) :
    conjSubgroup ρ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
  conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hρ)

theorem sec9_numerics (h34 : Stroth34Statement) (h1 : Step91OrderQBStatement)
    (h2 : Step91OrderVQBStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n ∧
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))) =
      Nat.card Z ^ 4 := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have h35' := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have h35 := h35'.2.1
  have hQQB : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := h35'.2.2.2
  set V := Vt M (LB M Q B) B Z t with hVd
  set W := Wt Q V with hWd
  have hWQ : W ≤ Q := inf_le_left
  have hVW : V ≤ W := fun v hv => ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hQBW : Q ⊓ QB B ⊓ W = QB B ⊓ W := by
    ext x
    constructor
    · rintro ⟨⟨_, hx⟩, hxW⟩
      exact ⟨hx, hxW⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨hWQ hxW, hx⟩, hxW⟩
  refine ⟨?_, ?_⟩
  · have e := h1 G M Q Z B hc n t hs _ _ rfl rfl
    rw [hQBW, hQQB] at e
    have e' : Nat.card ↥(QB B ⊓ W) * Nat.card Z = Nat.card Z ^ n * Nat.card Z := by
      rw [e]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) e'
  · have e := h2 G M Q Z B hc n t hs _ rfl
    have : V ⊓ (QB B ⊓ W) = V ⊓ QB B := by
      ext x
      constructor
      · rintro ⟨hxV, hxB, _⟩
        exact ⟨hxV, hxB⟩
      · rintro ⟨hxV, hxB⟩
        exact ⟨hxV, hxB, hVW hxV⟩
    rw [this]; exact e

theorem stroth91b_of_steps (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hNC : Sec9NCommStatement) (h1 : Step91OrderQBStatement) (h2 : Step91OrderVQBStatement)
    (h3 : Step91InterStatement) (h4 : Step91MixedCommStatement) : Stroth91bStatement := by
  intro G _ _ M Q Z B hc n t hs r hr V W hV hW
  subst hV hW
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr := hc.conj_of_mem hrM
  have h35' := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have h35 := h35'.2.1
  have hQQB : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := h35'.2.2.2
  set V := Vt M (LB M Q B) B Z t with hVd
  set W := Wt Q V with hWd
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hVW : V ≤ W := fun v hv => ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
  have hZW : Z ≤ W := hZV.trans hVW
  have hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    Subgroup.mem_centralizer_iff.mp hw.2 v hv
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hc.hyp.toHyp79.comm_mem_V (hWQ ha) (hWQ hb)
  have hZB : Z ⊔ B ≤ V := sup_le hZV (hc.B_le_Vt ht)
  have hZA : Z ⊔ conjSubgroup r B ≤ V :=
    sup_le hZV (le_sup_left.trans (hc.conj_Rt_le_Vt ht hrR))
  have hrW := sec9_conj_Wt_eq hc ht hrR
  have hrV := sec9_conj_Vt_eq hc ht hrR
  have hX₁eq : QB (conjSubgroup r B) ⊓ W = conjSubgroup r (QB B ⊓ W) := by
    rw [QB_conj, conjSubgroup_inf, hrW]
  have hVX₁eq : V ⊓ (QB (conjSubgroup r B) ⊓ W) = conjSubgroup r (V ⊓ (QB B ⊓ W)) := by
    rw [conjSubgroup_inf r V (QB B ⊓ W), hrV, hX₁eq]
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨hX₂c, hVX₂⟩ := sec9_numerics h34 h1 h2 hs
  have hX₁c : Nat.card ↥(QB (conjSubgroup r B) ⊓ W) = Nat.card Z ^ n := by
    rw [hX₁eq, card_conjSubgroup, hX₂c]
  have hVX₁ : Nat.card ↥(V ⊓ (QB (conjSubgroup r B) ⊓ W)) = Nat.card Z ^ 4 := by
    rw [hVX₁eq, card_conjSubgroup, hVX₂]
  have hI : Nat.card ↥((QB (conjSubgroup r B) ⊓ W) ⊓ (QB B ⊓ W)) ≤ Nat.card Z ^ 3 := by
    have e := h3 G M Q Z B hc n t hs r hr _ _ rfl rfl
    have : (QB (conjSubgroup r B) ⊓ W) ⊓ (QB B ⊓ W) = QB (conjSubgroup r B) ⊓ QB B ⊓ W := by
      ext x
      constructor
      · rintro ⟨⟨hA, hxW⟩, hB, _⟩
        exact ⟨⟨hA, hB⟩, hxW⟩
      · rintro ⟨⟨hA, hB⟩, hxW⟩
        exact ⟨⟨hA, hxW⟩, hB, hxW⟩
    rw [this]; exact e
  have hWc := hs.card_W h34
  have hVc5 := hs.card_V
  have hZX₁ : Z ≤ QB (conjSubgroup r B) ⊓ W := le_inf hcr.Z_le_QB.1 hZW
  have hZX₂ : Z ≤ QB B ⊓ W := le_inf hc.Z_le_QB.1 hZW
  have hn3 : 3 ≤ n := hs5.n_gt
  have hdir := sec9_directSum_of_card hVW inf_le_right inf_le_right hVc hcommW hZV hZX₁ hZX₂
    hq2 hn3 hWc hVc5 hX₁c hX₂c hI hVX₁ hVX₂
  have hsup := sec9_sup_eq_of_card hVW inf_le_right inf_le_right hVc hcommW hZV hZX₁ hZX₂
    hq2 hn3 hWc hVc5 hX₁c hX₂c hI hVX₁ hVX₂
  have hmul := sec9_exists_mul_of_card hVW inf_le_right inf_le_right hVc hcommW hZV hZX₁ hZX₂
    hq2 hn3 hWc hVc5 hX₁c hX₂c hI hVX₁ hVX₂
  refine ⟨hdir, ?_⟩
  obtain ⟨hprod, -, -⟩ := sec9_N51 h34 h311a hNC hs hr
  obtain ⟨hm1, hm2⟩ := h4 G M Q Z B hc n t hs r hr _ _ rfl rfl
  have hNle : ∀ s ∈ hc.CN t, s ∈ Rt M (LB M Q B) t := fun s hs' => (Ctx.mem_CN.mp hs').1
  refine sec9_comm_le_of_prod (L₁ := LB M Q B) (L₂ := LB M Q (conjSubgroup r B))
    (X₁ := QB (conjSubgroup r B) ⊓ W) (X₂ := QB B ⊓ W) hprod hmul inf_le_right inf_le_right
    hVc (fun s hs' v hv => (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht (hNle s hs')) v).mp hv) hm1 ?_ ?_ hm2
  · intro s hs' x hx
    exact hZB (hc.comm_LB_inf_QB_mem_sup hs'.1 ⟨hWQ hx.2, hx.1⟩)
  · intro s hs' x hx
    exact hZA (hcr.comm_LB_inf_QB_mem_sup hs'.1 ⟨hWQ hx.2, hx.1⟩)

theorem sec9_card_X₁ (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) := by
  rw [QB_conj, ← sec9_conj_Wt_eq hc ht hr, ← conjSubgroup_inf, sec9_conj_Wt_eq hc ht hr,
    card_conjSubgroup]

theorem step92Nontriv_of (h34 : Stroth34Statement) (hA : Sec9AExistsStatement)
    (h91b : Stroth91bStatement) (hn5 : Sec9NGeFiveStatement) (h1 : Step91OrderQBStatement)
    (h2 : Step91OrderVQBStatement) : Step92NontrivStatement := by
  intro G _ _ M Q Z B hc n t hs V W hV hW
  subst hV hW
  by_contra hcon
  push Not at hcon
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrR := hr.mem
  obtain ⟨⟨hV1, hA1, hV2, hA2, hsup, hinf⟩, -⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  set V := Vt M (LB M Q B) B Z t with hVd
  set W := Wt Q V with hWd
  have hVW : V ≤ W := fun v hv => ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
  have hVc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    Subgroup.mem_centralizer_iff.mp hw.2 v hv
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨hX₂c, hVX₂⟩ := sec9_numerics h34 h1 h2 hs
  have hX₁c : Nat.card ↥(QB (conjSubgroup r B) ⊓ W) = Nat.card Z ^ n := by
    rw [sec9_card_X₁ hc ht hrR, hX₂c]
  have hX₁le : QB (conjSubgroup r B) ⊓ W ≤ (QB B ⊓ W) ⊔ V := by
    intro x hx
    have hy : r⁻¹ * x * r ∈ QB B ⊓ W := by
      refine ⟨?_, ?_⟩
      · have h1 : x ∈ QB (conjSubgroup r B) := hx.1
        rw [QB_conj] at h1
        exact mem_conjSubgroup.mp h1
      · have := sec9_conj_mem_Wt hc ht ((Rt M (LB M Q B) t).inv_mem hrR) hx.2
        simpa using this
    have e : x = ⁅r, r⁻¹ * x * r⁆ * (r⁻¹ * x * r) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact ((QB B ⊓ W) ⊔ V).mul_mem (Subgroup.mem_sup_right (hcon r hrR _ hy.2))
      (Subgroup.mem_sup_left hy)
  have hA1le : (QB (conjSubgroup r B) ⊓ W) ⊔ V ≤ (QB B ⊓ W) ⊔ V :=
    sup_le hX₁le le_sup_right
  have hA1eq : (QB (conjSubgroup r B) ⊓ W) ⊔ V = V := by
    have h1 := inf_eq_left.mpr hA1le
    rw [hinf] at h1
    exact h1.symm
  have hX₁V : QB (conjSubgroup r B) ⊓ W ≤ V := le_sup_left.trans hA1eq.le
  have hle5 : Nat.card Z ^ n ≤ Nat.card Z ^ 5 := by
    rw [← hX₁c, ← hs.card_V]
    exact Subgroup.card_le_of_le hX₁V
  have hn5' : n ≤ 5 := (Nat.pow_le_pow_iff_right hq2).mp hle5
  have hn : n = 5 := le_antisymm hn5' (hn5 G M Q Z B hc n t hs)
  have hWeq : (QB B ⊓ W) ⊔ V = W := by
    rw [hA1eq] at hsup
    have h1 : V ⊔ ((QB B ⊓ W) ⊔ V) = (QB B ⊓ W) ⊔ V := sup_eq_right.mpr hV2
    exact h1.symm.trans hsup
  have hVfix : ∀ v ∈ V, ∀ y ∈ W, v * y * v⁻¹ = y := fun v hv y hy => by
    rw [mul_inv_eq_iff_eq_mul]; exact hVc v hv y hy
  have hnorm : V ≤ Subgroup.normalizer ((QB B ⊓ W : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hVfix v hv x hx.2]
      exact hx
    · intro hx
      have h1 := hVfix v⁻¹ (V.inv_mem hv) _ hx.2
      have e : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
      rw [e] at h1
      rw [← h1] at hx
      exact hx
  have hprod := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hWeq, inf_comm, hVX₂, hX₂c, hs.card_V, hs.card_W h34, hn] at hprod
  have h6 : Nat.card Z ^ (2 * 5 - 3) * Nat.card Z ^ 4 = Nat.card Z ^ 5 * Nat.card Z ^ 5 := hprod
  rw [← pow_add, ← pow_add] at h6
  have := Nat.pow_right_injective hq2 h6
  omega

end CFSG.RankThree.GF2n.Stroth80
