module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CTypeA
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_mem95 {S : Subgroup G} {x : G} (g : G) (hx : x ∈ S) :
    g * x * g⁻¹ ∈ conjSubgroup g S := by
  rw [mem_conjSubgroup]
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e]
  exact hx

theorem conj_inv_mem95 {S : Subgroup G} {x : G} (g : G) (hx : x ∈ S) :
    g⁻¹ * x * g ∈ conjSubgroup g⁻¹ S := by
  rw [mem_conjSubgroup, inv_inv]
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e]
  exact hx

theorem comm_CN_Q_mem_Wt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {y : G} (hy : y ∈ hc.CN t) {a : G} (ha : a ∈ Q) :
    ⁅y, a⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hchi := stroth91c_of_34 h34 G M Q Z B hc n t hs (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hSec : SecHyp (Rt M (LB M Q B) t) Q Z := n12l3_secHyp hc (fun r hr => hc.Rt_le_M t hr)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  exact n12l3_comm_mem_W hSec hchi (hc.Vt_le_Q t) (n12l3_Z_le_W hc t) hZV (Ctx.mem_CN.mp hy).1
    (Ctx.mem_CN.mp hy).2 ha

theorem comm_CN_Wt_mem_Vt (h91b : Stroth91bStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) {y : G} (hy : y ∈ hc.CN t) {w : G}
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) : ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t :=
  (h91b G M Q Z B hc n t hs r hr _ _ rfl rfl).2 y hy w hw

theorem Z_le_conj_Vt (hc : Ctx M Q Z B) {t z : G} (hzM : z ∈ M) :
    Z ≤ conjSubgroup z (Vt M (LB M Q B) B Z t) := fun ζ hζ => by
  rw [mem_conjSubgroup]
  have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hzM)) ζ).mp hζ
  exact sec39_Z_le_Vt (by simpa using this)

section Conj

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Z0 : Subgroup G} {z : G}

theorem conj_Vt_le_Wt (h34 : Stroth34Statement) (hs : Sec9Hyp hc n t) (hcen : Centre95 hc t Z0)
    (hzM : z ∈ M) (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t) :
    conjSubgroup z (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  classical
  obtain ⟨-, hrel, hV⟩ := hcen
  obtain ⟨s, hsZ0, hsQ⟩ : ∃ s ∈ Z0, s ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h1 : Q.relIndex Z0 = 1 := Subgroup.relIndex_eq_one.mpr hcon
    rw [hrel] at h1
    have := hc.hyp.q4
    omega
  have hVeq : Vt M (LB M Q B) B Z t = ⁅Q, Subgroup.zpowers s⁆ ⊔ Z := (hV s hsZ0 hsQ).symm
  have hXmem : ∀ g, g ∈ conjSubgroup z⁻¹ (Wt Q (Vt M (LB M Q B) B Z t)) ↔
      z * g * z⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro g
    rw [mem_conjSubgroup, inv_inv]
  have hAX : (⁅Q, Subgroup.zpowers s⁆ ⊔ Z : Subgroup G) ≤
      conjSubgroup z⁻¹ (Wt Q (Vt M (LB M Q B) B Z t)) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hXmem]
      have hsk : z * s ^ k * z⁻¹ ∈ hc.CN t := by
        rw [← conj_zpow]
        exact zpow_mem (hzN s hsZ0) k
      have e : z * ⁅a, s ^ k⁆ * z⁻¹ = ⁅z * a * z⁻¹, z * s ^ k * z⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, ← commutatorElement_inv]
      exact (Wt Q (Vt M (LB M Q B) B Z t)).inv_mem
        (comm_CN_Q_mem_Wt h34 hs hsk (n12l3_normalizes_Q hc hzM ha))
    · intro ζ hζ
      rw [hXmem]
      exact n12l3_Z_le_W hc t
        ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hzM) ζ).mp hζ)
  have hVX := hVeq.le.trans hAX
  intro g hg
  have h1 := hVX (mem_conjSubgroup.mp hg)
  rw [hXmem] at h1
  have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
  rwa [e] at h1

theorem conj_inv_Vt_le_Wt (h34 : Stroth34Statement) (hs : Sec9Hyp hc n t)
    (hcen : Centre95 hc t Z0) (hzM : z ∈ M) (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t) :
    conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  intro x hx
  have hx' : z * x * z⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have := mem_conjSubgroup.mp hx
    simpa using this
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  · have h1 := n12l3_normalizes_Q hc (M.inv_mem hzM) (hc.Vt_le_Q t hx')
    have e : z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x := by group
    rwa [e] at h1
  · have hzv : z * v * z⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
      conj_Vt_le_Wt h34 hs hcen hzM hzN (conj_mem95 z hv)
    have h := Subgroup.mem_centralizer_iff.mp hzv.2 (z * x * z⁻¹) hx'
    have e1 : z * x * z⁻¹ * (z * v * z⁻¹) = z * (x * v) * z⁻¹ := by group
    have e2 : z * v * z⁻¹ * (z * x * z⁻¹) = z * (v * x) * z⁻¹ := by group
    rw [e1, e2] at h
    exact (mul_left_cancel (mul_right_cancel h)).symm

theorem comm_Vt_le_conj (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) (hcen : Centre95 hc t Z0) (hzM : z ∈ M)
    (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t) {y : G} (hy : y ∈ hc.CN t) :
    ⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers (z * y * z⁻¹)⁆ ≤
      conjSubgroup z (Vt M (LB M Q B) B Z t) := by
  rw [Subgroup.commutator_le]
  intro v hv g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [conj_zpow]
  have hyk : y ^ k ∈ hc.CN t := zpow_mem hy k
  have hw : z⁻¹ * v * z ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    conj_inv_Vt_le_Wt h34 hs hcen hzM hzN (conj_inv_mem95 z hv)
  have h1 : ⁅y ^ k, z⁻¹ * v * z⁆ ∈ Vt M (LB M Q B) B Z t :=
    comm_CN_Wt_mem_Vt h91b hs hr hyk hw
  have e : ⁅v, z * y ^ k * z⁻¹⁆ = z * ⁅y ^ k, z⁻¹ * v * z⁆⁻¹ * z⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, mem_conjSubgroup]
  have e2 : z⁻¹ * (z * ⁅y ^ k, z⁻¹ * v * z⁆⁻¹ * z⁻¹) * z = ⁅y ^ k, z⁻¹ * v * z⁆⁻¹ := by group
  rw [e2]
  exact (Vt M (LB M Q B) B Z t).inv_mem h1

theorem inf_conj_le_CentMod (hs : Sec9Hyp hc n t) (hzM : z ∈ M) {y : G} (hy : y ∈ hc.CN t) :
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ≤
      CentMod Z (Vt M (LB M Q B) B Z t) (Vt_le_normalizer hc t) (z * y * z⁻¹) := by
  rintro v ⟨hvV, hvz⟩
  refine ⟨hvV, ?_⟩
  have hv' : z⁻¹ * v * z ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hvz
  have h1 : ⁅y, z⁻¹ * v * z⁆ ∈ Z := (Ctx.mem_CN.mp hy).2 _ hv'
  have e : ⁅z * y * z⁻¹, v⁆ = z * ⁅y, z⁻¹ * v * z⁆ * z⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hzM) _).mp h1

theorem comm_zpowers_le_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {x : G}
    (hxR : x ∈ Rt M (LB M Q B) t) :
    ⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ≤ Vt M (LB M Q B) B Z t := by
  rw [Subgroup.commutator_le]
  intro v hv y hy
  have hyR : y ∈ Rt M (LB M Q B) t := (Subgroup.zpowers_le.mpr hxR) hy
  have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Vt M (LB M Q B) B Z t).mul_mem hv
    ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hyR) _).mp
      ((Vt M (LB M Q B) B Z t).inv_mem hv))

end Conj

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  {Z0 : Subgroup G} {z : G} [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.cent_eq_inf (C : Coord95 hc t K) (h34 : Stroth34Statement)
    (h91b : Stroth91bStatement) (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    (hcen : Centre95 hc t Z0) (hzM : z ∈ M) (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t) {y : G}
    (hy : y ∈ hc.CN t) (hxL : z * y * z⁻¹ ∈ LB M Q B) (hxN : z * y * z⁻¹ ∉ hc.CN t) :
    CentMod Z (Vt M (LB M Q B) B Z t) (Vt_le_normalizer hc t) (z * y * z⁻¹) =
        Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ∧
      (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers (z * y * z⁻¹)⁆ ⊔ Z : Subgroup G) =
        Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) := by
  obtain ⟨w, hw, hind, hEw, hcard, hvec, hcent⟩ := C.plane_facts hs hxL hxN
  have ht : t ∈ LB M Q B := hs.mem
  have hxR : z * y * z⁻¹ ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hSV : (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers (z * y * z⁻¹)⁆ ⊔ Z : Subgroup G) ≤
      Vt M (LB M Q B) B Z t := sup_le (comm_zpowers_le_Vt hc ht hxR) sec39_Z_le_Vt
  have hSz : (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers (z * y * z⁻¹)⁆ ⊔ Z : Subgroup G) ≤
      conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    sup_le (comm_Vt_le_conj h34 h91b hs hr hcen hzM hzN hy) (Z_le_conj_Vt hc hzM)
  have hSD := le_inf hSV hSz
  have hDC := inf_conj_le_CentMod hs hzM hy
  have hSC : (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers (z * y * z⁻¹)⁆ ⊔ Z : Subgroup G) =
      CentMod Z (Vt M (LB M Q B) B Z t) (Vt_le_normalizer hc t) (z * y * z⁻¹) :=
    Subgroup.eq_of_le_of_card_ge (hSD.trans hDC) (by rw [hcent, hcard])
  exact ⟨(le_antisymm hDC (hSC.ge.trans hSD)).symm, le_antisymm hSD (hDC.trans hSC.ge)⟩

end Coord

end HS9

end CFSG.RankThree.GF2n.Stroth80
