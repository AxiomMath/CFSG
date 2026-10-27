module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

private theorem card_LB_eq_sq_mul_card_inf_CN (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    Nat.card ↥(LB M Q B) = Nat.card Z ^ 2 * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  have h := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  rw [relIndex_LB_CN h34 hs, inf_comm] at h
  exact h.symm

private theorem card_inf_X_le_sq_mul_card_CN (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X : Subgroup G} :
    Nat.card ↥(LB M Q B ⊓ X) ≤ Nat.card Z ^ 2 * Nat.card ↥(hc.CN t) := by
  calc Nat.card ↥(LB M Q B ⊓ X) ≤ Nat.card ↥(LB M Q B) := Subgroup.card_le_of_le inf_le_left
    _ = Nat.card Z ^ 2 * Nat.card ↥(LB M Q B ⊓ hc.CN t) :=
        card_LB_eq_sq_mul_card_inf_CN h34 hc hs
    _ ≤ Nat.card Z ^ 2 * Nat.card ↥(hc.CN t) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le inf_le_right)

private theorem card_Rt_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    Nat.card ↥(Rt M (LB M Q B) t) =
      Nat.card ↥(hc.CN t) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) ^ 2 := by
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hs.plus4
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hφ, card_omegaPlus_four hK4, hK] at h1
  have h2 : Nat.card ↥((hc.CN t).subgroupOf (Rt M (LB M Q B) t)) = Nat.card ↥(hc.CN t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  rw [h2] at h1
  exact h1.symm

private theorem card_Rt_mul_card_Q_eq {t : G}
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    Nat.card ↥(Rt M (LB M Q B) t) * Nat.card ↥Q = Nat.card ↥X * Nat.card ↥Y := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, -⟩ := hsplit
  have hnorm : X ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ Q := hcomm x hx y hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (hQY hxy) hy
  have h := card_sup_mul_card_inf_of_le_normalizer (L := Y) (E := X) hnorm
  rw [sup_comm, inf_comm, hXY, hXYQ] at h
  exact h.trans (mul_comm (Nat.card ↥Y) (Nat.card ↥X))

private theorem card_Y_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) :
    Nat.card ↥Y = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
  obtain ⟨⟨-, -, hQY, -⟩, hYsl, -⟩ := hsplit
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hc.hyp.q4
    (by obtain ⟨e, -, he, -⟩ := hc.hyp.cp; exact ⟨e, he⟩) hYmod
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf Y), hYcard]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQY).toEquiv]

private theorem card_X_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    Nat.card ↥X = Nat.card ↥(hc.CN t) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) := by
  have hmul : Nat.card ↥X * Nat.card ↥Y =
      (Nat.card ↥(hc.CN t) * (Nat.card Z * (Nat.card Z ^ 2 - 1))) * Nat.card ↥Y := by
    rw [← card_Rt_mul_card_Q_eq hsplit,
      card_Rt_eq (n := n) (t := t) hc hs, card_Y_eq (n := n) (t := t) hc hsplit]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Y)) hmul

theorem card_sup_lt_Rt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) < Nat.card ↥(Rt M (LB M Q B) t) := by
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hnorm : (LB M Q B ⊓ X) ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ Q := hcomm x hx.2 y hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (hQY hxy) hy
  have hEinf : (LB M Q B ⊓ X) ⊓ Y = Q := by
    refine le_antisymm ?_ (le_inf (le_inf le_sup_left hQX) hQY)
    intro x hx
    exact hXYQ ▸ Subgroup.mem_inf.mpr ⟨hx.1.2, hx.2⟩
  have hEprod : Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) *
      Nat.card ↥((LB M Q B ⊓ X) ⊓ Y) =
      Nat.card ↥(LB M Q B ⊓ X) * Nat.card ↥Y := by
    have h := card_sup_mul_card_inf_of_le_normalizer (L := Y) (E := LB M Q B ⊓ X) hnorm
    rw [sup_comm, inf_comm (Y : Subgroup G) (LB M Q B ⊓ X)] at h
    exact h.trans (mul_comm (Nat.card ↥Y) (Nat.card ↥(LB M Q B ⊓ X)))
  have hE_lt_X : Nat.card ↥(LB M Q B ⊓ X) < Nat.card ↥X := by
    have hle := card_inf_X_le_sq_mul_card_CN h34 hc hs (X := X)
    have hNpos : 0 < Nat.card ↥(hc.CN t) := Nat.card_pos
    have hq : Nat.card Z ^ 2 < Nat.card Z * (Nat.card Z ^ 2 - 1) := by
      have hq2 : 2 ≤ Nat.card Z := by omega
      have hsq : 2 ^ 2 ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hq2 2
      have hsub : Nat.card Z ^ 2 - 1 + 1 = Nat.card Z ^ 2 := Nat.sub_add_cancel (by omega)
      nlinarith
    have hlt : Nat.card Z ^ 2 * Nat.card ↥(hc.CN t) < Nat.card ↥X := by
      rw [card_X_eq (n := n) (t := t) hc hs hsplit0]
      simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right hq hNpos
    exact lt_of_le_of_lt hle hlt
  have hlt : Nat.card ↥(LB M Q B ⊓ X) * Nat.card ↥Y <
      Nat.card ↥(Rt M (LB M Q B) t) * Nat.card ↥Q := by
    have h1 : Nat.card ↥(LB M Q B ⊓ X) * Nat.card ↥Y < Nat.card ↥X * Nat.card ↥Y :=
      Nat.mul_lt_mul_of_pos_right hE_lt_X (Nat.card_pos (α := ↥Y))
    rwa [← card_Rt_mul_card_Q_eq hsplit0] at h1
  have h2 : Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) * Nat.card ↥Q <
      Nat.card ↥(Rt M (LB M Q B) t) * Nat.card ↥Q := by
    calc Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) * Nat.card ↥Q
        = Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) * Nat.card ↥((LB M Q B ⊓ X) ⊓ Y) := by
          rw [hEinf]
      _ = Nat.card ↥(LB M Q B ⊓ X) * Nat.card ↥Y := hEprod
      _ < Nat.card ↥(Rt M (LB M Q B) t) * Nat.card ↥Q := hlt
  exact Nat.lt_of_mul_lt_mul_right h2

theorem Split95.conjSubgroup_eq_self_of_mem_Rt {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) :
    ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ Y = Y := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, -⟩ := hsplit
  have hXn : X ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ Q := hcomm x hx y hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (hQY hxy) hy
  have hRn : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hXY]
    exact sup_le hXn Subgroup.le_normalizer
  intro ρ hρ
  exact conjSubgroup_eq_self_iff.mpr (hRn hρ)

private theorem mem_LB_inf_X_of_mem_centre (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : Centre95 hc t Z0)
    {s nn : G} (hs0 : s ∈ Z0) (hsn : ConjMod M Q s nn) (hnZ : nn ∉ Z0) :
    s ∈ LB M Q B ⊓ X ∧ s ∉ Q := by
  have hsN : s ∈ hc.CN t := (hcen.1 hs0).2
  have hsL : s ∈ LB M Q B := (hcen.1 hs0).1
  have hNX : hc.CN t ≤ X :=
    (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  refine ⟨⟨hsL, hNX hsN⟩, ?_⟩
  rintro hsQ
  obtain ⟨-, g, hg, hq⟩ := hsn
  have haQ : g * s * g⁻¹ ∈ Q := by
    have h : g * s * g⁻¹ ∈ conjSubgroup g Q := by
      rw [mem_conjSubgroup]
      show g⁻¹ * (g * s * g⁻¹) * g ∈ Q
      rwa [show g⁻¹ * (g * s * g⁻¹) * g = s by group]
    rwa [hc.conj_Q_eq hg] at h
  have hnnQ : nn ∈ Q := by
    have e : nn = (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq haQ
  exact hnZ (hc.Q_le_centre hs.toSec5.mem hZ0 hnnQ)

private theorem Rt_le_of_mem_centre (hc : Ctx M Q Z B) {t s r : G}
    (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : Centre95 hc t Z0)
    (hs0 : s ∈ Z0) :
    Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s := by
  have hsL : s ∈ LB M Q B := (hcen.1 hs0).1
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcomm : ⁅s, r⁆ ∈ Q := ((hZ0 s).mp hs0).2 r hrR
  have hconjQ : r⁻¹ * s * r * s⁻¹ ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hrM)) ⁅s, r⁆).mp
      hcomm
    have e : r⁻¹ * ⁅s, r⁆ * r⁻¹⁻¹ = r⁻¹ * s * r * s⁻¹ := by
      simp only [commutatorElement_def, inv_inv]
      group
    rwa [e] at h
  have hmem : r⁻¹ * s * r ∈ LB M Q B := by
    have e : r⁻¹ * s * r = (r⁻¹ * s * r * s⁻¹) * s := by group
    rw [e]
    exact (LB M Q B).mul_mem ((show Q ≤ LB M Q B from le_sup_left) hconjQ) hsL
  have hsconj : s ∈ conjSubgroup r (LB M Q B) := by
    rw [mem_conjSubgroup]
    exact hmem
  have hLB2 : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) s :=
    hc.LB_conj_le_Rt hrM hsconj
  calc Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B) := hr.gen
    _ ≤ Rt M (LB M Q B) s := sup_le (le_Rt (LB M Q B) hsL) hLB2

private theorem sec9Hyp_of_mem_centre (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hcen : Centre95 hc t Z0) {s nn : G} (hs0 : s ∈ Z0) (hsn : ConjMod M Q s nn)
    (hnZ : nn ∉ Z0) : Sec9Hyp hc n s := by
  obtain ⟨hsLX, hsQ⟩ := mem_LB_inf_X_of_mem_centre h34 h311a hc hs hsplit hZ0 hcen hs0 hsn hnZ
  have hRtle : Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s :=
    Rt_le_of_mem_centre hc hr hZ0 hcen hs0
  obtain ⟨-, -, hcase, -⟩ := h1 s hsLX hsQ
  have hOm : OmegaPlusNat hc s 2 := by
    rcases hcase with hR | h
    · exfalso
      have hcard : Nat.card ↥(Rt M (LB M Q B) t) ≤
          Nat.card ↥((LB M Q B ⊓ X) ⊔ Y) := by
        rw [← hR]
        exact Subgroup.card_le_of_le hRtle
      exact absurd hcard (not_le.mpr (card_sup_lt_Rt h34 hc hs hsplit))
    · exact h
  exact ⟨⟨hs.toSec5.width, hs.toSec5.n_gt, hs.toSec5.noA2, hs.toSec5.gen, hsLX.1, hsQ⟩,
    hOm, hs.large⟩

private theorem Vt_eq_of_mem_centre (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hcen : Centre95 hc t Z0) {s : G}
    (hs0 : s ∈ Z0) (hsQ : s ∉ Q) (hss : Sec9Hyp hc n s) :
    Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hV := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hss.toSec5.mem hss.toSec5.notQ
    (sec9_notQB h34 hss)
  rw [hV.1]
  simpa [Ut] using hcen.2.2 s hs0 hsQ

private theorem conjSubgroup_Rt_of_mem_Q (hc : Ctx M Q Z B) {g s nn : G} (hg : g ∈ M) (hsM : s ∈ M)
    (hq : nn * (g * s * g⁻¹)⁻¹ ∈ Q) :
    conjSubgroup g (Rt M (LB M Q B) s) = Rt M (LB M Q B) nn := by
  have haM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hyQ : (g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM))
      (nn * (g * s * g⁻¹)⁻¹)).mp hq
    simpa using h
  have h := Rt_mul_of_mem_Q hc (t := g * s * g⁻¹)
    (y := (g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) hyQ
  have e : (g * s * g⁻¹) *
      ((g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) = nn := by group
  rw [e] at h
  rw [conjSubgroup_Rt_eq hg s]
  exact h.symm

private theorem conjSubgroup_Vt_of_mem_Q (hc : Ctx M Q Z B) {g s nn : G} (hg : g ∈ M) (hsM : s ∈ M)
    (hq : nn * (g * s * g⁻¹)⁻¹ ∈ Q) :
    conjSubgroup g (Vt M (LB M Q B) B Z s) = Vt M (LB M Q B) B Z nn := by
  have haM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hyQ : (g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM))
      (nn * (g * s * g⁻¹)⁻¹)).mp hq
    simpa using h
  have h := Vt_mul_of_mem_Q hc (t := g * s * g⁻¹)
    (y := (g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) hyQ
  have e : (g * s * g⁻¹) *
      ((g * s * g⁻¹)⁻¹ * (nn * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) = nn := by group
  rw [e] at h
  rw [conjSubgroup_Vt_eq hg (hc.conj_Z_eq hg) s]
  exact h.symm

private theorem mem_LB_inf_X_of_ConjMod (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {r : G} (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {nn : G}
    (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t) (hnZ : nn ∉ Z0) :
    r⁻¹ * nn * r ∈ LB M Q B ⊓ X ∧ r⁻¹ * nn * r ∉ Q := by
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hNX : hc.CN t ≤ X :=
    (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have heL : r⁻¹ * nn * r ∈ LB M Q B := by
    have h := hnn.1
    rw [hc.LB_conj hrM] at h
    exact mem_conjSubgroup.mp h
  have heN : r⁻¹ * nn * r ∈ hc.CN t := by
    simpa using hc.CN_conj_mem hs.toSec5.mem ((Rt M (LB M Q B) t).inv_mem hrR) hnn.2
  refine ⟨⟨heL, hNX heN⟩, ?_⟩
  intro heQ
  have hnnQ : nn ∈ Q := by
    have e : nn = r * (r⁻¹ * nn * r) * r⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) (r⁻¹ * nn * r)).mp heQ
  exact hnZ (hc.Q_le_centre hs.toSec5.mem hZ0 hnnQ)

private theorem normal_and_unique_of_ConjMod (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {nn : G}
    (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t) (hnZ : nn ∉ Z0) :
    (∀ ρ ∈ Rt M (LB M Q B) nn, conjSubgroup ρ Y = Y) ∧
      ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ Rt M (LB M Q B) nn →
        (∀ ρ ∈ Rt M (LB M Q B) nn, conjSubgroup ρ Y' = Y') →
        QuotSat Y' Q (IsSLModel 2 (Nat.card Z)) → Y' = Y := by
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hYn : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ Y = Y :=
    hsplit.conjSubgroup_eq_self_of_mem_Rt
  have hconjY : conjSubgroup r Y = Y := hYn r hrR
  obtain ⟨heE, heQ⟩ := mem_LB_inf_X_of_ConjMod h34 h311a hc hs hsplit hr hZ0 hnn hnZ
  obtain ⟨-, hnorme, -, huniqe⟩ := h1 (r⁻¹ * nn * r) heE heQ
  have hconjRe : conjSubgroup r (Rt M (LB M Q B) (r⁻¹ * nn * r)) = Rt M (LB M Q B) nn := by
    rw [conjSubgroup_Rt_eq hrM]
    congr 1
    show r * (r⁻¹ * nn * r) * r⁻¹ = nn
    group
  have hconjRe' : conjSubgroup r⁻¹ (Rt M (LB M Q B) nn) =
      Rt M (LB M Q B) (r⁻¹ * nn * r) := by
    rw [← hconjRe, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hconjYinv : conjSubgroup r⁻¹ Y = Y := by
    have h : conjSubgroup r⁻¹ (conjSubgroup r Y) = conjSubgroup r⁻¹ Y := by rw [hconjY]
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
    exact h.symm
  have hnormnn : ∀ ρ ∈ Rt M (LB M Q B) nn, conjSubgroup ρ Y = Y := by
    intro ρ hρ
    have hρe : r⁻¹ * ρ * r ∈ Rt M (LB M Q B) (r⁻¹ * nn * r) := by
      rw [← hconjRe] at hρ
      exact mem_conjSubgroup.mp hρ
    have h1 := hnorme (r⁻¹ * ρ * r) hρe
    calc conjSubgroup ρ Y
        = conjSubgroup r (conjSubgroup (r⁻¹ * ρ * r) (conjSubgroup r⁻¹ Y)) := by
          rw [← conjSubgroup_mul, ← conjSubgroup_mul]
          congr 1
          group
      _ = conjSubgroup r (conjSubgroup (r⁻¹ * ρ * r) Y) := by rw [hconjYinv]
      _ = conjSubgroup r Y := by rw [h1]
      _ = Y := hconjY
  refine ⟨hnormnn, ?_⟩
  intro Y' hQY' hY'R hnormY' hY'sl
  have hQY'e : Q ≤ conjSubgroup r⁻¹ Y' := by
    rw [← hc.conj_Q_eq (M.inv_mem hrM)]
    exact Subgroup.map_mono hQY'
  have hY'e : conjSubgroup r⁻¹ Y' ≤ Rt M (LB M Q B) (r⁻¹ * nn * r) := by
    calc conjSubgroup r⁻¹ Y' ≤ conjSubgroup r⁻¹ (Rt M (LB M Q B) nn) :=
          Subgroup.map_mono hY'R
      _ = Rt M (LB M Q B) (r⁻¹ * nn * r) := hconjRe'
  have hnormY'e : ∀ ρ ∈ Rt M (LB M Q B) (r⁻¹ * nn * r),
      conjSubgroup ρ (conjSubgroup r⁻¹ Y') = conjSubgroup r⁻¹ Y' := by
    intro ρ hρ
    have hρnn : r * ρ * r⁻¹ ∈ Rt M (LB M Q B) nn := by
      rw [← hconjRe]
      rw [mem_conjSubgroup]
      show r⁻¹ * (r * ρ * r⁻¹) * r ∈ Rt M (LB M Q B) (r⁻¹ * nn * r)
      rwa [show r⁻¹ * (r * ρ * r⁻¹) * r = ρ by group]
    have h := hnormY' (r * ρ * r⁻¹) hρnn
    calc conjSubgroup ρ (conjSubgroup r⁻¹ Y')
        = conjSubgroup r⁻¹ (conjSubgroup (r * ρ * r⁻¹) Y') := by
          rw [← conjSubgroup_mul, ← conjSubgroup_mul]
          congr 1
          group
      _ = conjSubgroup r⁻¹ Y' := by rw [h]
  have hsat : QuotSat (conjSubgroup r⁻¹ Y') Q (IsSLModel 2 (Nat.card Z)) :=
    hc.conj_Q_eq (M.inv_mem hrM) ▸
      QuotSat.conj (fun X Y _ _ e h => IsSLModel.congr e h) hY'sl r⁻¹
  have hY'Y : conjSubgroup r⁻¹ Y' = Y := huniqe _ hQY'e hY'e hnormY'e hsat
  calc Y' = conjSubgroup r (conjSubgroup r⁻¹ Y') := by
        rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    _ = conjSubgroup r Y := by rw [hY'Y]
    _ = Y := hconjY

theorem five_transport (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) (h1 : HS9.OneConcl hc X Y) {r : G}
    (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : HS9.Centre95 hc t Z0)
    {s nn : G} (hs0 : s ∈ Z0) (hsn : ConjMod M Q s nn)
    (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t) (hnZ : nn ∉ Z0) :
    ∃ g₀ ∈ M, nn * (g₀ * s * g₀⁻¹)⁻¹ ∈ Q ∧ conjSubgroup g₀ Y = Y ∧
      conjSubgroup g₀ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z nn ∧
      conjSubgroup g₀ (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) nn := by
  obtain ⟨hnnM, g₀, hg₀, hq₀⟩ := hsn
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hsM : s ∈ M := hc.centre_le_M t hZ0 hs0
  have hsn' : ConjMod M Q s nn := ⟨hnnM, g₀, hg₀, hq₀⟩
  obtain ⟨hsLX, hsQ⟩ :=
    mem_LB_inf_X_of_mem_centre h34 h311a hc hs hsplit0 hZ0 hcen hs0 hsn' hnZ
  have hRtle : Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s :=
    Rt_le_of_mem_centre hc hr hZ0 hcen hs0
  have hss : Sec9Hyp hc n s :=
    sec9Hyp_of_mem_centre h34 h311a hc hs hsplit0 h1 hr hZ0 hcen hs0 hsn' hnZ
  have hVt : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t :=
    Vt_eq_of_mem_centre h34 hc hs hcen hs0 hsQ hss
  have hat := normal_and_unique_of_ConjMod h34 h311a hc hs hsplit0 h1 hr hZ0 hnn hnZ
  have hRconj : conjSubgroup g₀ (Rt M (LB M Q B) s) = Rt M (LB M Q B) nn :=
    conjSubgroup_Rt_of_mem_Q hc hg₀ hsM hq₀
  have hVconj : conjSubgroup g₀ (Vt M (LB M Q B) B Z s) = Vt M (LB M Q B) B Z nn :=
    conjSubgroup_Vt_of_mem_Q hc hg₀ hsM hq₀
  obtain ⟨-, hnormYs, -, -⟩ := h1 s hsLX hsQ
  have hYconj : conjSubgroup g₀ Y = Y := by
    refine hat.2 (conjSubgroup g₀ Y) ?_ ?_ ?_ ?_
    · rw [← hc.conj_Q_eq hg₀]
      exact Subgroup.map_mono hQY
    · calc conjSubgroup g₀ Y ≤ conjSubgroup g₀ (Rt M (LB M Q B) s) :=
            Subgroup.map_mono (hYR.trans hRtle)
        _ = Rt M (LB M Q B) nn := hRconj
    · intro ρ hρ
      have hρs : g₀⁻¹ * ρ * g₀ ∈ Rt M (LB M Q B) s := by
        rw [← hRconj] at hρ
        exact mem_conjSubgroup.mp hρ
      calc conjSubgroup ρ (conjSubgroup g₀ Y)
          = conjSubgroup g₀ (conjSubgroup (g₀⁻¹ * ρ * g₀) Y) := by
            rw [← conjSubgroup_mul, ← conjSubgroup_mul]
            congr 1
            group
        _ = conjSubgroup g₀ Y := by rw [hnormYs _ hρs]
    · exact hc.conj_Q_eq hg₀ ▸ QuotSat.conj (fun X Y _ _ e h => IsSLModel.congr e h) hYsl g₀
  refine ⟨g₀, hg₀, hq₀, hYconj, ?_, ?_⟩
  · rw [← hVt]
    exact hVconj
  · calc conjSubgroup g₀ (Rt M (LB M Q B) t) ≤
        conjSubgroup g₀ (Rt M (LB M Q B) s) := Subgroup.map_mono hRtle
      _ = Rt M (LB M Q B) nn := hRconj

end HS9

end CFSG.RankThree.GF2n.Stroth80
