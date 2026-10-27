module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec97K5
public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveDefs
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
import CFSG.RankThree.GF2n.Stroth80.CarterSec97K5Contain
import CFSG.RankThree.GF2n.Stroth80.HeringSec95COpp
import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
import CFSG.RankThree.GF2n.Stroth80.CarterSec97K5Proof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conj_Vt_le_Wt_of_vanish (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hcen : Centre95 hc t Z0) {s g : G} (hs0 : s ∈ Z0) (hsQ : s ∉ Q) (hg : g ∈ M)
    (hgs : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * s * g⁻¹, v⁆ ∈ Z) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hsLB : s ∈ LB M Q B := (Subgroup.mem_inf.mp (hcen.1 hs0)).1
  have hsM : s ∈ M := hc.LB_le_M hsLB
  have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hxZ : g * s * g⁻¹ ∈ Subgroup.centralizer (Z : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : g⁻¹ * z * g ∈ Z := by
      refine mem_conjSubgroup.mp ?_
      rw [hc.conj_Z_eq hg]
      exact hz
    have hscomm : s * (g⁻¹ * z * g) = (g⁻¹ * z * g) * s :=
      mul_inv_eq_iff_eq_mul.mp (hc.LB_centralizes_Z hsLB (g⁻¹ * z * g) hz')
    calc z * (g * s * g⁻¹) = g * ((g⁻¹ * z * g) * s) * g⁻¹ := by group
      _ = g * (s * (g⁻¹ * z * g)) * g⁻¹ := by rw [← hscomm]
      _ = g * s * g⁻¹ * z := by group
  have hUt := Ut_le_Wt_of_vanish hc (hc.Vt_le_Q t) ⟨hxM, hxZ⟩ hgs
  have hV : Ut Q Z s = Vt M (LB M Q B) B Z t := hcen.2.2 s hs0 hsQ
  have hEq : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * s * g⁻¹) := by
    rw [← hV]
    exact (Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) s).symm
  rw [hEq]
  exact hUt

theorem comm_LB_pointT_mem_Vt (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    {r nn g : G} (h13 : Sec97K13 hc t X Y r nn g)
    (hVnW : Vt M (LB M Q B) B Z nn ≤ Wt Q (Vt M (LB M Q B) B Z t)) :
    ∀ x ∈ pointT hc X Y nn g, ∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  intro x hxT l hl
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hTW : pointT hc X Y nn g ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    (pointT_le_Vt h13).trans hVnW
  set V := Vt M (LB M Q B) B Z t
  have hRnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (V : Set G) :=
    hc.Rt_normalizes_Vt ht
  let S : Subgroup G :=
    { carrier := {a | a ∈ Rt M (LB M Q B) t ∧ ∀ y ∈ pointT hc X Y nn g, ⁅a, y⁆ ∈ V}
      mul_mem' := by
        rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
        refine ⟨(Rt M (LB M Q B) t).mul_mem haR hbR, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRnorm haR) _).mp (hb y hy))
          (ha y hy)
      one_mem' := ⟨(Rt M (LB M Q B) t).one_mem, fun y _ => by
        rw [commutatorElement_one_left]; exact V.one_mem⟩
      inv_mem' := by
        rintro a ⟨haR, ha⟩
        refine ⟨(Rt M (LB M Q B) t).inv_mem haR, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa using (Subgroup.mem_normalizer_iff.mp
          (hRnorm ((Rt M (LB M Q B) t).inv_mem haR)) _).mp (V.inv_mem (ha y hy)) }
  have hSX : LB M Q B ⊓ X ≤ S := by
    intro a ha
    exact ⟨(le_Rt (M := M) (LB M Q B) ht) ha.1,
      fun y hy => hsplit.2.2 a ha.2 y (hTW hy)⟩
  have hSY : LB M Q B ⊓ Y ≤ S := by
    intro b hb
    refine ⟨(le_Rt (M := M) (LB M Q B) ht) hb.1, fun y hy => ?_⟩
    exact sec39_Z_le_Vt ((mem_CQtGrp.mp (Subgroup.mem_inf.mp hy).2).2 b hb)
  have hle : LB M Q B ≤ S := by
    rw [h4.2.2]
    exact sup_le hSX hSY
  exact (hle hl).2 x hxT

theorem sec97K5_of_K13 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {r nn g : G}
    (hr : Sec7A hc t r) (h13 : Sec97K13 hc t X Y r nn g)
    (hVnW : Vt M (LB M Q B) B Z nn ≤ Wt Q (Vt M (LB M Q B) B Z t)) :
    Sec97K5 M Q Z B hc t (pointT hc X Y nn g) := by
  have hTW : pointT hc X Y nn g ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    (pointT_le_Vt h13).trans hVnW
  have hcomm := comm_LB_pointT_mem_Vt hc hs hsplit h4 h13 hVnW
  have hopp := isOppDecomp95 h34 h91b hs hr
  set V := Vt M (LB M Q B) B Z t
  have hnorm : Wt Q V ⊓ QB B ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_left.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer (V : Set G))
  have htle : pointT hc X Y nn g ≤ V ⊔ (Wt Q V ⊓ QB B) := by
    intro x hx
    have hxA := (hopp.2.2.2.2.2.2.2.2.2 x (hTW hx)).mpr (fun l hl => hcomm x hx l hl)
    rw [sup_comm, inf_comm]
    exact hxA
  refine ⟨?_, htle, ?_, pointT_not_le_Z h13 hc.ne, pointT_inf_V_le h13⟩
  · refine Subgroup.commutator_le.mpr fun l hl x hx => ?_
    have hx' : x ∈ (Wt Q V ⊓ QB B) ⊔ V := by
      rw [sup_comm]
      exact htle hx
    obtain ⟨d, hd, v, hv, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := Wt Q V ⊓ QB B) (K := V) hnorm hx'
    have hlL : l ∈ LB M Q B := hl.1
    have hlv : ⁅l, v⁆ ∈ Z := (Ctx.mem_CN.mp hl.2).2 v hv
    have hdcent : d ∈ Subgroup.centralizer (Z : Set G) :=
      Subgroup.centralizer_le (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
        (Subgroup.mem_inf.mp hd.1).2
    have hld : ⁅l, d⁆ ∈ Z ⊔ B :=
      hc.comm_LB_inf_QB_mem_sup hlL ⟨(Subgroup.mem_inf.mp hd.1).1, hd.2⟩
    have hdk : d * ⁅l, v⁆ * d⁻¹ = ⁅l, v⁆ := by
      have h := Subgroup.mem_centralizer_iff.mp hdcent ⁅l, v⁆ hlv
      rw [h.symm]
      group
    have e : ⁅l, d * v⁆ = ⁅l, d⁆ * (d * ⁅l, v⁆ * d⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hdk, sup_comm]
    exact (Z ⊔ B).mul_mem hld (Subgroup.mem_sup_left hlv)
  · intro x hxT hxZ
    have hx' : x ∈ (Wt Q V ⊓ QB B) ⊔ V := by
      rw [sup_comm]
      exact htle hxT
    obtain ⟨d, hd, v, hv, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := Wt Q V ⊓ QB B) (K := V) hnorm hx'
    have hdcent : d ∈ Subgroup.centralizer (Z : Set G) :=
      Subgroup.centralizer_le (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
        (Subgroup.mem_inf.mp hd.1).2
    have hdQB : d ∈ QB B := hd.2
    have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd.1).1
    have hdV : d ∈ V := by
      refine centLam91 h34 hs d ⟨hdQ, hdQB⟩ fun l hl => ?_
      have hlL : l ∈ LB M Q B := le_sup_right (a := Q) hl.1
      have hlN : l ∈ hc.CN t := hl.2
      have hlZ : ⁅l, d * v⁆ ∈ Z := hxZ l (Subgroup.mem_inf.mpr ⟨hlL, hlN⟩)
      have hlv : ⁅l, v⁆ ∈ Z := (Ctx.mem_CN.mp hlN).2 v hv
      have hdk : d * ⁅l, v⁆ * d⁻¹ = ⁅l, v⁆ := by
        have h := Subgroup.mem_centralizer_iff.mp hdcent ⁅l, v⁆ hlv
        rw [h.symm]
        group
      have e : ⁅l, d * v⁆ = ⁅l, d⁆ * (d * ⁅l, v⁆ * d⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e, hdk] at hlZ
      have h : ⁅l, d⁆ * ⁅l, v⁆ * ⁅l, v⁆⁻¹ ∈ Z := Z.mul_mem hlZ (Z.inv_mem hlv)
      rwa [mul_inv_cancel_right] at h
    exact V.mul_mem hdV hv

end HS9

end CFSG.RankThree.GF2n.Stroth80
