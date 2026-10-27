module

public import CFSG.Monster.B.Classical.UnitarySixInvolutions
public import Mathlib.LinearAlgebra.Projectivization.Action
import all CFSG.Fischer.F4
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open scoped LinearAlgebra.Projectivization

noncomputable instance instMulActionSU6 : MulAction (SU frobeniusF4 6) V := inferInstance

noncomputable instance instDistribMulActionSU6 : DistribMulAction (SU frobeniusF4 6) V :=
  inferInstance

instance instSMulCommClassSU6 : SMulCommClass (SU frobeniusF4 6) F4 V := inferInstance

theorem smul_def (g : SU frobeniusF4 6) (v : V) :
    g • v = ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v :=
  rfl

theorem herm_smul_smul (g : SU frobeniusF4 6) (v w : V) : herm (g • v) (g • w) = herm v w :=
  isIsometry_of_mem g v w

@[expose] def IsIsoPt (p : ℙ F4 V) : Prop := herm p.rep p.rep = 0

@[expose] def Orth (p q : ℙ F4 V) : Prop := herm p.rep q.rep = 0

theorem herm_units_smul (a b : F4ˣ) (v w : V) :
    herm (a • v) (b • w) = (a : F4) * bar b * herm v w := by
  rw [Units.smul_def, Units.smul_def, herm_smul_left, herm_smul_right, mul_assoc]

theorem orth_mk {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    Orth (Projectivization.mk F4 v hv) (Projectivization.mk F4 w hw) ↔ herm v w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep F4 w hw
  rw [Orth, ← ha, ← hb, herm_units_smul]
  have h1 : (a : F4) ≠ 0 := a.ne_zero
  have h2 : bar (b : F4) ≠ 0 := fun h => b.ne_zero (bar_eq_zero_iff.mp h)
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h1 h2)
  · intro h
    rw [h, mul_zero]

theorem isIsoPt_mk {v : V} (hv : v ≠ 0) :
    IsIsoPt (Projectivization.mk F4 v hv) ↔ herm v v = 0 :=
  orth_mk hv hv

theorem orth_comm {p q : ℙ F4 V} (h : Orth p q) : Orth q p := herm_eq_zero_comm h

theorem smul_mk (g : SU frobeniusF4 6) {v : V} (hv : v ≠ 0) :
    g • Projectivization.mk F4 v hv =
      Projectivization.mk F4 (g • v) ((smul_ne_zero_iff_ne g).mpr hv) :=
  Projectivization.smul_mk g hv

theorem orth_smul_iff (g : SU frobeniusF4 6) (p q : ℙ F4 V) : Orth (g • p) (g • q) ↔ Orth p q := by
  induction p using Projectivization.ind with
  | h v hv =>
  induction q using Projectivization.ind with
  | h w hw =>
  rw [smul_mk, smul_mk, orth_mk, orth_mk, herm_smul_smul]

@[expose] noncomputable def isoPts : SubMulAction (SU frobeniusF4 6) (ℙ F4 V) where
  carrier := {p | IsIsoPt p}
  smul_mem' g p hp := (orth_smul_iff g p p).mpr hp

abbrev IsoPt : Type := ↥isoPts

theorem isIsoPt_of (p : IsoPt) : herm p.1.rep p.1.rep = 0 := p.2

@[expose] noncomputable def pt (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0) : IsoPt :=
  ⟨Projectivization.mk F4 v hv0, (isIsoPt_mk hv0).mpr hv⟩

theorem IsoPt.ind {P : IsoPt → Prop} (h : ∀ (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0),
    P (pt v hv0 hv)) (p : IsoPt) : P p := by
  obtain ⟨p, hp⟩ := p
  induction p using Projectivization.ind with
  | h v hv0 => exact h v hv0 ((isIsoPt_mk hv0).mp hp)

theorem pt_rep (p : IsoPt) : pt p.1.rep p.1.rep_nonzero (isIsoPt_of p) = p :=
  Subtype.ext (Projectivization.mk_rep _)

theorem pt_eq_pt_iff {v w : V} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : herm v v = 0)
    (hw : herm w w = 0) : pt v hv0 hv = pt w hw0 hw ↔ ∃ c : F4, c • w = v := by
  rw [← Projectivization.mk_eq_mk_iff' F4 v w hv0 hw0]
  exact Subtype.ext_iff

theorem pt_smul_eq {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) {c : F4}
    (hcv0 : c • v ≠ 0) (hcv : herm (c • v) (c • v) = 0) : pt (c • v) hcv0 hcv = pt v hv0 hv :=
  (pt_eq_pt_iff _ _ _ _).mpr ⟨c, rfl⟩

theorem smul_pt (g : SU frobeniusF4 6) {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    g • pt v hv0 hv = pt (g • v) ((smul_ne_zero_iff_ne g).mpr hv0)
      (by rw [herm_smul_smul]; exact hv) :=
  rfl

theorem orth_pt {v w : V} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : herm v v = 0) (hw : herm w w = 0) :
    Orth (pt v hv0 hv).1 (pt w hw0 hw).1 ↔ herm v w = 0 :=
  orth_mk hv0 hw0

@[expose] noncomputable def stdPt (i : Fin 6) : IsoPt :=
  pt (Pi.single i 1) (by simp) (herm_single_self i)

@[expose] def isoGraph : SimpleGraph IsoPt where
  Adj p q := p ≠ q ∧ Orth p.1 q.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, orth_comm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem isoGraph_adj {p q : IsoPt} : isoGraph.Adj p q ↔ p ≠ q ∧ Orth p.1 q.1 := Iff.rfl

theorem isoGraph_adj_smul (g : SU frobeniusF4 6) (p q : IsoPt) :
    isoGraph.Adj (g • p) (g • q) ↔ isoGraph.Adj p q := by
  rw [isoGraph_adj, isoGraph_adj, SubMulAction.val_smul, SubMulAction.val_smul, orth_smul_iff,
    (MulAction.injective g).ne_iff]

theorem exists_SU_smul_stdPt_of_frame {e : Fin 6 → V} (he : IsFrame e) :
    ∃ g : SU frobeniusF4 6, ∀ i (h0 : e i ≠ 0) (hi : herm (e i) (e i) = 0),
      g • stdPt i = pt (e i) h0 hi := by
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he
  refine ⟨g, fun i h0 hi => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hg i
  rw [stdPt, smul_pt]
  refine (pt_eq_pt_iff _ _ _ _).mpr ⟨c, ?_⟩
  rw [smul_def, hc]

theorem frame_ne_zero {e : Fin 6 → V} (he : IsFrame e) (i : Fin 6) : e i ≠ 0 := by
  intro h
  have := he i (Fin.rev i)
  rw [h, herm_zero_left] at this
  simp at this

theorem frame_iso {e : Fin 6 → V} (he : IsFrame e) (i : Fin 6) : herm (e i) (e i) = 0 := by
  rw [he i i]
  have : ∀ i : Fin 6, i ≠ Fin.rev i := by decide
  simp [this i]

theorem exists_SU_smul_stdPt (p : IsoPt) : ∃ g : SU frobeniusF4 6, g • stdPt 0 = p := by
  obtain ⟨e, he, he0⟩ := exists_frame_of_isotropic p.1.rep_nonzero (isIsoPt_of p)
  obtain ⟨g, hg⟩ := exists_SU_smul_stdPt_of_frame he
  refine ⟨g, ?_⟩
  rw [hg 0 (frame_ne_zero he 0) (frame_iso he 0)]
  conv_rhs => rw [← pt_rep p]
  exact (pt_eq_pt_iff _ _ _ _).mpr ⟨1, by rw [one_smul, he0]⟩

theorem exists_SU_smul_adj (p q : IsoPt) (hpq : isoGraph.Adj p q) :
    ∃ g : SU frobeniusF4 6, g • stdPt 0 = p ∧ g • stdPt 1 = q := by
  rw [isoGraph_adj] at hpq
  have hne : p.1 ≠ q.1 := fun h => hpq.1 (Subtype.ext h)
  have hli : LinearIndependent F4 ![p.1.rep, q.1.rep] :=
    Projectivization.linearIndependent_pair_iff_ne.mpr hne
  obtain ⟨e, he, he0, he1⟩ := exists_frame_of_pair hli (isIsoPt_of p) (isIsoPt_of q) hpq.2
  obtain ⟨g, hg⟩ := exists_SU_smul_stdPt_of_frame he
  refine ⟨g, ?_, ?_⟩
  · rw [hg 0 (frame_ne_zero he 0) (frame_iso he 0)]
    conv_rhs => rw [← pt_rep p]
    exact (pt_eq_pt_iff _ _ _ _).mpr ⟨1, by rw [one_smul, he0]⟩
  · rw [hg 1 (frame_ne_zero he 1) (frame_iso he 1)]
    conv_rhs => rw [← pt_rep q]
    exact (pt_eq_pt_iff _ _ _ _).mpr ⟨1, by rw [one_smul, he1]⟩

theorem bar_inv (a : F4) : bar a⁻¹ = (bar a)⁻¹ := by
  revert a; decide

theorem exists_SU_smul_nonadj (p q : IsoPt) (hpq : p ≠ q) (hna : ¬ isoGraph.Adj p q) :
    ∃ g : SU frobeniusF4 6, g • stdPt 0 = p ∧ g • stdPt 5 = q := by
  have hc : herm p.1.rep q.1.rep ≠ 0 := fun h => hna (isoGraph_adj.mpr ⟨hpq, h⟩)
  set c := herm p.1.rep q.1.rep with hcdef
  set w := (bar c)⁻¹ • q.1.rep with hw
  have hbc : bar c ≠ 0 := fun h => hc (bar_eq_zero_iff.mp h)
  have hvw : herm p.1.rep w = 1 := by
    rw [hw, herm_smul_right, ← hcdef, bar_inv, bar_bar, inv_mul_cancel₀ hc]
  have hww : herm w w = 0 := by
    rw [hw, herm_smul_left, herm_smul_right, isIsoPt_of q, mul_zero, mul_zero]
  obtain ⟨e, he, he0, he5⟩ := exists_frame_of_hyperbolic (isIsoPt_of p) hww hvw
  obtain ⟨g, hg⟩ := exists_SU_smul_stdPt_of_frame he
  refine ⟨g, ?_, ?_⟩
  · rw [hg 0 (frame_ne_zero he 0) (frame_iso he 0)]
    conv_rhs => rw [← pt_rep p]
    exact (pt_eq_pt_iff _ _ _ _).mpr ⟨1, by rw [one_smul, he0]⟩
  · rw [hg 5 (frame_ne_zero he 5) (frame_iso he 5)]
    conv_rhs => rw [← pt_rep q]
    exact (pt_eq_pt_iff _ _ _ _).mpr ⟨(bar c)⁻¹, by rw [he5, hw]⟩

end CFSG.Monster.B.Classical.UnitarySix
