module

public import CFSG.Quasithin.Background.SmithB51SL3G

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section XQ

variable {K : Type} [Field K]

@[expose] noncomputable def xQ (w : Fin 3 → K) : ↥(StatedSL 3 K) :=
  xW (w - Pi.single 2 (w 2)) (by simp)

theorem slAct_xQ (w v : Fin 3 → K) :
    slAct (xQ w) v = v + v 2 • (w - Pi.single 2 (w 2)) :=
  slAct_xW _ _ v

theorem xQ_mem (w : Fin 3 → K) : xQ w ∈ axisSub (stdAxis K) := xW_mem _ _

theorem xQ_eq {w : Fin 3 → K} (hw : w 2 = 0) : xQ w = xW w hw := by
  apply ext_slAct
  intro v
  rw [slAct_xQ, slAct_xW, hw, Pi.single_zero, sub_zero]

theorem xQ_add (w w' : Fin 3 → K) : xQ (w + w') = xQ w * xQ w' := by
  apply ext_slAct
  intro v
  rw [slAct_mul, slAct_xQ, slAct_xQ, slAct_xQ]
  have h2 : ((v + v 2 • (w' - Pi.single 2 (w' 2)) : Fin 3 → K)) 2 = v 2 := by simp
  rw [h2, Pi.add_apply, Pi.single_add]
  module

theorem xQ_eq_one {w : Fin 3 → K} (h : w - Pi.single 2 (w 2) = 0) : xQ w = 1 := by
  apply ext_slAct
  intro v
  rw [slAct_xQ, h, smul_zero, add_zero, slAct_one]

theorem xQ_zero : xQ (0 : Fin 3 → K) = 1 := by
  apply ext_slAct
  intro v
  rw [slAct_xQ, slAct_one]
  simp

theorem slAct_single_two {g : ↥(StatedSL 3 K)} (hg : g ∈ levi K) (c : K) :
    slAct g (Pi.single 2 c) = Pi.single 2 c := by
  have h : (Pi.single 2 c : Fin 3 → K) = c • Pi.single 2 1 := by
    funext k
    simp [Pi.single_apply]
  rw [h, slAct_smul, hg.2]

theorem conj_xQ {g : ↥(StatedSL 3 K)} (hg : g ∈ levi K) (w : Fin 3 → K) :
    g * xQ w * g⁻¹ = xQ (slAct g w) := by
  rw [xQ, conj_xW hg]
  apply ext_slAct
  intro v
  rw [slAct_xW, slAct_xQ, slAct_sub, hg.1 w, slAct_single_two hg]

end XQ

section QC

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

@[expose] noncomputable def qc (π : ↥(StatedSL 3 K) →* ↥L) (v : V) (w : Fin 3 → K) : V :=
  ((π (xQ w) : ↥L) : MulAut V) v * v⁻¹

theorem qc_mul (π : ↥(StatedSL 3 K) →* ↥L) (v v' : V) (w : Fin 3 → K) :
    qc π (v * v') w = qc π v w * qc π v' w := by
  unfold qc
  rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem qc_inv (π : ↥(StatedSL 3 K) →* ↥L) (v : V) (w : Fin 3 → K) :
    qc π v⁻¹ w = (qc π v w)⁻¹ := by
  unfold qc
  rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]

theorem qc_one (π : ↥(StatedSL 3 K) →* ↥L) (w : Fin 3 → K) : qc π (1 : V) w = 1 := by
  unfold qc
  rw [map_one, inv_one, mul_one]

theorem qc_zero (π : ↥(StatedSL 3 K) →* ↥L) (v : V) : qc π v (0 : Fin 3 → K) = 1 := by
  unfold qc
  rw [xQ_zero, map_one, Subgroup.coe_one, MulAut.one_apply, mul_inv_cancel]

theorem qc_mem_fixV {π : ↥(StatedSL 3 K) →* ↥L} {A : Subgroup (MulAut V)}
    (hA : ∀ w : Fin 3 → K, ((π (xQ w) : ↥L) : MulAut V) ∈ A) (hquad : IsQuadratic A) (v : V)
    (w : Fin 3 → K) : qc π v w ∈ fixV A :=
  hquad (Subgroup.subset_closure ⟨_, hA w, v, rfl⟩)

theorem qc_add {π : ↥(StatedSL 3 K) →* ↥L} {A : Subgroup (MulAut V)}
    (hA : ∀ w : Fin 3 → K, ((π (xQ w) : ↥L) : MulAut V) ∈ A) (hquad : IsQuadratic A) (v : V)
    (w w' : Fin 3 → K) : qc π v (w + w') = qc π v w * qc π v w' := by
  have h1 : ((π (xQ w) : ↥L) : MulAut V) (qc π v w') = qc π v w' :=
    qc_mem_fixV hA hquad v w' _ (hA w)
  have h2 : ((π (xQ w') : ↥L) : MulAut V) v = qc π v w' * v := by
    unfold qc
    group
  show ((π (xQ (w + w')) : ↥L) : MulAut V) v * v⁻¹ = qc π v w * qc π v w'
  rw [xQ_add, map_mul, Subgroup.coe_mul, MulAut.mul_apply, h2, map_mul, h1]
  unfold qc
  simp only [mul_comm, mul_left_comm]

theorem qc_neg {π : ↥(StatedSL 3 K) →* ↥L} {A : Subgroup (MulAut V)}
    (hA : ∀ w : Fin 3 → K, ((π (xQ w) : ↥L) : MulAut V) ∈ A) (hquad : IsQuadratic A) (v : V)
    (w : Fin 3 → K) : qc π v (-w) = (qc π v w)⁻¹ := by
  have h := qc_add hA hquad v w (-w)
  rw [add_neg_cancel, qc_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

@[expose] noncomputable def qcRange {π : ↥(StatedSL 3 K) →* ↥L} {A : Subgroup (MulAut V)}
    (hA : ∀ w : Fin 3 → K, ((π (xQ w) : ↥L) : MulAut V) ∈ A) (hquad : IsQuadratic A) (v : V) :
    Subgroup V where
  carrier := {x | ∃ w, qc π v w = x}
  one_mem' := ⟨0, qc_zero π v⟩
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', qc_add hA hquad v w w'⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨-w, qc_neg hA hquad v w⟩

@[expose] noncomputable def leviLifts (π : ↥(StatedSL 3 K) →* ↥L) (W X : Subgroup V) :
    Subgroup V where
  carrier := {v | v ∈ W ∧ (∀ γ ∈ levi K, ((π γ : ↥L) : MulAut V) v = v) ∧
    ∀ w : Fin 3 → K, w 2 = 0 → qc π v w ∈ X}
  one_mem' := ⟨W.one_mem, fun γ _ => map_one _, fun w _ => by rw [qc_one]; exact X.one_mem⟩
  mul_mem' := by
    rintro v v' ⟨hv, hvf, hvX⟩ ⟨hv', hv'f, hv'X⟩
    refine ⟨W.mul_mem hv hv', fun γ hγ => by rw [map_mul, hvf γ hγ, hv'f γ hγ],
      fun w hw => ?_⟩
    rw [qc_mul]
    exact X.mul_mem (hvX w hw) (hv'X w hw)
  inv_mem' := by
    rintro v ⟨hv, hvf, hvX⟩
    refine ⟨W.inv_mem hv, fun γ hγ => by rw [map_inv, hvf γ hγ], fun w hw => ?_⟩
    rw [qc_inv]
    exact X.inv_mem (hvX w hw)

theorem qc_levi (π : ↥(StatedSL 3 K) →* ↥L) {g : ↥(StatedSL 3 K)} (hg : g ∈ levi K) {v : V}
    (hv : ((π g : ↥L) : MulAut V) v = v) (w : Fin 3 → K) :
    ((π g : ↥L) : MulAut V) (qc π v w) = qc π v (slAct g w) := by
  have hc : ((π (xQ (slAct g w)) : ↥L) : MulAut V) * ((π g : ↥L) : MulAut V) =
      ((π g : ↥L) : MulAut V) * ((π (xQ w) : ↥L) : MulAut V) := by
    rw [← conj_xQ hg, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    group
  unfold qc
  rw [map_mul, map_inv, hv, ← MulAut.mul_apply, ← hc, MulAut.mul_apply, hv]

theorem NatSec.qc_mem {W U : Subgroup V} (c : NatSec L W U K) (hLW : L ≤ stabSub W) (v : ↥W)
    (w : Fin 3 → K) : qc c.π v w ∈ W :=
  W.mul_mem (((hLW (c.π (xQ w)).2) v).2 v.2) (W.inv_mem v.2)

theorem NatSec.toAdd_f_qc {W U : Subgroup V} (c : NatSec L W U K) (hLW : L ≤ stabSub W)
    (v : ↥W) (w : Fin 3 → K) :
    Multiplicative.toAdd (c.f ⟨qc c.π v w, c.qc_mem hLW v w⟩) =
      Multiplicative.toAdd (c.f v) 2 • (w - Pi.single 2 (w 2)) := by
  have hv : ((c.π (xQ w) : ↥L) : MulAut V) v ∈ W := ((hLW (c.π (xQ w)).2) v).2 v.2
  have e1 : (⟨qc c.π v w, c.qc_mem hLW v w⟩ : ↥W) = ⟨_, hv⟩ * v⁻¹ := rfl
  rw [e1, map_mul, map_inv, c.hfe _ v hv, toAdd_mul, toAdd_inv]
  show slAct (xQ w) _ + -_ = _
  rw [slAct_xQ]
  abel

end QC

end B5

end CFSG.Quasithin
