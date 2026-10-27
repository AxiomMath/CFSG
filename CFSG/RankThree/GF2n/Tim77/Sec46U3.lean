module

public import CFSG.RankThree.GF2n.Tim77.Sec41
public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.T75N CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

def invComm {L : Type} [Group L] (x : L) : Subgroup L :=
  Subgroup.closure {y | orderOf y = 2 ∧ Commute y x}

theorem mem_invComm {L : Type} [Group L] {x y : L} (hy : orderOf y = 2) (hc : Commute y x) :
    y ∈ invComm x :=
  Subgroup.subset_closure ⟨hy, hc⟩

theorem invComm_sq {L : Type} [Group L] [Finite L] (hB : IsBenderGroup L) {x : L}
    (hx : orderOf x = 2) : ∀ y ∈ invComm x, y * y = 1 := by
  have hel : CFSG.Open.IsElemAbelian 2 (invComm x) := by
    apply sec41_isElemAbelian_closure
    · rintro y ⟨hy2, hyx⟩ y' ⟨hy2', hy'x⟩
      exact (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hB hy2 hx hy2' hyx
        hy'x.symm).eq
    · rintro y ⟨hy2, -⟩
      rw [← sq, ← hy2]
      exact pow_orderOf_eq_one y
  intro y hy
  exact sec41_invol hel hy

theorem invComm_conj {L : Type} [Group L] (g x : L) :
    invComm (g * x * g⁻¹) = (invComm x).map (MulAut.conj g).toMonoidHom := by
  unfold invComm
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨hz2, hzc⟩
    refine ⟨g⁻¹ * z * g, ⟨?_, ?_⟩, ?_⟩
    · have : orderOf ((MulAut.conj g).toMonoidHom (g⁻¹ * z * g)) = orderOf (g⁻¹ * z * g) :=
        orderOf_injective _ (MulAut.conj g).injective _
      have e : (MulAut.conj g).toMonoidHom (g⁻¹ * z * g) = z := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at this
      rw [← this, hz2]
    · have h := hzc.eq
      show g⁻¹ * z * g * x = x * (g⁻¹ * z * g)
      calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [h]
        _ = x * (g⁻¹ * z * g) := by group
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨w, ⟨hw2, hwc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [orderOf_injective _ (MulAut.conj g).injective, hw2]
    · have h := hwc.eq
      have e1 : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := rfl
      rw [e1]
      show g * w * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
        _ = g * (x * w) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group

theorem u3_two_roots_ne_top {L : Type} [Group L] [Finite L] {m : ℕ} (hm : 2 ≤ m)
    (e : L ≃* PSU3Model m) {u v : L} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    invComm u ⊔ invComm v ≠ ⊤ := by
  have hB : IsBenderGroup L := IsBenderGroup.isPSU3 m hm e
  obtain ⟨g, hg⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB hu hv)
  have hmap : invComm v = (invComm u).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact invComm_conj g u
  rw [hmap]
  exact sup_conj_ne_top_of_psu3 hm e (invComm u) (invComm_sq hB hu) g

end CFSG.RankThree.GF2n.Tim77
