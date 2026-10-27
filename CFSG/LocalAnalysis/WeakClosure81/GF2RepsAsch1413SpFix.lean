module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Fix

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

@[expose] def spIota {Q : Type} [Group Q] {L : Subgroup Q} {K : Type} [Field K]
    (e : ↥L ≃* StatedProj (StatedSp 2 K)) : StatedProj (StatedSp 2 K) →* Q :=
  L.subtype.comp e.symm.toMonoidHom

theorem asch1413_sp4_fixed_point {Q : Type} [Group Q] [Finite Q] {L A : Subgroup Q}
    (hLn : L.Normal) {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (e : ↥L ≃* StatedProj (StatedSp 2 K)) (hA : Nat.card A = 4)
    (hAe : IsElemAbelian 2 A) :
    ∃ e' : ↥L ≃* StatedProj (StatedSp 2 K),
      (∀ x : ↥L, IsConj (u1 K) (e' x) ↔ IsConj (u1 K) (e x)) ∧
        ∀ a ∈ A, a * spIota e' (u1 K) = spIota e' (u1 K) * a := by
  let P := StatedProj (StatedSp 2 K)
  let D' : Set Q := {x | ∃ hx : x ∈ L, IsConj (u1 K) (e ⟨x, hx⟩)}
  have hD' : ∀ a ∈ A, ∀ d ∈ D', a * d * a⁻¹ ∈ D' := by
    intro a _ d hd
    rcases hd with ⟨hdL, hdconj⟩
    refine ⟨hLn.conj_mem d hdL a, ?_⟩
    have hmem : (⟨a * d * a⁻¹, hLn.conj_mem d hdL a⟩ : ↥L) =
        (MulAut.conjNormal a) ⟨d, hdL⟩ := by
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    have hcongr : e ⟨a * d * a⁻¹, hLn.conj_mem d hdL a⟩ =
        (MulAut.congr e (MulAut.conjNormal a)) (e ⟨d, hdL⟩) := by
      rw [show (MulAut.congr e (MulAut.conjNormal a)) (e ⟨d, hdL⟩) =
        e ((MulAut.conjNormal a) ⟨d, hdL⟩) from by
          simp [MulAut.congr, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]]
      rw [hmem]
    rw [hcongr]
    exact psp4_conj_class_invariant hodd (MulAut.congr e (MulAut.conjNormal a)) hdconj
  have hcard : Nat.card D' = Nat.card {x : P // IsConj (u1 K) x} := by
    apply Nat.card_congr
    refine
      { toFun := fun d => ⟨e ⟨d.1, d.2.1⟩, d.2.2⟩
        invFun := fun x => ⟨↑(e.symm x.1), (e.symm x.1).2, by simpa using x.2⟩
        left_inv := fun d => by simp
        right_inv := fun x => by simp }
  have hodd' : Odd (Nat.card D') := by
    rw [hcard]
    exact psp4_card_conj_u1_odd hodd h5
  have hApg : IsPGroup 2 ↥A := by
    apply IsPGroup.of_card (n := 2)
    rw [hA]
    norm_num
  obtain ⟨z, hzD, hzfix⟩ := a1413_exists_fixed_of_odd hApg hD' hodd'
  rcases hzD with ⟨hzL, hzconj⟩
  rcases (isConj_iff.mp hzconj) with ⟨c, hc⟩
  let e' : ↥L ≃* P := e.trans (MulAut.conj c⁻¹)
  refine ⟨e', ?_, ?_⟩
  · intro x
    have he'x : e' x = c⁻¹ * e x * c := by
      simp [e', MulEquiv.trans_apply, MulAut.conj_apply]
    rw [he'x]
    constructor
    · intro h
      rcases (isConj_iff.mp h) with ⟨d, hd⟩
      refine isConj_iff.mpr ⟨c * d, ?_⟩
      calc
        c * d * u1 K * (c * d)⁻¹ = c * (d * u1 K * d⁻¹) * c⁻¹ := by group
        _ = c * (c⁻¹ * e x * c) * c⁻¹ := by rw [hd]
        _ = e x := by group
    · intro h
      rcases (isConj_iff.mp h) with ⟨d, hd⟩
      refine isConj_iff.mpr ⟨c⁻¹ * d, ?_⟩
      calc
        (c⁻¹ * d) * u1 K * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * u1 K * d⁻¹) * c := by group
        _ = c⁻¹ * e x * c := by rw [hd]
  · intro a ha
    have hsp : spIota e' (u1 K) = z := by
      have hsymm : e'.symm (u1 K) = ⟨z, hzL⟩ := by
        apply e'.injective
        rw [MulEquiv.apply_symm_apply]
        symm
        simp only [e', MulEquiv.trans_apply, MulAut.conj_apply]
        rw [← hc]
        group
      change L.subtype (e'.symm (u1 K)) = z
      rw [hsymm]
      rfl
    rw [hsp]
    calc
      a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [hzfix a ha]

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
