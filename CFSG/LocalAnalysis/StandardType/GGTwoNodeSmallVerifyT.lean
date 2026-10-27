module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallWord
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRefl

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pwt_vec_eq_natCast_ent (P : Pt) (v : Vec) (j : Fin P.D) :
    P.vec v j = ((P.ent v j : ℕ) : ZMod P.p) := by
  simp only [Pt.vec, Pt.ent]
  rw [ZMod.natCast_mod]

private lemma pwt_vec_ne_zero_of_vecNZ (P : Pt) [Fact P.p.Prime] {v : Vec}
    (h : P.vecNZ v = true) : P.vec v ≠ 0 := by
  haveI : NeZero P.p := ⟨(Fact.out (p := P.p.Prime)).ne_zero⟩
  intro hv
  rw [Pt.vecNZ, List.any_eq_true] at h
  obtain ⟨j, hjmem, hjnz⟩ := h
  rw [List.mem_range] at hjmem
  have hcast : ((v.getD j 0 : ℕ) : ZMod P.p) = 0 := by
    have h0 := congrFun hv ⟨j, hjmem⟩
    simpa [Pt.vec] using h0
  have hval : (v.getD j 0 : ZMod P.p).val = 0 := by rw [hcast, ZMod.val_zero]
  rw [ZMod.val_natCast] at hval
  have hne : P.ent v j ≠ 0 := by simpa using hjnz
  exact hne (by simpa [Pt.ent] using hval)

private lemma pwt_sum_single {p D : ℕ} (w : Fin D → ZMod p) :
    (∑ i : Fin D, w i • Pi.single i (1 : ZMod p)) = w := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · exact fun hbj => hb hbj.symm
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private def pwt_phi (P : Pt) (φ : Vec) : Module.Dual (ZMod P.p) P.V :=
  { toFun := fun w => P.dot (P.vec φ) w
    map_add' := by
      intro x y
      simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp only [Pt.dot, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [RingHom.id_apply]
      ring }

private lemma pwt_phi_apply (P : Pt) (φ : Vec) (w : P.V) :
    pwt_phi P φ w = P.dot (P.vec φ) w := rfl

private lemma pwt_phi_unit (P : Pt) (φ : Vec) (i : Fin P.D) :
    pwt_phi P φ (Pi.single i (1 : ZMod P.p)) = ((P.ent φ i : ℕ) : ZMod P.p) := by
  rw [pwt_phi_apply]
  simp only [Pt.dot, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [pwt_vec_eq_natCast_ent]
  · intro b _ hb
    rw [if_neg hb]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma pwt_linear_ext {p D : ℕ} [Fact p.Prime]
    (f : (Fin D → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p))
    (u : Fin D → ZMod p) (φ : Module.Dual (ZMod p) (Fin D → ZMod p))
    (h : ∀ i : Fin D, f (Pi.single i (1 : ZMod p)) = Pi.single i (1 : ZMod p) + φ (Pi.single i (1 : ZMod p)) • u)
    (w : Fin D → ZMod p) : f w = w + φ w • u := by
  calc
    f w = f (∑ i : Fin D, w i • Pi.single i (1 : ZMod p)) := by rw [pwt_sum_single]
    _ = ∑ i : Fin D, w i • f (Pi.single i (1 : ZMod p)) := by
          rw [map_sum]
          simp only [map_smul]
    _ = ∑ i : Fin D, w i • (Pi.single i (1 : ZMod p) + φ (Pi.single i (1 : ZMod p)) • u) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h i]
    _ = (∑ i : Fin D, w i • Pi.single i (1 : ZMod p))
          + ∑ i : Fin D, w i • (φ (Pi.single i (1 : ZMod p)) • u) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_add]
    _ = w + ∑ i : Fin D, w i • (φ (Pi.single i (1 : ZMod p)) • u) := by
          rw [pwt_sum_single]
    _ = w + ∑ i : Fin D, (w i * φ (Pi.single i (1 : ZMod p))) • u := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul]
    _ = w + (∑ i : Fin D, w i * φ (Pi.single i (1 : ZMod p))) • u := by
          rw [Finset.sum_smul]
    _ = w + φ w • u := by
          congr 1
          have hsum : (∑ i : Fin D, w i * φ (Pi.single i (1 : ZMod p))) = φ w := by
            conv_rhs => rw [← pwt_sum_single w]
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
          rw [hsum]

theorem verifyT_sound {P : Pt} [Fact P.p.Prime] (hwf : P.WF) {t : TWit} (h : verifyT P t = true) :
    ∃ g ∈ P.group, IsTransv g := by
  simp only [verifyT, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hwordOK, huNZ, hφNZ, hdot0, hall⟩ := h
  have hdot : P.dotv t.φ t.u = 0 := by simpa using hdot0
  obtain ⟨γ, hγmem, hγ⟩ := Pt.applyWord_spec P hwf t.word hwordOK
  have hcoord : ∀ (i j : ℕ), i < P.D → j < P.D →
      P.ent (P.applyWord t.word (P.unit i)) j
        = ((if i = j then 1 else 0) + P.ent t.φ i * P.ent t.u j) % P.p := by
    intro i j hi hj
    have h1 := (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)
    have h2 := (List.all_eq_true.mp h1) j (List.mem_range.mpr hj)
    simpa using h2
  have hbase : ∀ i : Fin P.D,
      γ (Pi.single i (1 : ZMod P.p))
        = Pi.single i (1 : ZMod P.p)
            + pwt_phi P t.φ (Pi.single i (1 : ZMod P.p)) • P.vec t.u := by
    intro i
    have hγi := hγ (P.unit i)
    rw [Pt.vec_unit P i] at hγi
    rw [hγi]
    funext j
    rw [pwt_vec_eq_natCast_ent]
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, pwt_phi_unit,
      pwt_vec_eq_natCast_ent]
    rw [hcoord i.val j.val i.isLt j.isLt]
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
    have hif : (((if (i : ℕ) = (j : ℕ) then 1 else 0 : ℕ) : ZMod P.p))
        = (if j = i then (1 : ZMod P.p) else 0) := by
      by_cases hij : i = j
      · subst hij
        simp
      · have hnat : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
        have hji : ¬ j = i := fun hji => hij hji.symm
        rw [if_neg hnat, if_neg hji]
        simp
    rw [hif]
  have hlin : ∀ w : P.V, γ w = w + pwt_phi P t.φ w • P.vec t.u :=
    pwt_linear_ext γ.toLinearMap (P.vec t.u) (pwt_phi P t.φ) hbase
  have hu : P.vec t.u ≠ 0 := pwt_vec_ne_zero_of_vecNZ P huNZ
  have hφ : pwt_phi P t.φ ≠ 0 := by
    intro hφ0
    apply pwt_vec_ne_zero_of_vecNZ (P := P) (v := t.φ) hφNZ
    funext i
    rw [pwt_vec_eq_natCast_ent]
    have h0 := congrArg (fun f : Module.Dual (ZMod P.p) P.V =>
      f (Pi.single i (1 : ZMod P.p))) hφ0
    simpa [pwt_phi_unit] using h0
  have hφu : pwt_phi P t.φ (P.vec t.u) = 0 := by
    rw [pwt_phi_apply]
    have hd := Pt.dotv_spec P t.φ t.u
    rw [hdot] at hd
    simpa using hd.symm
  exact ⟨γ, hγmem, isTransv_of_witness γ (P.vec t.u) (pwt_phi P t.φ) hlin hu hφ hφu⟩

end CFSG.TwoNodeSmall
