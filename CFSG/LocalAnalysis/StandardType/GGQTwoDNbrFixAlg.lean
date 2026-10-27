module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma plnf_dBasis_apply (m : ℕ) (j i : Fin m) :
    dBasis m j i = if i = j then 1 else 0 := by
  simp [dBasis, Pi.single_apply]

private lemma plnf_coord_left_basis (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (j : Fin m) :
    dTau m ε a b (dBasis m j) a = (if ε then (-1 : ZMod 3) else 1) * dBasis m j b := by
  by_cases hja : j = a
  · rw [hja, dTau_apply_left m ε hab, Pi.smul_apply, plnf_dBasis_apply, plnf_dBasis_apply]
    simp [hab, hab.symm]
  · by_cases hjb : j = b
    · rw [hjb, dTau_apply_right m ε hab, Pi.smul_apply, plnf_dBasis_apply, plnf_dBasis_apply]
      simp
    · rw [dTau_apply_of_ne m ε hja hjb, plnf_dBasis_apply, plnf_dBasis_apply]
      simp [Ne.symm hja, Ne.symm hjb]

private lemma plnf_coord_of_ne_basis (m : ℕ) (ε : Bool) {a b i : Fin m} (hab : a ≠ b)
    (hia : i ≠ a) (hib : i ≠ b) (j : Fin m) :
    dTau m ε a b (dBasis m j) i = dBasis m j i := by
  by_cases hja : j = a
  · rw [hja, dTau_apply_left m ε hab, Pi.smul_apply, plnf_dBasis_apply, plnf_dBasis_apply]
    simp [hia, hib]
  · by_cases hjb : j = b
    · rw [hjb, dTau_apply_right m ε hab, Pi.smul_apply, plnf_dBasis_apply, plnf_dBasis_apply]
      simp [hia, hib]
    · rw [dTau_apply_of_ne m ε hja hjb]

theorem dTau_coord_left (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (v : DVec m) :
    dTau m ε a b v a = (if ε then (-1 : ZMod 3) else 1) * v b := by
  have h : (LinearMap.proj a : DVec m →ₗ[ZMod 3] ZMod 3) ∘ₗ
      (dTau m ε a b : DVec m →ₗ[ZMod 3] DVec m) =
      (if ε then (-1 : ZMod 3) else 1) • (LinearMap.proj b : DVec m →ₗ[ZMod 3] ZMod 3) := by
    refine (dBasis m).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact plnf_coord_left_basis m ε hab j
  exact congrArg (fun f => f v) h

theorem dTau_coord_right (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (v : DVec m) :
    dTau m ε a b v b = (if ε then (-1 : ZMod 3) else 1) * v a := by
  rw [dTau_symm m ε a b]
  exact dTau_coord_left m ε hab.symm v

theorem dTau_coord_of_ne (m : ℕ) (ε : Bool) {a b i : Fin m} (hab : a ≠ b) (hia : i ≠ a)
    (hib : i ≠ b) (v : DVec m) : dTau m ε a b v i = v i := by
  have h : (LinearMap.proj i : DVec m →ₗ[ZMod 3] ZMod 3) ∘ₗ
      (dTau m ε a b : DVec m →ₗ[ZMod 3] DVec m) =
      (LinearMap.proj i : DVec m →ₗ[ZMod 3] ZMod 3) := by
    refine (dBasis m).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply]
    exact plnf_coord_of_ne_basis m ε hab hia hib j
  exact congrArg (fun f => f v) h

theorem dTau_coord_of_fix (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) {v : DVec m}
    (hv : dTau m ε a b v = v) :
    v a = (if ε then (-1 : ZMod 3) else 1) * v b ∧
      v b = (if ε then (-1 : ZMod 3) else 1) * v a := by
  have h1 := dTau_coord_left m ε hab v
  have h2 := dTau_coord_right m ε hab v
  rw [hv] at h1 h2
  exact ⟨h1, h2⟩

private lemma plnf_sg_mul_self (ε : Bool) :
    (if ε then (-1 : ZMod 3) else 1) * (if ε then (-1 : ZMod 3) else 1) = 1 := by
  cases ε <;> decide

theorem dTau_mul_self (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (v : DVec m) :
    dTau m ε a b (dTau m ε a b v) = v := by
  funext i
  by_cases hia : i = a
  · rw [hia, dTau_coord_left m ε hab, dTau_coord_right m ε hab, ← mul_assoc,
      plnf_sg_mul_self, one_mul]
  · by_cases hib : i = b
    · rw [hib, dTau_coord_right m ε hab, dTau_coord_left m ε hab, ← mul_assoc,
        plnf_sg_mul_self, one_mul]
    · rw [dTau_coord_of_ne m ε hab hia hib, dTau_coord_of_ne m ε hab hia hib]

theorem dTau_inv (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    (dTau m ε a b)⁻¹ = dTau m ε a b := by
  refine inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun v => ?_)
  rw [LinearEquiv.mul_apply, dTau_mul_self m ε hab]
  rfl

theorem dTau_comm_of_disjoint (m : ℕ) (ε ε' : Bool) {c d c' d' : Fin m} (hcd : c ≠ d)
    (hcd' : c' ≠ d') (h1 : c ≠ c') (h2 : c ≠ d') (h3 : d ≠ c') (h4 : d ≠ d') (v : DVec m) :
    dTau m ε c d (dTau m ε' c' d' v) = dTau m ε' c' d' (dTau m ε c d v) := by
  funext i
  by_cases hic : i = c
  · simp only [hic, dTau_coord_left m ε hcd, dTau_coord_of_ne m ε' hcd' h3 h4,
      dTau_coord_of_ne m ε' hcd' h1 h2]
  · by_cases hid : i = d
    · simp only [hid, dTau_coord_right m ε hcd, dTau_coord_of_ne m ε' hcd' h1 h2,
        dTau_coord_of_ne m ε' hcd' h3 h4]
    · by_cases hic' : i = c'
      · simp only [hic', dTau_coord_of_ne m ε hcd (Ne.symm h1) (Ne.symm h3),
          dTau_coord_left m ε' hcd', dTau_coord_of_ne m ε hcd (Ne.symm h2) (Ne.symm h4)]
      · by_cases hid' : i = d'
        · simp only [hid', dTau_coord_of_ne m ε hcd (Ne.symm h2) (Ne.symm h4),
            dTau_coord_right m ε' hcd', dTau_coord_of_ne m ε hcd (Ne.symm h1) (Ne.symm h3)]
        · simp only [dTau_coord_of_ne m ε hcd hic hid, dTau_coord_of_ne m ε' hcd' hic' hid']

theorem dTau_comm_of_same (m : ℕ) (ε ε' : Bool) {c d : Fin m} (hcd : c ≠ d) (v : DVec m) :
    dTau m ε c d (dTau m ε' c d v) = dTau m ε' c d (dTau m ε c d v) := by
  funext i
  by_cases hic : i = c
  · simp only [hic, dTau_coord_left m ε hcd, dTau_coord_right m ε hcd,
      dTau_coord_left m ε' hcd, dTau_coord_right m ε' hcd]
    ring
  · by_cases hid : i = d
    · simp only [hid, dTau_coord_left m ε hcd, dTau_coord_right m ε hcd,
        dTau_coord_left m ε' hcd, dTau_coord_right m ε' hcd]
      ring
    · simp only [dTau_coord_of_ne m ε hcd hic hid, dTau_coord_of_ne m ε' hcd hic hid]

theorem dTau_not_comm_of_share (m : ℕ) (ε ε' : Bool) {x y y' : Fin m} (hxy : x ≠ y)
    (hxy' : x ≠ y') (hyy' : y ≠ y') :
    ¬ ∀ v : DVec m, dTau m ε x y (dTau m ε' x y' v) = dTau m ε' x y' (dTau m ε x y v) := by
  intro h
  have h1 := congrFun (h (dBasis m x)) y'
  simp only [dTau_coord_of_ne m ε hxy (Ne.symm hxy') (Ne.symm hyy'), dTau_coord_right m ε' hxy',
    dTau_coord_left m ε hxy, plnf_dBasis_apply, if_pos rfl, if_neg hxy.symm] at h1
  cases ε' <;> simp at h1

theorem dTau_comm_iff (m : ℕ) (ε ε' : Bool) {c d c' d' : Fin m} (hcd : c ≠ d)
    (hcd' : c' ≠ d') :
    (∀ v : DVec m, dTau m ε c d (dTau m ε' c' d' v) = dTau m ε' c' d' (dTau m ε c d v)) ↔
      ((c ≠ c' ∧ c ≠ d' ∧ d ≠ c' ∧ d ≠ d') ∨ (c = c' ∧ d = d') ∨ (c = d' ∧ d = c')) := by
  constructor
  · intro h
    by_cases e1 : c = c'
    · by_cases e2 : d = d'
      · exact Or.inr (Or.inl ⟨e1, e2⟩)
      · subst e1
        exact absurd h (dTau_not_comm_of_share m ε ε' hcd hcd' e2)
    · by_cases e3 : c = d'
      · by_cases e4 : d = c'
        · exact Or.inr (Or.inr ⟨e3, e4⟩)
        · subst e3
          rw [dTau_symm m ε' c' c] at h
          exact absurd h (dTau_not_comm_of_share m ε ε' hcd e1 e4)
      · by_cases e5 : d = c'
        · subst e5
          rw [dTau_symm m ε c d] at h
          exact absurd h (dTau_not_comm_of_share m ε ε' hcd.symm hcd' e3)
        · by_cases e6 : d = d'
          · subst e6
            rw [dTau_symm m ε c d, dTau_symm m ε' c' d] at h
            exact absurd h (dTau_not_comm_of_share m ε ε' hcd.symm e5 e1)
          · exact Or.inl ⟨e1, e3, e5, e6⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩) v
    · exact dTau_comm_of_disjoint m ε ε' hcd hcd' h1 h2 h3 h4 v
    · rw [← h5, ← h6]
      exact dTau_comm_of_same m ε ε' hcd v
    · rw [← h5, ← h6, dTau_symm m ε' d c]
      exact dTau_comm_of_same m ε ε' hcd v

end CFSG.StandardType.QTwo

end
