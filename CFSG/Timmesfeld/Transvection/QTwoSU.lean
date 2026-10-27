module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary Matrix
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

abbrev idx₀ (m : ℕ) (hm : 2 ≤ m) : Fin m := ⟨m / 2 - 1, by omega⟩

abbrev coord₀ (m : ℕ) (hm : 2 ≤ m) : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩

theorem idx₀_ne_rev (hm : 2 ≤ m) : idx₀ m hm ≠ Fin.rev (idx₀ m hm) := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  omega

theorem weight_idx₀ (hm : 2 ≤ m) : weight m (idx₀ m hm) = Pi.single (coord₀ m hm) 1 := by
  funext c
  rw [SUExtras.weight_apply', Pi.single_apply]
  have hc := c.isLt
  simp only [coord₀, Fin.ext_iff]
  split_ifs <;> omega

theorem toStd_unitaryLongRoot (hm : 2 ≤ m) :
    toStd m (unitaryLongRoot m hm) = 2 • weight m (idx₀ m hm) := by
  rw [weight_idx₀]
  funext a
  have ha := a.isLt
  by_cases he : Even m
  · have hm2 : m % 2 = 0 := Nat.even_iff.1 he
    simp only [toStd, unitaryLongRoot, he, hm2, ite_true, one_smul, Symplectic.toStd,
      Pi.smul_apply, Pi.single_apply, coord₀, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs <;> omega
  · have hm2 : ¬ m % 2 = 0 := fun h => he (Nat.even_iff.2 h)
    simp only [toStd, unitaryLongRoot, he, hm2, ite_false, Pi.smul_apply, Pi.single_apply,
      coord₀, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs <;> omega

theorem eq_of_weight_sub_eq (hm : 2 ≤ m) {a b : Fin m}
    (h : weight m a - weight m b = 2 • weight m (idx₀ m hm)) :
    a = idx₀ m hm ∧ b = Fin.rev (idx₀ m hm) := by
  have hk := congrFun h (coord₀ m hm)
  rw [weight_idx₀] at hk
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, Nat.cast_ofNat,
    mul_one] at hk
  have ha := SUExtras.weight_apply_bounds a (coord₀ m hm)
  have hb := SUExtras.weight_apply_bounds b (coord₀ m hm)
  have ha1 : weight m a (coord₀ m hm) = 1 := by omega
  have hb1 : weight m b (coord₀ m hm) = -1 := by omega
  rw [SUExtras.weight_apply'] at ha1 hb1
  have hav := a.isLt
  have hbv := b.isLt
  constructor
  · apply Fin.ext
    simp only at ha1 ⊢
    split_ifs at ha1 <;> omega
  · apply Fin.ext
    simp only [Fin.val_rev] at hb1 ⊢
    split_ifs at hb1
    omega

noncomputable def longRootElt (hm : 2 ≤ m) : SU frob m :=
  longRootHom frob (idx₀_ne_rev hm) (Multiplicative.ofAdd ⟨1, one_add_frob_one⟩)

theorem mat_longRootElt (hm : 2 ≤ m) :
    ((longRootElt hm : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      longRootMatrix (idx₀ m hm) 1 :=
  coe_longRootHom frob (idx₀_ne_rev hm) _

theorem add_frob_eq_zero_of_longRootMatrix {i : Fin m} (hi : i ≠ Fin.rev i) {c : K}
    (h : conjTr frob (longRootMatrix i c) * antidiag m * longRootMatrix i c = antidiag m) :
    c + frob c = 0 := by
  have h1 : Fin.rev i ≠ i := fun h => hi h.symm
  rw [conjTr_longRootMatrix frob, longRootMatrix] at h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    antidiag_mul_single, single_mul_antidiag, single_mul_single_of_ne _ _ _ _ h1] at h
  rw [add_zero, add_assoc, add_eq_left, ← Matrix.single_add] at h
  have := congrFun (congrFun h (Fin.rev i)) (Fin.rev i)
  rw [Matrix.single_apply_same, Matrix.zero_apply] at this
  rw [add_comm]
  exact this

theorem rootGroup_unitaryLongRoot_eq (hm : 4 ≤ m) (hσ : ∀ c : K, frob (frob c) = c) :
    Unitary.rootGroup frob hσ m (unitaryLongRoot m (by omega)) =
      Subgroup.zpowers (longRootElt (m := m) (by omega)) := by
  have hm2 : 2 ≤ m := by omega
  have hi₀ := idx₀_ne_rev hm2
  have hw : 2 • weight m (idx₀ m hm2) = toStd m (unitaryLongRoot m hm2) :=
    (toStd_unitaryLongRoot hm2).symm
  apply le_antisymm
  · intro x hx
    have hoff : ∀ a b, ¬ (a = idx₀ m hm2 ∧ b = Fin.rev (idx₀ m hm2)) →
        SUExtras.mat frob m x a b = (1 : Matrix (Fin m) (Fin m) K) a b := by
      intro a b hab
      refine SUExtras.mat_apply_of_mem_rootGroup hσ hx ?_ ?_
      · rw [← hw]
        exact fun h => hab (eq_of_weight_sub_eq hm2 h)
      · rw [← hw, smul_smul]
        intro h
        have h0 := SUExtras.eq_zero_of_weight_sub_eq_nsmul (k := 2 * 2) h (by norm_num)
        rw [weight_idx₀] at h0
        have := congrFun h0 (coord₀ m hm2)
        simp at this
    set c := SUExtras.mat frob m x (idx₀ m hm2) (Fin.rev (idx₀ m hm2))
    have hX : SUExtras.mat frob m x = longRootMatrix (idx₀ m hm2) c := by
      ext a b
      by_cases hab : a = idx₀ m hm2 ∧ b = Fin.rev (idx₀ m hm2)
      · obtain ⟨rfl, rfl⟩ := hab
        simp [c, longRootMatrix, Matrix.one_apply_ne hi₀]
      · rw [hoff a b hab, longRootMatrix, Matrix.add_apply, Matrix.single_apply,
          ite_eq_right_iff.2 (fun h => absurd ⟨h.1.symm, h.2.symm⟩ hab), add_zero]
    have hc : c + frob c = 0 := by
      apply add_frob_eq_zero_of_longRootMatrix hi₀
      rw [← hX, SUExtras.mat_apply]
      exact (mem_SU.1 x.2).2
    rcases (add_frob_eq_zero_iff c).1 hc with h0 | h1
    · have : x = 1 := SUExtras.mat_injective (by
        rw [hX, h0, map_one]
        simp [longRootMatrix])
      rw [this]
      exact one_mem _
    · have : x = longRootElt hm2 := SUExtras.mat_injective (by
        rw [hX, h1, SUExtras.mat_apply, mat_longRootElt])
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact SUExtras.longRootHom_mem hσ hi₀ hw _

theorem herm_col_eq {P : GL (Fin m) K}
    (hP : conjTr frob (P : Matrix (Fin m) (Fin m) K) * (P : Matrix (Fin m) (Fin m) K) =
      antidiag m) (i : Fin m) (x : Fin m → K) :
    herm frob (fun k => (P : Matrix (Fin m) (Fin m) K) k i) x =
      ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).mulVec x (Fin.rev i) := by
  have hJ : conjTr frob (P : Matrix (Fin m) (Fin m) K) =
      antidiag m * ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    rw [← hP, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have h1 : herm frob (fun k => (P : Matrix (Fin m) (Fin m) K) k i) x =
      (conjTr frob (P : Matrix (Fin m) (Fin m) K)).mulVec x i := by
    rw [herm_def, Matrix.mulVec, dotProduct]
    rfl
  rw [h1, hJ, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, antidiag, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem conjEquiv_longRoot (hm : 2 ≤ m) {P : GL (Fin m) K}
    (hP : conjTr frob (P : Matrix (Fin m) (Fin m) K) * (P : Matrix (Fin m) (Fin m) K) =
      antidiag m) :
    let v : Fin m → K := fun k => (P : Matrix (Fin m) (Fin m) K) k (idx₀ m hm)
    v ≠ 0 ∧ herm frob v v = 0 ∧ conjEquiv P hP (longRootElt hm) = tvU v := by
  intro v
  set i₀ := idx₀ m hm
  have hv : v = (P : Matrix (Fin m) (Fin m) K).mulVec (Pi.single i₀ 1) := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hPinv : ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).mulVec v = Pi.single i₀ 1 := by
    rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hvv : herm frob v v = 0 := by
    rw [herm_col_eq hP, hPinv, Pi.single_eq_of_ne (idx₀_ne_rev hm).symm]
  refine ⟨fun h0 => ?_, hvv, ?_⟩
  · have := hPinv
    rw [h0, Matrix.mulVec_zero] at this
    have h1 := congrFun this i₀
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact zero_ne_one h1
  · apply ext_smul
    intro x
    set y := ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).mulVec x
    have hxy : (P : Matrix (Fin m) (Fin m) K).mulVec y = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hsingle : Function.update (0 : Fin m → K) i₀ (1 * y (Fin.rev i₀)) =
        y (Fin.rev i₀) • Pi.single i₀ 1 := by
      ext k
      rw [Function.update_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, one_mul]
      split_ifs <;> simp
    rw [tvU_smul hvv, smul_def, coe_conjEquiv, Units.val_mul, Units.val_mul, mat_longRootElt,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, longRootMatrix, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec, Matrix.mulVec_add, hxy, hsingle,
      Matrix.mulVec_smul, ← hv, herm_col_eq hP]

theorem suConclusion {H : Type} [Group H] {Δ : Set (Subgroup H)} {D : Set H}
    (hΔ : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ x ∈ D, X = Subgroup.zpowers x)
    (hD : ∀ x ∈ D, ∀ y, IsConj x y ↔ y ∈ D) {m : ℕ} (hm : 4 ≤ m)
    (ψ : H ≃* U2 m) (hψ : ψ '' D = DU m) :
    ∃ m : ℕ, ∃ hm : 4 ≤ m,
      ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) m) →* H,
        Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
          ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul (le_refl 1)) m).rootGroup
            (unitaryLongRoot m (by omega))) g).map Φ := by
  have hm2 : 2 ≤ m := by omega
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := 2) (f := 1) card_K m
  let κ : SU frob m ≃* SUid frob m := conjEquiv P hP
  let π : SUid frob m →* PG m := QuotientGroup.mk' _
  let Φ : SU frob m →* H :=
    ψ.symm.toMonoidHom.comp ((u2Equiv m).symm.toMonoidHom.comp (π.comp κ.toMonoidHom))
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SUid frob m))
      (u2Equiv m (ψ y))
    refine ⟨κ.symm z, ?_⟩
    simp only [Φ, π, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, hz, MulEquiv.symm_apply_apply]
  refine ⟨m, hm, Φ, hΦ, ?_, fun X => ?_⟩
  ·
    ext x
    rw [MonoidHom.mem_ker]
    change ψ.symm ((u2Equiv m).symm (QuotientGroup.mk (κ x))) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      apply κ.injective
      rw [map_mul, map_mul]
      exact h (κ g)
    · intro h g
      obtain ⟨g', rfl⟩ := κ.surjective g
      rw [← map_mul, ← map_mul, h g']
  ·
    have hT : (Unitary.rootDatum (card_galoisField_two_mul (le_refl 1)) m).rootGroup
        (unitaryLongRoot m (by omega)) = Subgroup.zpowers (longRootElt (m := m) hm2) :=
      rootGroup_unitaryLongRoot_eq hm frob_frob
    obtain ⟨hv0, hvv, hκ⟩ := conjEquiv_longRoot hm2 hP
    have ht₀ : Φ (longRootElt hm2) ∈ D := by
      have hmem : (u2Equiv m).symm (π (κ (longRootElt hm2))) ∈ ψ '' D := by
        rw [hψ]
        change (u2Equiv m).symm (QuotientGroup.mk (κ (longRootElt hm2))) ∈ DU m
        rw [show κ (longRootElt hm2) = conjEquiv P hP (longRootElt hm2) from rfl, hκ]
        exact tqU_mem_DU hv0 hvv
      obtain ⟨g, hg, hge⟩ := hmem
      change ψ.symm ((u2Equiv m).symm (π (κ (longRootElt hm2)))) ∈ D
      rw [← hge, MulEquiv.symm_apply_apply]
      exact hg
    exact mem_iff_conjSub_map hΔ hD Φ hΦ hT ht₀ X

end CFSG.Timmesfeld.Transvection.QTwo
