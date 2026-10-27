module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFa
public import CFSG.Quasithin.Background.HConj
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem eq_one_of_pow_prime {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hrG : ¬ r ∣ Nat.card G) {g : G} (hg : g ^ r = 1) : g = 1 := by
  rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hg) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ orderOf_dvd_natCard g) hrG

theorem eq_one_of_pow_prime_of_dvd {L : Type*} [Field L] [Finite L] {r N : ℕ} (hr : r.Prime)
    (hN : Nat.card L - 1 ∣ N) (hrN : ¬ r ∣ N) {c : L} (hc : c ^ r = 1) : c = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at hc
    exact zero_ne_one hc
  have hu : Units.mk0 c hc0 ^ r = 1 := Units.ext (by simp [hc])
  have h1 := eq_one_of_pow_prime hr (fun h => hrN (h.trans (by rw [Nat.card_units]; exact hN))) hu
  simpa using congrArg Units.val h1

section Nat

variable {V : Type} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def smOf (e : V ≃* StdMod ι K) (c : K) : V →* V where
  toFun v := e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e v)))
  map_one' := by simp
  map_mul' v w := by simp only [map_mul, toAdd_mul, smul_add, ofAdd_add]

omit [Fintype ι] [DecidableEq ι] in
theorem apply_smOf (e : V ≃* StdMod ι K) (c : K) (v : V) :
    e (smOf e c v) = Multiplicative.ofAdd (c • Multiplicative.toAdd (e v)) :=
  e.apply_symm_apply _

omit [Fintype ι] [DecidableEq ι] in
theorem isScalarAct_smOf (e : V ≃* StdMod ι K) : IsScalarAct (smOf e) where
  add c d v := e.injective (by
    rw [map_mul, apply_smOf, apply_smOf, apply_smOf, add_smul, ofAdd_add])
  mul c d v := e.injective (by rw [apply_smOf, apply_smOf, apply_smOf, toAdd_ofAdd, mul_smul])
  one v := e.injective (by rw [apply_smOf, one_smul, ofAdd_toAdd])

variable {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut V)} {π : ↥Γ →* ↥H} {e : V ≃* StdMod ι K}

theorem smOf_comm (hπ : Function.Surjective π)
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) :
    ∀ h ∈ H, ∀ c v, smOf e c (h v) = h (smOf e c v) := by
  intro h hh c v
  obtain ⟨γ, hγ⟩ := hπ ⟨h, hh⟩
  rw [show h = ((π γ : ↥H) : MulAut V) from (congrArg Subtype.val hγ).symm]
  apply e.injective
  rw [apply_smOf, he, he, apply_smOf]
  simp only [natAct, toAdd_ofAdd, Matrix.mulVec_smul]

theorem smOf_commutant (hΓ : HasScalarCommutant Γ)
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) :
    ∀ f : V →* V, (∀ h ∈ H, ∀ v, f (h v) = h (f v)) → ∃ c, ∀ v, f v = smOf e c v := by
  intro f hf
  let f' : (ι → K) →+ (ι → K) := AddMonoidHom.mk'
    (fun w => Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd w)))))
    (fun w₁ w₂ => by simp only [ofAdd_add, map_mul, toAdd_mul])
  obtain ⟨c, hc⟩ := hΓ f' fun γ hγ w => by
    have h1 : e.symm (Multiplicative.ofAdd ((γ : Matrix ι ι K) *ᵥ w)) =
        ((π ⟨γ, hγ⟩ : ↥H) : MulAut V) (e.symm (Multiplicative.ofAdd w)) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, he, MulEquiv.apply_symm_apply]
      rfl
    change Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd
      ((γ : Matrix ι ι K) *ᵥ w))))) =
      (γ : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd w))))
    rw [h1, hf _ (π ⟨γ, hγ⟩).2, he]
    rfl
  refine ⟨c, fun v => e.injective ?_⟩
  have h2 := hc (Multiplicative.toAdd (e v))
  change Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd
    (Multiplicative.toAdd (e v)))))) = _ at h2
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h2
  rw [apply_smOf, ← h2, ofAdd_toAdd]

theorem injective_of_natAct (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply natAut_injective Γ
  rw [map_one]
  ext x
  rw [natAut_apply, ← e.apply_symm_apply x, ← he, hγ]
  simp

theorem card_eq_of_natAct (hπ : Function.Surjective π)
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) :
    Nat.card H = Nat.card Γ :=
  (Nat.card_congr (MulEquiv.ofBijective π ⟨injective_of_natAct he, hπ⟩).toEquiv).symm

omit [Fintype ι] [DecidableEq ι] in
theorem isSemilinear_congrHom {x : MulAut V} (hx : IsSemi (smOf e) x 1) :
    IsSemilinear (congrHom e x) (RingEquiv.refl K) := by
  intro c w
  have h2 : smOf e c (e.symm (Multiplicative.ofAdd w)) =
      e.symm (Multiplicative.ofAdd (c • w)) := by
    apply e.injective
    rw [apply_smOf, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have h1 := hx c (e.symm (Multiplicative.ofAdd w))
  rw [h2] at h1
  change Multiplicative.toAdd (e (x (e.symm (Multiplicative.ofAdd (c • w))))) =
    c • Multiplicative.toAdd (e (x (e.symm (Multiplicative.ofAdd w))))
  rw [h1, apply_smOf, toAdd_ofAdd]
  rfl

theorem congrHom_mem_natNorm [Finite V] (hπ : Function.Surjective π)
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) {x : MulAut V}
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) : congrHom e x ∈ natNorm Γ := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hxH' := inv_conj_mem hxH
  have hx : x ∈ Subgroup.normalizer (H : Set (MulAut V)) :=
    Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => hxH h hh, fun hh => by simpa [mul_assoc] using hxH' _ hh⟩
  have h1 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (StdMod ι K))) :
        Set (MulAut (StdMod ι K))) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
  rw [natNorm, ← map_congrHom_eq_natImage Γ hπ e he, ← h1]
  exact ⟨x, hx, rfl⟩

theorem eq_one_natSL [Finite K] {H : Subgroup (MulAut V)} {π : ↥(StatedSL 2 K) →* ↥H}
    (hπ : Function.Surjective π) {e : V ≃* StdMod (Fin 2) K}
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct (StatedSL 2 K) γ (e v))
    {r : ℕ} (hr : r.Prime) (hrH : ¬ r ∣ Nat.card H) {x : MulAut V}
    (hx : IsSemi (smOf e) x 1) (hxr : x ^ r = 1) : x = 1 := by
  obtain ⟨A, hA⟩ := exists_matAut_of_mem_linSub (isSemilinear_congrHom hx)
  have hAr : A ^ r = 1 := by
    apply matHom_injective
    rw [map_pow, matHom_apply, ← hA, ← map_pow, hxr, map_one, map_one]
  have hcard : Nat.card H = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [card_eq_of_natAct hπ he, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    refine eq_one_of_pow_prime_of_dvd hr (N := Nat.card H) ?_ hrH ?_
    · rw [hcard]
      exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2) _
    · rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hAr, Units.val_one, Matrix.det_one]
  have hAm : A ∈ StatedSL 2 K := Subgroup.subset_closure hdet
  have h1 : (⟨A, hAm⟩ : ↥(StatedSL 2 K)) = 1 :=
    eq_one_of_pow_prime hr (by rwa [← card_eq_of_natAct hπ he]) (Subtype.ext (by simp [hAr]))
  have hA1 : A = 1 := congrArg Subtype.val h1
  apply congrHom_injective e
  rw [hA, hA1, map_one]
  exact toAddMap_injective fun v => by
    rw [toAddMap_matAut, Units.val_one, Matrix.one_mulVec, toAddMap_one]

end Nat

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
