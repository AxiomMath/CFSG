module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open scoped commutatorElement IsMulCommutative

open CFSG.SignalizerFunctorTheorem.McBride

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

variable {Γ : Type u} [Group Γ]

@[expose] def conjOn {A R : Subgroup Γ} (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (a : A) :
    ↥R →* ↥R :=
  ((MulAut.conj (a : Γ)).toMonoidHom.comp R.subtype).codRestrict R fun r => by
    have := Subgroup.le_normalizer_iff.mp hAR (a : Γ) a.2 (r : Γ) r.2
    simpa [MulAut.conj_apply] using this

theorem coe_conjOn {A R : Subgroup Γ} (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (a : A)
    (r : R) : ((conjOn hAR a r : R) : Γ) = (a : Γ) * r * (a : Γ)⁻¹ := rfl

theorem conjOn_mul {A R : Subgroup Γ} (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (a b : A)
    (r : R) : conjOn hAR (a * b) r = conjOn hAR a (conjOn hAR b r) := by
  apply Subtype.ext
  simp only [coe_conjOn, Subgroup.coe_mul, mul_inv_rev]
  group

theorem commutator_inf_centralizer_eq_bot [Finite Γ] {p : ℕ} (hp : p.Prime) {A R : Subgroup Γ}
    (hA : IsPGroup p A) (hAR : A ≤ Subgroup.normalizer (R : Set Γ))
    (hcop : Nat.Coprime p (Nat.card R)) [IsMulCommutative R] :
    ⁅R, A⁆ ⊓ Subgroup.centralizer (A : Set Γ) = ⊥ := by
  have : Fintype A := Fintype.ofFinite A
  have := Fact.mk hp
  let T : R →* R :=
    MonoidHom.mk' (fun r => ∏ a : A, conjOn hAR a r) fun r s => by
      simp only [map_mul]
      exact Finset.prod_mul_distrib
  have hT : ∀ r, T r = ∏ a : A, conjOn hAR a r := fun r => rfl
  have hTconj : ∀ (b : A) (r : R), T (conjOn hAR b r) = T r := by
    intro b r
    rw [hT, hT]
    simp_rw [← conjOn_mul]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ fun a => rfl
  have hcomm : ∀ r ∈ R, ∀ a ∈ A, ⁅r, a⁆ ∈ (T.ker).map R.subtype := by
    intro r hr a ha
    have hcomm' : ⁅r, a⁆ = ((⟨r, hr⟩ * (conjOn hAR ⟨a, ha⟩ ⟨r, hr⟩)⁻¹ : R) : Γ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn, commutatorElement_def]
      group
    rw [hcomm']
    refine ⟨⟨r, hr⟩ * (conjOn hAR ⟨a, ha⟩ ⟨r, hr⟩)⁻¹, ?_, rfl⟩
    change _ ∈ T.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hTconj, mul_inv_cancel]
  have hle : ⁅R, A⁆ ≤ (T.ker).map R.subtype := Subgroup.commutator_le.mpr hcomm
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxc, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, rfl⟩ := hle hxc
  have hxA' := Subgroup.mem_centralizer_iff.mp hxA
  have hfix : ∀ a : A, conjOn hAR a y = y := fun a =>
    Subtype.ext (by
      have h' : (a : Γ) * y = y * a := hxA' a a.2
      rw [coe_conjOn, h']
      group)
  have hTy : T y = y ^ Nat.card A := by
    rw [hT]
    simp_rw [hfix]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hy1 : y ^ Nat.card A = 1 := by rw [← hTy]; exact MonoidHom.mem_ker.mp hy
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hd1 : orderOf y ∣ p ^ k := hk ▸ orderOf_dvd_of_pow_eq_one hy1
  have hd2 : orderOf y ∣ Nat.card R := orderOf_dvd_natCard y
  have hord : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) hd1 hd2
  have := orderOf_eq_one_iff.mp hord
  rw [this]
  simp


theorem projIn_map_conj [Finite Γ] {S : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) {a : Γ}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (ha' : ∀ J ∈ S, J.map (MulAut.conj a⁻¹).toMonoidHom ∈ S) {J X : Subgroup Γ} (hJ : J ∈ S)
    (hX : a ∈ Subgroup.normalizer (X : Set Γ)) :
    projIn S (J.map (MulAut.conj a).toMonoidHom) X =
      (projIn S J X).map (MulAut.conj a).toMonoidHom := by
  have hJ' := ha J hJ
  have hXa' : a⁻¹ ∈ Subgroup.normalizer (X : Set Γ) := inv_mem hX
  ext z
  rw [hK.mem_projIn_iff hJ', Subgroup.mem_map]
  constructor
  · rintro ⟨y, hyX, rfl⟩
    have hy'K : a⁻¹ * (y : Γ) * (a⁻¹)⁻¹ ∈ K := hK.conj_mem ha' y.2
    have hy'X : a⁻¹ * (y : Γ) * (a⁻¹)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hXa' _).mp hyX
    refine ⟨((hK.coord hJ ⟨_, hy'K⟩ : J) : Γ),
      (hK.mem_projIn_iff hJ).mpr ⟨⟨_, hy'K⟩, hy'X, rfl⟩, ?_⟩
    have key := hK.coord_conj ha hJ hy'K
    have hy : a * (a⁻¹ * (y : Γ) * (a⁻¹)⁻¹) * a⁻¹ = (y : Γ) := by group
    have hyy : (⟨a * (a⁻¹ * (y : Γ) * (a⁻¹)⁻¹) * a⁻¹, hK.conj_mem ha hy'K⟩ : ↥K) = y :=
      Subtype.ext hy
    rw [hyy] at key
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    exact key.symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hyX, rfl⟩ := (hK.mem_projIn_iff hJ).mp hw
    have hayK : a * (y : Γ) * a⁻¹ ∈ K := hK.conj_mem ha y.2
    refine ⟨⟨_, hayK⟩, (Subgroup.mem_normalizer_iff.mp hX _).mp hyX, ?_⟩
    have key := hK.coord_conj ha hJ y.2
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    exact key

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
