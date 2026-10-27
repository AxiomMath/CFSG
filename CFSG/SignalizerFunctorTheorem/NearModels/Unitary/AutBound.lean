module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic

public section

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

variable {p f : ℕ} {K : Type} [Field K]

section Isometries

variable {r ε : ℕ}

theorem toLin_mem_sesqUnitaryGroup_iff_mem_hypUnitary (h : UnitaryFieldData p f K)
    (g : GL (HypIndex r ε) K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (hypForm h r ε) ↔
      g ∈ hypUnitary h r ε := by
  rw [mem_sesqUnitaryGroup, mem_hypUnitary, ← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

theorem card_hypUnitary_eq (h : UnitaryFieldData p f K) :
    Nat.card (hypUnitary h r ε) = Nat.card (sesqUnitaryGroup (hypForm h r ε)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
    (toLin_mem_sesqUnitaryGroup_iff_mem_hypUnitary h g).symm)

theorem card_hypUnitary (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε) :
    Nat.card (hypUnitary h r ε) = (p ^ f + 1) * Nat.card (hypSU h r ε) := by
  have hdim : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  obtain ⟨hU, -⟩ := unitary_full_group_order h (hypForm_isSymm h) (hypForm_separatingLeft h)
    hdim hn
  have hSU := (card_hypSU h hn).1
  have hsplit := prod_Icc_one_eq_mul (fun i => (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i)) hn
  have key : (Nat.card (hypUnitary h r ε) : ℤ) =
      ((p ^ f + 1 : ℕ) : ℤ) * (Nat.card (hypSU h r ε) : ℤ) := by
    rw [card_hypUnitary_eq, hU, hSU, hsplit]
    push_cast
    ring
  exact_mod_cast key

end Isometries

section Semilinear

variable (h : UnitaryFieldData p f K) (r ε : ℕ)

theorem glAut_mem_hypUnitary {σ : K ≃+* K} {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) : glAut σ A ∈ hypUnitary h r ε := by
  have := map_similitude h (μ := (1 : K)) (by rw [one_smul]; exact mem_hypUnitary.mp hA) σ
  rw [map_one, one_smul] at this
  exact mem_hypUnitary.mpr (by rw [coe_glAut]; exact this)

@[expose] def semilinearIsometries : Subgroup (SemiGL (HypIndex r ε) K) where
  carrier := {x | x.left ∈ hypUnitary h r ε}
  mul_mem' {x y} hx hy := by
    have hx' : x.left ∈ hypUnitary h r ε := hx
    have hy' : y.left ∈ hypUnitary h r ε := hy
    show (x * y).left ∈ hypUnitary h r ε
    rw [SemidirectProduct.mul_left]
    exact mul_mem hx' (glAut_mem_hypUnitary h r ε hy')
  one_mem' := by
    show (1 : SemiGL (HypIndex r ε) K).left ∈ hypUnitary h r ε
    rw [SemidirectProduct.one_left]
    exact one_mem _
  inv_mem' {x} hx := by
    have hx' : x.left ∈ hypUnitary h r ε := hx
    show (x⁻¹).left ∈ hypUnitary h r ε
    rw [SemidirectProduct.inv_left]
    exact glAut_mem_hypUnitary h r ε (inv_mem hx')

variable {h r ε}

theorem mem_semilinearIsometries {x : SemiGL (HypIndex r ε) K} :
    x ∈ semilinearIsometries h r ε ↔ x.left ∈ hypUnitary h r ε :=
  Iff.rfl

theorem semilinearIsometries_le : semilinearIsometries h r ε ≤ semilinearSimilitudes h r ε :=
  fun _ hx => ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact mem_hypUnitary.mp hx⟩

variable (h r ε)

@[expose] def semilinearIsometriesEquiv :
    semilinearIsometries h r ε ≃ hypUnitary h r ε × (K ≃+* K) where
  toFun x := (⟨x.1.left, x.2⟩, x.1.right)
  invFun y := ⟨⟨y.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_semilinearIsometries :
    Nat.card (semilinearIsometries h r ε) =
      Nat.card (hypUnitary h r ε) * Nat.card (K ≃+* K) := by
  rw [Nat.card_congr (semilinearIsometriesEquiv h r ε), Nat.card_prod]

@[expose] noncomputable def isometryAut (hr : 1 ≤ r) (hε : ε ≤ 1) :
    semilinearIsometries h r ε →* MulAut (hypPSU h r ε) :=
  (semilinearAutHom h hr hε).comp (Subgroup.inclusion semilinearIsometries_le)

theorem isometryAut_surjective (hq : 2 < p ^ f) :
    Function.Surjective (isometryAut h 1 1 le_rfl le_rfl) := by
  intro α
  obtain ⟨σ, B, hB, hα⟩ :=
    CFSG.ShultStronglyClosedTI.UnitaryAutomorphism.exists_isometry_hypPSU h hq α
  refine ⟨⟨⟨B, σ⟩, mem_hypUnitary.mpr hB⟩, MulEquiv.ext fun y => ?_⟩
  obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 y
  obtain ⟨_, hαg⟩ := hα g
  exact (semilinearAutHom_apply h le_rfl le_rfl _ g).trans hαg.symm

end Semilinear

section Orders

variable (h : UnitaryFieldData p f K)

include h in
theorem card_ringEquiv_unitary : Nat.card (K ≃+* K) = 2 * f := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (by have := h.one_le; omega) h.card
  exact hcard

theorem card_semilinearIsometries_one_one :
    Nat.card (semilinearIsometries h 1 1) =
      (p ^ f + 1) * Nat.card (hypSU h 1 1) * (2 * f) := by
  rw [card_semilinearIsometries, card_hypUnitary h (by norm_num),
    card_ringEquiv_unitary h]

theorem pow_add_one_dvd_card_hypSU_one_one : p ^ f + 1 ∣ Nat.card (hypSU h 1 1) := by
  have h1 := (card_hypSU h (r := 1) (ε := 1) (by norm_num)).1
  have hI : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  refine Int.natCast_dvd_natCast.mp ?_
  rw [h1]
  push_cast
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ⟨((p : ℤ) ^ f) ^ 2 - (p : ℤ) ^ f + 1, by ring⟩ _) _

end Orders

theorem card_pSubgroup_mulAut_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 p (GaloisField 2 (2 * p)))
    (hS : ¬ p ∣ Nat.card (hypSU h 1 1))
    {G : Type*} [Group G] (e : hypPSU h 1 1 ≃* G)
    (P : Subgroup (MulAut G)) (hP : IsPGroup p P) : Nat.card P ∣ p := by
  have hq : 2 < 2 ^ p :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
  let s : semilinearIsometries h 1 1 →* MulAut G :=
    (MulAut.congr e).toMonoidHom.comp (isometryAut h 1 1 le_rfl le_rfl)
  have hs : Function.Surjective s :=
    (MulAut.congr e).surjective.comp (isometryAut_surjective h hq)
  have hdvd : Nat.card P ∣ (2 ^ p + 1) * Nat.card (hypSU h 1 1) * (2 * p) := by
    rw [← card_semilinearIsometries_one_one]
    exact (Subgroup.card_subgroup_dvd_card P).trans (Subgroup.card_dvd_of_surjective hs)
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (hypSU h 1 1) := finite_hypSU h
  have : Finite G := Finite.of_equiv _ e.toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hm : ¬ p ∣ (2 ^ p + 1) * Nat.card (hypSU h 1 1) * 2 := by
    intro hdiv
    rcases (Nat.Prime.dvd_mul hp).mp hdiv with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact hS (h2.trans (pow_add_one_dvd_card_hypSU_one_one h))
      · exact hS h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hcop : Nat.Coprime (p ^ k) ((2 ^ p + 1) * Nat.card (hypSU h 1 1) * 2) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  rw [hk] at hdvd ⊢
  have hdvd' : p ^ k ∣ ((2 ^ p + 1) * Nat.card (hypSU h 1 1) * 2) * p := by
    convert hdvd using 1
    ring
  exact hcop.dvd_of_dvd_mul_left hdvd'

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
