module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourNorm

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem card_sesqSpecialUnitaryGroup_three {ℓ f : ℕ} {E : Type} [Field E]
    (h : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {B : W →ₛₗ[h.bar] W →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank E W = 3) :
    Nat.card ↥(sesqSpecialUnitaryGroup B) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hK := card_eq_sq_of_unitaryFieldData h
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  obtain ⟨e₁⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid h e₀ he₀
  rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution h] at e₁
  obtain ⟨P, hP⟩ := exists_wittMatrix hK (Module.finrank E W)
  rw [Nat.card_congr (e₁.trans (conjEquiv P hP).symm).toEquiv, hn]
  exact card_SU_three hK

theorem OddOrderIsometry.isSolvable_specialBlock_three_two
    (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hdeg2 : h.natDegree = 2)
    (hm : primaryMultiplicity x.toLinearMap h = 3) (hK2 : Nat.card K = 2) :
    Group.IsSolvable ↥(specialBlock Q x h) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hd1 : d = 1 := by omega
  subst hd1
  have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
    have hn3 : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 3 := hm
    rw [card_sesqSpecialUnitaryGroup_three hU hBsymm hBl hn3]
    have hℓf : ℓ ^ (f * 1) = 2 := by rw [mul_one, ← hq, hK2]
    rw [hℓf]
    norm_num
  have e₂ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hfin : Finite ↥(sesqSpecialUnitaryGroup B) :=
    Nat.finite_of_card_ne_zero (by rw [h216]; norm_num)
  have hsolv : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) :=
    isSolvable_of_card_primeFactors_le_two (by
      rw [h216, show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide)
  exact solvable_of_solvable_injective (f := e₂.toMonoidHom) e₂.injective

end SelfDual

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary OrthRestOdd

theorem unitaryThreeInput_holds : UnitaryThreeInput := by
  intro K _ _ _ hK2 V _ _ _ Q a hx h _ hh hne hself hm
  have hpK : ((3 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_odd Nat.prime_three (by norm_num)
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK2]
  have hdeg2 : h.natDegree = 2 :=
    SpNS.natDegree_eq_two Nat.prime_three (by norm_num) hpK
      (CoordSU.dvd_cyclotomic_of_dvd Nat.prime_three (irreducible_of_mem_primaryFactors hh)
        (monic_of_mem_primaryFactors hh) (by rw [C_1]; exact hx.dvd_X_pow_sub_one hh)
        (by rw [C_1]; exact hne)) hpq
  exact hx.isSolvable_specialBlock_three_two (by norm_num) hh hne hself hdeg2 hm hK2

end SmallOrthUn

end CFSG.StandardType

end
