module

public import CFSG.RankThree.PartOne.S11d.ThreeCompAL
public import CFSG.RankThree.PartOne.S11d.PSUTwistGood
public import CFSG.RankThree.PartOne.S11d.PSUInvol
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.RankThree.PartOne.TCU CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_involution_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : ∃ t : Q, orderOf t = 2 := by
  obtain ⟨-, hs, hnab⟩ := hQ
  have := hs
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (Subgroup.center Q)
  have h2 : 2 ∣ Nat.card Q := by
    rw [hk]
    exact Dvd.dvd.mul_right (even_iff_two_dvd.mp heven) k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem psuThreeA : PSUThreeA := by
  intro T _ _ p hp hp5 hLR2 h2 f₀ hf₀ hM hpQ α hαp hαinn hLRA hX x hxp hx1 hαx D hD hDα
  obtain ⟨K, _, h, φ, σ, -, hσ, hZp, hφα⟩ :=
    exists_fieldAut_model_PSU hp hp5 hM hLR2 α hαp hαinn hLRA hX
  have hfinK : Finite K := h.finite
  have hF5 : 5 ≤ p * f₀ := by nlinarith
  have hq : 4 ≤ 2 ^ (p * f₀) :=
    calc 4 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) hF5
  have hxp' : (φ x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hx1' : φ x ≠ 1 := fun e => hx1 (φ.injective (by rw [e, map_one]))
  have hφα' : fieldAut h σ = MulAut.congr φ α := hφα.symm
  have hσx : fieldAut h σ (φ x) = φ x := by
    rw [hφα']
    simp [MulAut.congr_apply, hαx]
  obtain ⟨A, hAp, hAx⟩ := exists_lift_pow h (by norm_num : 1 ≤ 3) hZp hxp'
  have hσA : glAut σ (A : GL (Fin 3) K) = A :=
    lift_sigma_fixed h (by norm_num) hZp hAp (by rw [hAx]; exact hσx)
  have hA1 : A ≠ 1 := fun e => hx1' (by rw [← hAx, e]; rfl)
  have hD' := isComponentOf_map_mulEquiv φ hD
  rw [map_centralizer_singleton_mulEquiv_good] at hD'
  have hDq : CFSG.IsQuasisimple ↥(D.map φ.toMonoidHom) := hD'.2.1
  obtain ⟨τ', hτ'⟩ := exists_involution_of_isQuasisimple hDq
  have hτ2' : τ' ^ 2 = 1 := by
    have := pow_orderOf_eq_one τ'
    rwa [hτ'] at this
  have hτ2 : (τ' : PSUn h 3) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hτ2']
    rfl
  have hτ1 : (τ' : PSUn h 3) ≠ 1 := fun e => by
    have : τ' = 1 := Subtype.ext e
    rw [this, orderOf_one] at hτ'
    omega
  have hτc : (τ' : PSUn h 3) * φ x = φ x * τ' :=
    Subgroup.mem_centralizer_singleton_iff.mp (hD'.1 τ'.2)
  obtain ⟨g, hg2, hgτ⟩ := exists_lift_two_pow h (by norm_num : 1 ≤ 3) (k := 1)
    (by rw [pow_one]; exact hτ2)
  have hgA : g * A = A * g :=
    commute_of_mk_commute h (by norm_num) hZp hAp (by rw [hgτ, hAx]; exact hτc)
  have hg1 : g ≠ 1 := fun e => hτ1 (by rw [← hgτ, e]; rfl)
  obtain ⟨w, μ, hw0, hww, hAw⟩ := exists_isotropic_eigenvector_of_involution h
    (A := (A : GL (Fin 3) K)) (τ := (g : GL (Fin 3) K)) (linOf_isom_A h g.2)
    (by simpa using congrArg Subtype.val hg2) (fun e => hg1 (Subtype.ext e))
    (congrArg Subtype.val hgA.symm)
  obtain ⟨u, S⟩ := exists_twistSetup h hp hp5 hpQ hq hAp hA1 hw0 hww hAw
  have hσc : σ μ = μ := S.sigma_eq hp hp5 hAp hA1 hσ hσA
  have hσu : glAut σ S.gl = S.gl := S.glAut_gl hσc hσA
  have hR : LinearMap.range (u - 1) ≠ ⊥ := fun hb => by
    have hfr := S.finrank_range_eq_one hp hp5 hAp hA1
    rw [hb, finrank_bot] at hfr
    exact absurd hfr (by norm_num)
  have hgood := goodConclusion_of_twistSetup S hf₀ rfl hp hp5 hσ hZp (by norm_num) hAp hR hσu
  have hgood' : GoodConclusion p (PSUn h 3) (MulAut.congr φ α) (φ x) := by
    rw [← hφα', ← hAx]
    exact hgood
  exact (GoodConclusion.of_mulEquiv φ α x hgood').2.1 D hD hDα

end CFSG.RankThree.PartOne.TCX
