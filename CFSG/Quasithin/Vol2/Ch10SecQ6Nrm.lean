module

public import CFSG.Quasithin.Vol2.Ch10SecDFacts33
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Quasithin.Background.DicksonPerfectPSL2
import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.GorensteinWalter
open scoped MatrixGroups

namespace C10P06

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_eq_one_of_prime {p : ℕ} [Fact p.Prime] (σ : ZMod p ≃+* ZMod p) : σ = 1 :=
  RingEquiv.ext fun x =>
    congrArg (fun f : ZMod p →+* ZMod p => f x) (Subsingleton.elim σ.toRingHom (RingHom.id _))

theorem pgl2InnerAutPSL2_surjective {p : ℕ} [hp : Fact p.Prime]
    (hK : IsOddPrimePower (Nat.card (ZMod p))) (hcard : 3 < Nat.card (ZMod p)) :
    Function.Surjective (pgl2InnerAutPSL2 (ZMod p) hK hcard) := by
  intro α
  obtain ⟨y, hy⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) hK hcard α
  refine ⟨y.left, ?_⟩
  rw [← hy]
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right y]
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
    ringEquiv_eq_one_of_prime y.right, map_one, mul_one]

theorem le_of_normalizes {p : ℕ} (hp : p.Prime) [CharP K p]
    {A' B' : Subgroup (PGL2 K)} (hBA : B' ≤ Subgroup.normalizer (A' : Set (PGL2 K)))
    (hA60 : Nat.card A' = 60)
    (hAns : ¬ Group.IsSolvable A') (hp60 : ¬ p ∣ 60 * Nat.card B') : B' ≤ A' := by
  set J := B' ⊔ A' with hJ
  have hAJ : A' ≤ J := le_sup_right
  have hBJ : B' ≤ J := le_sup_left
  have := Subgroup.normal_subgroupOf_of_le_normalizer hBA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B' A' hBA
  have hcardJ : Nat.card J = 60 * Nat.card (↥B' ⧸ A'.subgroupOf B') := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A'.subgroupOf J), mul_comm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv, hA60, Nat.card_congr e.toEquiv]
  have hdvd : Nat.card J ∣ 60 * Nat.card B' := by
    rw [hcardJ]
    exact mul_dvd_mul_left 60 (Subgroup.card_quotient_dvd_card _)
  have hJns : ¬ Group.IsSolvable J := by
    intro hs
    have : Group.IsSolvable (A'.subgroupOf J) := subgroup_solvable_of_solvable _
    exact hAns (Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hAJ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAJ).surjective)
  have h60 := (CFSG.LinearGroups.tame_projective_linear_two_nonsolvable_order_sixty hp J
    (fun h => hp60 (h.trans hdvd)) hJns).1
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [h60]; norm_num)
  have hJA : A' = J := Subgroup.eq_of_le_of_card_ge hAJ (by rw [h60, hA60])
  rw [hJA]
  exact hBJ

theorem not_dvd_sixty_mul {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (k : ℕ) : ¬ p ∣ 60 * 2 ^ k := by
  intro h
  have h1 : p ∣ 2 ^ (k + 2) * 3 * 5 := by
    have e : 60 * 2 ^ k = 2 ^ (k + 2) * 3 * 5 := by ring
    rwa [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  · have := Nat.le_of_dvd (by norm_num) h2
    omega

end C10P06

theorem factPSL2NormA5 : FactPSL2NormA5 := by
  intro p hp hp7 A hAe B hB hBA
  obtain ⟨eA⟩ := hAe
  have : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hKodd : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hKcard, pow_one]⟩
  have hcard : 3 < Nat.card (ZMod p) := by rw [hKcard]; omega
  set Ψ := pgl2InnerAutPSL2 (ZMod p) hKodd hcard with hΨ
  have hΨinj : Function.Injective Ψ := pgl2InnerAutPSL2_injective (ZMod p) hKodd hcard
  have hΨsurj : Function.Surjective Ψ := C10P06.pgl2InnerAutPSL2_surjective hKodd hcard
  set ι := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p) with hι
  have hιinj : Function.Injective ι := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  set A' := A.map ι with hA'
  set B' := B.comap Ψ with hB'
  have hBcard : Nat.card B' = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hΨinj, Subgroup.map_comap_eq_self_of_surjective hΨsurj]
  have hA60 : Nat.card A' = 60 := by
    rw [Subgroup.card_map_of_injective hιinj, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hAns : ¬ Group.IsSolvable A' := fun hs => CFSG.Quasithin.Dickson.not_isSolvable_alt_five
    (Group.isSolvable_of_surjective
      (f := ((A.equivMapOfInjective ι hιinj).symm.trans eA).toMonoidHom) (MulEquiv.surjective _))
  have hconj : ∀ g ∈ B', ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro g hg x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← toPGL_pgl2InnerAutPSL2_apply (ZMod p) hKodd hcard g a]
    refine ⟨Ψ g a, ?_, rfl⟩
    rw [← hBA (Ψ g) hg]
    exact Subgroup.mem_map_of_mem (Ψ g).toMonoidHom ha
  have hBA' : B' ≤ Subgroup.normalizer (A' : Set (PGL2 (ZMod p))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun h => ?_⟩
    have h1 := hconj g⁻¹ (B'.inv_mem hg) _ h
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hB
  have hle := C10P06.le_of_normalizes hp hBA' hA60 hAns
    (by rw [hBcard, hk]; exact C10P06.not_dvd_sixty_mul hp hp7 k)
  have hdvd : 2 ^ k ∣ 60 := by
    rw [← hk, ← hBcard, ← hA60]
    exact Subgroup.card_dvd_of_le hle
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

end CFSG.Quasithin.Vol2.Ch10.SecD
