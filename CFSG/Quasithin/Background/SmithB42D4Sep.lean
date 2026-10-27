module

public import CFSG.Quasithin.Background.SmithB42D4Pure
public import CFSG.LieType.Steinberg.Adjoint.RankOne
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem orderOf_conj' {G : Type*} [Group G] (a b : G) : orderOf (b * a * b⁻¹) = orderOf a := by
  have h := orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective a
  rw [← h]
  rfl

theorem rho_fixed_roots {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hρ : permLattice TwistTag.D4.perm α = α) :
    α = d4C ∨ α = d4P ∨ α = d4H ∨ α = -d4C ∨ α = -d4P ∨ α = -d4H := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  revert hρ
  have hlen : TwistTag.D4.tag.rootCertificate.roots.length = 24 := by decide
  rw [hlen] at hk
  interval_cases k <;> decide +kernel

section SL2

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem pinnedX_eq_eltUnit_two {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (c : K) : Xr α c = (rootOperatorFamily TwistTag.D4.tag).eltUnit K ⟨α, hα⟩ c := by
  rw [(rootOperatorFamily TwistTag.D4.tag).pinnedX_eq_eltUnit K hα c]
  congr 1
  rcases (rootOperatorFamily TwistTag.D4.tag).pinnedFamilySign_eq α with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem orderOf_C_negC_dvd [Finite K] (μ lam : K) :
    orderOf (Xr d4C μ * Xr (-d4C) lam) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hk : TwistTag.D4.tag.cartan ⟨2, by decide⟩ ⟨0, by decide⟩ = -1 := by decide
  obtain ⟨φ, hφ, hup, hlow⟩ :=
    CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom (K := K) (rootOperatorFamily TwistTag.D4.tag) hk
  have hC : d4C = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e1 : Xr d4C μ = ((φ (CFSG.LieType.Steinberg.sl2Upper μ) :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    rw [hup, RootOperatorFamily.coe_eltElement, hC, pinnedX_eq_eltUnit_two]
    rfl
  have e2 : Xr (-d4C) lam = ((φ (CFSG.LieType.Steinberg.sl2Lower lam) :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    rw [hlow, RootOperatorFamily.coe_eltElement, hC, pinnedX_eq_eltUnit_two]
    rfl
  rw [e1, e2, ← Subgroup.coe_mul, ← map_mul, Subgroup.orderOf_coe, orderOf_injective φ hφ]
  exact orderOf_dvd_natCard _

end SL2

section Orders

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem pow_two_HH (μ lam : K) : (Xr d4H μ * Xr d4H lam) ^ 2 = 1 := by
  rw [← pinnedX_add, sq, Xr_mul_self]

theorem pow_two_of_comm {α : Fin TwistTag.D4.tag.rank → ℤ} (h : d4CommB d4H α = true)
    (μ lam : K) : (Xr d4H μ * Xr α lam) ^ 2 = 1 := by
  have hc := (commute_of_d4CommB (K := K) h μ lam).eq
  rw [sq, mul_assoc, ← mul_assoc (Xr α lam), ← hc, mul_assoc, Xr_mul_self, mul_one,
    Xr_mul_self]

theorem pow_four_of_sum {α γ : Fin TwistTag.D4.tag.rank → ℤ} (h : d4SumB d4H α γ = true)
    (μ lam : K) : (Xr d4H μ * Xr α lam) ^ 4 = 1 := by
  have hc := commutator_of_d4SumB (K := K) h μ lam
  rw [commutatorElement_def, Xr_inv, Xr_inv] at hc
  have h2 : (Xr d4H μ * Xr α lam) ^ 2 = Xr γ (μ * lam) := by
    rw [sq, ← hc]; group
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq, Xr_mul_self]

end Orders

section Bruhat

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hσ3 in
theorem U_comm_H {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) (x : K) :
    u * Xr d4H x = Xr d4H x * u := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := (mem_U_iff σ hσ3).1 hu
  have h1 : qE σ b c d e f * Xr d4H x = Xr d4H x * qE σ b c d e f := by
    rw [qE_H σ, qE_commute_iff σ hσ3]
    simp [tr]
  rw [mul_assoc, h1, ← mul_assoc, ← (commute_H_ox₁ x a σ).eq, mul_assoc]

include hσ3 in
theorem borel_conj_H {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K τ₀) (x : K) :
    ∃ y : K, b * Xr d4H x * b⁻¹ = Xr d4H y := by
  have hb' : b ∈ (graphFixedRootBorel TwistTag.D4 K τ₀ : Set (ModGL TwistTag.D4.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul σ.surjective] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  have hhT : h ∈ torusGroup TwistTag.D4.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  refine ⟨(rootChar c d4H : K) * x, ?_⟩
  have e1 : rootDiagUnit TwistTag.D4.tag c * u * Xr d4H x * (rootDiagUnit TwistTag.D4.tag c * u)⁻¹ =
      rootDiagUnit TwistTag.D4.tag c * Xr d4H x * (rootDiagUnit TwistTag.D4.tag c)⁻¹ := by
    rw [mul_assoc (rootDiagUnit TwistTag.D4.tag c), U_comm_H σ hσ3 hu]; group
  rw [e1, rootDiagUnit_conj_pinnedX c (isRoot_of_d4 (by decide +kernel))]

omit
  [Finite K] in
theorem orderOf_H_negH_dvd [Finite K] (μ lam : K) :
    orderOf (Xr d4H μ * Xr (-d4H) lam) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K (rB * rA)
  have hC : (rB * rA) • d4C = d4H := by rw [mul_smul, rA_C, rB_P]
  have h1 : n * Xr d4C μ * n⁻¹ = Xr d4H μ := by
    rw [canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)), hC]
  have h2 : n * Xr (-d4C) lam * n⁻¹ = Xr (-d4H) lam := by
    rw [canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)), smul_neg, hC]
  rw [← h1, ← h2, ← conj_mul2, orderOf_conj']
  exact orderOf_C_negC_dvd μ lam

include hσ3 in
theorem order_mul_conj {g : ModGL TwistTag.D4.tag K} (hg : g ∈ C₀) :
    orderOf (Xr d4H 1 * (g * Xr d4H 1 * g⁻¹)) ∣ 4 ∨
      orderOf (Xr d4H 1 * (g * Xr d4H 1 * g⁻¹)) ∣
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hg' : g ∈ (C₀ : Set (ModGL TwistTag.D4.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hw
  obtain ⟨lam, hlam⟩ := borel_conj_H σ hσ3 hb' 1
  obtain ⟨μ, hμ⟩ := borel_conj_H σ hσ3 (inv_mem hb) 1
  have hroot : IsRoot TwistTag.D4.tag ((w : WeylGroup TwistTag.D4.tag) • d4H) :=
    IsRoot.smul (isRoot_of_d4 (by decide +kernel)) _
  have hfixw : permLattice TwistTag.D4.perm ((w : WeylGroup TwistTag.D4.tag) • d4H) =
      (w : WeylGroup TwistTag.D4.tag) • d4H := by
    rw [← weylTwist_smul_permLattice, (mem_relWeylTwist TwistTag.D4).1 w.2]
    congr 1
    exact List.ofFn_injective (by decide +kernel)
  have e1 : (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K (w : WeylGroup TwistTag.D4.tag) *
      b') * Xr d4H 1 * (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (w : WeylGroup TwistTag.D4.tag) * b')⁻¹ =
      b * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam * b⁻¹ := by
    rw [← canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)) lam, ← hlam]
    group
  have e2 : Xr d4H 1 * (b * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam * b⁻¹) =
      b * (Xr d4H μ * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam) * b⁻¹ := by
    rw [← hμ, inv_inv]; group
  rw [e1, e2, orderOf_conj']
  rcases rho_fixed_roots hroot hfixw with h | h | h | h | h | h <;> rw [h]
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one
      (pow_two_of_comm (by decide +kernel) μ lam)).trans (by norm_num))
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one
      (pow_two_of_comm (by decide +kernel) μ lam)).trans (by norm_num))
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one (pow_two_HH μ lam)).trans (by norm_num))
  · exact Or.inl (orderOf_dvd_of_pow_eq_one (pow_four_of_sum (γ := d4P) (by decide +kernel) μ lam))
  · exact Or.inl (orderOf_dvd_of_pow_eq_one (pow_four_of_sum (γ := d4C) (by decide +kernel) μ lam))
  · exact Or.inr (orderOf_H_negH_dvd μ lam)

end Bruhat

end CFSG.Quasithin.B42D4
