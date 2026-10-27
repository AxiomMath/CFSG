module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcF4
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.Ree

namespace AutSt

theorem exists_orth_F4 : ∀ j : Fin (Tag.rank .F4), ∃ k, k ≠ j ∧ Tag.cartan .F4 k j = 0 := by
  intro j
  fin_cases j <;> decide


variable {K : Type} [Field K]

theorem goodAut_of_entrywise {τ : Tag} [Finite K] [CharP K 2] {D : AdjData τ} (hD : D.Valid)
    (hτ : NoG2 τ) (horth : ∀ j : Fin τ.rank, ∃ k, k ≠ j ∧ τ.cartan k j = 0)
    (hnb : ∀ k : Fin τ.rank, ∃ l, τ.cartan k l = -1) {σ : K ≃+* K}
    (hJ : IsSimpleGroup (fixSub (entrywiseAdjointAut τ σ))) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {u z : adjointGroup τ K} (hz : z ∈ rootGroup (rootOperatorFamily τ) K γ)
    (hz1 : z ≠ 1) : GGGoodAut (u * z * u⁻¹) (entrywiseAdjointAut τ σ) := by
  obtain ⟨g, j, hg⟩ := exists_conj_xPar_single (F := rootOperatorFamily τ) hγ hz hz1
  obtain ⟨k, hkj, h0⟩ := horth j
  obtain ⟨l, hkl⟩ := hnb k
  have ha3 := orderOf_xPar_mul_xPar_neg (F := rootOperatorFamily τ) (K := K) hkl
  have hcomm := commute_xPar_single_xy (F := rootOperatorFamily τ) hD hτ hkj.symm h0 (1 : K)
  have hconj : g * u⁻¹ * (u * z * u⁻¹) * (g * u⁻¹)⁻¹ = g * z * g⁻¹ := by group
  refine goodAut_of_fixed_simple hJ (g * u⁻¹) ?_
    (xPar (rootOperatorFamily τ) (Pi.single k 1) 1 * xPar (rootOperatorFamily τ) (-Pi.single k 1) 1)
    ?_ ?_ ?_ ?_
  · rw [hconj, hg, entrywiseAdjointAut_xPar_one]
  · rw [map_mul, entrywiseAdjointAut_xPar_one, entrywiseAdjointAut_xPar_one]
  · rw [hconj, hg]
    exact hcomm.eq.symm
  · intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  · rw [ha3]
    decide

theorem autModel_F4
    {f : ℕ} (hf : 1 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) :
    GGAutModel (adjointGroup .F4 K) (GGModelRoot (f4Datum K) .F4 (MonoidHom.id _)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨hord₀, -, ⟨Θ₀, hΘ₀, -, hker₀⟩, hinv₀, -, hFr₀, -⟩ :=
    even_F4_exact_automorphism_normal_form hf K hK
  let φ : MulAut (adjointGroup .F4 K) := ReeTag.F4.finiteExceptionalAut K
  let Fr : MulAut (adjointGroup .F4 K) := ReeTag.F4.finiteFrobeniusAut K
  let Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * f)) := Θ₀
  have hord : orderOf φ = 2 * f := hord₀
  have hker : Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    hker₀
  have hΘ : ∀ (α : MulAut (adjointGroup .F4 K)) (g : adjointGroup .F4 K) (k : ℕ),
      α = MulAut.conj g * φ ^ k → Θ α = Multiplicative.ofAdd (k : ZMod (2 * f)) := hΘ₀
  have hinv : ∀ (α : MulAut (adjointGroup .F4 K)) (g : adjointGroup .F4 K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * φ ^ k → α ^ 2 = 1 → k = 0 ∨ k = f := hinv₀
  have hFr : ∀ e : ℕ, f = 2 * e → φ ^ f = Fr ^ e := hFr₀
  have hΘk : ∀ k : ℕ, Θ (φ ^ k) = Multiplicative.ofAdd (k : ZMod (2 * f)) := fun k =>
    hΘ _ 1 k (by rw [map_one, one_mul])
  have hpow : ∀ c ∈ Subgroup.zpowers φ, ∃ n, n < 2 * f ∧ c = φ ^ n := by
    intro c hc
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h0 : (0 : ℤ) < ((2 * f : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < 2 * f)
    have hnn := Int.emod_nonneg z h0.ne'
    have hlt := Int.emod_lt_of_pos z h0
    refine ⟨(z % ((2 * f : ℕ) : ℤ)).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← hord, zpow_mod_orderOf]
  have : NeZero (2 * f) := ⟨by omega⟩
  refine autModel_of_hom Θ (Subgroup.zpowers φ) (by rw [hker])
    (by rw [hker, Subgroup.relIndex_self]; exact odd_one) (fun σ => ?_) (fun c hc h1 => ?_) ?_
  · refine ⟨φ ^ (Multiplicative.toAdd (Θ σ)).val, Subgroup.npow_mem_zpowers _ _, ?_⟩
    rw [hΘk, ZMod.natCast_zmod_val]
    rfl
  · obtain ⟨n, hn, rfl⟩ := hpow c hc
    rw [hΘk, ofAdd_eq_one, ZMod.natCast_eq_zero_iff] at h1
    rw [Nat.eq_zero_of_dvd_of_lt h1 hn, pow_zero]
  · rintro r hr c hc hc2 hc1 e he
    rw [hker] at he
    refine goodAut_conj_inner ?_ he
    obtain ⟨n, hn, rfl⟩ := hpow c hc
    rcases hinv _ 1 n hn (by rw [map_one, one_mul]) hc2 with rfl | rfl
    · exact absurd (pow_zero φ) hc1
    obtain ⟨e, he'⟩ := hfe
    have hf2 : n = 2 * e := by omega
    subst hf2
    have he1 : 1 ≤ e := by omega
    set σ := frobeniusEquiv K 2 ^ e
    have hσ : ∀ c, σ c = c ^ 2 ^ e := RootDetectExc.frobeniusEquiv_pow_apply e
    obtain ⟨-, -, hFrφ₀, hent₀, -, hmap₀, ⟨-, hsimple₀, -⟩, -⟩ :=
      even_F4_canonical_field_full_centralizer he1 K hK σ hσ
    have hFrφ : Fr ^ e = φ ^ (2 * e) := hFrφ₀
    have hent : entrywiseAdjointAut .F4 σ = Fr ^ e := hent₀
    have hmap : (fixSub (φ ^ (2 * e))).map (adjointGroup .F4 K).subtype = fixedFieldImage .F4 σ :=
      hmap₀
    have hsimple : IsSimpleGroup (fixedFieldImage .F4 σ) := hsimple₀
    have hc : φ ^ (2 * e) = entrywiseAdjointAut .F4 σ := by rw [hent, hFrφ]
    rw [hc]
    have hJ : IsSimpleGroup (fixSub (entrywiseAdjointAut .F4 σ)) := by
      rw [← hc]
      let e₁ : fixSub (φ ^ (2 * e)) ≃* fixedFieldImage .F4 σ :=
        (Subgroup.equivMapOfInjective _ (adjointGroup .F4 K).subtype Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hmap)
      have : Nontrivial (fixSub (φ ^ (2 * e))) := e₁.toEquiv.nontrivial
      exact IsSimpleGroup.isSimpleGroup_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective
    obtain ⟨hr2, γ, ⟨hγ, -⟩, u, z, hz, hrz⟩ := hr
    rw [MonoidHom.id_apply] at hrz
    subst hrz
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [mul_one, mul_inv_cancel, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    exact goodAut_of_entrywise f4Data_valid noG2_F4 exists_orth_F4
      (fun k => (CFSG.LieType.Steinberg.Adjoint.neighbour_F4 k).imp fun _ h => h.1) hJ
      (mem_adjDatum_roots.mp hγ) hz hz1

end AutSt

section Family


theorem ggAutModelAt_F4 : GGAutModelAt .F4 := by
  intro n f hadm _ hF
  obtain ⟨-, hf, -⟩ := hadm
  have hfe : Even f := by
    rcases Nat.even_or_odd f with h | h
    · exact h
    · exact absurd ⟨rfl, h⟩ hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨(ggU .F4 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_,
    AutSt.autModel_F4 hf hfe hK⟩
  rw [MonoidHom.ker_id]
  exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm

theorem ggAutStructureAt_F4 : GGAutStructureAt .F4 :=
  ggAutStructureAt_of_autModelAt ggAutModelAt_F4

end Family

end CFSG.StandardType
