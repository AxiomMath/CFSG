module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofExc
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Levi
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open Res417Three Res417Five Res417Six

namespace Res417Seven

section Certs


theorem exists_graphFixedRootGroup_of_trialityD4 {X : Type} [Group X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K),
      Nat.card K = (2 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧ σ ^ 3 = 1 ∧ 1 ≤ f ∧
      IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨hadm, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hX
  have hf : 1 ≤ f := hadm.2.1
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 3)
      (by rw [Fintype.card_eq_nat_card, hK3, ← pow_mul])
  have hσs : Function.Surjective σ := Finite.injective_iff_surjective.1 σ.injective
  set σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσs⟩ with hσ'def
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨-, -, hTG, hsimple, hnonab⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group 2 f Nat.prime_two hf K hK3
      L 1 (Or.inl rfl) σ (fun c => by rw [pow_one]; exact hσ c) (iterateFrobenius L 2 f)
      (fun c => iterateFrobenius_def 2 f c)
  set e3 := MulEquiv.subgroupCongr hTG
  have : IsSimpleGroup (twistedFixedGroup TwistTag.D4 K σ) := MulEquiv.isSimpleGroup e3
  obtain ⟨e2⟩ := Sec11.KS11Lie3Proof.nonempty_derivedCentralQuotient_mulEquiv
    (twistedFixedGroup TwistTag.D4 K σ) (by
      obtain ⟨x, y, hxy⟩ := hnonab
      refine ⟨e3.symm x, e3.symm y, fun h => hxy ?_⟩
      have := congrArg e3 h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)
  have hpow : ∀ c : K, σ' (σ' (σ' c)) = c := fun c => by
    have := Fintype.ofFinite K
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have h1 : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [Fintype.card_eq_nat_card, hK3]
      ring
    rw [h1, FiniteField.pow_card]
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ', hK3, hσ, ?_, hf, ?_, ?_⟩
  · apply RingEquiv.ext
    intro c
    exact hpow c
  · rw [hσσ']
    exact hsimple
  · rw [hσσ']
    exact ⟨e.trans (e2.trans e3)⟩

theorem exists_conj_le_graphFixedParabolicLevi (t : TwistTag) {k : Type} [Field k] [Finite k]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p) (σ : k ≃+* k)
    (hσ : σ ^ t.order = 1) {A R : Subgroup (ModGL t.tag k)}
    (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom) (hAp : IsPGroup p A)
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    ∃ x ∈ graphFixedRootGroup t k σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      J ≠ Set.univ ∧
        A.map (MulAut.conj x).toMonoidHom ≤ graphFixedParabolicLevi t k σ.toRingHom J := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL t.tag k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ graphFixedRootGroup t k σ.toRingHom := hg
  have hJ' : ((RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l :
      Set (Fin t.foldedTag.rank)) ≠ Set.univ := hJ
  set J : Set (Fin t.foldedTag.rank) := (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l
  change {x : ModGL t.tag k | x ∈ graphFixedRootGroup t k σ.toRingHom ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule t.tag k)) = F c} =
    ((graphFixedParabolic t k σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL t.tag k)) at hset
  have hA1 : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
      (graphFixedParabolic t k σ.toRingHom J)).index := by
    rw [graphFixedParabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
    exact not_dvd_card_of_isPGroup hrp (hfin r)
  have hA1p : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) := hAp.map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1 hA1p hindex
  have hyC : y ∈ graphFixedRootGroup t k σ.toRingHom :=
    graphFixedParabolic_le t k σ.toRingHom J hy
  refine ⟨y * g'⁻¹, mul_mem hyC (inv_mem hgC), J, hJ', ?_⟩
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  rw [hmap]
  exact hyA

theorem not_three_dvd_card_units_of_odd {K : Type} [Field K] {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 3) : ¬ 3 ∣ Nat.card Kˣ := by
  rw [Nat.card_units, hK, ← pow_mul]
  have h := (two_pow_mod_three (f * 3)).2 (hf.mul (by decide))
  generalize 2 ^ (f * 3) = m at h ⊢
  omega

end Certs

section Main


theorem k417NoDatumD4Odd_holds : K417NoDatumD4Odd := by
  intro X _ f hf hX D hD
  obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hD
  obtain ⟨K, _, _, _, σ, hK, -, hσ3, -, -, ⟨φ⟩⟩ := exists_graphFixedRootGroup_of_trialityD4 hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set ψ : X →* ModGL TwistTag.D4.tag K := C.subtype.comp φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψC : ∀ x, ψ x ∈ C := fun x => (φ x).2
  have hT1 : T ≠ ⊥ := fun h => hTF (h ▸ bot_le)
  have hT'1 : T.map ψ ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hT'C : T.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'C : F.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'T' : F.map ψ ≤ Subgroup.normalizer ((T.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map ψ)
  have hF'3 : ∀ y ∈ F.map ψ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hDe.2 x (hFD hx), map_one]
  have hF'p : IsPGroup 3 (F.map ψ) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF'3 _ y.2)⟩
  obtain ⟨x, -, J, hJ, hle⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 hF'C hF'p hT'C (hT2.map ψ) hT'1 hF'T'
  have hcard := card_le_three_of_le_graphFixedParabolicLevi σ hσ3
    (not_three_dvd_card_units_of_odd hf hK) hJ hle (by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hF'3 y hy, map_one])
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
    Subgroup.card_map_of_injective hψ] at hcard
  omega

end Main

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
