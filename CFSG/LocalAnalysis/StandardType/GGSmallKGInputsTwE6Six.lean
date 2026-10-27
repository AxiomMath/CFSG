module

public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6Cover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Polynomial
open scoped Matrix

namespace SmallKG

theorem pow_three_mem_of_relIndex_dvd {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h : H.relIndex (Subgroup.zpowers x) ∣ 3) : x ^ 3 ∈ H := by
  have h1 : x ^ H.relIndex (Subgroup.zpowers x) ∈ H := by
    have := Subgroup.pow_index_mem (H.subgroupOf (Subgroup.zpowers x))
      (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x)
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul]
  exact pow_mem h1 k

theorem nine_dvd_two_pow_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) (h3n : 3 ∣ n) :
    9 ∣ 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ := h3n
  have hm : Odd m := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | hm
    · exfalso
      have h0 : (((2 ^ (3 * (k + k)) + 1 : ℕ)) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).2 h3
      have e : (((2 ^ (3 * (k + k)) + 1 : ℕ)) : ZMod 3) = 2 := by
        rw [show 3 * (k + k) = 6 * k by ring, pow_mul]
        push_cast
        rw [show ((64 : ZMod 3)) = 1 by decide, one_pow]
        decide
      rw [e] at h0
      exact absurd h0 (by decide)
    · exact hm
  have h := hm.nat_add_dvd_pow_add_pow 8 1
  rw [one_pow] at h
  rw [pow_mul]
  exact h

theorem twE6TwoMat_eq_neg_one : toMat TwistTag.E6.tag.rank twE6TwoMat = -1 := by
  decide +kernel


theorem exists_isElemAbelian_twistedE6_six {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (h9 : 9 ∣ 2 ^ n + 1) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  classical
  have h3 : 3 ∣ 2 ^ n + 1 := (by norm_num : 3 ∣ 9).trans h9
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    positivity
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  set v : WeylGroup TwistTag.E6.tag := (coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord
    with hvdef
  set M := toMat TwistTag.E6.tag.rank twE6TwoMat with hMdef
  have hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [hvdef, wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := 2) (f := n) hn L v
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hcube : ∀ x : ModGL TwistTag.E6.tag L, x ∈ adjointGroup TwistTag.E6.tag L →
      twistHom TwistTag.E6 L Fr x = x → x ^ 3 ∈ ι.range := by
    intro x hxC hxF
    have hX : Subgroup.zpowers x ≤ twistedFixedGroup TwistTag.E6 L Fr :=
      (Subgroup.zpowers_le).2 ((mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hxC, hxF⟩)
    have h := twisted_E6_relIndex_dvd_three Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr hX
    rw [← hrange] at h
    exact pow_three_mem_of_relIndex_dvd h
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) := by
    rw [hT0]
    exact CFSG.LieType.SeitzGeneration.isMulCommutative_map _ inferInstance
  have hMneg : M = -1 := twE6TwoMat_eq_neg_one
  have hfix : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ, (∀ i, b i ^ (2 ^ n + 1) = 1) →
      b ∈ fixedCharTuples M Fr := by
    intro b hb u
    have h1 : rootChar b u ^ (2 ^ n + 1) = 1 := by
      rw [rootChar, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb i, one_zpow]
    have h2 : rootChar b (-u) = (rootChar b u)⁻¹ := by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    have h3' : Units.map Fr.toMonoidHom (rootChar b u) = rootChar b u ^ (2 ^ n) :=
      Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
    rw [hMneg, Matrix.neg_mulVec, Matrix.one_mulVec, h2, h3']
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1])).symm
  have hchar : M.charpoly = cyclotomic 2 ℤ ^ 6 * 1 := by
    rw [hMdef, twE6Two_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hpq : ¬ 3 ∣ 2 ^ n := fun h => by
    have h1 := (Nat.dvd_add_right h).1 h3
    norm_num at h1
  have htors : Nat.card (torsionSubgroup (twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) (twistHom TwistTag.E6 L Fr)) hcomm 3) =
      3 ^ 6 := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm 3,
      natCard_fixedTorsion M Fr Nat.prime_two hFr Nat.prime_three (by norm_num),
      natCard_solutions_modMat Nat.prime_three M 1 twE6Two_pow (by norm_num) hchar hpq
        (orderOf_two_pow_zmod_three h3) (by simp)]
  set n₀ := canonicalRep (coxeterSystem TwistTag.E6.tag) L v with hn₀
  set Φ := twistHom TwistTag.E6 L Fr with hΦ
  let cg : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n₀ Φ
  set X : Subgroup (ModGL TwistTag.E6.tag L) := (twistedTorusOf n₀ Φ).map cg with hX
  have hXC : X ≤ adjointGroup TwistTag.E6.tag L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n₀ * Φ x * (g0 * n₀)⁻¹ = g0 * (n₀ * Φ x * n₀⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hXcomm : IsMulCommutative X := CFSG.LieType.SeitzGeneration.isMulCommutative_map cg hcomm
  set V : Subgroup (ModGL TwistTag.E6.tag L) := torsionSubgroup X hXcomm 3 with hV
  have hVcard : Nat.card V = 3 ^ 6 := by
    have hVmap : V = (torsionSubgroup (twistedTorusOf n₀ Φ) hcomm 3).map cg := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxp⟩
        refine ⟨y, ⟨hy, hcg ?_⟩, rfl⟩
        rw [map_pow, hxp, map_one]
      · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rw [← map_pow, hyp, map_one]
    rw [hVmap, Subgroup.card_map_of_injective hcg, htors]
  have hVrange : V ≤ ι.range := by
    rintro _ ⟨⟨t, ht, rfl⟩, htp⟩
    have ht3 : t ^ 3 = 1 := hcg (by rw [map_pow, htp, map_one])
    rw [hT0] at ht
    obtain ⟨a, -, rfl⟩ := ht
    have ha3 : a ^ 3 = 1 := by
      apply rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)
      have h1 : rootDiagUnitHom TwistTag.E6.tag L (a ^ 3) =
          rootDiagUnitHom TwistTag.E6.tag L 1 := by
        rw [map_pow, ht3, map_one]
      exact h1
    have hroot : ∀ i, ∃ b : Lˣ, b ^ 3 = a i := fun i => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a i : Lˣ) : L) (by norm_num : 0 < 3)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at hz
        exact (a i).ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
    choose b hb using hroot
    have hb3 : b ^ 3 = a := funext hb
    have hb9 : ∀ i, b i ^ (2 ^ n + 1) = 1 := by
      intro i
      obtain ⟨k, hk⟩ := h9
      rw [hk, pow_mul, show b i ^ 9 = (b i ^ 3) ^ 3 by rw [← pow_mul], hb i,
        show a i ^ 3 = 1 from congrFun ha3 i, one_pow]
    have hs : rootDiagUnitHom TwistTag.E6.tag L b ∈ twistedTorusOf n₀ Φ := by
      rw [hT0]
      exact ⟨b, hfix b hb9, rfl⟩
    have hst : rootDiagUnitHom TwistTag.E6.tag L a =
        (rootDiagUnitHom TwistTag.E6.tag L b) ^ 3 := by
      rw [← map_pow, hb3]
    rw [hst, map_pow]
    exact hcube _ (hXC ⟨_, hs, rfl⟩) (hXF _ ⟨_, hs, rfl⟩)
  have hcommE : IsMulCommutative (V.comap ι) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply hι
    have := hXcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact setLike_mul_comm a.2.1 b.2.1
  have hexpE : ∀ x ∈ V.comap ι, x ^ 3 = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hx.2
  have hmap : (V.comap ι).map ι = V := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hVrange
  exact ⟨V.comap ι, ⟨hcommE, hexpE⟩, by
    rw [← Subgroup.card_map_of_injective hι, hmap, hVcard]⟩


theorem exists_isElemAbelian_recipeR_six {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (h3n : 3 ∣ n) :
    ∃ E : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hbij : Function.Bijective (iterateFrobenius K 2 n) :=
    ⟨(iterateFrobenius K 2 n).injective,
      Finite.surjective_of_injective (iterateFrobenius K 2 n).injective⟩
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n) hbij with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨E₀, hE₀, hc⟩ := exists_isElemAbelian_twistedE6_six hn K hK σ hσ
    (nine_dvd_two_pow_add_one h3 h3n)
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := hσ
  obtain ⟨e, T₀, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ.toRingHom hσ'
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom
    hσ').2.2.1
  have hZ : Subgroup.center ↥(twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* ↥(twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hcard : Nat.card (E₀.map (recipeEquiv T hZ).toMonoidHom) = Nat.card E₀ :=
    Subgroup.card_map_of_injective (recipeEquiv T hZ).injective
  have h6 : 3 ^ 6 ≤ Nat.card (E₀.map (recipeEquiv T hZ).toMonoidHom) := by
    rw [hcard, hc]
  exact ⟨E₀.map (recipeEquiv T hZ).toMonoidHom, TableB.isElemAbelian_map hE₀ _, h6⟩

end SmallKG

theorem ggTwE6ThreeSixInput_holds :
    GGTwE6ThreeSixInput :=
  fun _ _ _ _ hn hK h3 h3n => SmallKG.exists_isElemAbelian_recipeR_six hn hK h3 h3n

theorem ggTwE6ThreeCoverRankInput_of_center
    (hC : GGTwE6ThreeCoverCenterInput) : GGTwE6ThreeCoverRankInput :=
  ggTwE6ThreeCoverRankInput_of_inputs ggTwE6ThreeSixInput_holds hC

end CFSG.StandardType
