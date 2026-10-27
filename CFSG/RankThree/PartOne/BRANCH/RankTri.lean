module

public import CFSG.RankThree.PartOne.BRANCH.RankFinal
public import CFSG.RankThree.PartOne.BRANCH.RankSylow
public import CFSG.RankThree.PartOne.BRANCH.RankArith
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQuadraticTorus

public section

namespace CFSG.RankThree.PartOne.BRANCH

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.N143X CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem torusCoordHom_injective_D4
    {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K - 1)) :
    Function.Injective (torusCoordHom Tag.D4 K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1 : t ∈ (zpowMatrix (G := Kˣ) Tag.D4.cartan).ker := by
    rw [MonoidHom.mem_ker]
    exact (torusCoordHom_eq_one_iff t).1 ht
  have hc := card_ker_zpowMatrix_D4_eq_one (K := K) hodd
  have : Subsingleton (zpowMatrix (G := Kˣ) Tag.D4.cartan).ker :=
    (Nat.card_eq_one_iff_unique.1 hc).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨t, h1⟩ : (zpowMatrix (G := Kˣ)
    Tag.D4.cartan).ker) 1)

theorem triality_split_bound
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (h3 : 2 ^ f % 3 = 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)} (hE : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (1 + 4) := by
  classical
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK, ← pow_mul]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hC, hTor, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K
    hK 1 (Or.inl rfl) σ (fun c => by rw [pow_one]; exact hσ c)
  have hle1 : graphFixedRootTorus TwistTag.D4 K σ ≤ graphFixedRootGroup TwistTag.D4 K σ :=
    graphFixedRootTorus_le _ _ _
  have hle2 : graphFixedRootTorus TwistTag.D4 K σ ≤ torusGroup TwistTag.D4.tag K :=
    graphFixedRootTorus_le_torusGroup _
  let T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ) :=
    (graphFixedRootTorus TwistTag.D4 K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ)
  let eT : T ≃* graphFixedRootTorus TwistTag.D4 K σ := Subgroup.subgroupOfEquivOfLe hle1
  have hinj : Function.Injective (torusCoordHom TwistTag.D4.tag K) :=
    torusCoordHom_injective_D4 hodd
  let eτ : (Fin TwistTag.D4.tag.rank → Kˣ) ≃* torusGroup TwistTag.D4.tag K :=
    MulEquiv.ofBijective (torusCoordHom TwistTag.D4.tag K) ⟨hinj, torusCoordHom_surjective⟩
  let ψ : T →* (Fin TwistTag.D4.tag.rank → Kˣ) :=
    eτ.symm.toMonoidHom.comp ((Subgroup.inclusion hle2).comp eT.toMonoidHom)
  have hψ : Function.Injective ψ :=
    eτ.symm.injective.comp ((Subgroup.inclusion_injective hle2).comp eT.injective)
  have hTcard : Nat.card T = ((2 ^ f) ^ 3 - 1) * (2 ^ f - 1) := by
    rw [Nat.card_congr eT.toEquiv]
    exact hTor
  have hidx : ¬ 3 ^ (1 + 1) ∣ T.index := by
    have hmul := T.index_mul_card
    rw [hTcard, hC] at hmul
    have := not_nine_dvd_triality_split hQ2 h3 (by rw [mul_comm]; exact hmul)
    simpa using this
  have hb := card_le_of_torus Nat.prime_three ψ hψ hidx hE
  have hrank : TwistTag.D4.tag.rank = 4 := rfl
  rwa [hrank] at hb

theorem triality_twisted_bound
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (h3 : 2 ^ f % 3 = 2)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (1 + 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hℓq : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_algebraicClosure_two (K := K) (g := f * 3) (by rw [hK, ← pow_mul])
  have : IsAlgClosed (AlgebraicClosure K) := inferInstance
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hnC : trialityOpposition L ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' trialityOpposition_mem_monomialSubgroup
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := 2) hf L (trialityOpposition L) hnC
  have hT := d4Q_twistedTorus Fr
  set Z : Subgroup (ModGL TwistTag.D4.tag L) :=
    (fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L) with hZdef
  have hZcard : Nat.card Z = (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) := by
    rw [hZdef, Subgroup.card_map_of_injective rootDiagUnit_injective]
    exact d4Q_card hℓq hFr
  have hN : (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) ≠ 0 := by positivity
  obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K
    hK 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  have hCpos : 0 < Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Nat.card_pos
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes
    (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * ((2 ^ f + 1) * ((2 ^ f) ^ 3 + 1))
      + 4)
  have hNpos : 0 < (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) := Nat.pos_of_ne_zero hN
  have hp3 : 3 < p := by omega
  have hpC : ¬ p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun h => by
    have := Nat.le_of_dvd hCpos h
    nlinarith
  have hpN : ¬ p ∣ (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) := fun h => by
    have := Nat.le_of_dvd hNpos h
    nlinarith
  have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      p ^ ((2 ^ f + 1) * ((2 ^ f) ^ 3 + 1)).factorization p := by
    rw [Nat.factorization_eq_zero_of_not_dvd hpC, Nat.factorization_eq_zero_of_not_dvd hpN]
  have hrange := triEmb_range Nat.prime_two hf hK hσ Fr hFr
  obtain ⟨hTdvd, hTdiv, -, -⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
    triEmb_injective (twistHom TwistTag.D4 L Fr) (trialityOpposition L) g0 hg0C hg0 hp hp3 hN
    (fun X hX hXC hXF => triEmb_rational Nat.prime_two hf hK hσ Fr hFr X hXC hXF) Z hT.symm.le
    hZcard hord
  set T := subtorusImage (triEmb K σ L) g0 Z with hTdef
  have hTcard : Nat.card T = (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) := by
    have h1 : (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) / Nat.card T = 1 := Nat.dvd_one.1 hTdiv
    have h2 := Nat.div_mul_cancel hTdvd
    rw [h1, one_mul] at h2
    exact h2
  have hidx : ¬ 3 ^ (1 + 1) ∣ T.index := by
    have hmul := T.index_mul_card
    rw [hTcard, hC] at hmul
    have := not_nine_dvd_triality_twisted hQ2 h3 (by rw [mul_comm]; exact hmul)
    simpa using this
  obtain ⟨g, E₁, hE₁, hcard, hmem⟩ :=
    exists_conj_le_of_not_dvd_index T Nat.prime_three hidx (isPGroup_of_pow_eq_one hE)
  have h9 := card_le_sq_of_conj_into_fixedTuples (L := L) (fixedCharTuples d4QM Fr)
    (fun a ha b hb h => eq_of_d4QCoord_eq hFr ha hb h) (p := 3) (by norm_num)
    (fun x hx => hE x (hE₁ hx)) g0 g⁻¹ fun y hy => by
      rw [inv_inv]
      exact (mem_subtorusImage_iff (triEmb K σ L) g0 Z _).1 (hmem y hy)
  calc Nat.card E ≤ 3 ^ 1 * Nat.card E₁ := hcard
    _ ≤ 3 ^ 1 * 3 ^ 2 := Nat.mul_le_mul_left _ h9
    _ = 3 ^ (1 + 2) := (pow_add 3 1 2).symm

theorem trialityThreeRank
    : TrialityThreeRank := by
  intro X _ _ f hX E hE hcard
  have hf : 1 ≤ f := hX.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hX.2
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv X e.toEquiv
  have hE3 : ∀ x ∈ E.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 3) y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  rcases two_pow_mod_three f with ⟨h3, -⟩ | ⟨h3, -⟩
  · have hb := triality_split_bound hf K hK' σ.toRingHom (fun c => hσ c) h3 hE3
    rw [hcard'] at hb
    norm_num at hb
  · have hb := triality_twisted_bound hf K hK' σ hσ h3 hE3
    rw [hcard'] at hb
    norm_num at hb

end CFSG.RankThree.PartOne.BRANCH
