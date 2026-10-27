module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace WitOmNs

open Module QuadraticMap CFSG.RankThree.Classical2

section Four

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

theorem exists_four_of_card {T : Finset (Fin s)} (h : 4 ≤ T.card) :
    ∃ i ∈ T, ∃ j ∈ T, ∃ k ∈ T, ∃ l ∈ T, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have h1 := Finset.card_erase_of_mem hi
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase i).card)
  have h2 := Finset.card_erase_of_mem hj
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < ((T.erase i).erase j).card)
  have h3 := Finset.card_erase_of_mem hk
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < (((T.erase i).erase j).erase k).card)
  simp only [Finset.mem_erase] at hj hk hl
  exact ⟨i, hi, j, hj.2, k, hk.2.2, l, hl.2.2.2, Ne.symm hj.1, Ne.symm hk.2.1, Ne.symm hl.2.2.1,
    Ne.symm hk.1, Ne.symm hl.2.1, Ne.symm hl.1⟩

theorem two_add (i j : Fin s) (a b a' b' : L) :
    two Φ i j (a + b) (a' + b') = two Φ i j a a' + two Φ i j b b' := by
  rw [two, two, two, blk_add, blk_add]
  abel

theorem exists_singular_four [CharP K 2]
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) {ζ : L} (hζ1 : ζ ≠ 1)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) (hQ : ∀ m, m = i ∨ m = j ∨ m = k ∨ m = l →
      ∀ a, Q (blk Φ m (ζ * a)) = Q (blk Φ m a)) :
    ∃ U : Submodule K V, finrank K U = finrank K (L × L) ∧ ∀ u ∈ U, Q u = 0 := by
  classical
  set ι : L × L →ₗ[K] V :=
    { toFun := fun z => two Φ i j z.1 z.1 + two Φ k l z.2 z.2
      map_add' := fun z z' => by
        simp only [Prod.fst_add, Prod.snd_add, two_add]
        abel
      map_smul' := fun c z => by
        simp only [Prod.smul_fst, Prod.smul_snd, two, blk_smul, RingHom.id_apply, smul_add] }
    with hι
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, y⟩ hz
    rw [LinearMap.mem_ker] at hz
    change two Φ i j x x + two Φ k l y y = 0 at hz
    have h0 : Φ.symm (two Φ i j x x + two Φ k l y y) = 0 := by rw [hz, map_zero]
    simp only [two, blk, map_add, LinearEquiv.symm_apply_apply] at h0
    have hx := congrFun (congrArg Prod.fst h0) i
    have hy := congrFun (congrArg Prod.fst h0) k
    simp [hij.symm, hik.symm, hil.symm, hjk.symm, hkl, hik] at hx hy
    exact Prod.ext hx hy
  have hQij := quad_blk_eq_of_inv hdec hζ1 (hQ i (Or.inl rfl)) (hQ j (Or.inr (Or.inl rfl)))
  have hQkl := quad_blk_eq_of_inv hdec hζ1 (hQ k (Or.inr (Or.inr (Or.inl rfl))))
    (hQ l (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨LinearMap.range ι, LinearMap.finrank_range_of_inj hinj, ?_⟩
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change Q (two Φ i j x x + two Φ k l y y) = 0
  have hpol : polar Q (two Φ i j x x) (two Φ k l y y) = 0 := by
    rw [two, two, polar_add_left, polar_add_right, polar_add_right, polar_blk hdec,
      polar_blk hdec, polar_blk hdec, polar_blk hdec]
    simp [hik, hil, hjk, hjl]
  rw [QuadraticMap.map_add (Q : V → K), hpol, add_zero, quad_two hdec hij, quad_two hdec hkl,
    ← hQij, ← hQkl, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

end Four

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem card_le_pow_three (hQ : (polarBilin Q).Nondegenerate)
    (hts : ∀ U : Submodule K V, finrank K U = 4 → ∃ u ∈ U, Q u ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K + 1) {A : Subgroup (V ≃ₗ[K] V)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAO : ∀ a ∈ A, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : Nat.card A ≤ p ^ 3 := by
  classical
  obtain ⟨g, hfact, s, κ, hκ, Φ, β, kf, hζo, hdeg, hβalt, hdecB, hkA⟩ :=
    exists_frame_of_comm hQ hp hpK hAc hAp hAO
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  have hL2 : finrank K (AdjoinRoot g) = 2 := by rw [(CoordSL.rootPB g).finrank, hdeg]
  have hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w')) := fun d d' w w' => by
    simpa only [polarBilin_apply_apply] using hdecB d d' w w'
  have := LayerCores.finite_linearEquiv (K := K) (V := V)
  have hFA : Function.Injective (fun a : A => ((a : V ≃ₗ[K] V) : V →ₗ[K] V)) :=
    fun a a' h => Subtype.ext (LinearEquiv.toLinearMap_injective h)
  set T : Finset (Fin s) :=
    Finset.univ.filter (fun l => ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) l) with hT
  have h1 := card_le_pow_of_supp hp hζp hFA (fun a => hkA a a.2) T (fun a l hl => by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
      not_not] at hl
    exact hl a a.2)
  have hinv : ∀ m ∈ T, ∀ a, Q (blk Φ m (ζ * a)) = Q (blk Φ m a) := by
    intro m hm a
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨a₀, ha₀, hk₀⟩ := hm
    exact quad_blk_mul_eq hp hζp (x := (a₀ : V →ₗ[K] V))
      (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hAO a₀ ha₀) v) (hkA a₀ ha₀) hk₀ a
  have hT3 : T.card ≤ 3 := by
    by_contra h
    push Not at h
    obtain ⟨i, hi, j, hj, k, hk, l, hl, hij, hik, hil, hjk, hjl, hkl⟩ :=
      exists_four_of_card (show 4 ≤ T.card by omega)
    obtain ⟨U, hU, hUs⟩ := exists_singular_four hdec hζ1 hij hik hil hjk hjl hkl (by
      rintro m (rfl | rfl | rfl | rfl)
      · exact hinv _ hi
      · exact hinv _ hj
      · exact hinv _ hk
      · exact hinv _ hl)
    rw [Module.finrank_prod, hL2] at hU
    obtain ⟨u, hu, hQu⟩ := hts U hU
    exact hQu (hUs u hu)
  exact h1.trans (Nat.pow_le_pow_right hp.pos hT3)

end Card

section MinusFour

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin.Twisted

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem false_of_minusFour {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {f : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2 ^ f) {ψ : spinGroup (quadMinus 4 K b c) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (minusDatum 4 hirr) .POmegaMinus 4 f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f + 1) : False := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr le_rfl]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      PsiDiag.SpinM.exists_mem_centralizer hirr le_rfl ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus 4 K b c le_rfl hirr
  set πe := MulEquiv.ofBijective (AutOm.spinModelMinus le_rfl hirr)
    ⟨AutOm.spinModelMinus_injective le_rfl hirr, AutOm.spinModelMinus_surjective le_rfl hirr⟩
    with hπe
  set e₁ := CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
    (coordinateQuadMinus 4 K (by omega) b c) with he₁
  set φ : ↥(orthDerived (coordinateQuadMinus 4 K (by omega) b c)) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp e₁.symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ := hψinj.comp (πe.symm.injective.comp e₁.symm.injective)
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨e₁ (πe u), ?_⟩
      simp [hφ]
  obtain ⟨hAc, hAp, hcardA⟩ := bstar_preimage hctx.2.1.2.1 hφinj (hφrange ▸ hBψ)
  have hAO : ∀ a ∈ (Bs.comap φ).map (orthDerived (coordinateQuadMinus 4 K (by omega) b c)).subtype,
      a ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus 4 K (by omega) b c) := by
    rintro _ ⟨Y, -, rfl⟩
    exact Subgroup.commutator_le_self _ Y.2
  have hts : ∀ U : Submodule K (Fin (2 * 4) → K), finrank K U = 4 →
      ∃ u ∈ U, coordinateQuadMinus 4 K (by omega) b c u ≠ 0 := by
    intro U hU
    set e := coordinateMinusIsometry 4 K (by omega) b c with he
    obtain ⟨u', hu', hQu'⟩ := CFSG.SeitzReduction.F4Pilot.exists_quadMinus_ne_zero hirr
      (n := 4) (by omega) (U.map e.symm.toLinearMap)
      ((CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.submodule_finrank_isometry
        e.symm U).trans hU)
    obtain ⟨u, hu, rfl⟩ := hu'
    refine ⟨u, hu, fun h0 => hQu' ?_⟩
    rw [← h0]
    exact e.symm.map_app u
  have h3 := card_le_pow_three hnd hts hp (hK ▸ hpq) hAc hAp hAO
  have h4 := (GGConfig.tableB_facts (G := G) ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩).2.2.2.2
  rw [hcardA] at h3
  have := Nat.pow_lt_pow_right hp.one_lt (show 3 < 4 by norm_num)
  omega

end MinusFour

end WitOmNs

section Inputs

theorem ggSixRootFusionWitnessOn_POmegaMinusQ1Four :
    GGSixRootFusionWitnessOn fun t n f p => t = .POmegaMinus ∧ p ∣ 2 ^ f + 1 ∧ n = 4 := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, hpq, rfl⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (WitOmNs.false_of_minusFour (K := GaloisField 2 f) (minusCoeffs_irr 2 f)
    (GaloisField.card 2 f (by have := hctx.2.2.2.1.1.2.1; omega)) hctx s1 hpq).elim

theorem ggSixRootFusionWitOmMinusQ1_holds : GGSixRootFusionWitOmMinusQ1 := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx
  obtain ⟨rfl, hpq⟩ := hP
  have hn4 : 4 ≤ n := hctx.2.2.2.1.1.2.2
  rcases Nat.lt_or_ge n 5 with hn | hn
  · obtain rfl : n = 4 := by omega
    exact ggSixRootFusionWitnessOn_POmegaMinusQ1Four G p B Bs x L D J .POmegaMinus 4 f ψ
      ⟨rfl, hpq, rfl⟩ hctx
  · exact ggSixRootFusionWitnessOn_POmegaMinusQ1Five G p B Bs x L D J .POmegaMinus n f ψ
      ⟨rfl, hpq, hn⟩ hctx

end Inputs

end CFSG.StandardType
