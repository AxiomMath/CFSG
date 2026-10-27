module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.ExcThreeAtTwo

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.RationalModel CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw

theorem notExcThree_of_two_pow_dvd {n k : ℕ} (hk : 13 ≤ k) (h : 2 ^ k ∣ n) :
    GGNotExcThreeOrder n := by
  have h13 : 2 ^ 13 ∣ n := (pow_dvd_pow 2 hk).trans h
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩ <;> subst hn <;> revert h13 <;> decide

private theorem fifteen_le_choose_two {d : ℕ} (hd : 6 ≤ d) : 15 ≤ d * (d - 1) / 2 :=
  (Nat.le_div_iff_mul_le (by norm_num)).2 (by
    have h := Nat.mul_le_mul hd (show 5 ≤ d - 1 by omega)
    omega)

theorem ordSU_ne_excThree {a d N₀ z : ℕ} (ha : 1 ≤ a) (hd : 3 ≤ d) (hne : ¬ (d = 4 ∧ a = 1))
    (hN₀ : N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) (hz : Odd z) :
    ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) ≠ ((N₀ * z : ℕ) : ℤ) := by
  intro h
  have h2 : 2 ^ (a * (d * (d - 1) / 2)) ∣ N₀ * z := by
    have h3 : ((2 ^ (a * (d * (d - 1) / 2)) : ℕ) : ℤ) ∣ ((N₀ * z : ℕ) : ℤ) := by
      rw [← h]
      push_cast
      rw [pow_mul]
      exact dvd_mul_right _ _
    exact Int.natCast_dvd_natCast.mp h3
  have h5 : ((N₀ : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [h, Nat.cast_mul]
    exact dvd_mul_right _ _
  obtain ⟨hb1, hb2, hb3⟩ := ggAKFG_le_of_dvd hz h2
  have hd5 : d ≤ 5 := by
    by_contra h5'
    have h15 := fifteen_le_choose_two (by omega : 6 ≤ d)
    have := Nat.mul_le_mul ha h15
    rcases hN₀ with rfl | rfl | rfl
    · have := hb1 rfl; omega
    · have := hb2 rfl; omega
    · have := hb3 rfl; omega
  clear h h2
  rcases hN₀ with rfl | rfl | rfl
  · have hb := hb1 rfl
    interval_cases d
    · have : a ≤ 4 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 2 := by norm_num at hb; omega
      interval_cases a
      · exact hne ⟨rfl, rfl⟩
      · revert h5
        decide +kernel
    · have : a ≤ 1 := by norm_num at hb; omega
      interval_cases a
      revert h5
      decide +kernel
  · have hb := hb2 rfl
    interval_cases d
    · have : a ≤ 2 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 1 := by norm_num at hb; omega
      interval_cases a
      exact hne ⟨rfl, rfl⟩
    · norm_num at hb; omega
  · have hb := hb3 rfl
    interval_cases d
    · have : a ≤ 1 := by norm_num at hb; omega
      interval_cases a
      revert h5
      decide +kernel
    · norm_num at hb; omega
    · norm_num at hb; omega

theorem ordPSU_notExcThree {d a : ℕ} (hd : 3 ≤ d) (ha : 1 ≤ a) (hne : ¬ (d = 4 ∧ a = 1)) :
    GGNotExcThreeOrder ((2 ^ a) ^ (d * (d - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
        Nat.gcd d (2 ^ a + 1)) := by
  have hQ1 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hodd : Odd (Nat.gcd d (2 ^ a + 1)) := by
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right d (2 ^ a + 1))
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hPcast : ((∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => Int.toNat_of_nonneg ?_
    have h1 : (1 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast (by omega))
    have h2 : ((-1 : ℤ)) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
    linarith
  have hgdvd : Nat.gcd d (2 ^ a + 1) ∣ (2 ^ a) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hPcast]
    refine Dvd.dvd.mul_left ?_ _
    have hmem : d ∈ Finset.Icc 2 d := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    refine (?_ : ((Nat.gcd d (2 ^ a + 1) : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) ^ d - (-1) ^ d).trans
      (Finset.dvd_prod_of_mem (fun i => ((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) hmem)
    have h1 : ((Nat.gcd d (2 ^ a + 1) : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) - (-1) := by
      rw [sub_neg_eq_add]
      exact_mod_cast Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right d (2 ^ a + 1))
    exact h1.trans (sub_dvd_pow_sub_pow _ _ d)
  have key : ∀ N₀, (N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) →
      (2 ^ a) ^ (d * (d - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd d (2 ^ a + 1) ≠ N₀ := by
    intro N₀ hN₀ heq
    have hmul := Nat.div_mul_cancel hgdvd
    rw [heq] at hmul
    refine ordSU_ne_excThree ha hd hne hN₀ hodd ?_
    rw [← hPcast, ← Nat.cast_pow, ← Nat.cast_mul, hmul]
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr (Or.inl rfl)), key _ (Or.inr (Or.inr rfl))⟩

section Char


theorem charP_two_of_langSetup_q_eq_two {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) : CharP L 2 := by
  obtain ⟨r, e, hr, hchar, he, hqre⟩ := S.exists_char_pow
  have hr2 : r = 2 := by
    have hpow : r ^ e = 2 := by rw [← hqre, hq2]
    have hdvd : r ∣ 2 := hpow ▸ dvd_pow_self r (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd
  exact hr2 ▸ hchar

end Char

section TypeA


theorem rationalComponent_typeA_model_dim {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ f, 1 ≤ f ∧
      (StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          .PSL (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f ∨
        StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          .PSU (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · obtain ⟨f, hf1, -, hmodel⟩ :=
      rationalComponent_rankOne_model S hT i hr1 (by rw [hA.2, hr1]) hQS
    exact ⟨f, hf1, Or.inl (by rw [hr1]; exact hmodel)⟩
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    have hcard : (frameRoots σ).ncard = ν * (ν - 1) := by
      have hinj : Set.InjOn (fun q : Fin ν × Fin ν => σ q.1 q.2) {q | q.1 ≠ q.2} := by
        rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv h
        simp only [Set.mem_setOf_eq] at hxy huv
        obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hxy huv h
        rfl
      have himg : frameRoots σ = (fun q : Fin ν × Fin ν => σ q.1 q.2) '' {q | q.1 ≠ q.2} := by
        ext r
        constructor
        · rintro ⟨x, y, hxy, rfl⟩
          exact ⟨(x, y), hxy, rfl⟩
        · rintro ⟨⟨x, y⟩, hxy, rfl⟩
          exact ⟨x, y, hxy, rfl⟩
      rw [himg, hinj.ncard_image]
      have hoff : ({q : Fin ν × Fin ν | q.1 ≠ q.2} : Set (Fin ν × Fin ν)) =
          ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
        ext q
        simp [Finset.mem_offDiag]
      rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
        Nat.mul_sub_left_distrib, mul_one]
    have hνr : ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
      have h : ν * (ν - 1) = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by
        rw [← hcard, ← hΨ]
        exact hA.2
      generalize compRank (componentRoots (rootCharHom a) i) = r at h h2 ⊢
      obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
      rw [Nat.add_sub_cancel] at h
      have hm : m = r := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
      omega
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have hm1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have hm2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, hm1, rfl⟩
      rw [hs, hΨ] at hm2
      exact hm2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · obtain ⟨f, hf1, -, hmodel⟩ :=
        rationalComponent_splitFrame_model S hT i hν hψ hΨ π hπ
      exact ⟨f, hf1, Or.inl (by rw [← hνr]; exact hmodel)⟩
    · obtain ⟨f, hf1, -, hmodel⟩ :=
        rationalComponent_unitaryFrame_model S hT i hν hψ hΨ π hπ hQS
      exact ⟨f, hf1, Or.inr (by rw [← hνr]; exact hmodel)⟩

theorem typeA_ggCQ_ne_three_two {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hr3 : compRank (componentRoots (rootCharHom a) i) ≠ 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  obtain ⟨f, hf1, hmodel⟩ := rationalComponent_typeA_model_dim S Nat.prime_three hT hap h1 i hA hqs
  rw [ringChar.eq L 2] at hmodel
  unfold ggCQ
  rcases hmodel with hPSL | hPSU
  · rw [card_of_statedClassicalModel_psl (by omega) hPSL]
    exact ggAKFG_ordSL_good (by omega) hf1
  · have hν3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) + 1 := hPSU.1.2.2.1
    rw [card_of_statedClassicalModel_psu (by omega) hPSU]
    exact ordPSU_notExcThree hν3 hf1 (fun h => hr3 (by omega))

end TypeA

section CardNe


theorem pow_card_dvd_centerQuotient_of_uniEmbed (hU : UniEmbed) {τ : Tag} {M : Type}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {R : Type} [Group R] (f : ↥(componentRootSpan K χ i) →* R)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan K χ i))
    (hperf : Group.IsPerfect ↥(componentRootSpan K χ i)) :
    Nat.card K ^ (posRoots (componentRoots χ i)).ncard ∣ Nat.card (R ⧸ Subgroup.center R) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, -, hVcard, hVZ⟩ := hU τ χ i K 2
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf f hf hker
  let g : ↥V →* ↥(componentRootSpan K χ i) ⧸ Subgroup.center ↥(componentRootSpan K χ i) :=
    (QuotientGroup.mk' _).comp V.subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : ↥(componentRootSpan K χ i)) ∈ Subgroup.center ↥(componentRootSpan K χ i) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : ↥(componentRootSpan K χ i)) ∈
        V ⊓ Subgroup.center ↥(componentRootSpan K χ i) := ⟨x.2, hx'⟩
    rw [hVZ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  rw [← hVcard, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_dvd_of_injective g hginj

theorem card_centerQuotient_notExcThree_of_uniEmbed (hU : UniEmbed) {τ : Tag} {M : Type}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {R : Type} [Group R] (f : ↥(componentRootSpan K χ i) →* R)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan K χ i))
    (hperf : Group.IsPerfect ↥(componentRootSpan K χ i))
    (hbig : 4096 < Nat.card K ^ (posRoots (componentRoots χ i)).ncard) :
    GGNotExcThreeOrder (Nat.card (R ⧸ Subgroup.center R)) := by
  have hdvd := pow_card_dvd_centerQuotient_of_uniEmbed hU χ i K f hf hker hperf
  obtain ⟨k, -, hk⟩ := LayerExcThree.exists_card_eq_two_pow K
  rw [hk, ← pow_mul] at hdvd hbig
  refine notExcThree_of_two_pow_dvd ?_ hdvd
  by_contra hlt
  have : 2 ^ (k * (posRoots (componentRoots χ i)).ncard) ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CardNe

section InnerBig


theorem inner_big_ggCQ_ne_of_data {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    [CharP L 2] {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (D : InnerData S a i)
    (hbig : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := isPerfect_componentRootSpan_of_big hτ D (by omega)
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  refine card_centerQuotient_notExcThree_of_uniEmbed uniEmbed_holds (rootCharHom a) i
    (fixSubfield D.σ) g hg hgk hperf ?_
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : 13 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  have hK2 : 2 ≤ Nat.card (fixSubfield D.σ) := Finite.one_lt_card
  calc 4096 < 2 ^ 13 := by norm_num
    _ ≤ 2 ^ (posRoots (componentRoots (rootCharHom a) i)).ncard :=
      Nat.pow_le_pow_right (by norm_num) hN
    _ ≤ Nat.card (fixSubfield D.σ) ^ (posRoots (componentRoots (rootCharHom a) i)).ncard :=
      Nat.pow_le_pow_left hK2 _

theorem inner_big_ggCQ_ne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  exact inner_big_ggCQ_ne_of_data hτ D h26

end InnerBig

theorem notExcThree_of_lieModel_pOmegaMinus {G : Type} [Group G] {n e : ℕ}
    (h : LieModel G .POmegaMinus n 2 e) : GGNotExcThreeOrder (Nat.card G) := by
  have hn4 : 4 ≤ n := h.admissible.2.2
  have he : 1 ≤ e := h.admissible.2.1
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
    (h.statedClassicalModel (by decide))]
  show GGNotExcThreeOrder (ordTwistedD n (2 ^ e))
  by_cases h4 : n = 4 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := h4
    unfold ordTwistedD GGNotExcThreeOrder
    decide +kernel
  · refine notExcThree_of_two_pow_dvd (k := e * (n * (n - 1))) ?_ ?_
    · have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
      rcases Nat.lt_or_ge n 5 with hn5 | hn5
      · have : n = 4 := by omega
        have : 2 ≤ e := by omega
        nlinarith
      · have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
        nlinarith
    · rw [pow_mul]
      exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedD n (2 ^ e)

section TwistedE6


theorem notExcThree_of_lieModel_twistedE6 {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .twistedE6 0 2 f) : GGNotExcThreeOrder (Nat.card G) := by
  have hf : 1 ≤ f := h.admissible.2.1
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
    (h.chevalleyExceptionalModel (by decide))]
  show GGNotExcThreeOrder (ordTwistedE6 (2 ^ f))
  refine notExcThree_of_two_pow_dvd (k := 36 * f) (by omega) ?_
  rw [mul_comm, pow_mul]
  exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 (2 ^ f)

end TwistedE6

section OuterD


theorem outerD_ggCQ_ne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  obtain ⟨m, e, -, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap h1 i h5 hn hout
      (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega))
      trivial
  rw [ringChar.eq L 2] at hlie
  exact notExcThree_of_lieModel_pOmegaMinus hlie

end OuterD

section OuterE


theorem outerE_ggCQ_ne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl | rfl
  · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i h6 hn).elim
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S Nat.prime_three h3L hT hTp i h6 hn hout
    rw [ringChar.eq L 2] at hlie
    exact notExcThree_of_lieModel_twistedE6 hlie
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S Nat.prime_three h3L hT hTp i h6 hn hout
    rw [ringChar.eq L 2] at hlie
    exact notExcThree_of_lieModel_twistedE6 hlie

end OuterE

end CFSG.StandardType.ExcThreeAtTwo
