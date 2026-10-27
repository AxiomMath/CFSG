module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOPCensusA
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.ABGLocalTools
  CFSG.LieType.Universal.Spin

theorem s16t3_plus_census {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) : S16t3PlusCensus K m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    letI := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    exact charP_of_card_eq_prime hK'
  classical
  have hD : ∀ d ∈ s16t3PlusCuts m, 1 ≤ d ∧ d ≤ m := fun d hd => by
    obtain ⟨h1, h2, -⟩ := s16t3_mem_plusCuts.mp hd
    exact ⟨h1, by omega⟩
  have hD' : ∀ d ∈ s16t3PlusCuts m, d ≤ m := fun d hd => (hD d hd).2
  have hD₂ : ∀ d ∈ s16t3PlusCuts m, 1 ≤ d ∧ d ≤ m - 2 := fun d hd => by
    obtain ⟨h1, h2, -⟩ := s16t3_mem_plusCuts.mp hd
    exact ⟨h1, h2⟩
  have hsup : (s16t3PlusCuts m).sup id = m - 2 := by
    refine le_antisymm (Finset.sup_le fun d hd => (s16t3_mem_plusCuts.mp hd).2.1) ?_
    have hm2 : m - 2 ∈ s16t3PlusCuts m :=
      s16t3_mem_plusCuts.mpr ⟨by omega, le_rfl, Or.inr rfl⟩
    simpa using Finset.le_sup (f := id) hm2
  have ht2 : (s16t3PlusCuts m).sup id + 2 = m := by omega
  have ht : (s16t3PlusCuts m).sup id = 0 ∨ (s16t3PlusCuts m).sup id ∈ s16t3PlusCuts m :=
    sup_eq_zero_or_mem _
  have hleBot : ∀ d ∈ s16t3PlusCuts m, d ≤ (s16t3PlusCuts m).sup id :=
    fun d hd => Finset.le_sup (f := id) hd
  haveI : Finite ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) := finite_plusAut (K := K) m
  let G₁ : ↥(s16t3PlusCuts m) → Type := fun b =>
    GL (Fin (b.1 - predCut (s16t3PlusCuts m) b.1)) K
  let G₂ : Fin 2 → Type := fun _ => GL (Fin 2) K
  let G : ↥(s16t3PlusCuts m) ⊕ Fin 2 → Type := plusSumGroup G₁ G₂
  let β : ↥(plusFlagStab K m (s16t3PlusCuts m)) →* (∀ j, G j) :=
    MonoidHom.pi fun j => match j with
      | Sum.inl b => plusEBlockHom hD' b.2
      | Sum.inr j => plusFamHom K hm hD₂ hD' ht ht2 j
  have hβ : Function.Surjective β := by
    rw [← MonoidHom.range_eq_top]
    refine top_le_iff.mp ?_
    rw [← Subgroup.pi_top Set.univ]
    rw [Subgroup.pi_le_iff]
    rintro (b | j) _ ⟨x, -, rfl⟩
    · have hx : x ∈ (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (b.1 - predCut (s16t3PlusCuts m) b.1)) K →*
            GL (Fin (b.1 - predCut (s16t3PlusCuts m) b.1)) K).range := by
        rw [s16t3_range_toGL_eq_top hK]
        exact Subgroup.mem_top x
      obtain ⟨q, hq, h1, h2⟩ := exists_plusFlagLevi_of_mem (K := K) hm hD' b.2 hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with b' | j'
      · by_cases hbb : b' = b
        · subst hbb
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => hbb (Sum.inl_injective h))]
          exact h1 b'.1 b'.2 (fun h => hbb (Subtype.ext h))
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inr_ne_inl]
        have hres : plusResBlockHom hD' ht ht2 q = 1 := h2 ht ht2 (hleBot b b.2)
        have hra : plusResAut hD' ht ht2 q = 1 := by
          show matrixEquiv 2 K (plusResBlockHom hD' ht ht2 q) = 1
          rw [hres, map_one]
        exact plusFamHom_eq_one (K := K) hm hD₂ hD' ht ht2 hra j'
    · have hx : x ∈ (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range := by
        rw [s16t3_range_toGL_eq_top hK]
        exact Subgroup.mem_top x
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hx
      fin_cases j
      · have hq := plusResExt_iotaTwo_mem (K := K) (D := s16t3PlusCuts m) (hr := hm)
          (htm := ht2) (fun d hd => hleBot d hd) A
        obtain ⟨e0, e1⟩ := plusFamHom_iotaTwo (K := K) hm hD₂ hD' ht ht2 hq
        refine ⟨⟨_, hq⟩, funext fun j' => ?_⟩
        rcases j' with b' | j'
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
          exact plusEBlockHom_plusResExt hD' ht2 (fun d hd => hleBot d hd) b'.2 hq
        · fin_cases j'
          · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
            exact e0
          · simpa [β, MonoidHom.pi_apply, Pi.mulSingle] using e1
      · have hq := plusResExt_iotaOne_mem (K := K) (D := s16t3PlusCuts m) (hr := hm)
          (htm := ht2) (fun d hd => hleBot d hd) A
        obtain ⟨e0, e1⟩ := plusFamHom_iotaOne (K := K) hm hD₂ hD' ht ht2 hq
        refine ⟨⟨_, hq⟩, funext fun j' => ?_⟩
        rcases j' with b' | j'
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
          exact plusEBlockHom_plusResExt hD' ht2 (fun d hd => hleBot d hd) b'.2 hq
        · fin_cases j'
          · simpa [β, MonoidHom.pi_apply, Pi.mulSingle] using e0
          · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
            exact e1
  have hker : IsPGroup 2 β.ker := by
    refine isPGroup_of_plusBlocks hD' (fun d hd => (hD d hd).1) fun g hg => ⟨?_, ?_⟩
    · intro b hb
      have h := congrFun (MonoidHom.mem_ker.mp hg) (Sum.inl ⟨b, hb⟩)
      simpa [β] using h
    · intro x hx
      have h0 : plusFamHom K hm hD₂ hD' ht ht2 0 g = 1 := by
        have h := congrFun (MonoidHom.mem_ker.mp hg) (Sum.inr 0)
        simpa [β] using h
      have h1 : plusFamHom K hm hD₂ hD' ht ht2 1 g = 1 := by
        have h := congrFun (MonoidHom.mem_ker.mp hg) (Sum.inr 1)
        simpa [β] using h
      have hra : plusResAut hD' ht ht2 g = 1 :=
        plusResAut_eq_one_of_plusFamHom (K := K) hm hD₂ hD' ht ht2 h0 h1
      exact sub_mem_of_plusResBlockHom_eq_one hD' ht ht2
        (plusResBlockHom_eq_one_of_plusResAut hD' ht ht2 hra) hx
  have hcardG : Nat.card (∀ j, G j) = 6 ^ ((m - 2) / 2) * 36 := by
    rw [Nat.card_congr (Equiv.sumPiEquivProdPi G), Nat.card_prod]
    congr 1
    · exact s16t3_plus_block_card K hK m
    · rw [Nat.card_fun, Nat.card_fin, s16t3_card_GL_two hK]
      norm_num
  have hH : Nat.card (∀ j, G j) = 2 ^ ((m + 2) / 2) * 3 ^ ((m + 2) / 2) := by
    rw [hcardG]
    have hk : (m - 2) / 2 + 2 = (m + 2) / 2 := by omega
    calc 6 ^ ((m - 2) / 2) * 36 = (2 * 3) ^ ((m - 2) / 2) * (2 * 3) ^ 2 := rfl
      _ = (2 * 3) ^ ((m - 2) / 2 + 2) := (pow_add (2 * 3) _ 2).symm
      _ = (2 * 3) ^ ((m + 2) / 2) := by rw [hk]
      _ = 2 ^ ((m + 2) / 2) * 3 ^ ((m + 2) / 2) := mul_pow 2 3 _
  have hH_exp : ∀ h : (∀ j, G j), ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1 := by
    intro h k hk
    funext j
    rcases j with b | j
    · have h1 : (h (Sum.inl b)) ^ 3 ^ k = 1 := by
        have := congrFun hk (Sum.inl b)
        simpa using this
      have hdvd : Nat.card (G (Sum.inl b)) ∣ 6 := by
        show Nat.card (GL (Fin (b.1 - predCut (s16t3PlusCuts m) b.1)) K) ∣ 6
        by_cases he : b.1 % 2 = 0
        · rw [s16t3_plus_blen_even b.2 he, s16t3_card_GL_two hK]
        · rw [s16t3_plus_blen_odd b.2 he, s16t3_card_GL_one hK le_rfl]
          norm_num
      exact s16t3_pow_three_of_card_dvd_six hdvd _ k h1
    · have h1 : (h (Sum.inr j)) ^ 3 ^ k = 1 := by
        have := congrFun hk (Sum.inr j)
        simpa using this
      refine s16t3_pow_three_of_card_dvd_six ?_ _ k h1
      show Nat.card (GL (Fin 2) K) ∣ 6
      rw [s16t3_card_GL_two hK]
  have hY : IsSylowOf 2 (posUnip m K) (orthElementaryGroup (quadPlus m K)) := by
    obtain ⟨S, hS⟩ := posUnip_isSylow (K := K) (p := 2) (r := m) (by omega)
      fun a ha => map_flag_top_ne_Xstar (K := K) (r := m) hm ha
    exact ⟨S, by rw [hS, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr posUnip_le_orthElementaryGroup]⟩
  have hYP : posUnip m K ≤ plusFlagStab K m (s16t3PlusCuts m) := by
    refine le_inf posUnip_le_orthElementaryGroup ?_
    refine le_iInf fun d => le_iInf fun _ => ?_
    exact posUnip_le_posBorel.trans (inf_le_right.trans (iInf_le _ d))
  have hPG : plusFlagStab K m (s16t3PlusCuts m) ≤ orthElementaryGroup (quadPlus m K) :=
    inf_le_left
  have hmain := s16t3_card_of_surjective_isPGroup_ker
    (E := (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) hPG hY hYP β hβ hker hH
  unfold S16t3PlusCensus
  refine ⟨?_, ?_⟩
  · simpa using hmain
  · intro p hp k hk
    have h := s16t3_pow_three_of_isPGroup_ker β hker hH_exp ⟨p, hp⟩ k
      (Subtype.ext (by simpa using hk))
    simpa using congrArg Subtype.val h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
