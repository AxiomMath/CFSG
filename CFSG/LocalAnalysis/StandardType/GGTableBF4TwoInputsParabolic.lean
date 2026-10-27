module

public import CFSG.RankThree.PartOne.KF.F4ParabolicSums
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.BorelTits CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.KFU

namespace TableBF4TwoInputs

section Complement

theorem exists_conj_le_of_complement {G : Type*} [Group G] [Finite G] {N M : Subgroup G}
    [N.Normal] (hdisj : N ⊓ M = ⊥) (hprod : ∀ g : G, ∃ n ∈ N, ∃ m ∈ M, g = n * m) {p : ℕ}
    (hp : p.Prime) (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hA : IsPGroup p A) :
    ∃ y : G, ∀ a ∈ A, y * a * y⁻¹ ∈ M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomp : Subgroup.IsComplement' N M := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hdisj) ?_
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod g
    exact ⟨n, hn, m, hm, rfl⟩
  have hcard : Nat.card N * Nat.card M = Nat.card G := hcomp.card_mul_card
  have hfM : (Nat.card G).factorization p = (Nat.card M).factorization p := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    have : (Nat.card N).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hN
    simp [this]
  obtain ⟨RM⟩ : Nonempty (Sylow p M) := inferInstance
  set R' : Subgroup G := (RM : Subgroup M).map M.subtype with hR'
  have hR'card : Nat.card R' = p ^ (Nat.card G).factorization p := by
    have h1 : Nat.card R' = Nat.card (RM : Subgroup M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [h1, Sylow.card_eq_multiplicity, hfM]
  set RS : Sylow p G := Sylow.ofCard R' hR'card with hRS
  obtain ⟨R, hAR⟩ := hA.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G R RS
  refine ⟨y, fun a ha => ?_⟩
  have hamem : a ∈ (R : Subgroup G) := hAR ha
  have hmem : y * a * y⁻¹ ∈ ((y • R : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨a, hamem, by simp [MulAut.conj_apply]⟩
  rw [hy] at hmem
  obtain ⟨m, -, hm⟩ := hmem
  rw [← hm]
  exact m.2

end Complement

section Parabolic

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_mem_parabolic_of_normalizes {U E : Subgroup (adjointGroup .F4 K)}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K))) :
    ∃ (J : Set (Fin Tag.F4.rank)) (g : adjointGroup .F4 K), J ≠ Set.univ ∧
      ∀ e ∈ E, ((g⁻¹ * e * g : adjointGroup .F4 K) : ModGL .F4 K) ∈
        parabolicSubgroup .F4 K J := by
  have hfin : Finite (ModGL .F4 K) := finite_modGL
  have hBC : borelGroup .F4 K ≤ adjointGroup .F4 K := borelGroup_le_adjointGroup' .F4
  have hUC : posUnipotent .F4 K ≤ adjointGroup .F4 K := le_sup_right.trans hBC
  obtain ⟨S, P, hPtop, hNU, -, -, hNS⟩ := holds_adjointGroup_tag .F4 K 2 U hU hU2
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((borelGroup .F4 K).subgroupOf (adjointGroup .F4 K)) P
    (by rw [hUc]; exact borelGroup_subgroupOf_le_normalizer .F4) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := exists_parabolic_of_borel_le .F4 _ hg hP₁top
  refine ⟨J, g, hJ, fun e he => hJP _ ?_⟩
  rw [Subgroup.mem_comap]
  have h1 : (MulAut.conj g).toMonoidHom (g⁻¹ * e * g) = e := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [h1]
  exact hNU (hE he)

@[expose] def f4CoatomMask : Fin Tag.F4.rank → ℕ := ![14, 13, 11, 7]

omit [CharP K 2] in
theorem f4CoatomMask_cover :
    ∀ i k : Fin Tag.F4.rank, k ≠ i → k ∈ maskSet .F4 (f4CoatomMask i) := by
  decide

omit [CharP K 2] in
theorem single_zero_of_mem_mask_zero : ∀ j : Fin Tag.F4.rank,
    j ∈ maskSet .F4 (f4CoatomMask ⟨0, by decide⟩) →
    (Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) ⟨0, by decide⟩ = 0 := by
  decide

omit [CharP K 2] in
theorem single_three_of_mem_mask_three : ∀ j : Fin Tag.F4.rank,
    j ∈ maskSet .F4 (f4CoatomMask ⟨3, by decide⟩) →
    (Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) ⟨3, by decide⟩ = 0 := by
  decide

omit [CharP K 2] in
theorem finsum_eq_parabolicSum_F4 [Fintype (WeylGroup .F4)] (J : Set (Fin Tag.F4.rank)) (q : ℕ) :
    ∑ᶠ w : parabolicWeylGroup .F4 J, q ^ (coxeterSystem .F4).length w.1 =
      parabolicSum .F4 J q := by
  classical
  rw [parabolicSum, finsum_eq_sum_of_fintype]
  simp only [parabolic_eq_parabolicWeylGroup]
  exact (Finset.sum_subtype (Finset.univ.filter (· ∈ parabolicWeylGroup .F4 J))
    (fun x => by simp) (fun w => q ^ (coxeterSystem .F4).length w)).symm

omit [CharP K 2] in
theorem not_dvd_card_parabolic (hK : Nat.card K = 2) {i : Fin Tag.F4.rank}
    (hi : i.val = 1 ∨ i.val = 2) :
    ¬ 3 ^ 3 ∣ Nat.card (parabolicSubgroup .F4 K
      (maskSet .F4 (f4CoatomMask i) : Set (Fin Tag.F4.rank))) := by
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells .F4 K
  rw [hcell, card_torusGroup_F4, ncard_posRoots_F4, hK, finsum_eq_parabolicSum_F4]
  have hs : parabolicSum .F4 (maskSet .F4 (f4CoatomMask i)) 2 = 63 := by
    rcases hi with h | h
    · have hi1 : i = ⟨1, by decide⟩ := Fin.ext h
      subst hi1
      exact parabolicSum_F4_two_A1A2
    · have hi2 : i = ⟨2, by decide⟩ := Fin.ext h
      subst hi2
      exact parabolicSum_F4_two_A2A1
  rw [hs]
  norm_num

theorem torusGroup_F4_eq_bot (hK : Nat.card K = 2) : torusGroup .F4 K = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (by rw [card_torusGroup_F4, hK]; norm_num)

theorem parabolicLevi_le_rootSpan (hK : Nat.card K = 2) {J : Set (Fin Tag.F4.rank)}
    {S : Set (Fin Tag.F4.rank → ℤ)}
    (hJS : ∀ j ∈ J, (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ S ∧ -Pi.single j 1 ∈ S) :
    parabolicLevi .F4 K J ≤ rootSpan .F4 K S := by
  rw [parabolicLevi, torusGroup_F4_eq_bot hK, bot_sup_eq, Subgroup.closure_le]
  rintro g ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, ← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .F4 K α) _ (hJS j hj).1 le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [SetLike.mem_coe, ← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .F4 K α) _ (hJS j hj).2 le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)

theorem exists_conj_mem_parabolicLevi {J : Set (Fin Tag.F4.rank)}
    {A : Subgroup (adjointGroup .F4 K)}
    (hAJ : ∀ a ∈ A, (a : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J) (hA : IsPGroup 3 A) :
    ∃ y ∈ parabolicSubgroup .F4 K J,
      ∀ a ∈ A, y * (a : ModGL .F4 K) * y⁻¹ ∈ parabolicLevi .F4 K J := by
  have hfin : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hQP, hQnorm, -, hMP, hQM, -, hfact, -, -, -, -, -, hpg⟩ :=
    parabolic_root_radical_Levi_factors .F4 K J
  obtain ⟨-, hQr, -⟩ := hpg 2
  set G : Type := ↥(parabolicSubgroup .F4 K J) with hG
  set N : Subgroup G := (parabolicRadical .F4 K J).subgroupOf (parabolicSubgroup .F4 K J) with hNdef
  set M' : Subgroup G := (parabolicLevi .F4 K J).subgroupOf (parabolicSubgroup .F4 K J) with hMdef
  have hNnormal : N.Normal := hQnorm
  have hdisj : N ⊓ M' = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hyN, hyM⟩ := Subgroup.mem_inf.1 hy
    have h1 : (y : ModGL .F4 K) ∈ parabolicRadical .F4 K J ⊓ parabolicLevi .F4 K J :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyN, Subgroup.mem_subgroupOf.1 hyM⟩
    rw [hQM, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hprod : ∀ g' : G, ∃ n ∈ N, ∃ m ∈ M', g' = n * m := by
    intro g'
    obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, -⟩ := hfact g' g'.2
    exact ⟨⟨q, hQP hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨m, hMP hm⟩, Subgroup.mem_subgroupOf.2 hm,
      Subtype.ext hqm⟩
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro hdvd
    have hNQ : Nat.card N = Nat.card (parabolicRadical .F4 K J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    obtain ⟨k, hk⟩ := hQr.exists_card_eq
    rw [hNQ, hk] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  have hle : A.map (adjointGroup .F4 K).subtype ≤ parabolicSubgroup .F4 K J := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAJ a ha
  set A₂ : Subgroup G := (A.map (adjointGroup .F4 K).subtype).subgroupOf
    (parabolicSubgroup .F4 K J) with hA₂
  have hA₂p : IsPGroup 3 A₂ :=
    (hA.map (adjointGroup .F4 K).subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  obtain ⟨y, hy⟩ := exists_conj_le_of_complement hdisj hprod Nat.prime_three hN3 hA₂p
  refine ⟨y, y.2, fun a ha => ?_⟩
  have h := hy ⟨(a : ModGL .F4 K), hAJ a ha⟩ (Subgroup.mem_subgroupOf.2 ⟨a, ha, rfl⟩)
  exact Subgroup.mem_subgroupOf.1 h

theorem exists_conj_le_C3Levi_or_B3Levi (hK : Nat.card K = 2)
    {V A : Subgroup (adjointGroup .F4 K)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set (adjointGroup .F4 K))) (hAp : IsPGroup 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A) :
    ∃ g : adjointGroup .F4 K, A.map (MulAut.conj g).toMonoidHom ≤ C3Levi K ∨
      A.map (MulAut.conj g).toMonoidHom ≤ B3Levi K := by
  have hfin : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨J, g₁, hJ, hmem⟩ := exists_conj_mem_parabolic_of_normalizes hV hV2 hAV
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  set M : Set (Fin Tag.F4.rank) := (maskSet .F4 (f4CoatomMask i) : Set (Fin Tag.F4.rank)) with hM
  have hsub : J ⊆ M := fun k hk => by
    exact_mod_cast f4CoatomMask_cover i k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup .F4 K J ≤ parabolicSubgroup .F4 K M :=
    ((standard_parabolic_cells .F4 K).2.2.2.1 J M).2 hsub
  set A₁ := A.map (MulAut.conj g₁⁻¹).toMonoidHom with hA₁
  have hA₁M : ∀ a ∈ A₁, (a : ModGL .F4 K) ∈ parabolicSubgroup .F4 K M := by
    rintro _ ⟨a, ha, rfl⟩
    apply hle
    have h := hmem a ha
    simpa [MulAut.conj_apply] using h
  have hA₁p : IsPGroup 3 A₁ := hAp.map _
  have hA₁card : Nat.card A₁ = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g₁⁻¹).injective
  have hi03 : i.val = 0 ∨ i.val = 3 := by
    by_contra hne
    have h12 : i.val = 1 ∨ i.val = 2 := by
      have := i.2
      change i.val < 4 at this
      omega
    apply not_dvd_card_parabolic hK h12
    have hleM : A₁.map (adjointGroup .F4 K).subtype ≤ parabolicSubgroup .F4 K M := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA₁M a ha
    have h1 : Nat.card A₁ ∣ Nat.card (parabolicSubgroup .F4 K M) := by
      have h2 := Subgroup.card_dvd_of_le hleM
      rwa [Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective] at h2
    obtain ⟨k, hk⟩ := hA₁p.exists_card_eq
    have hk3 : 3 ≤ k := by
      have h3 : 3 ^ 3 ≤ 3 ^ k := by rw [← hk, hA₁card]; exact h27
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
    exact (hk ▸ Nat.pow_dvd_pow 3 hk3).trans h1
  obtain ⟨y, hyP, hy⟩ := exists_conj_mem_parabolicLevi hA₁M hA₁p
  have hyC : y ∈ adjointGroup .F4 K := parabolicSubgroup_le_adjointGroup .F4 K M hyP
  have key : ∀ a ∈ A, (((MulAut.conj (⟨y, hyC⟩ * g₁⁻¹)).toMonoidHom a : adjointGroup .F4 K) :
      ModGL .F4 K) ∈ parabolicLevi .F4 K M := by
    intro a ha
    have h := hy _ ⟨a, ha, rfl⟩
    have e : (((MulAut.conj (⟨y, hyC⟩ * g₁⁻¹)).toMonoidHom a : adjointGroup .F4 K) :
        ModGL .F4 K) = y * (((MulAut.conj g₁⁻¹).toMonoidHom a : adjointGroup .F4 K) :
          ModGL .F4 K) * y⁻¹ := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact h
  refine ⟨⟨y, hyC⟩ * g₁⁻¹, ?_⟩
  rcases hi03 with h0 | h3
  · left
    have hi0 : i = ⟨0, by decide⟩ := Fin.ext h0
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_C3Levi_iff]
    refine parabolicLevi_le_rootSpan hK (fun j hj => ?_) (key a ha)
    have hj0 := single_zero_of_mem_mask_zero j (by rw [← hi0]; exact_mod_cast hj)
    exact ⟨⟨IsRoot.basis j, hj0⟩, ⟨CFSG.LieType.Chevalley.IsRoot.neg (IsRoot.basis j),
      by rw [Pi.neg_apply, hj0, neg_zero]⟩⟩
  · right
    have hi3 : i = ⟨3, by decide⟩ := Fin.ext h3
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_B3Levi_iff]
    refine parabolicLevi_le_rootSpan hK (fun j hj => ?_) (key a ha)
    have hj3 := single_three_of_mem_mask_three j (by rw [← hi3]; exact_mod_cast hj)
    exact ⟨⟨IsRoot.basis j, hj3⟩, ⟨CFSG.LieType.Chevalley.IsRoot.neg (IsRoot.basis j),
      by rw [Pi.neg_apply, hj3, neg_zero]⟩⟩

end Parabolic

end TableBF4TwoInputs

end CFSG.StandardType
