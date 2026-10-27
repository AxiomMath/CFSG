module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaRegular

public section

namespace CFSG.StandardType

namespace LayerExcThree

theorem ggAKFG_natAbs_dvd_of_odd {D : ℤ} {k n : ℕ} (hD : Odd D)
    (h : D ∣ ((2 ^ k * n : ℕ) : ℤ)) : D.natAbs ∣ n := by
  have h1 : D.natAbs ∣ 2 ^ k * n := by
    have := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_natCast] at this
  have hcop : Nat.Coprime D.natAbs (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hD))
  exact hcop.dvd_of_dvd_mul_left h1

theorem ggAKFG_orth_ne {a m k N₀ : ℕ} {ε : ℤ} (ha : 2 ≤ a) (hm : 1 ≤ m)
    (hm1 : m = 1 → ε = -1) (hN₀ : N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) :
    ((2 ^ k * N₀ : ℕ) : ℤ) ≠ 2 * ((2 ^ a : ℕ) : ℤ) ^ (m * (m + 1)) *
      (((2 ^ a : ℕ) : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, ((((2 ^ a : ℕ) : ℤ) ^ 2) ^ i - 1) := by
  intro h
  obtain ⟨e, n, hNe, hn⟩ : ∃ e n : ℕ, N₀ = 2 ^ e * n ∧ (n = 42525 ∨ n = 405 ∨ n = 45) := by
    rcases hN₀ with rfl | rfl | rfl
    · exact ⟨12, 42525, by norm_num, Or.inl rfl⟩
    · exact ⟨6, 405, by norm_num, Or.inr (Or.inl rfl)⟩
    · exact ⟨3, 45, by norm_num, Or.inr (Or.inr rfl)⟩
  have h' : ((2 ^ (k + e) * n : ℕ) : ℤ) = 2 * ((2 ^ a : ℕ) : ℤ) ^ (m * (m + 1)) *
      (((2 ^ a : ℕ) : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, ((((2 ^ a : ℕ) : ℤ) ^ 2) ^ i - 1) := by
    rw [← h, hNe, pow_add, mul_assoc]
  have hn0 : 0 < n := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hn' : (n : ℤ) ≤ 42525 := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hq : Even ((2 ^ a : ℕ) : ℤ) := by
    refine ⟨((2 ^ (a - 1) : ℕ) : ℤ), ?_⟩
    push_cast
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hq2 : Even (((2 ^ a : ℕ) : ℤ) ^ 2) := hq.pow_of_ne_zero two_ne_zero
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    obtain rfl := hm1 rfl
    have hD : ((((2 ^ a : ℕ) : ℤ) ^ 2 + 1) * (((2 ^ a : ℕ) : ℤ) ^ 2 - 1)) ∣
        ((2 ^ (k + e) * n : ℕ) : ℤ) := by
      rw [h', Finset.Icc_self, Finset.prod_singleton]
      exact ⟨2 * ((2 ^ a : ℕ) : ℤ) ^ (1 * (1 + 1)), by ring⟩
    have hdvd := ggAKFG_natAbs_dvd_of_odd (hq2.add_one.mul (hq2.sub_odd odd_one)) hD
    rcases (show a = 2 ∨ a = 3 ∨ 4 ≤ a by omega) with rfl | rfl | ha4
    · rcases hn with rfl | rfl | rfl <;> revert hdvd <;> decide
    · rcases hn with rfl | rfl | rfl <;> revert hdvd <;> decide
    · have hq16 : (16 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) := by
        have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha4
        exact_mod_cast this
      have hle := Nat.le_of_dvd hn0 hdvd
      generalize ((2 ^ a : ℕ) : ℤ) = q at hq16 hle
      have hq2' : (256 : ℤ) ≤ q ^ 2 := by nlinarith
      have hpos : 0 ≤ (q ^ 2 + 1) * (q ^ 2 - 1) := by nlinarith
      have hle' : (q ^ 2 + 1) * (q ^ 2 - 1) ≤ (n : ℤ) := by
        rw [← Int.natAbs_of_nonneg hpos]
        exact_mod_cast hle
      nlinarith
  · have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 m := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    have hP := Finset.prod_dvd_prod_of_subset _ _
      (fun i => (((2 ^ a : ℕ) : ℤ) ^ 2) ^ i - 1) hsub
    rw [Finset.prod_pair (by norm_num)] at hP
    have hD : (((((2 ^ a : ℕ) : ℤ) ^ 2) ^ 1 - 1) * ((((2 ^ a : ℕ) : ℤ) ^ 2) ^ 2 - 1)) ∣
        ((2 ^ (k + e) * n : ℕ) : ℤ) := by
      rw [h']
      exact Dvd.dvd.mul_left hP _
    have hdvd := ggAKFG_natAbs_dvd_of_odd
      (((hq2.pow_of_ne_zero one_ne_zero).sub_odd odd_one).mul
        ((hq2.pow_of_ne_zero two_ne_zero).sub_odd odd_one)) hD
    rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
    · rcases hn with rfl | rfl | rfl <;> revert hdvd <;> decide
    · have hq8 : (8 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) := by
        have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
        exact_mod_cast this
      have hle := Nat.le_of_dvd hn0 hdvd
      generalize ((2 ^ a : ℕ) : ℤ) = q at hq8 hle
      have hq2' : (64 : ℤ) ≤ q ^ 2 := by nlinarith
      have h1 : (63 : ℤ) ≤ (q ^ 2) ^ 1 - 1 := by nlinarith
      have h2 : (4095 : ℤ) ≤ (q ^ 2) ^ 2 - 1 := by nlinarith
      have hpos : 0 ≤ ((q ^ 2) ^ 1 - 1) * ((q ^ 2) ^ 2 - 1) := by nlinarith
      have hle' : ((q ^ 2) ^ 1 - 1) * ((q ^ 2) ^ 2 - 1) ≤ (n : ℤ) := by
        rw [← Int.natAbs_of_nonneg hpos]
        exact_mod_cast hle
      nlinarith

theorem ggAKFG_card_eq_two_pow_mul_commutator {G : Type*} [Group G] [Finite G] (O : Subgroup G)
    (hodd : ∀ g ∈ O, Odd (orderOf g) → g ∈ ⁅O, O⁆) :
    ∃ k, Nat.card O = 2 ^ k * Nat.card ↥⁅O, O⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ g : O, (g : G) ∈ ⁅O, O⁆ → g ∈ commutator O := by
    intro g hg
    rw [← Subgroup.map_subtype_commutator] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    rwa [show x = g from Subtype.ext hxg] at hx
  have hP : IsPGroup 2 (O ⧸ commutator O) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨i, u, hu, hgo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
      refine ⟨i, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine hcomm _ (hodd _ (g ^ 2 ^ i).2 ?_)
      rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (pow_ne_zero i two_ne_zero)
        (Dvd.intro _ hgo.symm), hgo, Nat.mul_div_cancel_left _ (pow_pos two_pos i)]
      exact hu
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  refine ⟨k, ?_⟩
  rw [(commutator O).card_eq_card_quotient_mul_card_subgroup, hk]
  congr 1
  exact Nat.card_congr (((commutator O).equivMapOfInjective _ O.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))).toEquiv

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  LayerCores LayerCores.OrthRegular

theorem ggNotExcThree_orthDerived {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (hK4 : 4 ≤ Nat.card K) (h3 : 3 ≤ finrank K W)
    (hns : ¬ (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0))
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) →
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hZ : Subgroup.center ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = ⊥) :
    GGNotExcThreeOrder (ggCQ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  rw [ggCQ_eq_card_of_center_eq_bot hZ]
  obtain ⟨k, hk⟩ := ggAKFG_card_eq_two_pow_mul_commutator _ hodd
  obtain ⟨m, hm⟩ : ∃ m, finrank K W = 2 * (m + 1) := by
    obtain ⟨j, hj⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
    exact ⟨j - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨a, -, ha⟩ := exists_card_eq_two_pow K
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine (ggNotExcThreeOrder_iff _).mpr fun N₀ hN₀ heq => ?_
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hm
      (Or.inl ⟨rfl, hplus⟩)
    rw [hk, heq, ha] at hcard
    refine ggAKFG_orth_ne ha2 hm1 (fun h1 => ?_) hN₀ hcard
    exfalso
    obtain ⟨W', hW', hW's⟩ := hplus
    exact hns ⟨by omega, W', by omega, hW's⟩
  · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hm
      (Or.inr ⟨rfl, hplus⟩)
    rw [hk, heq, ha] at hcard
    exact ggAKFG_orth_ne ha2 hm1 (fun _ => rfl) hN₀ hcard

theorem injective_specialRho_inl (K : Type*) [Field K] :
    Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h := congrArg (fun g : DeterminantIsometries K => g.val (1 : Matrix (Fin 2) (Fin 2) K)) hA
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at h
  rw [specialRho_apply] at h
  exact Subtype.ext (by simpa using h)

theorem injective_specialRho_inr (K : Type*) [Field K] :
    Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have h := congrArg (fun g : DeterminantIsometries K => g.val (1 : Matrix (Fin 2) (Fin 2) K)) hB
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at h
  rw [specialRho_apply] at h
  have h1 : B⁻¹ = 1 := Subtype.ext (by simpa using h)
  rw [← inv_inv B, h1, inv_one]

theorem exists_subCoreFamily_orthRegular_excThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (hK4 : 4 ≤ Nat.card K) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsSubCoreFamily (TauCeti.QuadraticMap.orthogonalGroup Q) S ∧
        ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  by_cases h3 : 3 ≤ finrank K W
  · obtain ⟨hexc, -⟩ := orthogonal_regular_space_coverage Q hQ h3
    by_cases hsmall : SmallFixedException Q
    · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
        (isSolvable_of_no_prime_gt_three' (hexc hsmall)), fun c => c.elim⟩
    have hZ : ∀ z ∈ ⁅O, O⁆, (∀ y ∈ ⁅O, O⁆, z * y = y * z) → z ^ 2 = 1 → z = 1 :=
      fun z hz hzc _ => eq_one_of_commute_orthDerived hQ h3 hsmall
        (LayerFacts.ggCommutator_self_le O hz) hzc
    have hder : LayerFacts.ggDer O 1 = ⁅O, O⁆ := by
      rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero]
    by_cases hsplit : finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    ·
      have hK2 : Nat.card K ≠ 2 := fun h => hsmall (Or.inr ⟨hsplit, Or.inl h⟩)
      have hK3 : Nat.card K ≠ 3 := fun h => hsmall (Or.inr ⟨hsplit, Or.inr h⟩)
      obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
        orthogonal_split_four_derived hK2 hK3 Q hQ hsplit.1 hsplit.2
      set L₁ := (determinantLeftFactor K).map e.symm.toMonoidHom with hL₁
      set L₂ := (determinantRightFactor K).map e.symm.toMonoidHom with hL₂
      let L : Bool → Subgroup ↥O := fun b => cond b L₁ L₂
      have hLle : ∀ b, L b ≤ commutator ↥O := by
        rintro (_ | _)
        · show L₂ ≤ _
          rw [hsup]
          exact le_sup_right
        · show L₁ ≤ _
          rw [hsup]
          exact le_sup_left
      have hLn : ∀ b, ((L b).subgroupOf (commutator ↥O)).Normal := by
        rintro (_ | _)
        · exact hn₂
        · exact hn₁
      have hLq : ∀ b, CFSG.IsQuasisimple (L b) := by
        rintro (_ | _)
        · exact hq₂
        · exact hq₁
      have hLgood : ∀ b, GGNotExcThreeOrder (ggCQ (L b)) := by
        rintro (_ | _)
        · show GGNotExcThreeOrder (ggCQ L₂)
          rw [hL₂, ggCQ_map_of_injective e.symm.toMonoidHom e.symm.injective]
          exact ggNotExcThree_of_mulEquiv_SL le_rfl
            (MonoidHom.ofInjective (injective_specialRho_inr K)).symm
        · show GGNotExcThreeOrder (ggCQ L₁)
          rw [hL₁, ggCQ_map_of_injective e.symm.toMonoidHom e.symm.injective]
          exact ggNotExcThree_of_mulEquiv_SL le_rfl
            (MonoidHom.ofInjective (injective_specialRho_inl K)).symm
      have hsupL : (⨆ b, (L b).map O.subtype) = ⁅O, O⁆ := by
        rw [← Subgroup.map_iSup, iSup_bool_eq]
        show (L₁ ⊔ L₂).map O.subtype = ⁅O, O⁆
        rw [← hsup, Subgroup.map_subtype_commutator]
      refine ⟨Bool, fun b => (L b).map O.subtype, ⟨fun b => Subgroup.map_subtype_le _,
        fun b => ?_, fun b => ?_, ⟨1, ?_⟩, fun z hz hzc hz2 => ?_⟩, fun b => ?_⟩
      · have hnorm : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
          (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
            (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
        have h1 : CFSG.Assembly.IsSubnormal (L b) ⊤ :=
          CFSG.Assembly.IsSubnormal.step (hLle b) (hLn b)
            (CFSG.Assembly.IsSubnormal.step le_top hnorm (CFSG.Assembly.IsSubnormal.refl ⊤))
        have h2 := ggSubnormal_map O.subtype h1
        rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((L b).equivMapOfInjective _ O.subtype_injective) (hLq b)
      · rw [hder, hsupL]
      · rw [hsupL] at hz hzc
        exact hZ z hz hzc hz2
      · rw [ggCQ_map_of_injective _ O.subtype_injective]
        exact hLgood b
    ·
      obtain ⟨hq, hodd⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hQ h3 hsplit
      refine ⟨Unit, fun _ => ⁅O, O⁆, ⟨fun _ => LayerFacts.ggCommutator_self_le O,
        fun _ => ggSubnormal_of_normal (LayerFacts.ggCommutator_self_le O)
          fun u hu s hs => LayerPDiv.conj_mem_commutator_self O hu hs, fun _ => hq, ⟨1, ?_⟩,
        fun z hz hzc hz2 => ?_⟩, fun _ => ?_⟩
      · rw [hder, iSup_const]
      · rw [iSup_const] at hz hzc
        exact hZ z hz hzc hz2
      · have hZbot : Subgroup.center ↥⁅O, O⁆ = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [Subgroup.mem_bot]
          exact Subtype.ext (eq_one_of_commute_orthDerived hQ h3 hsmall
            (LayerFacts.ggCommutator_self_le O x.2) fun y hy =>
              (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)).symm)
        exact ggNotExcThree_orthDerived hQ hK4 h3 hsplit hodd hZbot
  · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
      (isSolvable_orthogonalGroup_of_finrank_le_two hQ (by omega)), fun c => c.elim⟩

end LayerExcThree

end CFSG.StandardType
