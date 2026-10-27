module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofCharThree
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

@[expose] def NoOrderMersenne223 (S : Type) [Group S] : Prop :=
  ∀ s : S, ∀ m : ℕ, 1 < m → Odd m → orderOf s ≠ 3 * (2 ^ m - 1)

namespace Item223CensusProof

theorem exists_orderOf_eq_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : projSL 2 (GaloisField 2 m), orderOf c = 2 ^ m - 1 := by
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := (GaloisField 2 m)ˣ)
  have hord : orderOf t = 2 ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, Nat.card_units,
      GaloisField.card 2 m (by omega)]
  have hinj : Function.Injective (CentralCover.sl2DiagHom (GaloisField 2 m)) :=
    CentralCover.sl2Diag_injective
  refine ⟨(projSLTwoEquivSL (GaloisField 2 m)).symm (CentralCover.sl2DiagHom _ t), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective _ hinj, hord]

theorem coprime_three_two_pow_sub_one {m : ℕ} (hm : Odd m) : Nat.Coprime 3 (2 ^ m - 1) := by
  obtain ⟨k, rfl⟩ := hm
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  rw [h2]
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
  omega

theorem noL2Inner223_of_orderOf {S : Type} [Group S] [IsSimpleGroup S]
    (hS : NoOrderMersenne223 S) : NoL2Inner223 S := by
  intro Kb m a ⟨eK⟩ hm1 hmo haZ ha3 hcomm
  have hZ : Subgroup.center S = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
      fun htop => ?_
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eK
    have hy : ((y : Kb) : S) ∈ Subgroup.center S := htop ▸ Subgroup.mem_top _
    exact hxy (Subtype.ext (Subgroup.mem_center_iff.mp hy (x : S)))
  rw [hZ, Subgroup.mem_bot] at haZ ha3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha : orderOf a = 3 := orderOf_eq_prime ha3 haZ
  obtain ⟨c, hc⟩ := exists_orderOf_eq_two_pow_sub_one (m := m) (by omega)
  have hc' : orderOf ((eK.symm c : Kb) : S) = 2 ^ m - 1 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc]
  have hac : Commute a ((eK.symm c : Kb) : S) := hcomm _ (eK.symm c).2
  have h := hac.orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [ha, hc']; exact coprime_three_two_pow_sub_one hmo)
  rw [ha, hc'] at h
  exact hS _ m hm1 hmo h

theorem noL2Inner223_of_surjective {Y S : Type} [Group Y] [Group S] [IsSimpleGroup S]
    (π : Y →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (hS : NoL2Inner223 S) : NoL2Inner223 Y := by
  intro Kb m a ⟨eK⟩ hm1 hmo haZ ha3 hcomm
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := isSimpleGroup_projSL_two (by omega)
  have : IsSimpleGroup Kb := eK.isSimpleGroup
  have hinj : Function.Injective (π.comp Kb.subtype) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.comp Kb.subtype).ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff _).mp hk
    · exfalso
      obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eK
      have hy1 : (π.comp Kb.subtype) y = 1 := MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top y)
      have hy : (y : Y) ∈ Subgroup.center Y := hker (MonoidHom.mem_ker.mpr hy1)
      exact hxy (Subtype.ext (Subgroup.mem_center_iff.mp hy (x : Y)))
  have hZ : Subgroup.center S = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
      fun htop => ?_
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eK
    apply hxy
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top _) _
  have hcen : ∀ z ∈ Subgroup.center Y, π z ∈ Subgroup.center S := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := hπ s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  refine hS (π.comp Kb.subtype).range m (π a)
    ⟨(MonoidHom.ofInjective hinj).symm.trans eK⟩ hm1 hmo (fun h => haZ ?_)
    (by rw [← map_pow]; exact hcen _ ha3) ?_
  · rw [hZ, Subgroup.mem_bot] at h
    exact hker (MonoidHom.mem_ker.mpr h)
  · rintro _ ⟨k, rfl⟩
    change π a * π k = π k * π a
    rw [← map_mul, ← map_mul, hcomm k k.2]

theorem census223Fact_of_orderOf {S : Type} [Group S] [IsSimpleGroup S]
    (hS : NoOrderMersenne223 S) : Census223Fact S :=
  Or.inr (noL2Inner223_of_orderOf hS)

theorem census223Fact_of_isExtOf_orderOf {Y S : Type} [Group Y] [Group S] [IsSimpleGroup S]
    [Group.IsPerfect S] (h : Sec4.IsExtOf Y S (Multiplicative (ZMod 3)))
    (hS : NoOrderMersenne223 S) : Census223Fact Y := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h
  have h3 : Nat.card N = 3 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have : Group.IsPerfect (Y ⧸ N) := Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom)
    eQ.symm.surjective
  have hNZ := le_center_of_card_eq_three h3
  refine Or.inr (noL2Inner223_of_surjective (eQ.toMonoidHom.comp (QuotientGroup.mk' N))
    (eQ.surjective.comp (QuotientGroup.mk'_surjective N)) (fun y hy => hNZ ?_)
    (noL2Inner223_of_orderOf hS))
  have h1 : QuotientGroup.mk' N y = 1 := eQ.injective (by rw [map_one]; exact hy)
  exact (QuotientGroup.eq_one_iff y).mp h1

theorem census223Fact_of_quotientCenter_orderOf {Y S : Type} [Group Y] [Group S]
    [IsSimpleGroup S] (e : Y ⧸ Subgroup.center Y ≃* S) (hS : NoOrderMersenne223 S) :
    Census223Fact Y := by
  refine Or.inr (noL2Inner223_of_surjective (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun y hy => ?_)
    (noL2Inner223_of_orderOf hS))
  have h1 : QuotientGroup.mk' (Subgroup.center Y) y = 1 := e.injective (by rw [map_one]; exact hy)
  exact (QuotientGroup.eq_one_iff y).mp h1

theorem isPerfect_of_isSimpleGroup_of_card {S : Type} [Group S] [IsSimpleGroup S]
    (hnp : ¬ (Nat.card S).Prime) : Group.IsPerfect S := by
  refine isPerfect_of_isSimpleGroup ?_
  by_contra hc
  push Not at hc
  have : IsMulCommutative S := ⟨⟨hc⟩⟩
  exact hnp (Group.is_simple_iff_prime_card.mp inferInstance)

end Item223CensusProof

open Item223CensusProof

@[expose] def Census223Sp62Orders : Prop :=
  NoOrderMersenne223 (projSp 3 (GaloisField 2 1))

theorem census223Sp62_of (h : Census223Sp62Orders) : Census223Sp62 := by
  have : IsSimpleGroup (projSp 3 (GaloisField 2 1)) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (GaloisField 2 1)
      3 (by norm_num) (Or.inr (Or.inr ⟨by rw [GaloisField.card 2 1 (by norm_num)]; norm_num,
        le_rfl⟩))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 3 (GaloisField 2 1))).symm.isSimpleGroup
  exact census223Fact_of_orderOf h

@[expose] def Census223McLONOrders : Prop :=
  NoOrderMersenne223 (NativeSporadic.Carrier .McL) ∧
    NoOrderMersenne223 (NativeSporadic.Carrier .ONan)

theorem census223SporadicRest_of
    (h : Census223McLONOrders) : Census223SporadicRest := by
  have : IsSimpleGroup (NativeSporadic.Carrier .McL) := CFSG.Sporadic.McL.isSimpleGroup_McL
  have : IsSimpleGroup (NativeSporadic.Carrier .ONan) := CFSG.Sporadic.ON.fam_on_simplicity.2.2
  have : Group.IsPerfect (NativeSporadic.Carrier .McL) :=
    isPerfect_of_isSimpleGroup_of_card (by
      rw [show Nat.card (NativeSporadic.Carrier .McL) = 898128000 from
        CFSG.Sporadic.McL.card_McL]
      norm_num)
  have : Group.IsPerfect (NativeSporadic.Carrier .ONan) :=
    isPerfect_of_isSimpleGroup_of_card (by
      rw [show Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 from
        CFSG.Sporadic.ON.card_ON]
      norm_num)
  refine ⟨census223Fact_of_orderOf h.1, fun Y _ _ hY => ?_⟩
  rcases hY with hY | hY
  · exact census223Fact_of_isExtOf_orderOf hY h.1
  · exact census223Fact_of_isExtOf_orderOf hY h.2

@[expose] def Census223CharThreeOrders : Prop :=
  NoOrderMersenne223 (projSL 3 (GaloisField 3 2)) ∧
  (∀ (X : Type) [Group X], ChevalleyExceptionalModel X .G2 3 1 → NoOrderMersenne223 X) ∧
  NoOrderMersenne223 (projSU 4 3 1)

theorem census223CharThreeRest_of
    (h : Census223CharThreeOrders) : Census223CharThreeRest := by
  have hL : IsSimpleGroup (projSL 3 (GaloisField 3 2)) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := GaloisField 3 2) 3 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (Sec4.projSLEquivPSLn 3 _).isSimpleGroup
  have hU : IsSimpleGroup (projSU 4 3 1) := by
    have hF : Nat.card (GaloisField 3 (2 * 1)) = 3 ^ (2 * 1) := GaloisField.card 3 (2 * 1)
      (by norm_num)
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
      (GaloisField 3 (2 * 1)) 3 1 (by rw [hF, ← pow_mul, mul_comm]) 4 (by norm_num) (by
        intro h
        exact absurd (Prod.mk.inj h).1 (by norm_num))
    exact (Sec4.projSUEquivStatedProj 4 3 1).isSimpleGroup
  refine ⟨census223Fact_of_orderOf h.1, fun Y _ _ _ hY => ?_⟩
  rcases hY with hG2 | hU4
  · have := (CFSG.LieType.Simplicity.fam_g2_simplicity _ 3 1 hG2).2
    exact census223Fact_of_quotientCenter_orderOf (MulEquiv.refl _) (h.2.1 _ hG2)
  · obtain ⟨e⟩ := hU4
    exact census223Fact_of_quotientCenter_orderOf e h.2.2

end CFSG.RankThree.PartTwo.Sec21
