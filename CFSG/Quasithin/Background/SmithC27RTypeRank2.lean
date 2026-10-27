module

public import CFSG.Quasithin.Background.SmithC27RTypeAlt
public import CFSG.Quasithin.Background.SmithC27RTypeDefs
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

noncomputable def quotCenterEquivSelf {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem center_quasithinG2_eq_bot' {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m) : Subgroup.center ↥(quasithinG2 F) = ⊥ := by
  have : CharP F 2 := B42G2Id.charP_two_of_card hF
  obtain ⟨c, hc0, hc1⟩ := B42G2Id.exists_ne_zero_ne_one_of_three_le (K := F)
    (hF ▸ B42G2Id.three_le_two_pow hm)
  let e₀ : ↥(quasithinG2 F) ≃* ↥(CFSG.Quasithin.Explicit.cayleyGroup F) :=
    MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup
  have h1 := map_center_of_mulEquiv e₀
  rw [A318Excl.center_cayleyGroup_eq_bot hc0 hc1] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).1 h1

theorem isPSL_statedSL_three {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) :
    IsPSL 3 2 n (↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ⧸
      Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
  refine ⟨⟨Nat.prime_two, hn, by norm_num, ?_, ?_⟩, F, inferInstance, inferInstance,
    by rw [Nat.card_eq_fintype_card, hF],
    ⟨(quotCenterCongr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem isPSp4_statedSp_two {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) :
    IsPSp4 2 n (↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) ⧸
      Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 F
    ⟨Nat.prime_two, by omega, le_rfl, ?_⟩ (by rw [Nat.card_eq_fintype_card, hF])
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem isAlt_alternatingGroup_six :
    IsAlt 6 (↥(alternatingGroup (Fin 6)) ⧸ Subgroup.center ↥(alternatingGroup (Fin 6))) :=
  ⟨quotCenterEquivSelf (center_alternatingGroup_eq_bot' (Or.inr (Or.inl rfl)))⟩

section G2


theorem isG2_quasithinG2 {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) :
    IsG2 2 n (↥(quasithinG2 F) ⧸ Subgroup.center ↥(quasithinG2 F)) := by
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := B42G2Id.charP_two_of_card hF'
  obtain ⟨e⟩ := B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient hF' hn
  exact ⟨⟨Nat.prime_two, by omega, rfl, B42G2Id.three_le_two_pow hn⟩, F, inferInstance,
    inferInstance, hF', ⟨(quotCenterEquivSelf (center_quasithinG2_eq_bot' hn hF')).trans e⟩⟩

theorem ResidueRankTwo.isRankTwoLie2Derived {G : Type} [Group G] [Finite G]
    {R K V : Subgroup G} (hs : StarHyp R K V) (ht : ResidueRankTwo K V) :
    IsRankTwoLie2Derived ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  obtain ⟨e₀⟩ := hs.nonempty_quotCenterEquiv
  rcases ht with ⟨n, F, iF, fF, hn, hF, ⟨e⟩, -⟩ | ⟨n, F, iF, fF, hn, hF, ⟨e⟩, -⟩ |
    ⟨n, F, iF, fF, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨-, -, ⟨e⟩⟩, -⟩
  · exact Or.inl ⟨n, IsPSL.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm
      (isPSL_statedSL_three hn hF)⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n,
      IsPSp4.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm (isPSp4_statedSp_two hn hF)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n,
      IsG2.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm (isG2_quasithinG2 hn hF)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (IsAlt.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm isAlt_alternatingGroup_six)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₀.trans e⟩))))

end G2

end CFSG.Quasithin.SmithC27
