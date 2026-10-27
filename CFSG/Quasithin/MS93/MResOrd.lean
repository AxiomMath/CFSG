module

public import CFSG.Quasithin.MS93.MS93FrontierDeep
public import CFSG.Quasithin.MS93.ASC132
public import CFSG.Quasithin.MS93.ASC134Ord
public import CFSG.Quasithin.MS93.ASHyp
public import CFSG.Quasithin.MS93.MResDefs
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Pointwise

section Quot

variable {G : Type} [Group G]

@[expose] def NoSp4Quot (L : Subgroup G) : Prop :=
  ¬ ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSp 2 F)),
    2 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective α ∧ CFSG.pCore 2 ↥L ≤ α.ker

@[expose] def NoSL3Quot (L : Subgroup G) : Prop :=
  ¬ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

theorem notSL3Big_of_noSL3Quot {L : Subgroup G} (hL : NoSL3Quot L) : NotSL3Big L :=
  fun ⟨n, F, _, _, α, _, hF, hα⟩ => hL ⟨n, F, inferInstance, inferInstance, α, hF, hα⟩

theorem card_dvd_card_quot_of_le_ker {L : Subgroup G} {Γ : Type*} [Group Γ] (α : ↥L →* Γ)
    (hα : Function.Surjective α) (hk : CFSG.pCore 2 ↥L ≤ α.ker) :
    Nat.card Γ ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have h1 : α.ker.index ∣ (CFSG.pCore 2 ↥L).index := Subgroup.index_dvd_of_le hk
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hα, Subgroup.card_top] at h1
  exact h1

theorem noSp4Quot_of_not_dvd {L : Subgroup G}
    (hc : ¬ 2 ^ 8 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : NoSp4Quot L := by
  rintro ⟨k, F, _, _, α, hk, hcard, hα, hker⟩
  apply hc
  have hd := card_dvd_card_quot_of_le_ker α hα hker
  rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_eq_fintype_card,
    hcard] at hd
  have h4 : (2 : ℕ) ^ 8 ∣ ((2 : ℕ) ^ k) ^ (2 ^ 2) := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  exact h4.trans ((dvd_mul_right _ _).trans hd)

theorem noSp4Quot_of_isModO2Surj_two {L : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) :
    NoSp4Quot L := by
  refine noSp4Quot_of_not_dvd ?_
  rw [card_quot_of_isModO2Surj hα, card_statedSL3_eq (n := 1) (by rw [hF, pow_one])]
  decide

end Quot

section Desc

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem pCore_le_ker_of_natural_le {W Z : Subgroup G} (h : PUHyp M T L) (hWX : W ≤ Xq M)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ} {k : ℕ} (hk : 0 < k)
    (hn : IsSumOfNaturalModulesVia L W Z α false k) :
    CFSG.pCore 2 ↥L ≤ α.ker := by
  obtain ⟨-, -, β, hβ, -, hβeq⟩ := hn
  intro o ho
  have hoQ := mem_pCoreOf_of_mem_pCore h ho
  have hcent : ∀ u : ↥W, (o : G) * u * (o : G)⁻¹ = u := by
    intro u
    have hu := hWX u.2
    have hc := Subgroup.mem_centralizer_iff.mp
      (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hu)) _ hoQ
    rw [hc, mul_inv_cancel_right]
  have hfix : ∀ x : ι → F,
      ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => x)
    have := hβeq o u u (hcent u).symm ⟨0, hk⟩
    rw [hu] at this
    simpa [moduleAct] using this.symm
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply Units.ext
  show ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = 1
  have : Matrix.toLin' ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      Matrix.toLin' (1 : Matrix ι ι F) := by
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix, Matrix.one_mulVec]
  exact Matrix.toLin'.injective this

theorem isSp4Full_of_isSp4U_of_noSp4 (h : PUHyp M T L) (hS : NoSp4Quot L)
    (hU : IsSp4U M T L) : IsSp4Full M T L := by
  rcases hU with ⟨k, F, _, _, α, hk, hcard, hα, hn⟩ | ⟨α, hα, hnat⟩
  · exact (hS ⟨k, F, inferInstance, inferInstance, α, hk, hcard, hα,
      pCore_le_ker_of_natural_le h h.Uq_le_Xq one_pos hn⟩).elim
  · exact ⟨1, ZMod 2, inferInstance, inferInstance, α, le_rfl, by simp, hα, hnat⟩

theorem not_isSL3U_of_noSL3 (h : PUHyp M T L) (hSL : NoSL3Quot L) : ¬ IsSL3U M T L := by
  rintro ⟨-, -, n, F, _, _, α, hF, hα, -⟩
  exact hSL ⟨n, F, inferInstance, inferInstance, α, hF, isModO2Surj_of_surjective h hF hα⟩

theorem endConcl_of_noSp4 (hred : PUReduce) (hL : NotSL3Big L) (hS : NoSp4Quot L)
    (h : PUHyp M T L) : S34D.EndConcl T L := by
  obtain ⟨M₁, T₁, h₁, hT₁, hmin₁, -⟩ := exists_minimal_reduction hred h
  exact ⟨M₁, T₁, h₁, hT₁, hmin₁,
    Or.inr ⟨isSL3Full_of_isSL3U h₁ hL, isSp4Full_of_isSp4U_of_noSp4 h₁ hS⟩⟩

theorem ms93ConclAS_of_endConcl_noSL3 (h38 : S38) (h512 : S512) (h7 : S7Two)
    (h : PUHyp M T L) (hSL : NoSL3Quot L) (hb : 2 < critDist (puAmalgam h.le))
    (he : S34D.EndConcl T L) : MS93ConclAS M T L := by
  obtain ⟨M₁, T₁, h₁, hT₁T, hmin₁, hor⟩ := he
  have hV₁ : Vq M₁ L = Vq M L := h.vq_eq_vq h₁
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m, hm⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L M₁ T₁ h h₁ hT₁T hmin₁ hV₁ hb hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb with hSL' | hSp
      · exact hSL'.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact MS93ConclAS.of_case5 hX h5
  exfalso
  have hgood := hor.resolve_left hb₁
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G M₁ T₁ L h₁ hb₁' with hSL₁ | hSp₁
  · exact not_isSL3U_of_noSL3 h₁ hSL hSL₁
  · exact h512 G M₁ T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)

theorem ms93ConclAS_of_noQuot_of_items (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h38 : S38) (h512 : S512) (h7 : S7Two) (hred : PUReduce) (h : PUHyp M T L)
    (hSL : NoSL3Quot L) (hS : NoSp4Quot L) : MS93ConclAS M T L := by
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact ms93ConclAS_of_critDist_eq_two h32 h36 h37 h18 h hb
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    exact ms93ConclAS_of_endConcl_noSL3 h38 h512 h7 h hSL (by omega)
      (endConcl_of_noSp4 hred (notSL3Big_of_noSL3Quot hSL) hS h)

theorem ms93ConclAS_of_noSL3_of_items (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h38 : S38) (h512 : S512) (h7 : S7Two) (hred : PUReduce) (hdesc : S34RDescSp4)
    (h : PUHyp M T L) (hSL : NoSL3Quot L) : MS93ConclAS M T L := by
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact ms93ConclAS_of_critDist_eq_two h32 h36 h37 h18 h hb
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    exact ms93ConclAS_of_endConcl_noSL3 h38 h512 h7 h hSL (by omega)
      (endConcl_of_notSL3Big hred hdesc (notSL3Big_of_noSL3Quot hSL) _ M T h rfl)

end Desc

section C132

variable {G : Type} [Group G] [Finite G]

@[expose] def C132Concl (L : Subgroup G) : Prop :=
  IsG2Block L ∨ IsAltBlockType L 6 ∨ IsSp4Block L ∨ IsHatA6Block L ∨
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

theorem c132Concl_of_ms93ConclAS
    {G₀ R L : Subgroup G} (hMS : IsMSPair G₀ R)
    (h : PUHyp G₀ R L) (hc : MS93ConclAS G₀ R L) : C132Concl L := by
  rcases hc with h2 | h3 | h4 | ⟨-, h5⟩ | h6 | h8 | h10 | ⟨-, h11⟩ | ⟨-, h13⟩
  · exact Or.inr (Or.inl (isAltBlockType_of_case2 h h2))
  · rcases hMS.2.1 with ha | hb
    · exact Or.inr (Or.inr (Or.inl (isSp4Block_of_case3 h h3 (isOddRadical_of_msPair h.le ha))))
    · exact absurd h3 (not_case3_of_g2Two h hb.2.2.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case4 h h4))))
  · obtain ⟨n, F, _, _, α, hF, hmod, -⟩ := isModO2Surj_of_case5 h h5
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, α, hF, hmod⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isHatA6Block_of_case6 h h6))))
  · obtain ⟨α, hmod, -⟩ := isModO2Surj_of_case8 h h8
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, α,
      by rw [ZMod.card, pow_one], hmod⟩)))
  · exact Or.inl (isG2Block_of_case10 h h10)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case11 h h11))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case13 h h13))))

@[expose] def AS_C_1_32_NoSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) → NoSp4Quot L → C132Concl L

theorem AS_C_1_32_NoSp4.of_not_dvd (h : AS_C_1_32_NoSp4) {G : Type} [Group G] [Finite G]
    {G₀ R L : Subgroup G} (hMS : IsMSPair G₀ R) (hL : L ∈ cComp G₀)
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G))
    (hc : ¬ 2 ^ 8 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : C132Concl L :=
  h G G₀ R L hMS hL hG (noSp4Quot_of_not_dvd hc)

theorem asC132NoSp4_of_items
    (hS : RankTwoLieSimple) (h32 : S32) (h36 : S36) (h37 : S37)
    (h18 : S18) (h38 : S38) (h512 : S512) (h7 : S7Two) (hred : PUReduce) :
    AS_C_1_32_NoSp4 := by
  intro G _ _ G₀ R L hMS hL hG hSp
  by_cases hSL : NoSL3Quot L
  · have h := puHyp_of_msPair_of_simple hS hMS hL hG
    exact c132Concl_of_ms93ConclAS hMS h
      (ms93ConclAS_of_noQuot_of_items h32 h36 h37 h18 h38 h512 h7 hred h hSL hSp)
  · obtain ⟨n, F, _, _, α, hF, hmod⟩ := Classical.not_not.mp hSL
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, α, hF, hmod⟩)))

theorem asC132_of_items_descSp4
    (hS : RankTwoLieSimple) (h32 : S32) (h36 : S36) (h37 : S37)
    (h18 : S18) (h38 : S38) (h512 : S512) (h7 : S7Two) (hred : PUReduce)
    (hdesc : S34RDescSp4) : ASInputs.AS_C_1_32 := by
  intro G _ _ G₀ R L hMS hL hG
  by_cases hSL : NoSL3Quot L
  · have h := puHyp_of_msPair_of_simple hS hMS hL hG
    exact c132Concl_of_ms93ConclAS hMS h
      (ms93ConclAS_of_noSL3_of_items h32 h36 h37 h18 h38 h512 h7 hred hdesc h hSL)
  · obtain ⟨n, F, _, _, α, hF, hmod⟩ := Classical.not_not.mp hSL
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, α, hF, hmod⟩)))

end C132

section Holds

theorem asC132NoSp4_holds
    : AS_C_1_32_NoSp4 :=
  asC132NoSp4_of_items rankTwoLieSimple_holds s32_holds (s36_of_g2 s38G2_holds) s37_holds
    s18_holds (s38_of_g2 s38G2_holds) s512_holds
    (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds)
    puReduce_holds

theorem asC132_of_descSp4
    (hdesc : S34RDescSp4) : ASInputs.AS_C_1_32 :=
  asC132_of_items_descSp4 rankTwoLieSimple_holds s32_holds (s36_of_g2 s38G2_holds) s37_holds
    s18_holds (s38_of_g2 s38G2_holds) s512_holds
    (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds)
    puReduce_holds hdesc

end Holds

end CFSG.Quasithin.MS93.MRes
