module

public import CFSG.Quasithin.Vol2.Lie2ParabolicRadicalSp4
public import CFSG.Quasithin.Vol2.KGNatLevi
public import CFSG.Quasithin.Vol2.Lie2ParabolicRadical

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Lie2Parabolic CFSG.LieType.BorelTits

theorem exists_maxParabolic_of_isYAmalgam {G : Type} [Group G] {G₁ G₂ : Subgroup G}
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : (IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) ∨ IsPSp4 2 n Y) (hs : IsSimpleGroup Y)
    {T : Subgroup Y} (h : IsYAmalgam (RankTwoAmalgam.ofSubgroups G₁ G₂) T) :
    ∃ P : Subgroup Y, IsMaxParabolic2 (⊤ : Subgroup Y) P ∧
      Nonempty (↥(perfectCore G₂) ≃* ↥(perfectCore P)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M₁, M₂, hpair, ⟨φ⟩⟩ := h
  have hT := hpair.1
  obtain ⟨Pj, -, hcov, hj, -⟩ :=
    CFSG.Quasithin.H13.NQCat.factL2LieParabolic_holds Y n hn (lie_of_type hY) T hT
  obtain ⟨hM₂, hNM₂⟩ := (hpair.2.2 M₂).mpr (Or.inr rfl)
  have hnn : ∀ R : Subgroup Y, R ≠ ⊥ → IsPGroup 2 R → Subgroup.normalizer (R : Set Y) ≠ ⊤ := by
    intro R hR hR2 htop
    have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
    · exact hR h
    ·
      have hY2 : IsPGroup 2 Y :=
        (hR2.of_equiv (MulEquiv.subgroupCongr h)).of_equiv Subgroup.topEquiv
      have hnt := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n (hj 0).2.2).1
      have hC2 : IsPGroup 2 ↥(perfectCore (Pj 0)) := hY2.to_subgroup _
      have htop' : CFSG.pCore 2 ↥(perfectCore (Pj 0)) = ⊤ :=
        eq_top_iff.mpr (le_sSup ⟨inferInstance, hC2.of_equiv Subgroup.topEquiv.symm⟩)
      rw [← not_subsingleton_iff_nontrivial] at hnt
      apply hnt
      change Subsingleton (_ ⧸ CFSG.pCore 2 ↥(perfectCore (Pj 0)))
      rw [htop']
      exact QuotientGroup.subsingleton_quotient_top
  have hM₂top : M₂ ≠ ⊤ := by
    obtain ⟨R, hR, hR2, hM⟩ := hM₂.1
    rw [hM]
    exact hnn R hR hR2
  obtain ⟨M', hM', hM₂M'⟩ := (eq_top_or_exists_le_coatom M₂).resolve_left hM₂top
  have hM'cov : M' ⋖ ⊤ := covBy_top_iff.mpr hM'
  obtain ⟨j, hj'⟩ := (hcov M' (hNM₂.trans hM₂M')).mp hM'cov
  subst hj'
  have hPmax : IsMaxParabolic2 (⊤ : Subgroup Y) (Pj j) := by
    refine ⟨⟨le_top, T, hT, by simpa using hNM₂.trans hM₂M'⟩, hM'cov.lt.ne, fun Q _ hQ hPQ => ?_⟩
    exact (hM'cov.eq_or_eq hPQ le_top).resolve_right hQ
  have hO : pCoreOf 2 (Pj j) ≠ ⊥ := by
    obtain ⟨a, ha, o, ho, hY'⟩ : ∃ a, 2 ≤ a ∧ ∃ o, Odd o ∧ Nat.card Y = 2 ^ (a * n) * o := by
      rcases hY with hY | hY
      · exact ⟨3, by norm_num, (two_part_of_type (Y := Y)).1 hY⟩
      · exact ⟨4, by norm_num, (two_part_of_type (Y := Y)).2 hY⟩
    have hc := (card_perfectCore hn hY hPmax ho hY').1
    set C := perfectCore (Pj j) with hC
    have hC1 : pCoreOf 2 C ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card (CFSG.Open.pCore 2 ↥C) = 1 := by
        have := congrArg (fun X : Subgroup Y => Nat.card X) hbot
        simp only [Subgroup.card_bot] at this
        rw [← this]
        exact (Subgroup.card_map_of_injective C.subtype_injective).symm
      rw [hc] at h1
      have h2 : 1 ≤ (a - 1) * n := Nat.mul_pos (by omega) (by omega)
      have : 2 ^ ((a - 1) * n) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h2
      omega
    intro hbot
    apply hC1
    rw [eq_bot_iff, ← hbot]
    refine le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 C).trans (CFSG.Quasithin.perfectCore_le _)) ?_ (pCoreOf_isPGroup 2 C)
    exact (Subgroup.le_normalizer.trans
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)).trans
        (normalizer_le_normalizer_pCoreOf 2 C)
  have hPN : Pj j = Subgroup.normalizer (pCoreOf 2 (Pj j) : Set Y) :=
    ((hM'cov.eq_or_eq (le_normalizer_pCoreOf 2 (Pj j)) le_top).resolve_right
      (hnn _ hO (pCoreOf_isPGroup 2 (Pj j)))).symm
  have hloc : IsTwoLocal (Pj j) := ⟨_, hO, pCoreOf_isPGroup 2 (Pj j), hPN⟩
  have hPM : Pj j = M₂ := hM₂.2 (Pj j) hloc hM₂M'
  refine ⟨Pj j, hPmax, ⟨?_⟩⟩
  rw [hPM]
  exact (CFSG.Quasithin.Vol2.KGNat.perfectCoreEquiv G₂).trans
    ((CFSG.Quasithin.Vol2.KGNat.perfectResidualCongr φ.φ2).trans
      (CFSG.Quasithin.Vol2.KGNat.perfectCoreEquiv M₂).symm)

theorem of_isLieOverTwo_psl {Y : Type} [Group Y] {n : ℕ} (h : IsLieOverTwo .PSL 3 n Y) :
    Finite Y ∧ IsSimpleGroup Y ∧ IsPSL 3 2 n Y := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨CFSG.LieType.Simplicity.finite_of_statedClassicalModel hc,
      (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 n hc).2, hc⟩
  all_goals exact absurd h0 (by norm_num)

theorem of_isLieOverTwo_psp {Y : Type} [Group Y] {n : ℕ} (h : IsLieOverTwo .PSp 2 n Y) :
    Finite Y ∧ IsSimpleGroup Y ∧ IsPSp4 2 n Y := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨CFSG.LieType.Simplicity.finite_of_statedClassicalModel hc,
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 2 2 n hc, hc⟩
  all_goals exact absurd h0 (by norm_num)

theorem card_pCoreOf_eq_of_mulEquiv {X X' : Type*} [Group X] [Group X'] {A : Subgroup X}
    {A' : Subgroup X'} (e : ↥A ≃* ↥A') :
    Nat.card (pCoreOf 2 A) = Nat.card (CFSG.pCore 2 ↥A') := by
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]
  exact (Subgroup.card_map_of_injective A.subtype_injective).trans
    (Subgroup.card_map_of_injective e.injective).symm

theorem pCoreOf_perfectCore_of_amalgam {G : Type} [Group G] {G₁ G₂ : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) :
    (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .PSL 3 n) →
      Nat.card (pCoreOf 2 (perfectCore G₂)) = 2 ^ (2 * n)) ∧
    (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .PSp 2 n) →
      Nat.card (pCoreOf 2 (perfectCore G₂)) = 2 ^ (3 * n) ∧
        ⁅pCoreOf 2 (perfectCore G₂), perfectCore G₂⁆ = pCoreOf 2 (perfectCore G₂)) := by
  refine ⟨fun ⟨Y, _, hY, T, hT⟩ => ?_, fun ⟨Y, _, hY, T, hT⟩ => ?_⟩
  · obtain ⟨hfin, hs, hL⟩ := of_isLieOverTwo_psl hY
    have hY' : (IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) ∨ IsPSp4 2 n Y := Or.inl (Or.inl hL)
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_maxParabolic_of_isYAmalgam hn hY' hs hT
    obtain ⟨o, ho, hc⟩ := (two_part_of_type (Y := Y)).1 (Or.inl hL)
    rw [card_pCoreOf_eq_of_mulEquiv e, (card_perfectCore hn hY' hP ho hc).1]
  · obtain ⟨hfin, hs, hL⟩ := of_isLieOverTwo_psp hY
    have hY' : (IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) ∨ IsPSp4 2 n Y := Or.inr hL
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_maxParabolic_of_isYAmalgam hn hY' hs hT
    obtain ⟨o, ho, hc⟩ := (two_part_of_type (Y := Y)).2 hL
    refine ⟨by rw [card_pCoreOf_eq_of_mulEquiv e, (card_perfectCore hn hY' hP ho hc).1], ?_⟩
    exact (commutator_pCoreOf_congr e).mpr (commutator_pCoreOf_perfectCore hn hL hP)

end CFSG.Quasithin.H13
