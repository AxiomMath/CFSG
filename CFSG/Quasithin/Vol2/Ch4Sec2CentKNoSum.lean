module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKFin
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKIrr
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFo
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Big
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFe
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFt
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFx
public import CFSG.Quasithin.Vol2.Ch4Sec3C136

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank

@[expose] def Conf4212NoSum2ND : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
    Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K →
    ∀ n : ℕ, IsPSL 2 2 n (ModO2 (perfectCore (L ⊓ H))) → 1 < n →
      IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K →
      (∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (V₁ : Subgroup G), 1 < m ∧
        Fintype.card F = 2 ^ m ∧ IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁) →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F) (V₁ V₂ : Subgroup G),
        Fintype.card F = 2 ^ n ∧ ⁅reducedAggregate (L ⊔ T), L⁆ = V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
        IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₁
          (V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
          ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F) ∧
        IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₂
          (V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
          ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F)) →
      ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥

theorem conf4212NoSum2ND_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hCRK : Conf4212CentKND) : Conf4212NoSum2ND := by
  intro G _ _ T M L Mm I H K hy hIH c n hn hn1 h2 hline hsum hVL
  have hcent := hCRK G T M L Mm I H K hy hIH c n hn hn1 h2 hline hsum hVL
  obtain ⟨h41, ⟨-, -, -, -, -, -, -, hMS, -⟩⟩ := c.c41Case3_of_isC134Case2 h2
  have hKH : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨k, hk, rfl⟩
    have h1 := mem_conjClosure hh hk
    rw [h41.2.2.1] at h1
    exact h1
  obtain ⟨m, F, _, _, V₁, hm, hF, hstab⟩ := hline
  exact c.not_isC134Case2_core sl3ParabolicAutFact_holds lemmaC136_holds hy h37 h38 h39 hIH hKH
    hMS hm hF hstab hcent h2

end CFSG.Quasithin.H13.Ch4.CentK

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem ff_or_orth_of_cases_centk (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo) (hKG : KGG2BlockRuFF)
    (hNoSum2 : CentK.Conf4212NoSum2ND) (hNoBig : Conf4212NoSumBig) {Mm : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H)
    (hk : ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 (perfectCore (L ⊓ H))) →
      IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
        ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k → k ≤ 4)
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    (∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆)) ∨
      Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆ := by
  by_cases hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · rcases hcase with h1 | h2 | h3 | h4 | h5 | h7 | h8
    · obtain ⟨n, hpsl, ⟨F, _, _, hF, hnat⟩ | ⟨hn2, halt⟩ | ⟨hn1, h134, hline, hmod⟩⟩ := h1
      · exact Or.inl (c.ff_of_case1_natural hCV hF hnat)
      · subst hn2
        exact Or.inr (c.orth_of_case1_alt hCV hpsl halt)
      · obtain ⟨F₃, _, _, V₁, V₂, hF₃, hV, h₁, h₂⟩ := hmod
        by_cases hdisj : V₁ ⊓ V₂ = ⊥
        · exact absurd hCV (hNoSum2 G T M L Mm I H K hy hIH c n hpsl hn1 h134 hline
            ⟨F₃, inferInstance, inferInstance, V₁, V₂, hF₃, hV, hdisj, h₁, h₂⟩)
        · have hV₁ : V₁ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
            rw [hV]
            exact le_sup_left
          have hV₂ : V₂ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
            rw [hV]
            exact le_sup_right
          have hZ : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
              Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
            rw [← c.inf_centralizer_eq]
            exact hCV
          have hZ₁ : V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ :=
            eq_bot_iff.mpr ((inf_le_inf_right _ hV₁).trans hZ.le)
          have hZ₂ : V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ :=
            eq_bot_iff.mpr ((inf_le_inf_right _ hV₂).trans hZ.le)
          have h₁' := h₁
          have h₂' := h₂
          rw [hZ₁] at h₁'
          rw [hZ₂] at h₂'
          have hEq : V₁ = V₂ :=
            CentK.eq_of_inf_ne_bot_of_natural (two_eq_zero_of_card hF₃) h₁' h₂' hdisj
          have hVV : ⁅reducedAggregate (L ⊔ T), L⁆ = V₁ := by
            rw [hV, hEq, sup_idem]
          rw [← hVV] at h₁
          exact Or.inl (c.ff_of_case1_natural hCV hF₃ h₁)
    · obtain ⟨m, hm, hpsl, ⟨k, hk1, hsum⟩ | ⟨-, halt⟩⟩ := h2
      · by_cases hkm : k < m
        · exact Or.inl (c.ff_of_case2_sum hm hk1 hkm hsum)
        · exact (hNoBig G T M L Mm I H K hy hIH c m k hm (by omega) (hk m k hm hpsl hsum) hpsl
            hsum).elim
      · exact Or.inl (c.ff_of_case2_alt halt)
    · exact Or.inl (c.ff_of_altBlock6 hCV h3.2)
    · exact Or.inl (c.ff_of_case4 hCV h4.2)
    · exact Or.inl (c.ff_of_case5 h5.2)
    · exact Or.inl (c.ff_of_case7 hKG hCV h7)
    · exact Or.inl (c.ff_of_altBlock6 hCV h8.2)
  · exact Or.inl (c.ff_of_inf_centralizer_ne_bot h37 h38 h39 hC58 h317 h332 hCV)

end Conf4212

end CFSG.Quasithin.H13.Ch4
