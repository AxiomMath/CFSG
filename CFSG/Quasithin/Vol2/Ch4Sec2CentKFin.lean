module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKHyp
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreC
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKD

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

@[expose] def Conf4212CentKND : Prop :=
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
      ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) = ⊥

theorem conf4212CentKND_of (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h425 : Thm4_2_5) :
    Conf4212CentKND := by
  intro G _ _ T M L Mm I H K hy hIH c n hn hn1 h2 hline hsum hVL
  obtain ⟨F₃, _, _, V₁, V₂, hF₃, hV, hdisj, h₁, h₂⟩ := hsum
  have hKH : H ≤ Subgroup.normalizer (K : Set G) := by
    obtain ⟨h41, -⟩ := c.c41Case3_of_isC134Case2 h2
    intro h hh
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨k, hk, rfl⟩
    have h1 := mem_conjClosure hh hk
    rw [h41.2.2.1] at h1
    exact h1
  have hVcard : Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = 2 ^ (4 * n) := by
    rw [card_V_of_sum c hV hdisj h₁ h₂ hVL, hF₃, ← pow_mul, mul_comm]
  have s : Setting28 T M L Mm I H K n := ⟨hy, hIH, c, hn, hn1, h2, hKH, hVL, hVcard⟩
  obtain ⟨F, _, _, α, β, h⟩ :=
    exists_coreHyp s h36 h37 h38 h39 (h48 G) h425 hline hF₃ hV hdisj h₁ h₂
  by_contra hD
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_le 2 I).trans c.inH.1).trans hKH
  have hQU : c134Q (K ⊔ pCoreOf 2 I) K ≤ pCoreOf 2 K :=
    (commutator_le_pCoreOf_of_le (perfect_of_mem_cComp c.K_mem) hRK le_rfl).1
  have hQK : c134Q (K ⊔ pCoreOf 2 I) K ≤ K := hQU.trans (pCoreOf_le 2 K)
  have hZK : K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 K :=
    inf_centralizer_le_pCoreOf h.co h.αker hQK
  have hDR := D_le_R c h37 hKH hZK
  have hZC := omega_inf_centralizer_ne_bot_of_ne_bot c hKH hDR hD
  exact hZC (centk_core h)

end CFSG.Quasithin.H13.Ch4.CentK
