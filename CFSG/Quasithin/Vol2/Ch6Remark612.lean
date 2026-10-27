module

public import CFSG.Quasithin.Vol2.Ch6Sec1Basic
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

theorem card_quot (h : Hyp5_0_1 G T M L n) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rcases h.lie with ⟨-, -, K, hK, hKf, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hcard]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := h.two_le; omega⟩
    have hodd : Nat.gcd 2 (2 ^ (k + 1) - 1) = 1 := by
      refine Nat.coprime_two_left.mpr ⟨2 ^ k - 1, ?_⟩
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [hodd, Nat.div_one, Finset.Icc_self, Finset.prod_singleton]
    norm_num
  all_goals exact absurd h0 (by norm_num)

theorem n_eq_two_of_isBarS5_r612 (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    (hS5 : IsBarS5 L T V) : n = 2 := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hV.isTwoReducedIn.2.1
  have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card (autOn L V) := by
    rw [card_autOn_eq_relIndex hLV]
    show (CFSG.pCore 2 ↥L).index ∣ ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L).index
    refine Subgroup.index_dvd_of_le fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := h.inf_centralizer_le hLV hV.2.2 (Subgroup.mem_subgroupOf.mp hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have h2 : Nat.card (autOn L V) ∣ 120 := by
    obtain ⟨e⟩ := hS5
    have h120 : Nat.card (autOn (L ⊔ T) V) = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    rw [← h120]
    exact Subgroup.card_dvd_of_le (A4.autOn_mono le_sup_left)
  have h3 := h1.trans h2
  rw [h.card_quot] at h3
  have hn2 := h.two_le
  by_contra hne
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h64 : 64 ≤ (2 ^ n) ^ 2 :=
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
  have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
  have hle := Nat.le_of_dvd (by norm_num) h3
  have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
  omega

end Hyp5_0_1

theorem stmt6_1_2 (h512 : Stmt5_1_2) (h513 : Stmt5_1_3) : Stmt6_1_2 := by
  intro G _ _ T M L V n h
  have hL : ⁅L, L⁆ = L := h.toHyp5_0_1.commutator_eq
  have hT : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  refine ⟨?_, ?_⟩
  · rcases h513 G T M L V n h.toHyp5_0_1 h.module with
      h1 | ⟨h2n, -, h2⟩ | h3 | h4 | ⟨-, h5S, h5⟩
    · exact Or.inl h1
    · exact absurd ⟨h2n, (isA5ModuleSum_of_s5 (Or.inr h2) hL hT hTL).commutator⟩ h.not_a5
    · exact Or.inr (Or.inl h3)
    · by_cases hn : n = 2
      · exact absurd ⟨hn, (hn ▸ h4 : IsOrthCh5 L V 2).isA5ModuleSum_commutator⟩ h.not_a5
      · exact Or.inr (Or.inr ⟨by have := h.two_le; omega, h4⟩)
    · exact absurd ⟨h.toHyp5_0_1.n_eq_two_of_isBarS5_r612 h.module h5S,
        isA5ModuleSum_of_s5 (Or.inl h5) hL hT hTL⟩ h.not_a5
  · rcases h512 G T M L V n h.toHyp5_0_1 h.module with
      ⟨hJ, hJN, -, hJU, -⟩ | ⟨-, h2⟩ | ⟨-, h3n, -, -, h3⟩
    · exact Or.inr ⟨le_inf (GammaExtra.thompsonJ_le fun A hA => hA.1) (hJ.trans inf_le_right),
        h.centralizer_eq, hJN, hJU⟩
    · exact Or.inl h2.commutator
    · exact absurd ⟨h3n, isA5ModuleSum_of_s5 (Or.inl h3) hL hT hTL⟩ h.not_a5

end CFSG.Quasithin.H13
