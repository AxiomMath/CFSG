module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure Mem (T S X Y V : Subgroup G) (b : G) (n : ℕ) : Prop where
  nat : NatData Y V n
  perf : ⁅Y, Y⁆ = Y
  char : CharTwo Y
  comp : Y ∈ cComp X
  TX : T ≤ X
  T2 : IsPGroup 2 T
  ST : S ≤ T
  syl : IsSylowTwoOf (S ⊓ Y) Y
  SY : S ≤ Subgroup.normalizer (Y : Set G)
  bY : b ∈ Y
  bS : b ∈ Subgroup.normalizer (S : Set G)
  bo : orderOf b = 2 ^ n - 1
  hn : 2 ≤ n
  hZ : ∀ z ∈ quasithinOmegaOneCenter T, (∀ s ∈ T, z ∈ Subgroup.centralizer
    ((Y.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G)) → z = 1

namespace Mem

variable {T S X Y V : Subgroup G} {b : G} {n : ℕ} (m : Mem T S X Y V b n)
include m

theorem quasisimple : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  have e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact Ch11.SecA.isQuasisimple_of_mulEquiv_SL2 m.hn (by rw [Nat.card_eq_fintype_card, hF]) e

theorem blockQ_le_T : blockQ Y ≤ T :=
  (EscapingLocal.pCoreOf_le_of_isSylowTwoOf m.syl).trans (inf_le_left.trans m.ST)

theorem b_odd : Odd (orderOf b) ∧ orderOf b ≠ 1 := by
  have hn := m.hn
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) m.hn
  rw [m.bo]
  exact ⟨Nat.Even.sub_odd (by omega) ((by decide : Even 2).pow_of_ne_zero (by omega)) odd_one,
    by omega⟩

theorem inf_centralizer [Finite G] (hs : IsShort2 Y) :
    blockQ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ :=
  inf_centralizer_eq_bot m.T2 m.TX m.comp hs m.quasisimple m.blockQ_le_T m.hZ

theorem blockU_le_of_short [Finite G] (hs : IsShort2 Y) : blockU Y ≤ V := by
  have hVU : V ≤ blockU Y := by
    calc V = ⁅V, Y⁆ := m.nat.commutator_eq.symm
      _ ≤ ⁅blockQ Y, Y⁆ := Subgroup.commutator_mono m.nat.le le_rfl
  have h := SecC.C10KH.sup_blockZ_eq hs hVU m.nat.norm m.nat.not_central
  have hUQ : blockU Y ≤ blockQ Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (C1.le_normalizer_blockQ Y)
  have hZ : blockZ Y = ⊥ := by
    rw [eq_bot_iff, ← m.inf_centralizer hs]
    exact inf_le_inf_right _ hUQ
  rw [hZ, sup_bot_eq] at h
  exact h.symm.le

theorem final [Finite G] (hAS : Ch11.SecH.AS_I_1_3_L2) (hU : blockU Y ≤ V)
    (hres : n = 2 → IsShort2 Y → IsLin2Type Y n → blockZ Y = ⊥ →
      blockQ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ →
        Nat.card (blockQ Y) ≠ 2 * Nat.card (blockU Y)) :
    (IsShort2 Y ∧ IsLin2Type Y n ∧ blockZ Y = ⊥ ∧ blockQ Y = blockU Y) ∧ blockQ Y = V := by
  obtain ⟨hs, hlin, hZ, hUV⟩ := block_of_natData m.hn m.perf m.char m.nat hU
  have hQC := m.inf_centralizer hs
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  rcases blockQ_eq_or hAS m.hn hF m.perf α hαs hαk with h | ⟨h2, hcard⟩
  · exact ⟨⟨hs, hlin, hZ, h⟩, h.trans hUV⟩
  · exact absurd hcard (hres h2 hs hlin hZ hQC)

theorem sylow [Finite G] (hQV : blockQ Y = V) :
    ⁅S, Subgroup.zpowers b⁆ = S ⊓ Y ∧ Nat.card ↥(S ⊓ Y) = 2 ^ n * 4 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hsq := sq_ne_one m.hn α hαk m.bY m.bo
  exact ⟨commutator_eq_inf α hαk m.nat hQV m.bY hsq m.b_odd.1 m.b_odd.2 (m.T2.to_le m.ST) m.SY
    m.bS, card_inf_eq (by have := m.hn; omega) hF α hαs hαk m.nat hQV m.syl⟩

theorem transfer [Finite G]
    (hcard : Nat.card ↥(⁅S, Subgroup.zpowers b⁆ : Subgroup G) ≤ 2 ^ n * 4 ^ n) :
    blockU Y ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hsq := sq_ne_one m.hn α hαk m.bY m.bo
  have hbN : b ∈ Subgroup.normalizer ((S ⊓ Y : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨m.bS, Subgroup.le_normalizer m.bY⟩
  have hc : Nat.card ↥(⁅S ⊓ Y, Subgroup.zpowers b⁆ : Subgroup G) ≤ 2 ^ n * 4 ^ n :=
    (Subgroup.card_le_of_le (Subgroup.commutator_mono inf_le_left le_rfl)).trans hcard
  have h1 := commutator_blockQ_le (by have := m.hn; omega) hF α hαs hαk m.nat m.bY hsq
    m.b_odd.1 m.b_odd.2 m.syl hbN hc
  exact blockU_le_of_commutator m.hn hF m.perf α hαs hαk m.bY
    (fun h => hsq (by rw [h, one_pow])) m.nat.norm h1

end Mem

theorem blocks_of_mems [Finite G] (hAS : Ch11.SecH.AS_I_1_3_L2)
    {T S X₁ X₂ Y₁ Y₂ V₁ V₂ : Subgroup G} {b : G} {n : ℕ} (m₁ : Mem T S X₁ Y₁ V₁ b n)
    (m₂ : Mem T S X₂ Y₂ V₂ b n) (hs₁ : IsShort2 Y₁)
    (hres₁ : n = 2 → IsShort2 Y₁ → IsLin2Type Y₁ n → blockZ Y₁ = ⊥ →
      blockQ Y₁ ⊓ Subgroup.centralizer (Y₁ : Set G) = ⊥ →
        Nat.card (blockQ Y₁) ≠ 2 * Nat.card (blockU Y₁))
    (hres₂ : n = 2 → IsShort2 Y₂ → IsLin2Type Y₂ n → blockZ Y₂ = ⊥ →
      blockQ Y₂ ⊓ Subgroup.centralizer (Y₂ : Set G) = ⊥ →
        Nat.card (blockQ Y₂) ≠ 2 * Nat.card (blockU Y₂)) :
    IsSylowTwoOf ⁅S, Subgroup.zpowers b⁆ Y₁ ∧ IsSylowTwoOf ⁅S, Subgroup.zpowers b⁆ Y₂ ∧
      (IsShort2 Y₁ ∧ IsLin2Type Y₁ n ∧ blockZ Y₁ = ⊥ ∧ blockQ Y₁ = blockU Y₁) ∧
      (IsShort2 Y₂ ∧ IsLin2Type Y₂ n ∧ blockZ Y₂ = ⊥ ∧ blockQ Y₂ = blockU Y₂) := by
  obtain ⟨hb₁, hQ₁⟩ := m₁.final hAS (m₁.blockU_le_of_short hs₁) hres₁
  obtain ⟨hS₁, hc₁⟩ := m₁.sylow hQ₁
  obtain ⟨hb₂, hQ₂⟩ := m₂.final hAS (m₂.transfer (by rw [hS₁, hc₁])) hres₂
  obtain ⟨hS₂, -⟩ := m₂.sylow hQ₂
  exact ⟨hS₁ ▸ m₁.syl, hS₂ ▸ m₂.syl, hb₁, hb₂⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
