module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Props
public import CFSG.Quasithin.H13.VolIC113d1
public import CFSG.Quasithin.Vol2.Ch4Sec3C64Coord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZero
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace Gold14610

variable {G : Type} [Group G]

theorem wOf1469_eq_blockU [Finite G] {K : Subgroup G} (hK : IsShort2 K) :
    wOf1469 K = blockU K := by
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hK.2.2.1.1
  apply le_antisymm
  · have hA : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 K :=
      (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
    exact Subgroup.commutator_mono hA le_rfl
  · have hUA : blockU K ≤ omegaOneCenterOf (pCoreOf 2 K) := fun x hx =>
      Subgroup.subset_closure ⟨hUQ hx, hK.2.2.1.2 x hx⟩
    calc blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU hK).symm
      _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆ := Subgroup.commutator_mono hUA le_rfl

variable [Finite G]

theorem card_blockU_alt6 {K : Subgroup G} (hA : IsAltBlockType K 6) :
    Nat.card (blockU K) = 2 ^ 4 ∨ Nat.card (blockU K) = 2 ^ 5 := by
  obtain ⟨hsh, α, hα⟩ := hA
  have : IsMulCommutative ↥(blockU K) := VolI.isMulCommutative_blockU hsh
  have h1 := (VolI.Cover6.ofBlock hsh α hα).card_eq
  have h2 := (VolI.Cover6.ofBlock hsh α hα).card_Z_le
  have h3 : 0 < Nat.card (VolI.Cover6.ofBlock hsh α hα).Z := Nat.card_pos
  generalize Nat.card (VolI.Cover6.ofBlock hsh α hα).Z = z at h1 h2 h3
  omega

theorem card_evenWeight_seven : Nat.card ↥(evenWeight 7) = 2 ^ 6 := by
  have h1 : Nat.card ↥(G6.coreMod 7) = Nat.card (Multiplicative ↥(evenWeight 7)) :=
    Nat.card_congr (L246.coreEquiv 7).toEquiv
  have h2 : Nat.card ↥(G6.coreMod 7) = 2 ^ 6 := by rw [VolI.card_coreMod_seven]; norm_num
  have h3 : Nat.card (Multiplicative ↥(evenWeight 7)) = Nat.card ↥(evenWeight 7) :=
    Nat.card_congr Multiplicative.toAdd
  omega

theorem card_blockU_alt7 {K : Subgroup G} (hA : IsAltBlockType K 7) :
    Nat.card (blockU K) = 2 ^ 6 := by
  obtain ⟨hsh, α, hsurj, hker, β, hβs, hβk, hβe⟩ := hA
  have hb : Ch4.C64.A7Blk K α β := ⟨hsh, hsurj, hker, hβs, hβk, hβe⟩
  have hZ : blockZ K = ⊥ := hb.blockZ_eq_bot
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h : u ∈ β.ker := hu
    rwa [hβk, hZ, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩),
    Nat.card_congr Multiplicative.toAdd, ← Nat.card_congr Ch4.C64.heartEquiv.toEquiv,
    card_evenWeight_seven]

theorem card_blockU_exc {K : Subgroup G} (hE : IsExcA7Block K) :
    Nat.card (blockU K) = 2 ^ 4 := by
  have hZ : blockZ K = ⊥ := L246.C123.blockZ_eq_bot_of_isExcA7Block hE
  obtain ⟨-, -, hidx⟩ := hE
  have h := ((blockZ K).subgroupOf (blockU K)).index_mul_card
  rw [hidx, hZ, Subgroup.bot_subgroupOf, Subgroup.card_bot] at h
  omega

end Gold14610

theorem gold14610BlockOrders_holds :
    Gold14610.Gold14610BlockOrders := by
  intro G _ _ K
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [Gold14610.wOf1469_eq_blockU h.1]
    exact Gold14610.card_blockU_alt6 h
  · rw [Gold14610.wOf1469_eq_blockU h.1]
    exact Gold14610.card_blockU_alt7 h
  · rw [Gold14610.wOf1469_eq_blockU h.1]
    exact Gold14610.card_blockU_exc h

end CFSG.Quasithin
