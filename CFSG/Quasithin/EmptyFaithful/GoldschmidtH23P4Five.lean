module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Glue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4TitsInst
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Fin

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure FiveData (L S Y V : Subgroup G) : Prop where
  s2 : IsPGroup 2 S
  syl : IsSylowTwoOf (S ⊓ L) L
  y5 : IsPGroup 5 Y
  yN : Y ≤ Subgroup.normalizer (L : Set G)
  sy : (S : Set G) * Y = Y * S
  vN : V ≤ Subgroup.normalizer (L : Set G)
  lv : ⁅L, V⁆ ≠ ⊥
  vy : ⁅V, Y⁆ = V

namespace FiveData

variable [Finite G] {L S Y V : Subgroup G} (h : FiveData L S Y V)
include h

theorem le_cMod (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) : Y ≤ SBc17.cMod L :=
  le_cMod_of_rowOK h.s2 h.syl h.y5 h.yN h.sy hrow

omit [Finite G] in
theorem false_of_comm (hLY : ⁅L, Y⁆ = ⊥) : False :=
  false_of_comm_eq_bot h.vN h.lv h.vy hLY

theorem false_of_component (hq : CFSG.IsQuasisimple ↥L)
    (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) : False :=
  h.false_of_comm (comm_eq_bot_of_component hq (h.le_cMod hrow))

theorem false_of_block (hL : IsShort2 L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) {d : ℕ}
    (hd : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ d) (hd' : d = 3 ∨ d = 4 ∨ d = 6) :
    False :=
  h.false_of_comm (comm_eq_bot_of_block hL hq hd hd' h.y5 h.yN (h.le_cMod hrow))

theorem false_of_tits (hq : CFSG.IsQuasisimple ↥L) (hrow : RowTits ↥L) (hVS : V ≤ S)
    (hVSn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V) (hVYn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hVc : Nat.card V ≤ 16) : False := by
  have hQ : pCoreOf 2 L = ⊥ := by
    rw [← SBc13.map_pCore_eq_pCoreOf_J1, pCore_eq_bot_of_quasisimple hq hrow.center,
      Subgroup.map_bot]
  exact false_of_rowTits h.s2 h.syl h.y5 h.yN h.sy hQ h.vN hVS hVSn hVYn hVc h.vy h.lv
    (RowTits.quot_pCore hq hrow)

end FiveData

theorem index_eq_card_of_ker {A B : Type*} [Group A] [Group B] (β : A →* B)
    (hβ : Function.Surjective β) {K : Subgroup A} (hK : β.ker = K) : K.index = Nat.card B := by
  rw [← hK, Subgroup.index_ker, MonoidHom.range_eq_top.2 hβ, Subgroup.card_top]

theorem index_altBlock {L : Subgroup G} {m : ℕ} {α : ↥L →* ↥(alternatingGroup (Fin m))}
    (h : IsAltBlockTypeWith L m α) :
    ((blockZ L).subgroupOf (blockU L)).index = Nat.card (AltHeart m) := by
  obtain ⟨-, -, β, hβs, hβk, -⟩ := h
  rw [index_eq_card_of_ker β hβs hβk]
  exact Nat.card_congr Multiplicative.toAdd

theorem index_matrixBlock {L : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {H : Subgroup (Matrix.GeneralLinearGroup ι F)} (h : IsMatrixBlockType L H) :
    ((blockZ L).subgroupOf (blockU L)).index = Nat.card (ι → F) := by
  obtain ⟨α, -, -, β, hβs, hβk, -⟩ := h
  rw [index_eq_card_of_ker β hβs hβk]
  exact Nat.card_congr Multiplicative.toAdd

end CFSG.Quasithin.H23P4
