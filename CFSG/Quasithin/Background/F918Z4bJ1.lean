module

public import CFSG.Quasithin.Background.F918Z4bDef
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)

theorem rk_le_rk_of_forall_inner {L : Type*} [Group L] [Finite L]
    (hin : ∀ α : MulAut L, ∃ g : L, α = MulAut.conj g) (E : Subgroup (MulAut L)) :
    rk E ≤ rk L := by
  have hE : E ≤ (MulAut.conj : L →* MulAut L).range := fun α _ => by
    obtain ⟨g, rfl⟩ := hin α
    exact ⟨g, rfl⟩
  exact (rk_mono hE).trans
    (padicValNat_two_le_of_dvd Nat.card_pos.ne' (Subgroup.card_range_dvd _))

theorem forall_inner_of_isSporadic_j1
    {L : Type} [Group L] (h : IsSporadic .J1 L) :
    ∀ α : MulAut L, ∃ g : L, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  let e' : L ≃* NativeSporadic.J1 := e
  intro α
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 (MulAut.congr e' α)
  refine ⟨e'.symm g, (MulAut.congr e').injective ?_⟩
  rw [hg, congr_conj, e'.apply_symm_apply]

theorem autRankLe_j1
    {L : Type} [Group L] [Finite L] (h : IsSporadic .J1 L) : AutRankLe L 3 := by
  intro E _
  have hrk : rk L = 3 := by
    obtain ⟨e⟩ := h
    let e' : L ≃* NativeSporadic.J1 := e
    unfold rk
    rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.J1.card_J1]
    have h8 : (175560 : ℕ) = 2 ^ 3 * 21945 := by norm_num
    rw [h8, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  exact (rk_le_rk_of_forall_inner (forall_inner_of_isSporadic_j1 h) E).trans hrk.le

end CFSG.Quasithin
