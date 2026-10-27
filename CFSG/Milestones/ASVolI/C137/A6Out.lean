module

public import CFSG.Milestones.ASVolI.C137.A6Mark
public import CFSG.Milestones.ASVolI.C137.Gen
public import CFSG.Milestones.ASVolI.C137.Model

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.B3 CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem burnsideC137_natural_of_realizes {L U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hLU : L ≤ normalizer (U : Set G))
    {π : ↥(alternatingGroup (Fin 6)) →* ↥(autI hU L)}
    (h : (FFModel.altDn 6).RealizesVia (autI hU L) ⊤ (fixV (autI hU L)) π) :
    ∃ _ : IsMulCommutative ↥U, AlternatingNatural (V := ↥U) (autOn L U) ⊤
      ((centralizer (L : Set G)).subgroupOf U) 6 := by
  have hfix : fixV (autI hU L) =
      ((centralizer (L : Set G)).subgroupOf U : Subgroup (IntMod U hU)) := by
    ext w
    rw [mem_fixV_autI hU hLU w]
    rfl
  refine ⟨hU.1, π, ?_⟩
  rw [hfix] at h
  exact h

@[expose] def burnsideC137_Concl5 (X T L P V U : Subgroup G) : Prop :=
  Nonempty (↥(autOn X V) ≃* Equiv.Perm (Fin 6)) ∧
    InternalS6Natural X V U (U ⊓ centralizer (L : Set G)) ∧
    (U ⊓ centralizer (L : Set G)).relIndex U = 2 ^ 4 ∧
    IsIrrSection X (U ⊓ centralizer (L : Set G)) U ∧
    (∃ l : Subgroup G, U ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ U ∧
      (U ⊓ centralizer (L : Set G)).relIndex l = 4 ∧
      autOn P V = autOn (X ⊓ normalizer (l : Set G)) V) ∧
    (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) → ¬ oTwoUpper (oTwoZIn L) ≤ P) ∧
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V)

theorem burnsideC137_card_Dsp : Nat.card burnsideC137_Dsp.Mod = 16 := by
  rw [← Nat.card_congr burnsideC137_d6Sp4.toEquiv, card_modV_ut0]

theorem burnsideC137_concl5_of [Finite G] {X T L P V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXV : X ≤ normalizer (V : Set G)) (hU : IsElemAbelian 2 U) (hUV : U ≤ V)
    (hXU : X ≤ normalizer (U : Set G)) (hXL : X ≤ normalizer (L : Set G)) (hLX : L ≤ X)
    (hTX : T ≤ X) (hC : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G))
    {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (N : KModel k (autI hU L))
    (hXeq : (⊤ : Subgroup (Gp 6)).map N.ρ = autI hU X)
    (hirr : XMod.IsIrrSec ↥(autI hU L) (XMod.fixed ↥(autI hU L) (⊤ : Subgroup (IntMod U hU)))
      (⊤ : Subgroup (IntMod U hU)))
    (hPl : ∀ l : Subgroup G, P ≤ normalizer (l : Set G) → ¬ X ≤ normalizer (l : Set G) →
      autOn P V = autOn (X ⊓ normalizer (l : Set G)) V)
    (hw : (∃ l : Subgroup G, U ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ U ∧
        Nat.card ↥l = 4 * Nat.card ↥(U ⊓ centralizer (L : Set G)) ∧ P ≤ normalizer (l : Set G)) ∧
      (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) → ¬ oTwoUpper (oTwoZIn L) ≤ P) ∧
      ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A U)) :
    burnsideC137_Concl5 X T L P V U := by
  have hLU : L ≤ normalizer (U : Set G) := hLX.trans hXU
  have hXZ : X ≤ normalizer ((U ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXU hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (burnsideC137_mem_normalizer_centralizer (hXL hx)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  obtain ⟨f, hfs, hfk, hfaith, hX, hX'⟩ := burnsideC137_s6Marking hk N hXeq
  have hfk' : ∀ w : IntMod U hU, f w = 1 ↔ w.val ∈ U ⊓ centralizer (L : Set G) := by
    intro w
    rw [hfk, mem_fixV_autI hU hLU w]
    exact ⟨fun h1 => ⟨w.val_mem, h1⟩, fun h1 => h1.2⟩
  have hS6 : Nonempty (↥(autOn X V) ≃* Equiv.Perm (Fin 6)) := by
    have e1 : Equiv.Perm (Fin 6) ≃* ↥(autI hU X) :=
      (MonoidHom.ofInjective N.ρ_inj).trans (MulEquiv.subgroupCongr (by
        rw [← hXeq, MonoidHom.range_eq_map]))
    exact ⟨((burnsideC137_autIEquiv hU hV hXU hXV hC).symm.trans e1.symm)⟩
  have hmem : ∀ x : ↥X, convHom hU X hXU x ∈ autI hU X := fun x => by
    rw [← range_convHom hU X hXU]
    exact ⟨x, rfl⟩
  have hnat : InternalS6Natural X V U (U ⊓ centralizer (L : Set G)) := by
    refine burnsideC137_ims_of_marking burnsideC137_hDsp burnsideC137_hDsp_injective hU
      inf_le_left hUV hXU hXZ hC f hfs hfk' (fun x hx => hfaith _ (hmem x) hx)
      (fun x => hX _ (hmem x)) fun δ => ?_
    obtain ⟨φ, hφ, hφδ⟩ := hX' δ
    rw [← range_convHom hU X hXU] at hφ
    obtain ⟨x, rfl⟩ := hφ
    exact ⟨x, hφδ⟩
  have hidx : (U ⊓ centralizer (L : Set G)).relIndex U = 2 ^ 4 := by
    rw [burnsideC137_relIndex_of_surj hU f hfs hfk', burnsideC137_card_Dsp]
    norm_num
  have hirrX : IsIrrSection X (U ⊓ centralizer (L : Set G)) U :=
    burnsideC137_isIrrSection_of_isIrrSec hU hLX hXU hXL hirr
  obtain ⟨⟨l, hZl, hlU, hcardl, hPl'⟩, hhat, A, hA, hA2⟩ := hw
  have hidxl : (U ⊓ centralizer (L : Set G)).relIndex l = 4 := by
    have h1 := Subgroup.relIndex_mul_card (U ⊓ centralizer (L : Set G)) l
    rw [inf_eq_left.2 hZl, hcardl] at h1
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (L : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hXl : ¬ X ≤ normalizer (l : Set G) := by
    intro hXl
    rcases hirrX.2.2.2 l hZl hlU hXl with h2 | h2
    · rw [← h2, Subgroup.relIndex_self] at hidxl
      omega
    · rw [h2] at hidxl
      rw [hidxl] at hidx
      norm_num at hidx
  have hAV : Nat.card ↥(autOn A V) = Nat.card ↥(autOn A U) := by
    have hAX : A ≤ X := hA.1.trans hTX
    rw [card_autOn_eq_relIndex (hAX.trans hXV), card_autOn_eq_relIndex (hAX.trans hXU)]
    have hAC : A ⊓ centralizer (U : Set G) = A ⊓ centralizer (V : Set G) := by
      have h1 : A ⊓ (X ⊓ centralizer (U : Set G)) = A ⊓ (X ⊓ centralizer (V : Set G)) := by
        rw [hC]
      rwa [← inf_assoc, inf_eq_left.2 hAX, ← inf_assoc, inf_eq_left.2 hAX] at h1
    rw [hAC]
  exact ⟨hS6, hnat, hidx, hirrX, ⟨l, hZl, hlU, hidxl, hPl l hPl' hXl⟩, hhat, A, hA,
    hAV ▸ hA2⟩

end CFSG.ASVolI
