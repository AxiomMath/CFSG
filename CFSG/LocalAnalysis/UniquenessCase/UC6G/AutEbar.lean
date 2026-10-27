module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutKernels
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutInv
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem EL_inf_OL_eq_bot : m.EL ⊓ m.OL = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ^ m.r = 1 := m.isElemAbelian_A.2 x hx.1.1
  have h2 : orderOf x ∣ m.r := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf x ∣ Nat.card m.OL := Subgroup.orderOf_dvd_natCard m.OL hx.2
  have h4 : orderOf x ∣ Nat.gcd m.r (Nat.card m.OL) := Nat.dvd_gcd h2 h3
  rw [m.coprime_card_OL] at h4
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))

theorem card_Ebar (h620 : m.C620) : Nat.card m.Ebar = m.r ^ 2 := by
  have hf : ∀ x ∈ m.EL.subgroupOf m.L, (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L)) x = 1 → x = 1 := by
    intro x hx hx1
    have hxN : x ∈ CFSG.pPrimeCore m.r ↥m.L := (QuotientGroup.eq_one_iff x).1 hx1
    have hxOL : (x : G) ∈ m.OL := (m.mem_OL_iff x).2 hxN
    have hxEL : (x : G) ∈ m.EL := hx
    have : (x : G) ∈ m.EL ⊓ m.OL := ⟨hxEL, hxOL⟩
    rw [m.EL_inf_OL_eq_bot] at this
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hcard := UCK.N588A.card_map_of_injOn (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L))
    (H := m.EL.subgroupOf m.L) hf
  have hEb : m.Ebar = (m.EL.subgroupOf m.L).map (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L)) := by
    ext x
    rw [m.mem_Ebar_iff]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  rw [hEb, hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  exact m.card_A_inf_L h620

theorem isSylowOf_Ebar_map (h620 : m.C620) {S₀ : Type} [Group S₀] [Finite S₀] (φ : m.Lbar ≃* S₀)
    (hS₀ : (Nat.card S₀).factorization m.r = 2) :
    IsSylowOf m.r (m.Ebar.map φ.toMonoidHom) ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine isSylowOf_of_card le_top ?_
  rw [Subgroup.card_map_of_injective φ.injective, m.card_Ebar h620, Subgroup.card_top, hS₀]

theorem kc633_of_model (h620 : m.C620) {S₀ : Type} [Group S₀] [Finite S₀] (φ : m.Lbar ≃* S₀)
    (hS₀ : (Nat.card S₀).factorization m.r = 2) {E₀ : Subgroup S₀} (h₀ : IsSylowOf m.r E₀ ⊤)
    (hK : AbsKC S₀ m.r E₀) : m.KC633 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact m.kc633_of_abs (AbsKC.of_iso_sylow φ h₀ (m.isSylowOf_Ebar_map h620 φ hS₀) hK)

theorem kn633_of_model (h620 : m.C620) {S₀ : Type} [Group S₀] [Finite S₀] (φ : m.Lbar ≃* S₀)
    (hS₀ : (Nat.card S₀).factorization m.r = 2) {E₀ : Subgroup S₀} (h₀ : IsSylowOf m.r E₀ ⊤)
    (hK : AbsKN S₀ m.r E₀ (m.r = 3 ∧ CFSG.Blueprint.LieModel m.Lbar .PSL 3 2 2)) : m.KN633 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact m.kn633_of_abs (AbsKN.of_iso_sylow φ h₀ (m.isSylowOf_Ebar_map h620 φ hS₀) hK)

theorem kinv633_of_model (h620 : m.C620) {S₀ : Type} [Group S₀] [Finite S₀] (φ : m.Lbar ≃* S₀)
    (hS₀ : (Nat.card S₀).factorization m.r = 2) {E₀ : Subgroup S₀} (h₀ : IsSylowOf m.r E₀ ⊤)
    (hK : AbsKInv S₀ E₀) : m.KInv633 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact m.kinv633_of_abs (AbsKInv.of_iso_sylow φ h₀ (m.isSylowOf_Ebar_map h620 φ hS₀) hK)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
