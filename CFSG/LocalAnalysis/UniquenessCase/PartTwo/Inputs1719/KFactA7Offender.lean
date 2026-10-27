module

public import CFSG.GroupTheory.AltSevenModule.Offender
public import CFSG.Quasithin.Background.SmithC27Perm2
import CFSG.Quasithin.Background.G6PGroup
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin

variable {U : Type} [CommGroup U] [Finite U]

theorem a7_offender (hU2 : ∀ u : U, u ^ 2 = 1) (hUcard : Nat.card U = 2 ^ 4)
    {H : Subgroup (MulAut U)} (hH : IsAlt 7 ↥H) {E : Subgroup (MulAut U)} (hEH : E ≤ H)
    (hE : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hoff : Nat.card U ≤ Nat.card E * Nat.card (fixV E)) :
    Nat.card E = 4 ∧ Nat.card (Subgroup.normalizer (E.subgroupOf H : Set H)) = 72 := by
  classical
  have hU16 : Nat.card U = 16 := by rw [hUcard]; norm_num
  obtain ⟨eH⟩ := hH
  let φ : ↥(alternatingGroup (Fin 7)) ≃* ↥H := eH.symm
  let ρ : ↥(alternatingGroup (Fin 7)) →* MulAut U := H.subtype.comp φ.toMonoidHom
  have hρ : Function.Injective ρ := fun a b hab => φ.injective (Subtype.ext hab)
  have hrange : ρ.range = H := by
    rw [show ρ = H.subtype.comp φ.toMonoidHom from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr φ.surjective, ← Subgroup.subgroupOf_self H,
      Subgroup.map_subgroupOf_eq_of_le le_rfl]
  have hHcard : Nat.card ↥H = 2520 := by
    rw [← Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hirr := CFSG.GroupTheory.AltSevenModule.isIrrSec_of_card_sixteen hU16 φ
  have hcommV_ne_bot : commV H ≠ ⊥ := by
    intro hbot
    have hfix : (⊤ : Subgroup U) ≤ fixV H := by
      rw [← commSub_eq_bot_iff, ← commV_eq_commSub]
      exact hbot
    have hHbot : H = ⊥ := by
      rw [eq_bot_iff]
      intro h hh
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro u
      exact mem_fixV.mp (hfix (Subgroup.mem_top u)) h hh
    have h1 : Nat.card ↥H = 1 := by rw [hHbot, Subgroup.card_bot]
    omega
  have hcommV_inv : XMod.IsInv ↥H (commV H) := by
    intro h w hw
    show (h : MulAut U) w ∈ commV H
    exact G6.apply_mem_commV (X := H)
      (fun x hx => H.mul_mem (H.mul_mem h.2 hx) (H.inv_mem h.2)) hw
  have hcommV_top : commV H = ⊤ := by
    rcases hirr.2 (commV H) hcommV_inv bot_le le_top with h | h
    · exact absurd h hcommV_ne_bot
    · exact h
  have hcommV16 : Nat.card (commV ρ.range) = 16 := by
    rw [hrange, hcommV_top, Subgroup.card_top, hU16]
  let A : Subgroup ↥(alternatingGroup (Fin 7)) := (E.subgroupOf H).comap φ.toMonoidHom
  have hmapA : A.map φ.toMonoidHom = E.subgroupOf H :=
    Subgroup.map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr φ.surjective]
      exact le_top)
  have hmapρ : A.map ρ = E := by
    rw [show ρ = H.subtype.comp φ.toMonoidHom from rfl, ← Subgroup.map_map, hmapA,
      Subgroup.map_subgroupOf_eq_of_le hEH]
  have hcardA_E : Nat.card A = Nat.card E := by
    have h1 : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective φ.injective
    rw [hmapA] at h1
    have h2 : Nat.card (E.subgroupOf H) = Nat.card E := by
      rw [← Subgroup.card_subtype H (E.subgroupOf H),
        Subgroup.map_subgroupOf_eq_of_le hEH]
    rw [← h1, h2]
  have hA1 : A ≠ ⊥ := by
    intro hA0
    have hEsub : E.subgroupOf H = ⊥ := by
      rw [← hmapA, hA0, Subgroup.map_bot]
    have hEbot : E = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hEH, hEsub, Subgroup.map_bot]
    exact hE1 hEbot
  have hAel : IsElemAbelian 2 A := (hE.subgroupOf H).comap φ.injective
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hAel.2 a ha
  have hoffA : Nat.card U ≤ Nat.card A * Nat.card (fixV (A.map ρ)) := by
    rw [hmapρ, hcardA_E]
    exact hoff
  obtain ⟨c, hc, hle⟩ :=
    CFSG.GroupTheory.AltSevenModule.exists_conj_kleinRegular7_le hU2 ρ hρ hcommV16 hA1 hA2 hoffA
  let K : Subgroup (Equiv.Perm (Fin 7)) := CFSG.Quasithin.kleinRegular7
  let f : Equiv.Perm (Fin 7) ≃* Equiv.Perm (Fin 7) := MulAut.conj c
  let Kc : Subgroup (Equiv.Perm (Fin 7)) := K.map f.toMonoidHom
  have hKcard : Nat.card K = 4 := by
    simpa [K, CFSG.Quasithin.kleinRegular7, CFSG.QuasithinUnique.B42A57.V0]
      using CFSG.QuasithinUnique.B42A57.card_V0
  have hKc_card : Nat.card Kc = 4 := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hKcard
  have hK_le_A7 : K ≤ alternatingGroup (Fin 7) := by
    change CFSG.Quasithin.kleinRegular7 ≤ alternatingGroup (Fin 7)
    unfold CFSG.Quasithin.kleinRegular7
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
    · exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hKc_le_A7 : Kc ≤ alternatingGroup (Fin 7) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [f, MulAut.conj_apply] using
      (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem k (hK_le_A7 hk) c
  have hKc_sub_le_A : Kc.subgroupOf (alternatingGroup (Fin 7)) ≤ A := by
    intro y hy
    have hyK : (y : Equiv.Perm (Fin 7)) ∈ Kc := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp (hle hyK)
    have : a = y := Subtype.ext hay
    rwa [← this]
  have hKc_sub_card : Nat.card (Kc.subgroupOf (alternatingGroup (Fin 7))) = 4 := by
    rw [← Subgroup.card_subtype (alternatingGroup (Fin 7))
      (Kc.subgroupOf (alternatingGroup (Fin 7))), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKc_le_A7, hKc_card]
  have hA_le_four : Nat.card A ≤ 4 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAel.isPGroup
    have hk2 : k ≤ 2 := by
      have h1 := CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (H := ⊤) (E := A)
        le_top hAel hk
      exact h1.trans CFSG.GH74.SmallRanks.twoRank_alternatingGroup_seven_le_two
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hcardA : Nat.card A = 4 := by
    have h4le : 4 ≤ Nat.card A := by
      rw [← hKc_sub_card]
      exact Subgroup.card_le_of_le hKc_sub_le_A
    omega
  have hA_eq : A = Kc.subgroupOf (alternatingGroup (Fin 7)) := by
    refine (Subgroup.eq_of_le_of_card_ge hKc_sub_le_A ?_).symm
    rw [hcardA, hKc_sub_card]
  have hnorm_A7 : Nat.card (Subgroup.normalizer (A : Set ↥(alternatingGroup (Fin 7)))) = 72 := by
    rw [hA_eq, ← Subgroup.subgroupOf_normalizer_eq hKc_le_A7]
    set N : Subgroup (Equiv.Perm (Fin 7)) :=
      Subgroup.normalizer (Kc : Set (Equiv.Perm (Fin 7))) with hNdef
    set M : Subgroup (Equiv.Perm (Fin 7)) :=
      Subgroup.normalizer (K : Set (Equiv.Perm (Fin 7))) with hMdef
    have hN : N = M.map f.toMonoidHom := by
      simpa [N, M, Kc] using (Subgroup.map_equiv_normalizer_eq K f).symm
    have hA7map : (alternatingGroup (Fin 7)).map f.toMonoidHom = alternatingGroup (Fin 7) := by
      simpa [f] using (Subgroup.Normal.map_conj_eq (H := alternatingGroup (Fin 7)) c)
    have hinf : N ⊓ alternatingGroup (Fin 7) =
        (M ⊓ alternatingGroup (Fin 7)).map f.toMonoidHom := by
      calc N ⊓ alternatingGroup (Fin 7)
          = (M.map f.toMonoidHom) ⊓
              ((alternatingGroup (Fin 7)).map f.toMonoidHom) := by rw [hN, hA7map]
        _ = (M ⊓ alternatingGroup (Fin 7)).map f.toMonoidHom :=
              (Subgroup.map_inf M (alternatingGroup (Fin 7)) f.toMonoidHom f.injective).symm
    have hquad : alternatingGroup (Fin 7) ⊓ M =
        CFSG.Quasithin.SmithC27.quadStab 7 := by
      simpa [M, K] using CFSG.Quasithin.SmithC27.alt_inf_normalizer_kleinRegular7
    have hmapNsub : (N.subgroupOf (alternatingGroup (Fin 7))).map
        (alternatingGroup (Fin 7)).subtype = N ⊓ alternatingGroup (Fin 7) :=
      Subgroup.subgroupOf_map_subtype N (alternatingGroup (Fin 7))
    have hcardNsub : Nat.card ↥(N.subgroupOf (alternatingGroup (Fin 7))) =
        Nat.card ↥(N ⊓ alternatingGroup (Fin 7)) := by
      rw [← Subgroup.card_subtype (alternatingGroup (Fin 7))
        (N.subgroupOf (alternatingGroup (Fin 7))), hmapNsub]
    have hcardmap : Nat.card ↥((M ⊓ alternatingGroup (Fin 7)).map f.toMonoidHom) =
        Nat.card ↥(M ⊓ alternatingGroup (Fin 7)) :=
      Subgroup.card_map_of_injective f.injective
    rw [hcardNsub, hinf, hcardmap, inf_comm, hquad]
    exact CFSG.Quasithin.SmithC27.card_quadStab_seven
  have hnorm_H : Nat.card (Subgroup.normalizer (E.subgroupOf H : Set H)) = 72 := by
    have hmapN : (Subgroup.normalizer (A : Set ↥(alternatingGroup (Fin 7)))).map
        φ.toMonoidHom = Subgroup.normalizer (E.subgroupOf H : Set H) := by
      rw [Subgroup.map_equiv_normalizer_eq A φ, hmapA]
    rw [← hmapN, Subgroup.card_map_of_injective φ.injective]
    exact hnorm_A7
  have hEcard : Nat.card E = 4 := by rw [← hcardA_E, hcardA]
  exact ⟨hEcard, hnorm_H⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
