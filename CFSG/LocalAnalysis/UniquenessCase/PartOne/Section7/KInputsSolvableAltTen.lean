module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSect
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BlockStabPerfect
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BlockStabSections
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTen
import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding.KFactProofs.SmallIdent
open CFSG.AGLEmbedding.A15Local.Sect (SectionsOrder60)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open Equiv

theorem altTen_alternative {X : Type} [Group X] [Finite X] {K N : Subgroup X} [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) (e : ↥K ≃* alternatingGroup (Fin 10))
    (T : Sylow 5 ↥K) (hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K)
    (hne : N.subgroupOf K ≠ ⊤) :
    (Nat.card N).factorization 5 ≤ 2 ∧
      (∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600) ∧
      ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → SectionsOrder60 ↥Y := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKcard : Nat.card ↥K = 1814400 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hout : Nat.card (Outer ↥K) ∣ 2 :=
    outer_card_dvd_two_of_equiv_outside_six (n := 10) (by omega) e
  have hQle : Nat.card (X ⧸ K) ≤ Nat.card (Outer ↥K) :=
    CFSG.RankThree.PartOne.CTP.card_quotient_le_outer K hKC
  have hQpos : 0 < Nat.card (X ⧸ K) := Nat.card_pos
  have hQdvd : Nat.card (X ⧸ K) ∣ 2 := by
    have h1 : Nat.card (X ⧸ K) ≤ 2 :=
      hQle.trans (Nat.le_of_dvd (by norm_num) hout)
    have h2 : Nat.card (X ⧸ K) = 1 ∨ Nat.card (X ⧸ K) = 2 := by omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> norm_num
  have hX : Nat.card X ∣ 3628800 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hKcard]
    have h := Nat.mul_dvd_mul_right hQdvd 1814400
    rwa [show 2 * 1814400 = 3628800 by norm_num] at h
  have hN : Nat.card N ∣ 3628800 :=
    (Subgroup.card_subgroup_dvd_card N).trans hX
  have hfac : (Nat.card N).factorization 5 ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ (Nat.card N).factorization 5 := by omega
    have h53 : 5 ^ 3 ∣ Nat.card N :=
      (Nat.prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h3
    exact (by norm_num : ¬ 5 ^ 3 ∣ 3628800) (h53.trans hN)
  suffices hYs : ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y →
      Nat.card Y ≤ 3600 ∧ SectionsOrder60 ↥Y from
    ⟨hfac, fun Y hYN hY => (hYs Y hYN hY).1, fun Y hYN hY => (hYs Y hYN hY).2⟩
  intro Y hYN hY
  have hYK : Y ≤ K := by
    let π : X →* X ⧸ K := QuotientGroup.mk' K
    have hord : ∀ g : X ⧸ K, orderOf g ∣ 2 := fun g =>
      (orderOf_dvd_natCard g).trans hQdvd
    have hQcomm : ⁅(⊤ : Subgroup (X ⧸ K)), ⊤⁆ = ⊥ :=
      le_bot_iff.1 (Subgroup.commutator_le.2 fun a _ b _ => by
        rw [Subgroup.mem_bot]
        exact (Commute.of_orderOf_dvd_two hord a b).commutator_eq)
    have hperfect : Subgroup.map π Y = ⁅Subgroup.map π Y, Subgroup.map π Y⁆ := by
      rw [← Subgroup.map_commutator, hY]
    have hle_bot : Subgroup.map π Y ≤ ⁅(⊤ : Subgroup (X ⧸ K)), ⊤⁆ :=
      hperfect.le.trans (Subgroup.commutator_mono le_top le_top)
    rw [hQcomm] at hle_bot
    have hbot : Subgroup.map π Y = ⊥ := le_bot_iff.1 hle_bot
    have hle_ker := (Subgroup.map_eq_bot_iff (f := π) Y).1 hbot
    rwa [QuotientGroup.ker_mk'] at hle_ker
  let W : Subgroup (alternatingGroup (Fin 10)) := (N.subgroupOf K).map e.toMonoidHom
  have hWne : W ≠ ⊤ := by
    intro hW
    apply hne
    have htop : Subgroup.map e.toMonoidHom (⊤ : Subgroup ↥K) = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact e.surjective
    have hW' : Subgroup.map e.toMonoidHom (N.subgroupOf K) = ⊤ := hW
    have h' : Subgroup.map e.toMonoidHom (N.subgroupOf K) =
        Subgroup.map e.toMonoidHom (⊤ : Subgroup ↥K) := by rw [hW', htop]
    exact Subgroup.map_injective e.injective h'
  let S : Sylow 5 (alternatingGroup (Fin 10)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  have hScoe : (S : Subgroup (alternatingGroup (Fin 10))) =
      (T : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  have hNW : Subgroup.normalizer
      ((S : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) ≤ W := by
    rw [hScoe, ← Subgroup.map_equiv_normalizer_eq (T : Subgroup ↥K) e]
    exact Subgroup.map_mono hle
  obtain ⟨B, hBcard, -, -, hBover⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.kFactAltTenOvergroup_holds S
  let f : ↥Y →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp
      (e.toMonoidHom.comp ((Y.subgroupOf K).subtype.comp
        (Subgroup.subgroupOfEquivOfLe hYK).symm.toMonoidHom))
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : e (((Subgroup.subgroupOfEquivOfLe hYK).symm a : ↥(Y.subgroupOf K)) : ↥K) =
        e (((Subgroup.subgroupOfEquivOfLe hYK).symm b : ↥(Y.subgroupOf K)) : ↥K) := by
      apply Subtype.ext
      simpa [f] using hab
    have h3 : ((Subgroup.subgroupOfEquivOfLe hYK).symm a : ↥(Y.subgroupOf K)) =
        ((Subgroup.subgroupOfEquivOfLe hYK).symm b : ↥(Y.subgroupOf K)) :=
      Subtype.val_injective (e.injective h1)
    exact (Subgroup.subgroupOfEquivOfLe hYK).symm.injective h3
  let V : Subgroup (Perm (Fin 10)) := Subgroup.map f (⊤ : Subgroup ↥Y)
  have hYtop : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = (⊤ : Subgroup ↥Y) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Y)
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hY]
  have hVcard : Nat.card ↥V = Nat.card ↥Y :=
    (Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥Y)) hfinj).trans Subgroup.card_top
  have hVperf : ⁅V, V⁆ = V := by
    show ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆ = Subgroup.map f ⊤
    rw [← Subgroup.map_commutator, hYtop]
  have hpresV : ∀ y ∈ V, (∀ i ∈ B, y i ∈ B) ∨ ∀ i ∈ B, y i ∉ B := by
    intro y hy
    obtain ⟨y0, -, rfl⟩ := Subgroup.mem_map.1 hy
    have hyK : (y0 : X) ∈ K := hYK y0.2
    have hmemW : e ⟨(y0 : X), hyK⟩ ∈ W := by
      refine Subgroup.mem_map.2 ⟨⟨(y0 : X), hyK⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hYN y0.2
    have h := hBover W hNW hWne (e ⟨(y0 : X), hyK⟩) hmemW
    have hcoe : ((Subgroup.subgroupOfEquivOfLe hYK).symm y0 : ↥K) = ⟨(y0 : X), hyK⟩ :=
      Subtype.ext rfl
    simpa [f, hcoe] using h
  refine ⟨?_, (sectionsOrder60_of_perfect_of_preserves hBcard (by simp [hBcard]) hVperf
    hpresV).of_injective
      (Subgroup.topEquiv.symm.trans (Subgroup.equivMapOfInjective ⊤ f hfinj)).toMonoidHom
      (MulEquiv.injective _)⟩
  have hVle : Nat.card V ≤ 3600 :=
    card_le_of_perfect_of_preserves hBcard hVperf hpresV
  rw [← hVcard]
  exact hVle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
