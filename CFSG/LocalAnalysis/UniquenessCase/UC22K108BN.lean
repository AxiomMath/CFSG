module

public import CFSG.Open.SplitBNPair
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Quasithin.Vol2.Ch11SecC37N1
public import CFSG.Assembly.QuasithinDefs
import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.InternalSecData
import CFSG.Quasithin.Background.InternalSecIso
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ASVolI.ChIJK
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

variable {S : Type} [Group S] [Finite S]

theorem uc22k108bn_normalizer_eq {p : ℕ} (hp : p.Prime) {B N U : Subgroup S}
    (hBN : IsSplitBNPair p B N) (hUB : U ≤ B) (hUn : (U.subgroupOf B).Normal)
    (hUp : IsPGroup p U) (hUi : ¬ p ∣ U.index) : normalizer (U : Set S) = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U₀, hU₀⟩ := hBN.exists_sylow_normalizer hp
  have hBU : B ≤ normalizer (U : Set S) := (normal_subgroupOf_iff_le_normalizer hUB).1 hUn
  have h₀ : (U₀ : Subgroup S) ≤ normalizer (U : Set S) :=
    (Subgroup.le_normalizer.trans hU₀.le).trans hBU
  have hsup : (U₀ : Subgroup S) ⊔ U = U₀ :=
    U₀.is_maximal' (U₀.isPGroup'.to_sup_of_normal_right' hUp h₀) le_sup_left
  have hU : (U₀ : Subgroup S) = U :=
    (hUp.toSylow hUi).is_maximal' U₀.isPGroup' (le_sup_right.trans hsup.le)
  rw [← hU]
  exact hU₀

theorem uc22k108bn_exists_cartan {B N : Subgroup S} (hBN : IsSplitBNPair 2 B N) {T X : Subgroup S}
    (hT : IsSylowTwoOf T ⊤) (hXT : X ≤ normalizer (T : Set S)) (hX : Odd (Nat.card X)) :
    ∃ H' : Subgroup S, X ≤ H' ∧ H' ≤ normalizer (T : Set S) ∧ Odd (Nat.card H') ∧
      T ⊔ normalizer (H' : Set S) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUB, hUn, hUp, hUi, hUN, hUH, -⟩ := hBN.split
  set H : Subgroup S := B ⊓ N with hHdef
  have hNU : normalizer (U : Set S) = B :=
    uc22k108bn_normalizer_eq Nat.prime_two hBN hUB hUn hUp hUi
  have hHB : H ≤ B := inf_le_left
  have hcard : Nat.card U * Nat.card H = Nat.card B := by
    have htop : U.subgroupOf B ⊔ H.subgroupOf B = ⊤ := by
      rw [← subgroupOf_sup hUB hHB, hUH, subgroupOf_self]
    have hdisj : Disjoint (U.subgroupOf B) (H.subgroupOf B) := by
      rw [Subgroup.disjoint_def]
      intro x hxU hxH
      have h1 : (x : S) ∈ U ⊓ N := ⟨hxU, (mem_subgroupOf.1 hxH).2⟩
      rw [hUN, mem_bot] at h1
      exact Subtype.ext h1
    have hmul : (U.subgroupOf B : Set B) * (H.subgroupOf B : Set B) = Set.univ := by
      rw [← normal_mul, htop, coe_top]
    have hc := (isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul).card_mul_card
    rwa [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hHB).toEquiv] at hc
  obtain ⟨a, ha⟩ := hUp.exists_card_eq
  have hHidx : H.relIndex B = 2 ^ a := by
    have h1 := relIndex_mul_card H B
    rw [inf_eq_left.2 hHB, ← hcard, ha] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hHodd : Odd (Nat.card H) := by
    have h1 := relIndex_mul_card U B
    rw [inf_eq_left.2 hUB, ← hcard, mul_comm (Nat.card U)] at h1
    have h2 : U.relIndex B = Nat.card H := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h3 : ¬ 2 ∣ U.relIndex B := fun h => hUi (h.trans (relIndex_dvd_index_of_le hUB))
    rw [h2] at h3
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h3)
  have hUsyl : IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, hUp, ?_⟩
    change ¬ 2 ∣ U.relIndex ⊤
    rwa [relIndex_top_right]
  obtain ⟨c, -, rfl⟩ := hUsyl.exists_conj hT
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hNT : normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S) : Set S) =
      B.map (MulAut.conj c).toMonoidHom := by
    rw [← map_equiv_normalizer_eq U (MulAut.conj c), hNU]
  have hTN : IsSylowTwoOf (U.map (MulAut.conj c).toMonoidHom)
      (normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S) : Set S)) := by
    refine ⟨Subgroup.le_normalizer, hT.2.1, ?_⟩
    change ¬ 2 ∣ (U.map (MulAut.conj c).toMonoidHom).relIndex _
    intro h
    apply hT.2.2
    change 2 ∣ (U.map (MulAut.conj c).toMonoidHom).relIndex ⊤
    rw [relIndex_top_right]
    exact h.trans (relIndex_dvd_index_of_le Subgroup.le_normalizer)
  have hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf (H.map (MulAut.conj c).toMonoidHom)
      (normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S) : Set S)) := by
    rw [hNT]
    refine ⟨map_mono hHB, ?_, a, ?_⟩
    · rwa [card_map_of_injective hinj]
    · rw [relIndex_map_map_of_injective _ _ hinj, hHidx]
  obtain ⟨t, htT, hXt⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecC.exists_conj_le_of_normal_sylow hTN le_rfl hD hXT hX
  have hcomp : ∀ A : Subgroup S, (A.map (MulAut.conj c).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      A.map (MulAut.conj (t * c)).toMonoidHom := by
    intro A
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hTg : U.map (MulAut.conj (t * c)).toMonoidHom = U.map (MulAut.conj c).toMonoidHom := by
    rw [← hcomp]
    exact mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer htT)
  have hXH : X ≤ H.map (MulAut.conj (t * c)).toMonoidHom := by
    rw [← hcomp]
    exact hXt
  have hHN : H.map (MulAut.conj (t * c)).toMonoidHom ≤
      normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S) : Set S) := by
    rw [← hcomp]
    refine (map_mono hD.1).trans (le_of_eq ?_)
    exact mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (Subgroup.le_normalizer htT))
  have hNH : N ≤ normalizer (H : Set S) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).1 hBN.normal_inter
  refine ⟨_, hXH, hHN, ?_, ?_⟩
  · rwa [card_map_of_injective (MulAut.conj (t * c)).injective]
  rw [eq_top_iff]
  intro x _
  have hy : (t * c)⁻¹ * x * (t * c) ∈ U ⊔ H ⊔ N := by
    rw [hUH, hBN.gen]
    exact mem_top _
  have hx : x ∈ (U ⊔ H ⊔ N).map (MulAut.conj (t * c)).toMonoidHom :=
    ⟨_, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [Subgroup.map_sup, Subgroup.map_sup, hTg] at hx
  refine sup_le (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)) ?_ hx
  rw [← map_equiv_normalizer_eq H (MulAut.conj (t * c))]
  exact (map_mono hNH).trans le_sup_right

end CFSG.LocalAnalysis.UniquenessCase.UC22
