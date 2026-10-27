module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251L
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.Adapters.Certificate43Check
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem inner_or_commute_orderOf_three {Γ : Type} [Group Γ] [Finite Γ] {X : Subgroup Γ} {n : ℕ}
    (hX : IsL2 ↥X n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {b : Γ}
    (hb : b ∈ normalizer (X : Set Γ)) (hbr : b ^ r = 1) :
    (∃ y ∈ X, orderOf y = r ∧ ∀ x ∈ X, b * x * b⁻¹ = y * x * y⁻¹) ∨
      ∃ x ∈ X, orderOf x = 3 ∧ Commute b x := by
  haveI : Fact r.Prime := ⟨hr⟩
  set z : MulAut ↥X := X.normalizerMonoidHom ⟨b, hb⟩ with hz
  have hza : ∀ a : ↥X, ((z a : ↥X) : Γ) = b * a * b⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨b, hb⟩ a
  have hzr : z ^ r = 1 := by
    have h1 : (⟨b, hb⟩ : ↥(normalizer (X : Set Γ))) ^ r = 1 := Subtype.ext (by simpa using hbr)
    rw [hz, ← map_pow, h1, map_one]
  have hEv := (P22fin.isL2Ev_of_isL2 hX).1
  by_cases hz1 : z = 1
  · right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (three_dvd_card_of_isL2 hX)
    refine ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx, ?_⟩
    have h := hza x
    rw [hz1, MulAut.one_apply] at h
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [← h]
  have hzo : orderOf z = r := orderOf_eq_prime hzr hz1
  by_cases hzi : z ∈ (MulAut.conj : ↥X →* MulAut ↥X).range
  · left
    obtain ⟨y, hy⟩ := hzi
    have hinj := P22y.conj_injective_of_center_eq_bot (P22y.center_eq_bot_of_isL2Ev hEv)
    have hyo : orderOf y = r := by rw [← orderOf_injective _ hinj y, hy, hzo]
    refine ⟨y, y.2, (Subgroup.orderOf_coe y).trans hyo, fun x hx => ?_⟩
    have h1 := hza ⟨x, hx⟩
    rw [← hy] at h1
    simpa [MulAut.conj_apply] using h1.symm
  · right
    obtain ⟨x, hx3, hzx⟩ := P2251L.exists_fixed_orderOf_three hEv hr hr2 z hzo hzi
    refine ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx3, ?_⟩
    have h := hza x
    rw [hzx] at h
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [← h]

theorem dvd_or_commute_orderOf_three_pair {M K : Subgroup G} (hK : K ∈ calC M)
    (hc2 : (conjSetOf M K).ncard = 2) {n : ℕ} (hL2 : IsL2 (Bar2 K) n) {t : G} (htM : t ∈ M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {b : G} (hbM : b ∈ M) (hbr : b ^ r = 1) :
    r ∣ Nat.card K ∨
      ((∃ x ∈ barImage M K, orderOf x = 3 ∧
          Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) x) ∧
        ∃ x ∈ barImage M (K.map (MulAut.conj t).toMonoidHom), orderOf x = 3 ∧
          Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) x) := by
  have hodd : Odd (orderOf b) :=
    Odd.of_dvd_nat (hr.odd_of_ne_two hr2) (orderOf_dvd_of_pow_eq_one hbr)
  have hbK : b ∈ normalizer (K : Set G) := uc22p2214_mem_normalizer_of_odd hc2 hbM hodd
  have hbKt : b ∈ normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    uc22p2214_normalizes_of_pair hc2 ⟨t, htM, rfl⟩ hbM hbK
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC M := UC6S846.calC_map M _
    (Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer htM)) hK
  have hcard : Nat.card ↥(K.map (MulAut.conj t).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hnorm : ∀ {L : Subgroup G}, L ∈ calC M → b ∈ normalizer (L : Set G) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ ∈ normalizer (barImage M L : Set (Bar2 M)) :=
    fun hL hbL => Subgroup.le_normalizer_map _ ⟨⟨b, hbM⟩, by
      rw [← Subgroup.subgroupOf_normalizer_eq hL.1.le]
      exact Subgroup.mem_subgroupOf.2 hbL, rfl⟩
  have hdvd : ∀ {L : Subgroup G}, L ∈ calC M → ∀ y ∈ barImage M L, orderOf y = r →
      r ∣ Nat.card L := fun {L} hL y hy hyo => by
    rw [← hyo, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.1.le).toEquiv]
    exact (Subgroup.orderOf_dvd_natCard _ hy).trans ((L.subgroupOf M).card_map_dvd _)
  have hL2' : ∀ {L : Subgroup G}, L ∈ calC M → IsL2 (Bar2 L) n → IsL2 ↥(barImage M L) n :=
    fun hL h => by
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
      unfold IsL2 at h ⊢
      exact CFSG.Blueprint.LieModel.of_mulEquiv e h
  have hL2t : IsL2 (Bar2 (K.map (MulAut.conj t).toMonoidHom)) n := by
    unfold IsL2 at hL2 ⊢
    exact CFSG.Blueprint.LieModel.of_mulEquiv (UC6S846.bar2Equiv
      (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)) hL2
  have hβr : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ : Bar2 M) ^ r = 1 := by
    rw [← map_pow]
    have h1 : (⟨b, hbM⟩ : ↥M) ^ r = 1 := Subtype.ext (by simpa using hbr)
    rw [h1, map_one]
  rcases inner_or_commute_orderOf_three (hL2' hK hL2) hr hr2 (hnorm hK hbK) hβr
    with ⟨y, hy, hyo, -⟩ | h₁
  · exact Or.inl (hdvd hK y hy hyo)
  rcases inner_or_commute_orderOf_three (hL2' hKt hL2t) hr hr2 (hnorm hKt hbKt) hβr
    with ⟨y, hy, hyo, -⟩ | h₂
  · exact Or.inl (hcard ▸ hdvd hKt y hy hyo)
  · exact Or.inr ⟨h₁, h₂⟩

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
