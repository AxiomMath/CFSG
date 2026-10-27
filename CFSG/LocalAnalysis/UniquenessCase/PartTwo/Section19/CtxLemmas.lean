module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.GroupTheory.ZModSqElemAbelianPrime
public import CFSG.GroupTheory.ZModSqElemAbelianNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem A_le_H_of_ctx19_23 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : A ≤ H := by
  rw [h.hH]
  exact le_centralizer_of_isMulCommutative_of_le
    (isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard) h.ctx22.hA₀

theorem exists_isElemAbelian_card_prime_sq_of_isZModSq {A : Subgroup G} {n r : ℕ}
    (hA : IsZModSq A n) (hr : r.Prime) (hdvd : r ∣ Nat.card A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  obtain ⟨e⟩ := hA
  have hdvd' : r ∣ 2 ^ n - 1 := by
    rw [card_eq_of_isZModSq ⟨e⟩, ← pow_two] at hdvd
    exact hr.dvd_of_dvd_pow hdvd
  exact CFSG.GroupTheory.exists_isElemAbelian_card_prime_sq_of_mulEquiv_zmod_sq e hr hdvd'

theorem mem_powTorsionSubgroup {A : Subgroup G} [IsMulCommutative ↥A] {r : ℕ} {x : G} :
    x ∈ (MonoidHom.ker (powMonoidHom r : ↥A →* ↥A)).map A.subtype ↔
      x ∈ A ∧ x ^ r = 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
    exact ⟨a.2, by simpa using congrArg A.subtype ha⟩
  · rintro ⟨hxA, hxr⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact Subtype.ext (by simpa using hxr)

theorem card_powTorsionSubgroup_of_isZModSq {A : Subgroup G} [IsMulCommutative ↥A]
    {n r : ℕ} (hA : IsZModSq A n) (hr : r.Prime) (hrdvd : r ∣ Nat.card A) :
    Nat.card ↥((MonoidHom.ker (powMonoidHom r : ↥A →* ↥A)).map A.subtype) = r ^ 2 := by
  obtain ⟨e⟩ := hA
  rw [card_eq_of_isZModSq ⟨e⟩, ← pow_two] at hrdvd
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact CFSG.GroupTheory.card_powTorsionIn_of_mulEquiv e hr (hr.dvd_of_dvd_pow hrdvd)

theorem eq_powTorsionSubgroup_of_isElemAbelian_card {A E : Subgroup G}
    [IsMulCommutative ↥A] {n r : ℕ} (hA : IsZModSq A n) (hr : r.Prime)
    (hrdvd : r ∣ Nat.card A) (hEA : E ≤ A) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) :
    E = (MonoidHom.ker (powMonoidHom r : ↥A →* ↥A)).map A.subtype := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_powTorsionSubgroup]
    exact ⟨hEA hx, hEel.2 x hx⟩
  · rw [hEcard, card_powTorsionSubgroup_of_isZModSq hA hr hrdvd]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
