module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSym
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup Equiv Equiv.Perm
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

private theorem centralizer_eq_bot_of_fstar_le {X : Type} [Group X] [Finite X] {Λ : Subgroup X}
    (hF : genFittingFStar X ≤ Λ) (e : Λ ≃* alternatingGroup (Fin 10)) :
    centralizer (Λ : Set X) = ⊥ := by
  have hle : centralizer (Λ : Set X) ≤ Λ :=
    (Subgroup.centralizer_le hF).trans
      ((CFSG.Adapters.generalized_fitting_self_centralizing X).trans hF)
  rw [eq_bot_iff]
  intro x hx
  have hc : e ⟨x, hle hx⟩ ∈ center (alternatingGroup (Fin 10)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_centralizer_iff.mp hx w w.2))
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc
  exact mem_bot.mpr (congrArg Subtype.val (e.map_eq_one_iff.mp hc))

private theorem mem_of_pow_five {X : Type} [Group X] {Λ : Subgroup X} {φ : X →* Perm (Fin 10)}
    (hφ : Function.Injective φ) (e : Λ ≃* alternatingGroup (Fin 10))
    (he : ∀ w : Λ, φ (w : X) = ((e w : alternatingGroup (Fin 10)) : Perm (Fin 10))) {x : X}
    (hx : x ^ 5 = 1) : x ∈ Λ := by
  have hs : sign (φ x) = 1 := by
    have h := congrArg (fun y => sign (φ y)) hx
    simp only [map_pow, map_one] at h
    rcases Int.units_eq_one_or (sign (φ x)) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  obtain ⟨w, hw⟩ := e.surjective ⟨φ x, mem_alternatingGroup.mpr hs⟩
  have hwx : φ (w : X) = φ x := by rw [he, hw]
  rw [← hφ hwx]
  exact w.2

private theorem exists_perfect_le_centralizer (g : A10Perm.A10)
    (h5 : Nat.card (Function.fixedPoints ⇑(g : Perm (Fin 10))) = 5) :
    ∃ Q : Subgroup A10Perm.A10, ⁅Q, Q⁆ = Q ∧ Q ≤ centralizer (zpowers g : Set A10Perm.A10) ∧
      5 ∣ Nat.card Q := by
  let F := Function.fixedPoints ⇑(g : Perm (Fin 10))
  let κ : alternatingGroup F →* A10Perm.A10 :=
    (ofSubtype.comp (alternatingGroup F).subtype).codRestrict (alternatingGroup (Fin 10))
      fun σ => by rw [MonoidHom.comp_apply, mem_alternatingGroup, sign_ofSubtype]; exact σ.2
  have hκ : Function.Injective κ := fun σ τ h =>
    Subtype.ext (ofSubtype_injective (congrArg Subtype.val h))
  have : Group.IsPerfect (alternatingGroup F) := ⟨commutator_alternatingGroup_eq_top h5.ge⟩
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [h5]; norm_num)
  refine ⟨κ.range, Subgroup.isPerfect_iff.mp (Group.IsPerfect.range κ), ?_, ?_⟩
  · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨σ, rfl⟩
    exact Subtype.ext (disjoint_ofSubtype_of_memFixedPoints_self σ.1).commute.eq
  · rw [← Nat.card_congr (MonoidHom.ofInjective hκ).toEquiv, nat_card_alternatingGroup, h5]
    decide

private theorem card_fixedPoints_a₁ :
    Nat.card (Function.fixedPoints ⇑(A10Perm.a₁ : Perm (Fin 10))) = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_fixedPoints_a₂ :
    Nat.card (Function.fixedPoints ⇑(A10Perm.a₂ : Perm (Fin 10))) = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_dvd_derInf8 {X : Type} [Group X] [Finite X] {θ : A10Perm.A10 →* X}
    (hθ : Function.Injective θ) {L Q : Subgroup A10Perm.A10} (hQp : ⁅Q, Q⁆ = Q)
    (hQc : Q ≤ centralizer (L : Set A10Perm.A10)) :
    Nat.card Q ∣ Nat.card (F08.DerInf8 (centralizer (L.map θ : Set X))) := by
  have hle : Q.map θ ≤ centralizer (L.map θ : Set X) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hQc hq) u hu]
  have hperf : ⁅Q.map θ, Q.map θ⁆ = Q.map θ := by rw [← map_commutator, hQp]
  rw [← card_map_of_injective hθ]
  exact card_dvd_of_le (uc22p21c_le_Hinf hle hperf)

theorem kAltTen_holds : KAltTen := by
  intro X _ _ Λ _ hF hAlt E hE hE25
  obtain ⟨e₀⟩ := hAlt
  obtain ⟨φ, hφ, hφe⟩ := CFSG.OddStandard.AltStdSec.lookup_exists_perm_embedding Λ
    (centralizer_eq_bot_of_fstar_le hF e₀) (by norm_num) (by norm_num) e₀
  have hEΛ : E ≤ Λ := fun x hx => mem_of_pow_five hφ e₀ hφe (hE.2 x hx)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let T : Sylow 5 Λ := Sylow.ofCard (E.subgroupOf Λ) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEΛ).toEquiv, hE25, Nat.card_congr e₀.toEquiv,
      A10Perm.factorization_A10]
    norm_num)
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e₀ T
  let θ : A10Perm.A10 →* X := Λ.subtype.comp ψ.symm.toMonoidHom
  have hθ : Function.Injective θ := Λ.subtype_injective.comp ψ.symm.injective
  have hle : ∀ L ≤ A10Perm.S₀, L.map θ ≤ E := by
    rintro L hL _ ⟨a, ha, rfl⟩
    have h := (hψ (ψ.symm a)).2 (by rw [MulEquiv.apply_symm_apply]; exact hL ha)
    exact h
  obtain ⟨Q₁, hQ₁p, hQ₁c, hQ₁d⟩ := exists_perfect_le_centralizer A10Perm.a₁ card_fixedPoints_a₁
  obtain ⟨Q₂, hQ₂p, hQ₂c, hQ₂d⟩ := exists_perfect_le_centralizer A10Perm.a₂ card_fixedPoints_a₂
  refine ⟨A10Perm.line₁.map θ, A10Perm.line₂.map θ, hle _ A10Perm.line₁_le,
    hle _ A10Perm.line₂_le, by rw [card_map_of_injective hθ, A10Perm.card_line₁],
    by rw [card_map_of_injective hθ, A10Perm.card_line₂],
    fun h => A10Perm.line₁_ne_line₂ (map_injective hθ h),
    hQ₁d.trans (card_dvd_derInf8 hθ hQ₁p hQ₁c), hQ₂d.trans (card_dvd_derInf8 hθ hQ₂p hQ₂c)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
