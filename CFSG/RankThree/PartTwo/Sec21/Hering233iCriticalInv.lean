module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree.PartTwo.Sec4.Census
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem exists_criticalAt_invariant {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hP : pCore q X ≠ ⊥) :
    ∃ D : Subgroup X, CriticalAt q D ∧ ∀ σ : MulAut X, D.map σ.toMonoidHom = D := by
  set P := pCore q X with hPdef
  have : P.Normal := pCore_normal
  have hPchar : P.Characteristic := pCore_characteristic
  have hPq : IsPGroup q P := pCore_isPGroup
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨D₀, hD₀c, hD₀1, hD₀comm, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hPq
  have hinv : ∀ σ : MulAut X, (D₀.map P.subtype).map σ.toMonoidHom = D₀.map P.subtype := by
    intro σ
    have hD₀σ : D₀.map (MulAut.characteristic P σ).toMonoidHom = D₀ :=
      Subgroup.characteristic_iff_map_eq.mp hD₀c (MulAut.characteristic P σ)
    have hcomp : σ.toMonoidHom.comp P.subtype =
        P.subtype.comp (MulAut.characteristic P σ).toMonoidHom :=
      MonoidHom.ext fun x => rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hD₀σ]
  refine ⟨D₀.map P.subtype, ⟨inferInstance, Subgroup.map_subtype_le _, fun h => hD₀1 ?_, ?_, ?_,
    ?_⟩, hinv⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD₀exp x hx, Subgroup.coe_one]
  · rintro _ ⟨a, ha, rfl⟩ b hb
    have h1 : ⁅a, (⟨b, hb⟩ : P)⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _)
    obtain ⟨h2, h3⟩ := hD₀comm h1
    refine ⟨⟨_, h2, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have h4 := Subgroup.mem_centralizer_iff.mp h3 d hd
    exact (congrArg Subtype.val h4).symm
  · intro y hy
    set σ : MulAut P := MulAut.conjNormal y with hσ
    have hσfix : σ ∈ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      exact hy _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD₀fix ⟨σ, hσfix⟩
    refine ⟨k, fun x hx => ?_⟩
    have h1 : σ ^ (q ^ k) = 1 := congrArg Subtype.val hk
    have h2 := congrArg (fun τ : MulAut P => ((τ ⟨x, hx⟩ : P) : X)) h1
    simp only [hσ, ← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact h2

end CFSG.RankThree.PartTwo.Sec21.Hering233i
