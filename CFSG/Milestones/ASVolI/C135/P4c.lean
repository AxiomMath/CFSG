module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cnt

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom dualHom_dualHom
  coe_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot semi_eq_one lin_dual
  lin_of_dual tri_offender fixAll)
open CFSG.Quasithin.H13.Ch4 (matrix_eq_of_mulVec_eq)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G]

section Offender

variable {F : Type} [Field F]

theorem burnsideC135_offender [Finite F] [CharP F 2] {L U W Q A : Subgroup G}
    (ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F) (hρ : Function.Surjective ρ)
    (q0 : QC U ⊥ F) (q1 : QC W U F) (q2 : QC Q W F)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hnat₀ : ∀ (g : ↥L) (x : ↥U), q0.κ (cnj (hLU g.2) x) =
      ((ρ g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ q0.κ x)
    (hnat₁ : ∀ (g : ↥L) (x : ↥W), q1.κ (cnj (hLW g.2) x) =
      ((dualHom (ρ g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        q1.κ x)
    (hnat₂ : ∀ (g : ↥L) (x : ↥Q), q2.κ (cnj (hLQ g.2) x) =
      ((dualHom (ρ g) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        q2.κ x)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hA : IsElemAbelian 2 A) (hne : (q0.rep hAU (le_normalizer_bot A)).range ≠ ⊥) :
    Nat.card (q0.rep hAU (le_normalizer_bot A)).range * Nat.card F *
        Nat.card (fixAll (q0.rep hAU (le_normalizer_bot A))) *
        Nat.card (fixAll (q1.rep hAW hAU)) < 2 * Nat.card F ^ 6 ∧
      Nat.card (q0.rep hAU (le_normalizer_bot A)).range *
        Nat.card (fixAll (q0.rep hAU (le_normalizer_bot A))) *
        Nat.card (fixAll (q2.rep hAQ hAW)) < 2 * Nat.card F ^ 6 := by
  have hAb := le_normalizer_bot A
  set ρ₀ := q0.rep hAU hAb with hρ₀
  set ρ₁ := q1.rep hAW hAU with hρ₁
  set ρ₂ := q2.rep hAQ hAW with hρ₂
  have hsq : ∀ x : ↥A, x * x = 1 := fun x => Subtype.ext (by
    have := hA.2 x x.2
    rw [sq] at this
    exact this)
  have hρd : Function.Surjective (dualHom.comp ρ) := fun γ => by
    obtain ⟨g, hg⟩ := hρ (dualHom γ)
    exact ⟨g, by rw [MonoidHom.comp_apply, hg, dualHom_dualHom]⟩
  choose σ hσ using fun x => q0.exists_semi hAU hAb ρ hLU hnat₀ hAL hρ x
  choose σ₁ hσ₁ using fun x => q1.exists_semi hAW hAU (dualHom.comp ρ) hLW
    (fun g x => hnat₁ g x) hAL hρd x
  choose σ₂ hσ₂ using fun x => q2.exists_semi hAQ hAW (dualHom.comp ρ) hLQ
    (fun g x => hnat₂ g x) hAL hρd x
  refine tri_offender ρ₀ ρ₁ ρ₂ σ σ₁ σ₂ hsq (q0.rep_add hAU hAb) (q1.rep_add hAW hAU)
    (q2.rep_add hAQ hAW) hσ hσ₁ hσ₂ ?_ ?_ ?_ hne
  · intro x hx h1
    apply hx
    refine semi_eq_one (q0.rep_add hAU hAb x) (hσ x) ?_
    refine lin_of_dual q0 q1 hAU hAb hAW hAU ρ hρ hLU hLW hnat₀ hnat₁ hAL x (hsq x)
      fun c v => ?_
    rw [hσ₁, h1]
    rfl
  · intro x hx h1
    apply hx
    refine semi_eq_one (q0.rep_add hAU hAb x) (hσ x) ?_
    refine lin_of_dual q0 q2 hAU hAb hAQ hAW ρ hρ hLU hLQ hnat₀ hnat₂ hAL x (hsq x)
      fun c v => ?_
    rw [hσ₂, h1]
    rfl
  · intro x hx
    have hlin : ∀ (c : F) v, ρ₀ x (c • v) = c • ρ₀ x v := fun c v => by
      rw [hσ, hx]
      rfl
    obtain ⟨P, hP₀, hP₁⟩ := lin_dual q0 q1 hAU hAb hAW hAU ρ hρ hLU hLW hnat₀ hnat₁
      hAL x (hsq x) hlin
    obtain ⟨P', hP₀', hP₂⟩ := lin_dual q0 q2 hAU hAb hAQ hAW ρ hρ hLU hLQ hnat₀
      hnat₂ hAL x (hsq x) hlin
    have hPP : P' = P := Subtype.ext (matrix_eq_of_mulVec_eq fun v => by rw [← hP₀', hP₀])
    exact ⟨P, hP₀, hP₁, fun v => by rw [hP₂, hPP]⟩

end Offender

end CFSG.ASVolI

end
