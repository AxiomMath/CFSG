module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart24

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.DataValid

open CFSG.LieType.Steinberg.Adjoint

theorem f4Data_checkTables_without117 : f4Data.checkTables = true := by decide +kernel

theorem f4Data_checkSimple_without117 : f4Data.checkSimple = true := by decide +kernel

theorem f4Data_checkWeyl_without117 : f4Data.checkWeyl = true := by decide +kernel

theorem f4Data_checkPairs_without117 : f4Data.checkPairs = true := by decide +kernel

theorem f4Data_checkPairNorm_without117 : f4Data.checkPairNorm = true := by decide +kernel

theorem f4Data_valid_without117 : f4Data.Valid :=
  ⟨f4Data_checkTables_without117, f4Data_checkSimple_without117,
    f4Data_checkWeyl_without117, f4Data_checkPairs_without117,
    f4Data_checkPairNorm_without117⟩

end CFSG.StandardType.F4ExplicitPos.DataValid


namespace CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley IsNilpotent
open scoped Nat
open scoped commutatorElement
variable {τ : Tag}

section GroupLayer
variable {K : Type} [Field K]
variable {D : AdjData τ}

theorem commutator_xPar_without117
    {F : RootOperatorFamily τ} (hD : D.Valid) (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) (c d : K) :
    ⁅xPar F α c, xPar F β d⁆ =
      xPar F (α + β) ((RootOperatorFamily'.coeff11_without117 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c * d) *
        xPar F (α + 2 • β)
          ((RootOperatorFamily'.coeff12_without117 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c * d ^ 2) *
          xPar F (2 • α + β)
            ((RootOperatorFamily'.coeff21_without117 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c ^ 2 * d) := by
  refine endHom_injective ?_
  rw [commutatorElement_def, xPar_neg_without117 F, xPar_neg_without117 F]
  simp only [map_mul, endHom_xPar_without117 F,
    RootOperatorFamily'.eltOr_of_isRoot_without117 F K hα,
    RootOperatorFamily'.eltOr_of_isRoot_without117 F K hβ]
  exact RootOperatorFamily'.comm_formula_without117 F hD hτ (α := ⟨α, hα⟩) (β := ⟨β,
      hβ⟩) hne hne' c d

end GroupLayer

theorem eq_one_of_isRoot_nsmul_without117
    {γ : Fin τ.rank → ℤ} {n : ℕ} (h : IsRoot τ (n • γ)) :
    n = 1 := by
  have e : (n • γ : Fin τ.rank → ℤ) = (n : ℤ) • γ := (Nat.cast_smul_eq_nsmul ℤ n γ).symm
  rcases h.eq_one_or_neg_one_of_eq_smul e with h1 | h1 <;> omega

theorem prod_map_filter_of_eq_one_without117 {X G : Type*} [Monoid G] (L : List X) (q : X → Bool)
    (f : X → G) (h : ∀ x ∈ L, q x = false → f x = 1) :
    ((L.filter q).map f).prod = (L.map f).prod := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    by_cases ha : q a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, ih']
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.prod_cons,
        h a (by simp) (by simpa using ha), one_mul, ih']

section GroupCommute

variable {K : Type} [Field K]

theorem commute_xPar_without117
    (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)
    (hτ : NoG2 τ) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hne : γ + δ ≠ 0) (hn : ¬IsRoot τ (γ + δ)) (a b : K) :
    Commute (xPar F γ a) (xPar F δ b) := by
  by_cases hγδ : γ = δ
  · subst hγδ
    rw [Commute, SemiconjBy, ← xPar_add_without117 F, ← xPar_add_without117 F, add_comm]
  · have hne' : γ ≠ -δ := fun h => hne (by rw [h, neg_add_cancel])
    have h12 : ¬IsRoot τ (γ + 2 • δ) := fun h =>
      hn (isRoot_add_of_isRoot_add_two_smul hδ hγ hγδ hne' h)
    have h21 : ¬IsRoot τ (2 • γ + δ) := fun h => hn (by
      rw [add_comm]
      exact isRoot_add_of_isRoot_add_two_smul hγ hδ (Ne.symm hγδ)
        (fun h' => hne' (by rw [h', neg_neg])) (by rwa [add_comm]))
    rw [← commutatorElement_eq_one_iff_commute,
      commutator_xPar_without117 (F := F) hD hτ hγ hδ hγδ hne',
      xPar_of_not_isRoot_without117 F hn, xPar_of_not_isRoot_without117 F h12,
      xPar_of_not_isRoot_without117 F h21, mul_one, mul_one]

theorem commute_xPar_pairs_without117
    (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)
    (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) {p q : ℕ × ℕ} (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2)
    (hq1 : 1 ≤ q.1) (hq2 : 1 ≤ q.2) (a b : K) :
    Commute (xPar F (p.1 • α + p.2 • β) a) (xPar F (q.1 • α + q.2 • β) b) := by
  by_cases hrp : IsRoot τ (p.1 • α + p.2 • β)
  · by_cases hrq : IsRoot τ (q.1 • α + q.2 • β)
    · have hlin := linIndepPair_of_ne hα hβ hne hne'
      have e : p.1 • α + p.2 • β + (q.1 • α + q.2 • β) = (p.1 + q.1) • α + (p.2 + q.2) • β := by
        rw [add_nsmul, add_nsmul]
        abel
      refine commute_xPar_without117 F hD hτ hrp hrq ?_ ?_ a b
      · rw [e]
        exact nsmul_add_nsmul_ne_zero_without117 hlin (Or.inl (by omega))
      · rw [e]
        exact not_isRoot_nsmul_add_nsmul hτ hα hβ hne hne' (by omega) (by omega) (by omega)
    · rw [xPar_of_not_isRoot_without117 F hrq]
      exact Commute.one_right _
  · rw [xPar_of_not_isRoot_without117 F hrp]
    exact Commute.one_left _

end GroupCommute

end CFSG.LieType.Steinberg.Adjoint

end

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


namespace CFSG.StandardType.F4ExplicitPos.RootBaseChange

variable {τ : Tag} {R S : Type} [Field R] [Field S]

end CFSG.StandardType.F4ExplicitPos.RootBaseChange
end

end
