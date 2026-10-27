module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLift
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

theorem ggTorusReflGenW_of_selfCent_card {p r s : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R)
    (hbump : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → p ^ s ≤ Nat.card E)
    (h : GGTorusReflGenW p s R I) : GGTorusReflGenW p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨l, rfl⟩ := hψ x
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  exact h L' ψ A ⟨hψ, hker, hperf, hAe, hAI,
    hcardE ▸ hbump E hEab (by rw [hcardE]; exact hr) hscE, h3, hsc⟩

theorem card_eq_of_selfCentralizing_of_sylowTorus {R : Type} [Group R] [Finite R] {p N : ℕ}
    (hp : p.Prime) (hT : SylowTorus R p N) {E : Subgroup R} (hE : IsElemAbelian p E)
    (hsc : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) : Nat.card E = p ^ N := by
  obtain ⟨E₀, hE₀, hcard₀⟩ := hT.exists_elemAbelian
  obtain ⟨c, rfl⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hE₀ hcard₀ hE hsc
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard₀]

theorem ggTorusReflGenW_F4Plus_of_four
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1)
    (h : GGTorusReflGenW p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)) :
    GGTorusReflGenW p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hp2 : p ≠ 2 := by omega
  have := TableBF4.finite_recipeGroup (K := K)
  have he := ExcFramesHalf.orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  have hT : SylowTorus (TableBF4.RecipeGroup K) p 4 :=
    (OrdPInnerExc.sylowTorus_F4_two K hp hp3 he).of_mulEquiv (TableBF4.recipeEquiv K).symm
  refine ggTorusReflGenW_of_selfCent_card hp (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
    (fun E hE _ hsc => ?_) h
  rw [card_eq_of_selfCentralizing_of_sylowTorus hp hT hE hsc]

end CFSG.StandardType

end
