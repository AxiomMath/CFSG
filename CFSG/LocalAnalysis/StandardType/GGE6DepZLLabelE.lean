module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLOfGood
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.E6ThreeModel CFSG.StandardType.TableBExc.E6Three

variable {K : Type} [Field K] [Finite K]

theorem ggE6DepZLProp_E (hAL : GGAbelianLift) (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGE6DepZLProp (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units, hK]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have h3' : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have hcard : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* adjointGroup .E6 K),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Nat.card ψ.ker ∣ 3 := by
    intro L' _ _ ψ hψ hker hperf
    let ψ' : L' →* TableBExc.RecipeGroup .E6 K :=
      (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp ψ
    have hkerEq : ψ'.ker = ψ.ker := by
      ext l
      simp [ψ', MonoidHom.mem_ker]
    have h := card_ker_dvd_three_e6 hn hK
      ((TableBExc.recipeEquiv .E6 K).symm.surjective.comp hψ) (hkerEq ▸ hker) hperf
    rwa [hkerEq] at h
  refine zlProp_transport (TableBExc.recipeEquiv .E6 K).symm ((eFrame K ζ hζ).H : Set _)
    (TableBExc.RecipeID .E6 K) ?_
    (zlProp_of_good hAL _ (eFrame_good hζo hζ) _ rfl hcard
      fun L' _ _ ψ hψ hker hperf w hw =>
        eFrame_zl_row hK h3' ζ hζ hζo L' ψ hψ hker hperf w hw)
  intro φ
  refine (recipeID_iff_hatAut φ).trans ?_
  have h : (MulAut.congr (TableBExc.recipeEquiv .E6 K).symm).symm φ =
      MulAut.congr (TableBExc.recipeEquiv .E6 K) φ := by
    ext x
    simp
  rw [h]
  exact Iff.rfl

end CFSG.StandardType.E6Dep.ZL

end
