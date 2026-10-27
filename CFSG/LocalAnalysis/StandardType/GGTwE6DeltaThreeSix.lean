module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSixCube
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Open


theorem reflData_recipe {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hY : IsElemAbelian 3 Y)
    (hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hYc : Nat.card Y = 3 ^ 6) : ReflData Y := by
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨iterateFrobeniusEquiv K 2 n, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  have hY₀ : IsElemAbelian 3 (Y.comap (MulAut.congr ε).toMonoidHom) :=
    hY.comap (f := (MulAut.congr ε).toMonoidHom) (MulAut.congr ε).injective
  have hY₀c : Nat.card (Y.comap (MulAut.congr ε).toMonoidHom) = 3 ^ 6 := by
    rw [← hYc]
    exact Nat.card_congr ((MulAut.congr ε).toEquiv.subtypeEquiv fun _ => Iff.rfl)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, hgY⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 _ hFr hY₀
    (fun y hy => (hε y).1 (hYI hy)) hY₀c
  refine ReflData.of_comap ε ?_
  rw [hgY]
  exact TwE6DD2.reflData_langCube hn hK σ hσ h3 _ hFr hg hgn

theorem torusLiftInput_holds : TorusLiftInput := by
  intro K _ _ n hn hK h3 L' _ _ ψ hψ hker hperf hZ3 A hA h5 hind
  classical
  have hZR := TwE6Delta.center_recipeR_eq_bot hn hK
  have hkc : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hZR
  have hXI : ((A.map (BstarDesc.descAut hψ hkc) : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hind a ha
    have h1 : BstarDesc.descAut hψ hkc a = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [BstarDesc.descAut_apply, hφa]
    rw [h1]
    exact hφ
  obtain ⟨Y, hXY, hY, hYI, hYc, -⟩ := TwE6DD2.exists_cubeTorus_recipe hn hK h3
    (hA.map (BstarDesc.descAut hψ hkc)) hXI
    (by rw [Subgroup.card_map_of_injective (BstarDesc.descAut_injective hψ hkc hperf)]; exact h5)
  obtain ⟨E, hE, hEc, hEfix⟩ := exists_fixed_of_reflData hψ hker hZ3 hZR hY
    (reflData_recipe hn hK h3 hY hYI hYc)
  exact ⟨E, hE, hEc, fun a ha => hEfix a (hA.2 a ha)
    ⟨_, hXY ⟨a, ha, rfl⟩, BstarDesc.descAut_apply hψ hkc a⟩⟩

theorem torusLiftSixInput_holds : TorusLiftSixInput :=
  torusLiftSixInput_of_full torusLiftInput_holds

end CFSG.StandardType.TwE6D3
