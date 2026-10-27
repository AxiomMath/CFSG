module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType


theorem ggTwE6CubeNodeInput_of_c0
    (hc0 : ∀ {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
      (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
      (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
      (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 (AlgebraicClosure K)}
      (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
      (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
      {x : MulAut ↥(twistedE6RootGroup K σ)} (hx : x ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g)
      (hx1 : x ≠ 1) (hcomp : IsComponentOf (LargeEvenLayer (ggFix x)) (ggFix x))
      (hfix : ∀ y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g,
        (∀ j ∈ LargeEvenLayer (ggFix x), y j = j) ↔ y ∈ Subgroup.zpowers x)
      {E : Subgroup ↥(twistedE6RootGroup K σ)} (hE : IsElemAbelian 3 E) (hEx : E ≤ ggFix x),
      Nat.card E ≤ 3 * Nat.card (E ⊓ LargeEvenLayer (ggFix x) : Subgroup _)) :
    CFSG.StandardType.SmallExc.GGTwE6CubeNodeInput := by
  intro K _ _ n hn hK h3 Y hY hYI hYc x hxY hx1 hcomp hfix E hE hEx
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K 2 n) ⟨hinj, Finite.surjective_of_injective hinj⟩,
      fun c => iterateFrobenius_def 2 n c⟩
  obtain ⟨Fr, hFr⟩ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, ∀ c, Fr c = c ^ 2 ^ n :=
    ⟨iterateFrobenius _ 2 n, fun c => iterateFrobenius_def 2 n c⟩
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set Φ := MulAut.congr ε
  have hεi : Function.Injective ε.toMonoidHom := ε.injective
  have hY' : IsElemAbelian 3 (Y.map Φ.symm.toMonoidHom) := TableB.isElemAbelian_map hY _
  have hY'I : Y.map Φ.symm.toMonoidHom ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine (hε _).1 ?_
    change Φ (Φ.symm y) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hYI hy
  have hY'c : Nat.card (Y.map Φ.symm.toMonoidHom) = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (fun a b h => Φ.symm.injective h)).trans hYc
  obtain ⟨g, hg, hgn, hYeq⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 Fr hFr hY' hY'I hY'c
  obtain ⟨x', rfl⟩ := Φ.surjective x
  have hF : ggFix (Φ x') = (ggFix x').map ε.toMonoidHom := by
    ext r
    refine ⟨fun hr => ⟨ε.symm r, mem_ggFix.2 (ε.injective ?_), ε.apply_symm_apply r⟩, ?_⟩
    · rw [ε.apply_symm_apply]
      exact hr
    · rintro ⟨c, hc, rfl⟩
      show ε (x' (ε.symm (ε c))) = ε c
      rw [ε.symm_apply_apply, mem_ggFix.1 hc]
  have hL : LargeEvenLayer (ggFix (Φ x')) =
      (LargeEvenLayer (ggFix x')).map ε.toMonoidHom := by
    rw [hF, largeEvenLayer_map_of_injective ε.toMonoidHom hεi]
  have hcomp' : IsComponentOf (LargeEvenLayer (ggFix x')) (ggFix x') := by
    rw [hL, hF] at hcomp
    have h := (isComponentOf_comap_of_injective ε.toMonoidHom hεi hcomp).1
    rwa [Subgroup.comap_map_eq_self_of_injective hεi] at h
  have hfix' : ∀ y' ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g,
      (∀ j ∈ LargeEvenLayer (ggFix x'), y' j = j) ↔ y' ∈ Subgroup.zpowers x' := by
    intro y' hy'
    rw [← hYeq, Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy'
    have h := hfix (Φ y') hy'
    rw [hL] at h
    refine Iff.trans ?_ (h.trans ?_)
    · constructor
      · rintro h' _ ⟨c, hc, rfl⟩
        show ε (y' (ε.symm (ε c))) = ε c
        rw [ε.symm_apply_apply, h' c hc]
      · intro h' c hc
        have h1 := h' (ε c) ⟨c, hc, rfl⟩
        change ε (y' (ε.symm (ε c))) = ε c at h1
        rw [ε.symm_apply_apply] at h1
        exact ε.injective h1
    · simp only [Subgroup.mem_zpowers_iff, ← map_zpow, Φ.injective.eq_iff]
  have hE'x : E.comap ε.toMonoidHom ≤ ggFix x' := fun c hc => mem_ggFix.2 (ε.injective (by
    have h1 := mem_ggFix.1 (hEx (Subgroup.mem_comap.1 hc))
    change ε (x' (ε.symm (ε c))) = ε c at h1
    rwa [ε.symm_apply_apply] at h1))
  have hcard : Nat.card (E.comap ε.toMonoidHom) = Nat.card E :=
    Nat.card_congr (ε.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have hcard' : Nat.card (E.comap ε.toMonoidHom ⊓ LargeEvenLayer (ggFix x') : Subgroup _) =
      Nat.card (E ⊓ LargeEvenLayer (ggFix (Φ x')) : Subgroup _) := by
    refine Nat.card_congr (ε.toEquiv.subtypeEquiv fun c => ?_)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hL]
    exact and_congr Iff.rfl (Subgroup.mem_map_iff_mem hεi).symm
  have hx'Y : x' ∈ Y.map Φ.symm.toMonoidHom := ⟨Φ x', hxY, Φ.symm_apply_apply x'⟩
  rw [hYeq] at hx'Y
  have h := hc0 hn hK σ hσ h3 hFr hg hgn hx'Y (fun h1 => hx1 (by rw [h1, map_one])) hcomp'
    hfix' (hE.comap hεi) hE'x
  rwa [hcard, hcard'] at h

end CFSG.StandardType.TwE6Cube

end
