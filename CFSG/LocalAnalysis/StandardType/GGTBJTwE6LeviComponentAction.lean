module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three


theorem sectionFrameAut_eq_rootReflectionClosure_twE6
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    (hp : 4 < p) {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hTinj : Function.Injective T)
    (hT : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd x)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x))
    {X : Type} [Group X] [Finite X] (ψ : X →* twistedE6RootGroup K σ)
    (hker : ψ.ker ≤ Subgroup.center X) (hcp : ¬p ∣ Nat.card (Subgroup.center X))
    (s : (Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p)) →* X)
    (hs : ∀ f, ψ (s f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j))))
    (J : Subgroup X) (Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ))
    (v : WeylGroup TwistTag.E6.tag) (C : Set (Fin TwistTag.E6.tag.rank))
    (hΨ : Ψ = (v • ·) '' parabolicRoots TwistTag.E6.tag C)
    (hAnn : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p,
      (∀ γ ∈ Ψ, ∑ j, (γ j : ZMod p) * x j = 0) →
      ∀ a ∈ J, s (fun j => Multiplicative.ofAdd (x j)) * a =
        a * s (fun j => Multiplicative.ofAdd (x j)))
    (hLow : ∀ γ ∈ Ψ, ∃ a ∈ J, ggKGTwY F (ψ a) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ)) :
    FrameBs.sectionFrameAut s J =
      (Subgroup.closure (rootReflection '' Ψ)).map (adMulAutHom TwistTag.E6.tag p) := by
  classical
  have hcl : Subgroup.closure (rootReflection '' Ψ) =
      Subgroup.closure ((fun j => v * simple TwistTag.E6.tag j * v⁻¹) '' C) := by
    rw [hΨ]
    have hset : rootReflection '' ((v • ·) '' parabolicRoots TwistTag.E6.tag C) =
        {w : WeylGroup TwistTag.E6.tag |
          ∃ γ ∈ (v • ·) '' parabolicRoots TwistTag.E6.tag C, w = rootReflection γ} := by
      ext w
      constructor
      · rintro ⟨γ, hγ, he⟩
        exact ⟨γ, hγ, he.symm⟩
      · rintro ⟨γ, hγ, he⟩
        exact ⟨γ, hγ, he.symm⟩
    rw [hset]
    exact closure_rootReflection_smul_parabolicRoots v C
  apply le_antisymm
  · rintro τ ⟨a, haJ, ha⟩
    have hτtop : τ ∈ FrameBs.sectionFrameAut s (⊤ : Subgroup X) :=
      ⟨a, Subgroup.mem_top a, ha⟩
    obtain ⟨w, hwτ⟩ := (sectionFrameAut_le_adMulAutHom_range_twE6 F hζ T hTinj hT ψ s hs)
      hτtop
    have hfix : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p,
        (∀ γ ∈ Ψ, ∑ j, (γ j : ZMod p) * x j = 0) → adAct TwistTag.E6.tag p w x = x := by
      intro x hx
      let f : Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p) :=
        fun j => Multiplicative.ofAdd (x j)
      have hc := hAnn x hx a haJ
      have hsa : a * s f * a⁻¹ = s f := by
        rw [← hc, mul_inv_cancel_right]
      have hsEq : s (τ f) = s f := (ha f).symm.trans hsa
      have he := congrArg ψ hsEq
      rw [hs, hs] at he
      have hv := congrArg Multiplicative.toAdd (hTinj he)
      funext j
      have hj := congrFun hv j
      rw [← hwτ] at hj
      change Multiplicative.toAdd ((adMulAutHom TwistTag.E6.tag p w) f j) = x j at hj
      rw [adMulAutHom_apply] at hj
      exact hj
    have hlocal : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p,
        (∀ j ∈ C, x j = 0) → adAct TwistTag.E6.tag p (v⁻¹ * w * v) x = x := by
      intro x hx
      have hA : ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod p) * adAct TwistTag.E6.tag p v x j = 0 := by
        rintro γ hγ
        rw [hΨ] at hγ
        obtain ⟨β, hβ, rfl⟩ := hγ
        rw [adAct_pairing_smul]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ∈ C
        · rw [hx j hj, mul_zero]
        · rw [hβ.2 j hj, Int.cast_zero, zero_mul]
      rw [adAct_mul, adAct_mul, hfix _ hA, ← adAct_mul, inv_mul_cancel, adAct_one]
    let w' : WeylGroup Tag.E6 := v⁻¹ * w * v
    let C' : Set (Fin Tag.E6.rank) := C
    have hlocal' : ∀ x : Fin Tag.E6.rank → ZMod p, (∀ j ∈ C', x j = 0) →
        adAct Tag.E6 p w' x = x := hlocal
    have hwC : v⁻¹ * w * v ∈ parabolicWeylGroup TwistTag.E6.tag C :=
      mem_parabolicWeylGroup_of_adAct_fix hp (S := C') (w := w') hlocal'
    have hw : w ∈ (parabolicWeylGroup TwistTag.E6.tag C).map (MulAut.conj v).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨v⁻¹ * w * v, hwC, ?_⟩
      change v * (v⁻¹ * w * v) * v⁻¹ = w
      group
    rw [map_conj_parabolicWeylGroup, ← hcl] at hw
    exact Subgroup.mem_map.mpr ⟨w, hw, hwτ⟩
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro τ ⟨w, ⟨γ, hγ, rfl⟩, rfl⟩
    obtain ⟨a, ha, hw⟩ := hLow γ hγ
    exact adMulAutHom_mem_sectionFrameAut_of_weyl_point F hζ T hT ψ hker hcp s hs ha hw

end CFSG.StandardType

end
