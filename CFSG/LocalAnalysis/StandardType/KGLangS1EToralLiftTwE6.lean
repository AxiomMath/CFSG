module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EModelTwE6
public import CFSG.LocalAnalysis.StandardType.KGLangS1ETypeDetTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

theorem kgLangS1E_toral_lift_twE6
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) {K₁ : Type} [Field K₁] [Finite K₁]
    (hK₁ : Nat.card K₁ = (2 ^ n) ^ 2)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hen : e * 3 = n)
    (ρ : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) →*
      ModGL TwistTag.E6.tag L)
    (Θ : ratPts TwistTag.E6.tag L
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)))
    (hρ : Function.Injective ρ)
    (hρG : ∀ r, ρ r ∈ ratPts TwistTag.E6.tag L
      (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL TwistTag.E6.tag L) * ρ r *
      (g : ModGL TwistTag.E6.tag L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) =
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ))
    (hTor : GGExcToralAct J₀ (A : Set (MulAut K))) :
    ExcFramesHalf.IsToralSubgroup TwistTag.E6.tag L (Subgroup.closure
      {x : ModGL TwistTag.E6.tag L | x ∈ ratPts TwistTag.E6.tag L
            (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) ∧
          ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
            (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ∧
          ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}) := by
  let S : Set (ModGL TwistTag.E6.tag L) :=
    {x : ModGL TwistTag.E6.tag L | x ∈ ratPts TwistTag.E6.tag L
          (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) ∧
        ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
          (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}
  change ExcFramesHalf.IsToralSubgroup TwistTag.E6.tag L (Subgroup.closure S)
  have heeven : Even e := by
    rw [← hen] at heven
    exact (Nat.even_mul.mp heven).resolve_right (by decide)
  obtain ⟨k, hkF, hkFin, σ, ι, g, hkcard, hσ, hgadj, ψ, huniv⟩ :=
    kgLangS1E_J0_model_twE6 hn heven hK₁ he hen ρ Θ hρ hρG hΘ hI hconjΘ hFj θ hcomm A hA hAI hξ
      hξI hJ₀
  letI : Field k := hkF
  letI : Finite k := hkFin
  have hType := kgLangS1E_typeDet_twE6 he hkcard σ hσ ψ
  rcases hTor with hE6 | hE7 | hTwE6
  · obtain ⟨K₀, hK₀F, hK₀Fin, θ₀, W, hW, hact⟩ := hE6
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    exact False.elim ((hType.1 K₀).false θ₀)
  · obtain ⟨K₀, hK₀F, hK₀Fin, θ₀, W, hW, hact⟩ := hE7
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    exact False.elim ((hType.2.1 K₀).false θ₀)
  · obtain ⟨K₀, hK₀F, hK₀Fin, σ₀, hσ₀, θ₀, W, hW, hact⟩ := hTwE6
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    have hK₀ : Nat.card K₀ = (2 ^ e) ^ 2 := hType.2.2 K₀ σ₀ hσ₀ ⟨θ₀⟩
    let Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := θ₀.symm.trans ψ
    let Y : Set (ModGL TwistTag.E6.tag k) :=
      {y : ModGL TwistTag.E6.tag k | y ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom ∧
        ∃ x ∈ S, baseChangeGL (τ := TwistTag.E6.tag) ι y = g⁻¹ * x * g}
    have hY : ∀ y ∈ Y, ∃ hy : y ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom, ∃ w ∈ W,
        ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
          Ψ (RecipeExcLang.twConj K₀ σ₀ w z) =
            (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) * Ψ z *
              (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))⁻¹ := by
      intro y hy
      obtain ⟨hyadj, x, hxS, hxy⟩ := hy
      obtain ⟨y₁, hy₁, hy₁eq, α, hαA, hαact⟩ := huniv x hxS
      have hyy : y₁ = y :=
        baseChangeGL_injective (τ := TwistTag.E6.tag) ι (hy₁eq.trans hxy.symm)
      rw [hyy] at hαact
      obtain ⟨w, hwW, hwact⟩ := hact α hαA
      refine ⟨hyadj, w, hwW, ?_⟩
      intro z
      obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (θ₀.symm z)
      obtain ⟨j₁, hj₁K, hj₁ψ⟩ := hαact j
      obtain ⟨j₂, hj₂K, hj₂θ⟩ := hwact j
      have hj12 : j₁ = j₂ := Subtype.ext (by rw [hj₁K, hj₂K])
      have hz : z = θ₀ (QuotientGroup.mk j) := by rw [hj, MulEquiv.apply_symm_apply]
      rw [hz, ← hj₂θ, ← hj12]
      have hsym : ∀ x : ↥J₀, Ψ (θ₀ (QuotientGroup.mk x)) = ψ (QuotientGroup.mk x) := by
        intro x
        simp only [Ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hsym j₁, hsym j]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hj₁ψ
    have htor := kgLangS1E_normalForm_toral_twE6 he heeven hK₀ hkcard σ₀ hσ₀ σ hσ Ψ ι W hW Y hY
    rcases htor with ⟨h, hhadj, hconj⟩
    change ∃ q : ModGL TwistTag.E6.tag L, q ∈ adjointGroup TwistTag.E6.tag L ∧
      ∀ x ∈ Subgroup.closure S, q⁻¹ * x * q ∈ torusGroup TwistTag.E6.tag L
    refine ⟨g * h, mul_mem hgadj hhadj, ?_⟩
    intro x hx
    have hsub : S ⊆ Subgroup.comap (MulAut.conj (g * h)⁻¹).toMonoidHom
        (torusGroup TwistTag.E6.tag L) := by
      intro x hxS
      obtain ⟨y, hyadj, hyeq, _⟩ := huniv x hxS
      have hyY : y ∈ Y := ⟨hyadj, x, hxS, hyeq⟩
      have h1 : h⁻¹ * (baseChangeGL (τ := TwistTag.E6.tag) ι y) * h ∈
          torusGroup TwistTag.E6.tag L :=
        hconj _ (Subgroup.subset_closure ⟨y, hyY, rfl⟩)
      have hxeq : x = g * baseChangeGL (τ := TwistTag.E6.tag) ι y * g⁻¹ := by
        rw [hyeq]; group
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change (MulAut.conj (g * h)⁻¹) x ∈ torusGroup TwistTag.E6.tag L
      have h2 : (MulAut.conj (g * h)⁻¹) x =
          h⁻¹ * baseChangeGL (τ := TwistTag.E6.tag) ι y * h := by
        rw [hxeq, MulAut.conj_apply, inv_inv]
        group
      rw [h2]
      exact h1
    have hxH := (Subgroup.closure_le
      (Subgroup.comap (MulAut.conj (g * h)⁻¹).toMonoidHom (torusGroup TwistTag.E6.tag L))).mpr
        hsub hx
    rw [Subgroup.mem_comap] at hxH
    change (MulAut.conj (g * h)⁻¹) x ∈ torusGroup TwistTag.E6.tag L at hxH
    rw [MulAut.conj_apply, inv_inv] at hxH
    exact hxH

end CFSG.StandardType
