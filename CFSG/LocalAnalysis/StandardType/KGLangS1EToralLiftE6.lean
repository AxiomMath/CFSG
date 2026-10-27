module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EModelE6
public import CFSG.LocalAnalysis.StandardType.KGLangS1ETypeDetE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc

theorem kgLangS1E_toral_lift_E6
    {n : ℕ} (hn : 1 ≤ n) {K₁ : Type} [Field K₁] [Finite K₁] (hK₁ : Nat.card K₁ = 2 ^ n)
    (hodd : Odd n)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hen : e * 3 = n)
    (ρ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) →* ModGL .E6 L)
    (Θ : ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)))
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL .E6 L) * ρ r * (g : ModGL .E6 L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) = (endPow (frobTwistGL .E6 L 2 e 1) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenChevH (LargeEvenCartanE 6) K₁ false))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ))
    (hTor : GGExcToralAct J₀ (A : Set (MulAut K))) :
    ExcFramesHalf.IsToralSubgroup .E6 L (Subgroup.closure {x : ModGL .E6 L |
      x ∈ ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3) ∧ ∃ α ∈ A,
        kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
          (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}) := by
  let S : Set (ModGL .E6 L) :=
    {x : ModGL .E6 L | x ∈ ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3) ∧
      ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
          (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) ∧
        ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}
  change ExcFramesHalf.IsToralSubgroup .E6 L (Subgroup.closure S)
  have heodd : Odd e := by
    rw [← hen] at hodd
    exact (Nat.odd_mul.mp hodd).1
  obtain ⟨k, hkF, hkFin, ι, g, hkcard, hgadj, ψ, huniv⟩ :=
    kgLangS1E_J0_model_E6 hn hK₁ hodd he hen ρ Θ hρ hρG hΘ hI hconjΘ hFj θ hcomm A hA hAI hξ hξI hJ₀
  letI : Field k := hkF
  letI : Finite k := hkFin
  have hType := kgLangS1E_typeDet_E6 he hkcard ψ
  rcases hTor with hE6 | hE7 | hTwE6
  · obtain ⟨K₀, hK₀F, hK₀Fin, θ₀, W, hW, hact⟩ := hE6
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    have hK₀ : Nat.card K₀ = 2 ^ e := hType.2.2 K₀ ⟨θ₀⟩
    let Ψ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k) := θ₀.symm.trans ψ
    let Y : Set (ModGL .E6 k) :=
      {y : ModGL .E6 k | y ∈ adjointGroup .E6 k ∧
        ∃ x ∈ S, baseChangeGL (τ := .E6) ι y = g⁻¹ * x * g}
    have hY : ∀ y ∈ Y, ∃ hy : y ∈ adjointGroup .E6 k, ∃ w ∈ W,
        ∀ z : ↥(adjointGroup .E6 K₀),
          Ψ (RecipeExcLang.inndiagConj .E6 K₀ w z) =
            (⟨y, hy⟩ : ↥(adjointGroup .E6 k)) * Ψ z *
              (⟨y, hy⟩ : ↥(adjointGroup .E6 k))⁻¹ := by
      intro y hy
      obtain ⟨hyadj, x, hxS, hxy⟩ := hy
      obtain ⟨y₁, hy₁, hy₁eq, α, hαA, hαact⟩ := huniv x hxS
      have hyy : y₁ = y := baseChangeGL_injective (τ := .E6) ι (hy₁eq.trans hxy.symm)
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
      exact Subtype.ext (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hj₁ψ)
    have htor := kgLangS1E_normalForm_toral_E6 he heodd hK₀ hkcard Ψ ι W hW Y hY
    rcases htor with ⟨h, hhadj, hconj⟩
    change ∃ q : ModGL .E6 L, q ∈ adjointGroup .E6 L ∧
      ∀ x ∈ Subgroup.closure S, q⁻¹ * x * q ∈ torusGroup .E6 L
    refine ⟨g * h, mul_mem hgadj hhadj, ?_⟩
    intro x hx
    have hsub : S ⊆ Subgroup.comap (MulAut.conj (g * h)⁻¹).toMonoidHom
        (torusGroup .E6 L) := by
      intro x hxS
      obtain ⟨y, hyadj, hyeq, _⟩ := huniv x hxS
      have hyY : y ∈ Y := ⟨hyadj, x, hxS, hyeq⟩
      have h1 : h⁻¹ * (baseChangeGL (τ := .E6) ι y) * h ∈ torusGroup .E6 L :=
        hconj _ (Subgroup.subset_closure ⟨y, hyY, rfl⟩)
      have hxeq : x = g * baseChangeGL (τ := .E6) ι y * g⁻¹ := by rw [hyeq]; group
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change (MulAut.conj (g * h)⁻¹) x ∈ torusGroup .E6 L
      have h2 : (MulAut.conj (g * h)⁻¹) x =
          h⁻¹ * baseChangeGL (τ := .E6) ι y * h := by
        rw [hxeq, MulAut.conj_apply, inv_inv]
        group
      rw [h2]
      exact h1
    have hxH := (Subgroup.closure_le
      (Subgroup.comap (MulAut.conj (g * h)⁻¹).toMonoidHom (torusGroup .E6 L))).mpr hsub hx
    rw [Subgroup.mem_comap] at hxH
    change (MulAut.conj (g * h)⁻¹) x ∈ torusGroup .E6 L at hxH
    rw [MulAut.conj_apply, inv_inv] at hxH
    exact hxH
  · obtain ⟨K₀, hK₀F, hK₀Fin, θ₀, W, hW, hact⟩ := hE7
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    exact False.elim ((hType.1 K₀).false θ₀)
  · obtain ⟨K₀, hK₀F, hK₀Fin, σ, hσ, θ₀, W, hW, hact⟩ := hTwE6
    letI : Field K₀ := hK₀F
    letI : Finite K₀ := hK₀Fin
    exact False.elim ((hType.2.1 K₀ σ hσ).false θ₀)


end CFSG.StandardType
