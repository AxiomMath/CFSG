module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGX
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineTransport
import CFSG.LieType.Chevalley.EvenTrialityParameterData
import CFSG.RankThree.PartOne.KGD.D4T36Core

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure TriD4LineKGXData (n : ℕ) (K : Type) [Field K] (k : Type) [Field k] [Algebra k K] where
  z₀ : GGTriD4R n K
  α : MulAut (GGTriD4R n K)
  σ : K ≃ₐ[k] K
  Θ : Subgroup.centralizer {z₀} ≃* TriD4LineX k K
  orderOf_z₀ : orderOf z₀ = 3
  sylow_z₀ : ∃ P : Sylow 3 (GGTriD4R n K), z₀ ∈ (P : Subgroup (GGTriD4R n K)) ∧
    ∀ y ∈ (P : Subgroup (GGTriD4R n K)), y * z₀ = z₀ * y
  α_outer : α ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut _)
  orderOf_α : orderOf α = 3
  α_z₀ : α z₀ = z₀
  orderOf_σ : orderOf σ = 3
  Θ_α : ∀ (y : Subgroup.centralizer {z₀}) (hy : α y ∈ Subgroup.centralizer {z₀}),
    (Θ ⟨α y, hy⟩ : TriD4LineX k K) = triD4LineSigma k K σ (Θ y)

@[expose] noncomputable abbrev triD4LineE (n : ℕ) (K : Type) [Field K]
    (A : Subgroup (MulAut (GGTriD4R n K))) : Subgroup (GGTriD4R n K) :=
  A.comap (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K))

theorem mem_triD4LineE {n : ℕ} {K : Type} [Field K] {A : Subgroup (MulAut (GGTriD4R n K))}
    {e : GGTriD4R n K} : e ∈ triD4LineE n K A ↔ MulAut.conj e ∈ A :=
  Iff.rfl

theorem triD4Line_kgXData
    {n : ℕ} (K : Type) [Field K] (hev : Even n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n) :
    Nonempty (TriD4LineKGXData n K k) := by
  obtain ⟨z₀, α, σ, Θ, h1, h2, h3, h4, h5, h6, h7⟩ := triD4Line_kgX K hev hK k hk
  exact ⟨⟨z₀, α, σ, Θ, h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem triD4Line_exists_subfield {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k K), Nat.card k = 2 ^ n := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [pow_zero, one_pow] at hK
      haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
      have h2 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hn
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
  refine ⟨↥(CFSG.LieType.Chevalley.trialityFixedField K σ.toRingHom), inferInstance,
    inferInstance, ?_⟩
  exact CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hn hK σ hσ

@[expose] def triD4LineAlt (n : ℕ) (K : Type) [Field K] (A : Subgroup (MulAut (GGTriD4R n K)))
    (a₀ : MulAut (GGTriD4R n K)) : Prop :=
  (∃ m : GGTriD4R n K, (∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧
      ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
    MulAut.conj m * a₀ * (MulAut.conj m)⁻¹ ∉ Subgroup.zpowers a₀) ∨
  ∃ f ∈ A, f ∉ Subgroup.zpowers a₀ ∧
    ∀ J₁ : Subgroup (GGTriD4R n K), IsComponentOf J₁ (ggFix a₀) → ∀ l ∈ J₁, f l = l

theorem ggTriD4LineWeylStrong_iff (n : ℕ) (K : Type) [Field K] :
    GGTriD4LineWeylStrong n K ↔
      ∀ A : Subgroup (MulAut (GGTriD4R n K)), IsElemAbelian 3 A → 27 ≤ Nat.card A →
        ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ GGTriD4ID n K → triD4LineAlt n K A a₀ :=
  Iff.rfl

end CFSG.StandardType
