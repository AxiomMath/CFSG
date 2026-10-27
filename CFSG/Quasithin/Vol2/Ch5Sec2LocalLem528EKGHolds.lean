module

public import CFSG.Quasithin.Background.SL3SmallGroup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.SL3Small Matrix
open scoped MatrixGroups

theorem factSL3SmallModule_holds : FactSL3SmallModule := by
  intro G _ _ Y R _ F _ _ m hm hF hRY hR2 hcard hiso hfaith
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥R) := ⟨hR2⟩
  have := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) hFc
  obtain ⟨κ, hκs, hκ1, hκker⟩ := exists_kappa hiso
  obtain ⟨ψ, hψ, σ, hσs, hσk, hΦσ, hσe⟩ := exists_sigma hRY hFc hm hcard κ hκs hκ1 hfaith
  have hinv : ∀ g : SL(3, F), ∃ y : ↥Y, ∀ r, Multiplicative.toAdd (σ (SL3Small.conjAut hRY y r)) =
      ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (σ r) := by
    intro g
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (κ (ψ g))
    exact ⟨y, fun r => by rw [hσe (ψ g) y hy r, hψ]⟩
  have hΦ : frattini ↥R = ⊥ := frattini_eq_bot hRY hFc hm hcard σ hσs hΦσ hinv
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ∀ x : Fin 3 → F, ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
      intro x
      obtain ⟨r, hr⟩ := hσs (Multiplicative.ofAdd x)
      have h2 := hσe g 1 (by rw [hg]; rfl) r
      rw [map_one, MulAut.one_apply, hr, toAdd_ofAdd] at h2
      exact h2.symm
    have h2 : ψ g = 1 := by
      have hm : ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
        ext i j
        have h3 := congrFun (h1 (Pi.single j 1)) i
        rw [mulVec_single_one] at h3
        simpa [Matrix.one_apply, Pi.single_apply] using h3
      exact Subtype.ext hm
    have h3 := congrArg ψ h2
    rwa [hψ, map_one] at h3
  let e₁ : ↥Y ⧸ R.subgroupOf Y ≃* SL(3, F) := (MulEquiv.ofBijective κ ⟨hκinj, hκs⟩).symm
  have he₁ : ∀ q, κ (e₁ q) = q := fun q => (MulEquiv.ofBijective κ ⟨hκinj, hκs⟩).apply_symm_apply q
  let ψe : SL(3, F) ≃* SL(3, F) :=
    { ψ with invFun := ψ, left_inv := hψ, right_inv := hψ }
  refine ⟨fun r hr => ?_, e₁.trans ψe, σ, hσs, fun r hr y hy => ?_, fun y r r' hr' => ?_⟩
  ·
    obtain ⟨-, -, hsq, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient
      (Fact.out : IsPGroup 2 ↥R)
    have h1 := hsq ((⟨r, hr⟩ : ↥R) : ↥R ⧸ frattini ↥R)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hΦ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  ·
    have h1 := hσk r (MonoidHom.mem_ker.mp hr) ⟨y, hy⟩
    rw [hΦ, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact congrArg Subtype.val h1
  ·
    have hr'' : r' = SL3Small.conjAut hRY y r := Subtype.ext hr'
    rw [hr'', hσe (e₁ (QuotientGroup.mk y)) y (he₁ _).symm r]
    rfl

end CFSG.Quasithin.H13
