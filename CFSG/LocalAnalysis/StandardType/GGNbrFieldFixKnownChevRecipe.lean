module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevInn
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Chev

private theorem chev_fixStd_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem chev_fixStd {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (hord : orderOf f = p) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀,
          GGFixGeom (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f I₀
            θ₀ := by
  obtain ⟨k, hkF, hkFin, hk, hE⟩ := chevFixGroup_recipe hτ hn hK hp hf hord
  obtain ⟨E⟩ := hE
  letI : Field k := hkF
  letI : Finite k := hkFin
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  have hq := chev_isQuasisimple hτ k
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv k τ
  have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false)) := by
    haveI : IsSimpleGroup (AdjointQuotient τ k) := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false), a * b ≠ b * a :=
    chev_fixStd_nonabelian eR.symm hq.2.2
  haveI : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false)) := hsimple
  refine ⟨hsimple, hnab, ?_⟩
  let e : LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false) ≃* ↥(ggFixSub f) :=
    (TableBExc.recipeEquiv τ k).trans E
  exact ggFixGeom_of_inn (I := LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (I₀ := LargeEvenChevIDImage τ.cartan k (LargeEvenChevH τ.cartan k false))
    hnab (TableBExc.center_recipeGroup_eq_bot τ K)
    (chev_idImage_subset_inn hτ hK) (by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_chevIDImage (LargeEvenChevH τ.cartan k false) x) e

end Chev

end CFSG.StandardType

end
