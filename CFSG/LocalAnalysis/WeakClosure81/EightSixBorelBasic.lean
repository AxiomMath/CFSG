module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G} {S : Type} [Group S]
  {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S} {t₀ : S}

namespace Borel86Data

theorem kGenIn_le (hD : Borel86Data V H T S ψ ρ t₀) : kGenIn V H ≤ H :=
  kGenIn_le_H hD.hyp.le_H

theorem rho_eq_conj (hD : Borel86Data V H T S ψ ρ t₀) (y : ↥H) (k : ↥(kGenIn V H))
    (hyk : (y : G) = k) : ρ y = MulAut.conj (ψ k) := by
  ext s
  obtain ⟨x, rfl⟩ := hD.surj s
  have hmem : (y : G) * x * (y : G)⁻¹ ∈ kGenIn V H := by
    rw [hyk]
    exact mul_mem (mul_mem k.2 x.2) (inv_mem k.2)
  rw [hD.act y x ⟨_, hmem⟩ rfl, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext
  simp [hyk]

theorem exists_mem_not_mem (hD : Borel86Data V H T S ψ ρ t₀) :
    ∃ v ∈ V, v ∉ eCentSet V H T := by
  by_contra hcon
  have hle : V ≤ Subgroup.centralizer (eSub V H T : Set G) := fun v hv => by
    by_contra hv'
    exact hcon ⟨v, hv, hv'⟩
  have h1 := hD.rank
  rw [rankBarV, inf_eq_left.mpr hle, E3.mQuot_self] at h1
  exact absurd h1 (by norm_num)

theorem rho_apply_eq_of_mem_normalizer (hD : Borel86Data V H T S ψ ρ t₀) (y : ↥H)
    (hy : (y : G) ∈ Subgroup.normalizer (V : Set G)) : ρ y t₀ = t₀ := by
  obtain ⟨v, hv, hvE⟩ := hD.exists_mem_not_mem
  have hvK : v ∈ kGenIn V H := le_kGenIn_self V H hv
  have hyv : (y : G) * v * (y : G)⁻¹ ∈ V := (mem_normalizer_iff.mp hy v).mp hv
  have hyvK : (y : G) * v * (y : G)⁻¹ ∈ kGenIn V H := le_kGenIn_self V H hyv
  have hyvE : (y : G) * v * (y : G)⁻¹ ∉ eCentSet V H T := by
    intro hc
    apply hvE
    have h1 := hD.hyp.conj_mem_centralizer_eSub (inv_mem y.2)
      (show (y : G) * v * (y : G)⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) from hc)
    show v ∈ Subgroup.centralizer (eSub V H T : Set G)
    simpa [mul_assoc] using h1
  have h1 := hD.act y ⟨v, hvK⟩ ⟨_, hyvK⟩ rfl
  rwa [hD.root ⟨v, hvK⟩ hv hvE, hD.root ⟨_, hyvK⟩ hyv hyvE] at h1

end Borel86Data

end CFSG.LocalAnalysis.WeakClosure81

end
