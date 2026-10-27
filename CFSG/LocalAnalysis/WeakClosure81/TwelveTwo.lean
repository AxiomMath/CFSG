module

public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartOne
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSumSecSz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem twelveTwo_one_top (hNat : NatSumL2Input)
    (hMart : CFSG.RankThree.GF2n.MartineauSzInput) {G : Type} [Group G] (ρ : G →* LGL 2 V)
    (B : Subgroup G) (Z : Submodule (ZMod 2) V) (A : Subgroup G) (n m : ℕ)
    (hS : Setting12One ρ B Z A n m) (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤) :
    IsSumNatSection ρ ⊥ (commSub ((⊤ : Subgroup G).map ρ)) (cE ((⊤ : Subgroup G).map ρ)) n := by
  haveI : Finite G := rankOne_finite hS.type
  have hK : (⊤ : Subgroup G).map ρ = ρ.range := (MonoidHom.range_eq_map ρ).symm
  rw [hK]
  have h₁ : ∀ g : G, ∀ w ∈ commSub ρ.range, ρ g w ∈ commSub ρ.range :=
    fun g w hw => map_mem_commSub (A := ρ.range) ⟨g, rfl⟩ hw
  have h₂ : ∀ g : G, ∀ w ∈ cE ρ.range, ρ g w ∈ cE ρ.range :=
    fun g w hw => map_mem_cE ρ.range ⟨g, rfl⟩ hw
  have hW : cE ρ.range ≤ commSub ρ.range := cE_le_commSub _
  rcases hS.type with hPSL | hSz
  · obtain ⟨u, v, hu, hv, hord⟩ := rankOne_exists_pair_three hPSL
    have huv1 : u * v ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hfpf := twelveOne_fix_of_involutions hS hmin hu hv (by rw [hord]; decide) huv1
    exact isSumNatSection_of_fpf_psl hNat hPSL ρ hW h₁ h₂ hord hfpf
  · obtain ⟨u, v, hu, hv, hord⟩ := rankOne_exists_pair_five hSz
    have huv1 : u * v ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hfpf := twelveOne_fix_of_involutions hS hmin hu hv (by rw [hord]; decide) huv1
    exact isSumNatSection_of_fpf_sz hMart hSz ρ hW h₁ h₂ hord hfpf

end CFSG.LocalAnalysis.WeakClosure81
