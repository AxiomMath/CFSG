module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic

import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore

public section

namespace CFSG.StandardType

namespace TableBExc.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule


theorem card_ker_dvd_three_e6 {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* RecipeGroup .E6 K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Nat.card ψ.ker ∣ 3 := by
  have hfin : Finite (e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  set f := CFSG.LieType.Steinberg.Isogeny.e6Isogeny K with hf
  set q : e6Data_valid.minGroup K →* RecipeGroup .E6 K :=
    (recipeEquiv .E6 K).symm.toMonoidHom.comp f with hqdef
  have hq : Function.Surjective q := (recipeEquiv .E6 K).symm.surjective.comp
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* e6Data_valid.minGroup K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : e6Data_valid.minGroup K →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hcen => LayerCycExc.e6_minGroup_exists_section hK E π hπ hcen
  have h1 := E6ThreeKernel.card_ker_dvd_of_split hq hsplit hψ hker hperf
  have hqk : q.ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
    intro z hz
    have hz' : z ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hz ⊢
      have h2 : (recipeEquiv .E6 K).symm (f z) = 1 := hz
      rwa [MulEquiv.map_eq_one_iff] at h2
    rwa [hf, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center] at hz'
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
  have h3 : Nat.card (Subgroup.center (e6Data_valid.minGroup K)) ∣ 3 := by
    rw [hcard]
    exact Nat.gcd_dvd_left 3 _
  exact h1.trans ((Subgroup.card_dvd_of_le hqk).trans h3)

end TableBExc.E6Three

end CFSG.StandardType
