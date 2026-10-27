module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame

import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowA
import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowB
import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowC
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three
open CFSG.LieType.Steinberg (commutatorElement_mul_mul_of_mem_center)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem eFrame_zl_row {n : ℕ} (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ Nat.card K - 1) (ζ : Kˣ)
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (w : Fin 6 → L')
    (hw : ∀ i, ψ (w i) = (eFrame K ζ hζ).nb i) :
    ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ (eFrame K ζ hζ).V0) ∧
      ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) := by
  have hfin : Finite (e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* e6Data_valid.minGroup K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : e6Data_valid.minGroup K →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hcen => LayerCycExc.e6_minGroup_exists_section hK E π hπ hcen
  obtain ⟨α, hα, hαs⟩ :=
    E6ThreeKernel.exists_surjective_of_split (e6Isogeny_surjective K) hsplit hψ hker hperf
  have hcomm : ∀ i, ⁅w i, α (e6Data_valid.hm K i ζ)⁆ = α (e6Data_valid.hm K i ζ) := by
    intro i
    have hz : w i * (α (e6Data_valid.nm K i))⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hw i, zl_nb_eq ζ hζ i, mul_inv_cancel]
    calc ⁅w i, α (e6Data_valid.hm K i ζ)⁆
        = ⁅(w i * (α (e6Data_valid.nm K i))⁻¹) * α (e6Data_valid.nm K i),
            1 * α (e6Data_valid.hm K i ζ)⁆ := by
          rw [inv_mul_cancel_right, one_mul]
      _ = ⁅α (e6Data_valid.nm K i), α (e6Data_valid.hm K i ζ)⁆ :=
          commutatorElement_mul_mul_of_mem_center (hker hz) (Subgroup.one_mem _) _ _
      _ = α (e6Data_valid.hm K i ζ) := by
          rw [← map_commutatorElement, zl_comm_nm_hm ζ hζ i]
  have hfun : (fun i => ⁅w i, α (e6Data_valid.hm K i ζ)⁆) =
      fun i => α (e6Data_valid.hm K i ζ) := funext hcomm
  refine ⟨fun i => α (e6Data_valid.hm K i ζ), fun i => ?_, ?_⟩
  · show ψ (α (e6Data_valid.hm K i ζ)) ∈ (eFrame K ζ hζ).V0
    rw [hα]
    exact zl_hm_mem_V0 ζ hζ i
  · rw [hfun]
    set C := Subgroup.closure (Set.range fun i => α (e6Data_valid.hm K i ζ)) with hC
    have hS : ∀ i, e6Data_valid.hm K i ζ ∈ C.comap α := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    have hz : minTorus e6Data_valid K (zetaVec ζ hζ kappa) ∈ C.comap α :=
      zl_minTorus_kappa_mem ζ hζ _ hS
    have hkerS : (e6Isogeny K).ker ≤ C.comap α := by
      rw [zl_ker_isogeny_eq_zpowers h3 ζ hζ hζo, Subgroup.zpowers_le]
      exact hz
    intro y hy
    obtain ⟨s, rfl⟩ := hαs y
    have hs : s ∈ (e6Isogeny K).ker := by
      rw [MonoidHom.mem_ker, ← hα]
      exact (MonoidHom.mem_ker).1 hy
    exact hkerS hs

end CFSG.StandardType.E6Dep.ZL

end
