module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutPowerMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SL3TwoAutPowerMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem k_SL3TwoAutPowerMap_holds :
    K_SL3TwoAutPowerMap := by
  intro Y _ _ n hSL3 hodd S hS θ hpow hθS hfix
  classical
  obtain ⟨hq, hL3⟩ := hSL3
  have hn : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hL3).2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
  let U : Sylow 2 Y := hS.isPGroup.toSylow hidx
  have hU : (U : Subgroup Y) = S := IsPGroup.toSylow_coe hS.isPGroup hidx
  obtain ⟨K, hKf, hKfin, hKchar, αc, hcard, hα, hαc, hαU⟩ :=
    exists_cover_sylow_of_odd_center hq hL3 hodd U
  haveI : CharP K 2 := hKchar
  have hαU' : (unitriangular 3 K).map αc = S := by rw [hαU, hU]
  have hoddker : Odd (Nat.card αc.ker) :=
    odd_card_ker_of_le_scalars (n := 3) (by norm_num) hαc
  have hφU : ∀ x, x ∈ (unitriangular 3 K).map αc ↔
      θ x ∈ (unitriangular 3 K).map αc := by
    intro x
    rw [hαU']
    constructor
    · intro hx
      rw [← hθS]
      exact Subgroup.mem_map_of_mem θ.toMonoidHom hx
    · intro hx
      have hx' : θ x ∈ S.map θ.toMonoidHom := by rw [hθS]; exact hx
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := θ.injective hyx
      rwa [hyx'] at hy
  obtain ⟨ν, hνα, hνU⟩ :=
    exists_lift_sl3_of_odd_cover αc hα hαc hoddker θ hφU
  have hνQ : ∀ d : ℕ, 1 ≤ d → d < 3 →
      (stabilizer (flagSpace 3 K d)).map ν.toMonoidHom =
        stabilizer (flagSpace 3 K d) := by
    intro d hd hdn
    have hmax : IsMaxParabolicOver (⊤ : Subgroup Y) S
        ((stabilizer (flagSpace 3 K d)).map αc) := by
      have h := isMaxParabolicOver_image_stabilizer αc hα hαc hd hdn
      rwa [hαU'] at h
    have hfixP := hfix _ hmax
    exact map_eq_of_map_map_eq hα (hαc.trans (scalars_le_stabilizer _)) hνα hfixP
  obtain ⟨j, hj⟩ :=
    sl3_powerMap_of_fixes_flagParabolics ν hνU (hνQ 1 (by norm_num) (by norm_num))
      (hνQ 2 (by norm_num) (by norm_num))
  refine ⟨j, fun x hx => ?_⟩
  have hx' : x ∈ normalizer (((unitriangular 3 K).map αc : Subgroup Y) : Set Y) := by
    rwa [hαU']
  obtain ⟨e, he, hxe⟩ :=
    uc22pwI3_exists_torus_of_mem_normalizer αc hα
      (hαc.trans (scalars_le_center 3 K)) hx'
  obtain ⟨u, hu, hue⟩ := hxe
  have hxeq : x = αc u * αc e := by rw [hue]; group
  let b : Matrix.SpecialLinearGroup (Fin 3) K :=
    (u : Matrix.SpecialLinearGroup (Fin 3) K) *
      (e : Matrix.SpecialLinearGroup (Fin 3) K)
  have hbB : b ∈ upperTriangular (n := 3) (K := K) :=
    (upperTriangular (n := 3) (K := K)).mul_mem
      ((unitriangular_le_upperTriangular (n := 3) (K := K)) hu)
      (diagonalTorus_le_upperTriangular he)
  have hbN : b ∈ normalizer
      (((unitriangular (n := 3) (K := K) : Subgroup _) : Set _)) := by
    rw [normalizer_unitriangular]
    exact hbB
  have hpowb : ν b * (b ^ 2 ^ j)⁻¹ ∈ unitriangular (n := 3) (K := K) := hj b hbN
  have hxb : x = αc b := by rw [hxeq, ← map_mul]
  have hfirst : θ x * (x ^ 2 ^ j)⁻¹ =
      αc (ν b) * (αc (b ^ 2 ^ j))⁻¹ := by
    rw [hxb, ← hνα b, map_pow]
  have hmem : αc (ν b * (b ^ 2 ^ j)⁻¹) ∈ S := by
    rw [← hαU']
    exact Subgroup.mem_map_of_mem αc hpowb
  rw [hfirst, ← map_inv, ← map_mul]
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
