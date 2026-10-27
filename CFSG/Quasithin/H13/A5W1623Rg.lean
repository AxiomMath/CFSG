module

public import CFSG.Quasithin.H13.A5W1623Rad
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.H13.Ln2P

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic CFSG.Quasithin

theorem entry_of_mem_flagRadical {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (h : u ∈ flagRadical 4 (ZMod 2) 2) (i j : Fin 4)
    (hij : (j : ℕ) < 2 ∨ (2 ≤ (i : ℕ) ∧ 2 ≤ (j : ℕ))) :
    (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := h
  rcases hij with hj | ⟨hi, -⟩
  · have e := congrFun (h1 _ (single_mem_flagSpace (K := ZMod 2) hj)) i
    rw [mulVec_single_one] at e
    simpa [Pi.single_apply] using e
  · have e := (mem_flagSpace.mp (h2 (Pi.single j 1))) i hi
    rw [Pi.sub_apply, mulVec_single_one, sub_eq_zero] at e
    simpa [Pi.single_apply] using e

theorem mem_unitriangular_of_mem_flagRadical {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (h : u ∈ flagRadical 4 (ZMod 2) 2) :
    u ∈ unitriangular 4 (ZMod 2) ∧ (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1 = 0 ∧
      (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 = 0 := by
  have he := entry_of_mem_flagRadical h
  refine ⟨mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hij (by decide)
        | exact he _ _ (by decide)
  · fin_cases i <;> exact he _ _ (by decide)
  · exact he 0 1 (by decide)
  · exact he 2 3 (by decide)

theorem graphAut_mem_flagRadical {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (h : u ∈ flagRadical 4 (ZMod 2) 2) : graphAut 4 u ∈ flagRadical 4 (ZMod 2) 2 := by
  have hi := mem_unitriangular_of_mem_flagRadical (Subgroup.inv_mem _ h)
  refine mem_flagRadical_of_entries (graphFun_mem_unitriangular
    (mem_unitriangular_of_mem_flagRadical h).1) ?_ ?_
  · rw [graphAut_apply, coe_graphFun, submatrix_apply, transpose_apply]
    exact hi.2.2
  · rw [graphAut_apply, coe_graphFun, submatrix_apply, transpose_apply]
    exact hi.2.1

theorem isSylowTwoOf_unitriangular_four :
    CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 4 (ZMod 2))
      (⊤ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 4) (by norm_num)
  rw [← hP]
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))).subgroupOf ⊤).index =
    (P : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))).index from
      Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

theorem pCoreOf_le_flagRadical :
    pCoreOf 2 (flagStabilizer 4 (ZMod 2) {2}) ≤ flagRadical 4 (ZMod 2) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := flagStabilizer 4 (ZMod 2) {2} with hQ₂
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 4 (ZMod 2)) Q₂ :=
    CFSG.QuasithinUnique.isSylowTwoOf_of_le isSylowTwoOf_unitriangular_four
      (unitriangular_le_flagStabilizer _)
  have hOU : pCoreOf 2 Q₂ ≤ unitriangular 4 (ZMod 2) := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hON := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Q₂
  have hO2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Q₂
  have hcomm : ∀ {u d : SpecialLinearGroup (Fin 4) (ZMod 2)}, u ∈ pCoreOf 2 Q₂ → d ∈ Q₂ →
      u * d * u⁻¹ * d⁻¹ ∈ pCoreOf 2 Q₂ := by
    intro u d hu hd
    have h1 : d * u⁻¹ * d⁻¹ ∈ pCoreOf 2 Q₂ :=
      (Subgroup.mem_normalizer_iff.mp (hON hd) u⁻¹).mp (Subgroup.inv_mem _ hu)
    rw [show u * d * u⁻¹ * d⁻¹ = u * (d * u⁻¹ * d⁻¹) by group]
    exact Subgroup.mul_mem _ hu h1
  intro u hu
  by_contra hR
  rcases pow_twelve_inner (hOU hu) hR with ⟨h12, h4⟩ | ⟨h12, h4⟩
  · obtain ⟨e, he⟩ := hO2 ⟨_, hcomm hu levi1_mem⟩
    exact false_of_pow_twelve h12 h4 (by simpa using congrArg Subtype.val he)
  · obtain ⟨e, he⟩ := hO2 ⟨_, hcomm hu levi3_mem⟩
    exact false_of_pow_twelve h12 h4 (by simpa using congrArg Subtype.val he)

end CFSG.Quasithin.H13.Ln2P
