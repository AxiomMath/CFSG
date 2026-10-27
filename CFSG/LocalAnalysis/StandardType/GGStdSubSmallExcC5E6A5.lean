module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Orb
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Count
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc.E6Three E6TwoPilot E6ThreeEnd

@[expose] def coord0E6 : Multiplicative (Fin 4 → ZMod 3) →* Multiplicative (ZMod 3) where
  toFun w := Multiplicative.ofAdd (Multiplicative.toAdd w 0)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mem_ker_coord0E6 (w : Multiplicative (Fin 4 → ZMod 3)) :
    w ∈ coord0E6.ker ↔ Multiplicative.toAdd w 0 = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (Multiplicative.toAdd w 0) = 1 ↔ _
  exact ofAdd_eq_one

theorem card_ker_coord0E6 : Nat.card coord0E6.ker = 27 := by
  have hs : Function.Surjective coord0E6 := fun a =>
    ⟨Multiplicative.ofAdd (Pi.single 0 (Multiplicative.toAdd a)), by
      change Multiplicative.ofAdd (Multiplicative.toAdd (Multiplicative.ofAdd
        (Pi.single 0 (Multiplicative.toAdd a) : Fin 4 → ZMod 3)) 0) = a
      simp⟩
  have h := Subgroup.card_ker_mul_card_of_surjective hs
  have h1 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h2 : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [h1, h2] at h
  omega

section Count

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem neg_bE6_mem_perpB0 {k : Fin 4} (hk : k ≠ 0) : -bE6 k ∈ perpB0 :=
  ⟨isRoot_neg_bE6 k, by rw [iform_neg_left, (iform_bE6 k 0 hk).1, neg_zero]⟩

theorem uE6Two_mem_leviB0 {k : Fin 4} (hk : k ≠ 0) : uE6Two (K := K) k ∈ leviB0 K := by
  rw [leviB0, Subgroup.mem_subgroupOf]
  exact mul_mem (pinnedX_mem_rootSpan (bE6_mem_perpB0 hk) 1)
    (pinnedX_mem_rootSpan (neg_bE6_mem_perpB0 hk) 1)

theorem torusE6Two_mem_leviB0 (h2 : (2 : K) = 0) {w : Multiplicative (Fin 4 → ZMod 3)}
    (hw : Multiplicative.toAdd w 0 = 0) : torusE6Two h2 w ∈ leviB0 K :=
  torusE6Two_mem_of_coord_zero h2 0 (fun _ hi => uE6Two_mem_leviB0 hi) w hw

theorem nodeCount_u0 (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    NodeCount 3 (torusE6Two (K := K) h2).range (uE6Two 0) := by
  intro _ _
  have hfin : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  rw [(largeEvenLayer_centralizer_uE6Two_zero hK).1]
  have hle : coord0E6.ker.map (torusE6Two h2) ≤ (torusE6Two (K := K) h2).range ⊓ leviB0 K := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, rfl⟩, torusE6Two_mem_leviB0 h2 ((mem_ker_coord0E6 w).mp hw)⟩
  calc 3 ^ 3 = Nat.card (coord0E6.ker.map (torusE6Two h2)) := by
        rw [Subgroup.card_map_of_injective (torusE6Two_injective h2), card_ker_coord0E6]
        norm_num
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem nodeCount_norm_one (h2 : (2 : K) = 0) (hK : Nat.card K = 2) {v : Fin 4 → ZMod 3}
    (hv : normE6 v = 1) :
    NodeCount 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd v)) := by
  obtain ⟨g, hg, hgv⟩ := inOrbit_of_reachB h2 e0E6 4 v (reachB_one v hv)
  have hu : torusE6Two h2 (.ofAdd e0E6) = uE6Two (K := K) 0 := by
    rw [e0E6, torusE6Two_single, zmodPowHom_apply, ZMod.val_one, pow_one]
  rw [hu] at hgv
  exact nodeCount_of_normalizer hg hgv (nodeCount_u0 h2 hK)

end Count

end CFSG.StandardType.SmallExc

end
