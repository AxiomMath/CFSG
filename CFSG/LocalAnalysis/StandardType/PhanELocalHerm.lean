module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Module

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem herm_apply (u v : Fin 3 → K) :
    hermLin K f 3 0 3 u v = ∑ i, sg K f (u i) * v i := by
  rw [hermLin, LinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [i.isLt]

theorem herm_add_left (u u' v : Fin 3 → K) :
    hermLin K f 3 0 3 (u + u') v = hermLin K f 3 0 3 u v + hermLin K f 3 0 3 u' v := by
  simp [herm_apply, Finset.sum_add_distrib, add_mul]

theorem herm_smul_left (c : K) (u v : Fin 3 → K) :
    hermLin K f 3 0 3 (c • u) v = sg K f c * hermLin K f 3 0 3 u v := by
  simp [herm_apply, Finset.mul_sum, mul_assoc]

theorem herm_add_right (u v v' : Fin 3 → K) :
    hermLin K f 3 0 3 u (v + v') = hermLin K f 3 0 3 u v + hermLin K f 3 0 3 u v' :=
  map_add (hermLin K f 3 0 3 u) v v'

theorem herm_smul_right (c : K) (u v : Fin 3 → K) :
    hermLin K f 3 0 3 u (c • v) = c * hermLin K f 3 0 3 u v := by
  simpa using map_smul (hermLin K f 3 0 3 u) c v

theorem herm_symm (hK : Nat.card K = (2 ^ f) ^ 2) (u v : Fin 3 → K) :
    hermLin K f 3 0 3 v u = sg K f (hermLin K f 3 0 3 u v) := by
  rw [herm_apply, herm_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_mul, sg_sg hK]
  exact mul_comm _ _

theorem herm_self_fixed (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin 3 → K) :
    sg K f (hermLin K f 3 0 3 v v) = hermLin K f 3 0 3 v v :=
  (herm_symm hK v v).symm

theorem herm_nondeg {v : Fin 3 → K} (h : ∀ u : Fin 3 → K, hermLin K f 3 0 3 u v = 0) : v = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [herm_apply] at h1
  have hsingle : (∑ j, sg K f ((Pi.single i (1 : K) : Fin 3 → K) j) * v j) = v i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne' hji.symm, map_zero, zero_mul]
  rw [hsingle] at h1
  exact h1

theorem mem_perpB_iff (U : Submodule K (Fin 3 → K)) (v : Fin 3 → K) :
    v ∈ perpB K f 3 0 3 U ↔ ∀ u ∈ U, hermLin K f 3 0 3 u v = 0 := by
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]

theorem span_inf_perpB_eq_bot_iff {v : Fin 3 → K} (hv : v ≠ 0) :
    Submodule.span K {v} ⊓ perpB K f 3 0 3 (Submodule.span K {v}) = ⊥ ↔
      hermLin K f 3 0 3 v v ≠ 0 := by
  constructor
  · intro hinf hvv
    have hvperp : v ∈ perpB K f 3 0 3 (Submodule.span K {v}) := by
      rw [mem_perpB_iff]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [herm_smul_left, hvv, mul_zero]
    have hmem : v ∈ Submodule.span K {v} ⊓ perpB K f 3 0 3 (Submodule.span K {v}) :=
      ⟨Submodule.mem_span_singleton_self v, hvperp⟩
    rw [hinf] at hmem
    exact hv (by simpa using hmem)
  · intro hvv
    rw [Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_inf] at hu
    obtain ⟨huspan, huperp⟩ := hu
    rw [Submodule.mem_span_singleton] at huspan
    obtain ⟨c, rfl⟩ := huspan
    rw [mem_perpB_iff] at huperp
    have h0 : hermLin K f 3 0 3 v (c • v) = 0 :=
      huperp v (Submodule.mem_span_singleton_self v)
    rw [herm_smul_right] at h0
    have hc : c = 0 := (mul_eq_zero.mp h0).resolve_right hvv
    rw [hc, zero_smul]

theorem sup_inf_perpB_eq_bot_of_gram {x y : Fin 3 → K}
    (hg : hermLin K f 3 0 3 x x * hermLin K f 3 0 3 y y ≠
      hermLin K f 3 0 3 x y * hermLin K f 3 0 3 y x) :
    (Submodule.span K {x} ⊔ Submodule.span K {y}) ⊓
      perpB K f 3 0 3 (Submodule.span K {x} ⊔ Submodule.span K {y}) = ⊥ := by
  set A := hermLin K f 3 0 3 x x with hA
  set B := hermLin K f 3 0 3 x y with hB
  set C := hermLin K f 3 0 3 y x with hC
  set D := hermLin K f 3 0 3 y y with hD
  have hg' : A * D - B * C ≠ 0 := sub_ne_zero.mpr hg
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_inf, Submodule.mem_sup] at hu
  obtain ⟨huM, huperp⟩ := hu
  obtain ⟨a, ha, b, hb, hab⟩ := huM
  rw [Submodule.mem_span_singleton] at ha hb
  obtain ⟨α, rfl⟩ := ha
  obtain ⟨β, rfl⟩ := hb
  rw [← hab] at huperp ⊢
  rw [mem_perpB_iff] at huperp
  set M := Submodule.span K {x} ⊔ Submodule.span K {y} with hM
  have hxM : x ∈ M :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
  have hyM : y ∈ M :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  have h1 : α * A + β * B = 0 := by
    have h := huperp x hxM
    rwa [herm_add_right, herm_smul_right, herm_smul_right] at h
  have h2 : α * C + β * D = 0 := by
    have h := huperp y hyM
    rwa [herm_add_right, herm_smul_right, herm_smul_right] at h
  have hα : α * (A * D - B * C) = 0 := by linear_combination D * h1 - B * h2
  have hβ : β * (A * D - B * C) = 0 := by linear_combination A * h2 - C * h1
  have hα0 : α = 0 := (mul_eq_zero.mp hα).resolve_right hg'
  have hβ0 : β = 0 := (mul_eq_zero.mp hβ).resolve_right hg'
  rw [hα0, hβ0, zero_smul, zero_smul, add_zero]

theorem finrank_span_pair_of_gram {x y : Fin 3 → K}
    (hg : hermLin K f 3 0 3 x x * hermLin K f 3 0 3 y y ≠
      hermLin K f 3 0 3 x y * hermLin K f 3 0 3 y x) :
    finrank K ↥(Submodule.span K {x} ⊔ Submodule.span K {y}) = 2 := by
  set A := hermLin K f 3 0 3 x x with hA
  set B := hermLin K f 3 0 3 x y with hB
  set C := hermLin K f 3 0 3 y x with hC
  set D := hermLin K f 3 0 3 y y with hD
  have hg' : A * D - B * C ≠ 0 := sub_ne_zero.mpr hg
  have hli : LinearIndependent K ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s * A + t * B = 0 := by
      have h := congrArg (hermLin K f 3 0 3 x) hst
      rwa [herm_add_right, herm_smul_right, herm_smul_right, map_zero] at h
    have h2 : s * C + t * D = 0 := by
      have h := congrArg (hermLin K f 3 0 3 y) hst
      rwa [herm_add_right, herm_smul_right, herm_smul_right, map_zero] at h
    have hs : s * (A * D - B * C) = 0 := by linear_combination D * h1 - B * h2
    have ht : t * (A * D - B * C) = 0 := by linear_combination A * h2 - C * h1
    exact ⟨(mul_eq_zero.mp hs).resolve_right hg', (mul_eq_zero.mp ht).resolve_right hg'⟩
  have hrange : Set.range ![x, y] = ({x, y} : Set (Fin 3 → K)) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hspan : Submodule.span K (Set.range ![x, y]) =
      Submodule.span K {x} ⊔ Submodule.span K {y} := by
    rw [hrange, show ({x, y} : Set (Fin 3 → K)) = insert x {y} from rfl,
      Submodule.span_insert]
  rw [← hspan, finrank_span_eq_card hli]
  simp

private theorem plh2_blockU_a2pol (x : FlagK K 3) (r : ℕ) :
    blockU K 3 [0, 3] x.E 0 r = x.E r := by
  simp only [blockU, Vsub_zero, Vsub_self, List.getD_cons_zero, List.getD_cons_succ,
    inf_top_eq, sup_bot_eq, Nat.sub_self, Nat.zero_add]

theorem mem_a2pol_iff (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K 3) :
    x ∈ genSet K f 3 [0, 3] [true] ↔
      x.E 1 ⊓ perpB K f 3 0 3 (x.E 1) = ⊥ ∧ x.E 2 ⊓ perpB K f 3 0 3 (x.E 2) = ⊥ := by
  have hlen : [0, 3].length = 2 := rfl
  have hfar : x ∈ farSet 3 [0, 3] := by
    intro i hi j hj
    rw [hlen] at hi
    interval_cases i
    · have hd : [0, 3].getD 0 0 = 0 := rfl
      rw [hd, Vsub_zero, inf_bot_eq, finrank_bot]
      omega
    · have hd : [0, 3].getD 1 0 = 3 := rfl
      rw [hd, Vsub_self, inf_top_eq, x.dim j hj]
      omega
  have hle : ∀ i, i < [0, 3].length → [0, 3].getD i 0 ≤ 3 := by
    intro i hi
    rw [hlen] at hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < [0, 3].length → [0, 3].getD i 0 ≤ [0, 3].getD (i + 1) 0 := by
    intro i hi
    rw [hlen] at hi
    have hi2 : i < 2 := by omega
    interval_cases i
    · decide
    · exact absurd hi (by decide)
  have hiff := blockOK_iff_of_far (d := [0, 3]) (pol := [true]) f hle hmono hfar (i := 0)
    (by rw [hlen]; decide)
  simp only [genSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hb⟩
    have hb' := hiff.mp (hb 0 (by rw [hlen]; decide))
    constructor
    · simpa [plh2_blockU_a2pol, Vsub_zero] using hb' 1 (by decide) (by decide)
    · simpa [plh2_blockU_a2pol, Vsub_zero] using hb' 2 (by decide) (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨hfar, ?_⟩
    intro i hi
    have hi0 : i = 0 := by
      rw [hlen] at hi
      omega
    subst hi0
    rw [hiff]
    intro r hr0 hr3
    have hr3' : r < 3 := by
      have h : [0, 3].getD (0 + 1) 0 - [0, 3].getD 0 0 = 3 := by decide
      rwa [h] at hr3
    have hr : r = 1 ∨ r = 2 := by omega
    rcases hr with rfl | rfl
    · simpa [plh2_blockU_a2pol, Vsub_zero] using h1
    · simpa [plh2_blockU_a2pol, Vsub_zero] using h2

end CFSG.ClassicalInvolution.Phan.PhanE

end
