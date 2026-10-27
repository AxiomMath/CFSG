module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3EvenTools
import CFSG.RankThree.PartTwo.Sec19.Census194.RankOne
import CFSG.Open.PGLModelStated
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

theorem inspect189U3Even : Inspect189U3Even := by
  intro Y _ _ X Q x n hD hn hn2 ⟨e⟩
  set J := (X ⊓ Subgroup.normalizer (Q : Set Y)) ⊔
    (X ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set Y))
  show X ≤ J
  obtain ⟨T, hT⟩ := hD.sylow.inf_of_le_normalizer (N := X) le_top
    (Subgroup.normalizer_eq_top_iff.2 hD.normal).ge
  have hmem : ∀ z : X, z ∈ (T : Subgroup X) ↔ (z : Y) ∈ Q := fun z => by
    have h1 := Subgroup.mem_map_iff_mem X.subtype_injective (K := (T : Subgroup X)) (x := z)
    rw [hT, Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.2 h).1, fun h => h1.1 ⟨h, z.2⟩⟩
  set y : X := ⟨x, hD.mem⟩ with hydef
  have hyN : y ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hmem, hmem]
    exact Subgroup.mem_normalizer_iff.1 hD.mem_normalizer z
  have hy3 : orderOf y = 3 := by
    rw [hydef, Subgroup.orderOf_mk]
    exact hD.orderOf_eq
  have hTJ : (T : Subgroup X) ≤ J.subgroupOf X := fun z hz =>
    Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left ⟨z.2, Subgroup.le_normalizer ((hmem z).1 hz)⟩)
  have hJx : ∀ c : X, (c : Y) * x * (c : Y)⁻¹ ∈ Subgroup.zpowers x →
      (c : Y)⁻¹ * x * c ∈ Subgroup.zpowers x → c ∈ J.subgroupOf X := fun c h1 h2 =>
    Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_right ⟨c.2, mem_normalizer_zpowers_of_conj_mem189 h1 h2⟩)
  have hJc : ∀ c : X, c * y = y * c → c ∈ J.subgroupOf X := fun c hc => by
    have hc' : (c : Y) * x = x * c := congrArg Subtype.val hc
    refine hJx c ?_ ?_
    · rw [hc', mul_inv_cancel_right]
      exact Subgroup.mem_zpowers x
    · rw [mul_assoc, ← hc', inv_mul_cancel_left]
      exact Subgroup.mem_zpowers x
  have hJinv : ∀ c : X, c * y * c⁻¹ = y⁻¹ → c ∈ J.subgroupOf X := fun c hc => by
    have hc' : (c : Y) * x * (c : Y)⁻¹ = x⁻¹ := congrArg Subtype.val hc
    refine hJx c ?_ ?_
    · rw [hc']
      exact inv_mem (Subgroup.mem_zpowers x)
    · have h2 : (c : Y)⁻¹ * x * c = x⁻¹ := by
        calc (c : Y)⁻¹ * x * c = (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹)⁻¹ * c := by
              rw [hc', inv_inv]
          _ = x⁻¹ := by group
      rw [h2]
      exact inv_mem (Subgroup.mem_zpowers x)
  have hf3 : 2 ^ n % 3 = 1 := by
    obtain ⟨m, hm⟩ := hn
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), mul_comm, pow_mul]
  let e' : X ≃* StatedProj (StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
    e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 2 n)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have h := borelQuotient_su hcard (by norm_num : 2 ≤ 3) ζ hζ e'
  obtain ⟨π', hQ, hker, hS, k, hk, t, ht, hkt⟩ := exists_conj_mem_torus189 h T hyN hy3
  have hyJ : y ∈ J.subgroupOf X := hJc y rfl
  have hkJ : k ∈ J.subgroupOf X := sup_le hTJ (Subgroup.zpowers_le.2 hyJ) hk
  have hNJ := normalizer_le_of_conj_mem_torus189 hQ T hS ht hkt hTJ hkJ hJc
  have ht3 : t ^ 3 = 1 := by
    apply eq_one_of_borelQuotient_su_eq_one189 hcard hf3 e'
    rw [← MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker, map_pow, ← hkt, conj_pow, ← hy3,
      pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨w₀, hw₀, hw₀t⟩ := exists_inv_diag_su_three189 (F := GaloisField 2 (2 * n)) hf3
  have htw := hw₀t t (iSup_le (fun i => levelTorus_le_diagSubgroup i) ht) ht3
  have hww : (k⁻¹ * π' w₀ * k) * (k⁻¹ * π' w₀ * k) = 1 := by
    calc (k⁻¹ * π' w₀ * k) * (k⁻¹ * π' w₀ * k) = k⁻¹ * π' (w₀ * w₀) * k := by
          rw [map_mul]
          group
      _ = 1 := by rw [hw₀, map_one, mul_one, inv_mul_cancel]
  have hwy : (k⁻¹ * π' w₀ * k) * y * (k⁻¹ * π' w₀ * k)⁻¹ = y⁻¹ := by
    have hy : y = k⁻¹ * π' t * k := by
      rw [← hkt]
      group
    rw [hy]
    calc k⁻¹ * π' w₀ * k * (k⁻¹ * π' t * k) * (k⁻¹ * π' w₀ * k)⁻¹ =
        k⁻¹ * π' (w₀ * t * w₀⁻¹) * k := by
          rw [map_mul, map_mul, map_inv]
          group
      _ = (k⁻¹ * π' t * k)⁻¹ := by
          rw [htw, map_inv]
          group
  rcases Sec19.eq_normalizer_or_top_of_borelQuotient h rfl T (J.subgroupOf X) hNJ with h1 | h1
  · exact absurd (h1 ▸ hJinv _ hwy) (not_mem_normalizer_of_inv189 h T hyN hy3 hww hwy)
  · intro z hz
    have hz' : (⟨z, hz⟩ : X) ∈ J.subgroupOf X := by
      rw [h1]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hz'

end CFSG.RankThree.PartTwo.Sec18
