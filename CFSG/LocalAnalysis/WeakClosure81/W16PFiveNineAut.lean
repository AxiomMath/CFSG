module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
import CFSG.Quasithin.AppendixH.Common.InducedAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem SevenK.IsBarMap.exists_mulAut {K N : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : SevenK.IsBarMap K N φ) {a : G} (haK : a ∈ normalizer (K : Set G))
    (haN : a ∈ normalizer (N : Set G)) :
    ∃ α : MulAut X, ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k' := by
  let c : MulAut ↥K := Subgroup.normalizerMonoidHom (H := K) ⟨a, haK⟩
  have hc : ∀ k : ↥K, (c k : G) = a * (k : G) * a⁻¹ := fun k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨a, haK⟩ k
  have hker : ∀ k : ↥K, φ (c k) = 1 ↔ φ k = 1 := by
    intro k
    rw [hφ.ker_iff (c k), hφ.ker_iff k, hc k]
    exact (Subgroup.mem_normalizer_iff.mp haN (k : G)).symm
  obtain ⟨α, hα⟩ := CFSG.ASVolI.AppH.exists_induced_mulAut φ hφ.surjective c hker
  refine ⟨α, fun k k' hkk' => ?_⟩
  have hck : c k = k' := Subtype.ext (by rw [hc k]; exact hkk'.symm)
  rw [hα k, hck]

theorem SevenK.IsBarMap.exists_comm_mem_of_eq_conj {K N V : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : SevenK.IsBarMap K N φ) {a : G} (haK : a ∈ normalizer (K : Set G))
    {α : MulAut X} (hα : ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k') {y : X}
    (hy : y ∈ SevenK.barSub K φ V) (hαy : α = MulAut.conj y) :
    ∃ v ∈ V, ∀ k ∈ K, (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ N := by
  obtain ⟨vk, hvV, hvk⟩ := SevenK.mem_barSub.mp hy
  refine ⟨(vk : G), hvV, fun k hk => ?_⟩
  let kK : ↥K := ⟨k, hk⟩
  let k1 : ↥K := ⟨(vk : G)⁻¹ * k * (vk : G),
    K.mul_mem (K.mul_mem (K.inv_mem vk.2) hk) vk.2⟩
  let k' : ↥K := ⟨a * (k1 : G) * a⁻¹,
    (Subgroup.mem_normalizer_iff.mp haK (k1 : G)).mp k1.2⟩
  have hk1val : (k1 : G) = (vk : G)⁻¹ * k * (vk : G) := rfl
  have hk'val : (k' : G) = a * (k1 : G) * a⁻¹ := rfl
  have hkKval : (kK : G) = k := rfl
  have hconj : vk * k1 * vk⁻¹ = kK := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hk1val, hkKval]
    group
  have key : φ (vk * k1 * vk⁻¹) = φ k' := by
    have h := hα k1 k' hk'val
    rw [hαy, MulAut.conj_apply, ← hvk] at h
    rwa [← map_mul, ← map_inv, ← map_mul] at h
  have hφeq : φ k' = φ kK := by rw [← key, hconj]
  have hmem : (k' * kK⁻¹ : ↥K) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφeq, mul_inv_cancel]
  have hN := (hφ.ker_iff (k' * kK⁻¹)).mp hmem
  convert hN using 1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hk'val, hk1val, hkKval]
  group

end CFSG.LocalAnalysis.WeakClosure81

end
