module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.ModB


theorem card_inf_map_ge {I' Q : Type*} [Group I'] [Finite I'] [Group Q] (β : I' →* Q)
    (K T : Subgroup I') [hK : K.Normal] (hKT : K ⊔ T = ⊤) (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    {o : ℕ} (ho : Odd o) (hKb : Nat.card ↥(K.map β) = 8 * o) :
    8 ≤ Nat.card ↥(K.map β ⊓ T.map β) := by
  classical
  have hrel : T.index = (K ⊓ T).relIndex K :=
    CFSG.GorensteinWalter.index_eq_relIndex_inf_of_normal_sup K T hK hKT
  let D₀ : Subgroup ↥K := (K ⊓ T).subgroupOf K
  let f : ↥K →* ↥(K.map β) := β.subgroupMap K
  have hf : Function.Surjective f := β.subgroupMap_surjective K
  let D₁ : Subgroup ↥(K.map β) := D₀.map f
  have hKfin : Finite ↥(K.map β) := Finite.of_surjective f hf
  have hD₁fin : Finite ↥D₁ := Finite.of_injective D₁.subtype D₁.subtype_injective
  have hD₀idx : D₀.index = T.index := hrel.symm
  have hdvd : D₁.index ∣ D₀.index := Subgroup.index_map_dvd (f := f) (H := D₀) hf
  have hD₁odd : ¬ 2 ∣ D₁.index := fun h => hTi (hD₀idx ▸ h.trans hdvd)
  have hD₀p : IsPGroup 2 ↥D₀ := by
    have h1 : IsPGroup 2 ↥(K ⊓ T) := hT2.to_le inf_le_right
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ T ≤ K)).symm
  have hD₁p : IsPGroup 2 ↥D₁ := hD₀p.of_surjective (f.subgroupMap D₀) (f.subgroupMap_surjective D₀)
  obtain ⟨j, hj⟩ := hD₁p.exists_card_eq
  have hcard := Subgroup.card_mul_index D₁
  rw [hKb, hj] at hcard
  have hj3 : j = 3 := by
    rcases Nat.lt_or_ge j 3 with h | h
    · exfalso
      have hodd : ¬ 2 ∣ D₁.index := hD₁odd
      have ho2 : ¬ 2 ∣ o := by simpa [Nat.odd_iff] using ho
      interval_cases j <;> omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      have ho2 : ¬ 2 ∣ o := by simpa [Nat.odd_iff] using ho
      rw [pow_add] at hcard
      rcases m with _ | m
      · rfl
      · exfalso
        have h8 : 8 * (2 ^ (m + 1) * D₁.index) = 8 * o := by
          rw [← hcard]
          ring
        have h9 := Nat.eq_of_mul_eq_mul_left (by norm_num) h8
        exact ho2 (h9 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero m)) _)
  have hD₁8 : Nat.card ↥D₁ = 8 := by rw [hj, hj3]; norm_num
  have hle : D₁.map (K.map β).subtype ≤ K.map β ⊓ T.map β := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    have hdKT : (d : I') ∈ K ⊓ T := hd
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(d : I'), hdKT.1, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨(d : I'), hdKT.2, rfl⟩
  have hfin3 : Finite ↥(K.map β ⊓ T.map β) := Finite.of_injective
    (Subgroup.inclusion (inf_le_left : K.map β ⊓ T.map β ≤ K.map β)) (Subgroup.inclusion_injective _)
  have hc := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (K.map β).subtype_injective, hD₁8] at hc
  exact hc

end CFSG.Quasithin.ModB
