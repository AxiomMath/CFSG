module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G Q : Type} [Group G] [Group Q]

theorem spUCited_le_map_of_normal_two [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : ¬ 2 ∣ Nat.card π.ker) {Pα Q₀ : Subgroup G}
    (hPα : π.ker ≤ Pα)
    (hlargest : ∀ N : Subgroup G, N ≤ Pα → (N.subgroupOf Pα).Normal → IsPGroup 2 N → N ≤ Q₀)
    {N : Subgroup Q} (hNP : N ≤ Pα.map π) (hN : (N.subgroupOf (Pα.map π)).Normal)
    (hN2 : IsPGroup 2 N) : N ≤ Q₀.map π := by
  haveI : Finite Q := Finite.of_surjective π hπ
  let M : Subgroup G := N.comap π ⊓ Pα
  have hMle : M ≤ Pα := inf_le_right
  have hmap : M.map π = N := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ha).1
    · intro n hn
      obtain ⟨a, haP, haπ⟩ := Subgroup.mem_map.mp (hNP hn)
      exact Subgroup.mem_map.mpr
        ⟨a, ⟨Subgroup.mem_comap.mpr (by rw [haπ]; exact hn), haP⟩, haπ⟩
  have hMnorm : (M.subgroupOf Pα).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMle]
    intro h k hh hk
    refine ⟨?_, ?_⟩
    · change k * h * k⁻¹ ∈ N.comap π
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hkN : π k ∈ Pα.map π := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      have hhN : π h ∈ N := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hh).1
      exact (Subgroup.normal_subgroupOf_iff hNP).mp hN (π h) (π k) hhN hkN
    · exact Pα.mul_mem (Pα.mul_mem hk (Subgroup.mem_inf.mp hh).2) (Pα.inv_mem hk)
  let φ : ↥M →* ↥N := (π.comp M.subtype).codRestrict N fun x =>
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp x.2).1
  have hφsurj : Function.Surjective φ := by
    intro n
    have hnM : (n : Q) ∈ M.map π := by rw [hmap]; exact n.2
    obtain ⟨m, hm, hmπ⟩ := Subgroup.mem_map.mp hnM
    exact ⟨⟨m, hm⟩, Subtype.ext hmπ⟩
  have hφker : φ.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : G) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg (fun z : ↥N => (z : Q)) hx
      simpa [φ] using this
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    exact Subgroup.mem_center_iff.mp (hker hxZ) (y : G)
  haveI hNnil : Group.IsNilpotent ↥N := hN2.isNilpotent
  haveI hMnil : Group.IsNilpotent ↥M := Subgroup.isNilpotent_of_ker_le_center φ hφker
  let T : Sylow 2 ↥M := default
  haveI hTfin : Finite (Sylow 2 ↥M) := Sylow.finite_of_finiteIndex T
  have hTnorm : T.Normal := inferInstance
  have hTchar : (T : Subgroup ↥M).Characteristic := Sylow.characteristic_of_normal T hTnorm
  let M₂ : Subgroup G := (T : Subgroup ↥M).map M.subtype
  have hM₂leM : M₂ ≤ M := Subgroup.map_subtype_le (T : Subgroup ↥M)
  have hM₂lePα : M₂ ≤ Pα := hM₂leM.trans hMle
  have hM₂isP : IsPGroup 2 M₂ := T.isPGroup'.map M.subtype
  have hM₂norm : (M₂.subgroupOf Pα).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM₂lePα]
    intro h k hh hk
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
    have hconj := (Subgroup.normal_subgroupOf_iff hMle).mp hMnorm
    let φk : ↥M ≃* ↥M :=
      { toFun := fun x => ⟨k * x * k⁻¹, hconj x k x.2 hk⟩
        invFun := fun x => ⟨k⁻¹ * x * k, by simpa using hconj x k⁻¹ x.2 (Pα.inv_mem hk)⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun x => Subtype.ext (by group)
        map_mul' := fun x y => Subtype.ext (by
          show k * (↑x * ↑y) * k⁻¹ = (k * ↑x * k⁻¹) * (k * ↑y * k⁻¹)
          group) }
    have hfix : (T : Subgroup ↥M).map φk.toMonoidHom = T :=
      (Subgroup.characteristic_iff_map_eq.mp hTchar) φk
    have hmemT : φk t ∈ T := by
      have : φk t ∈ (T : Subgroup ↥M).map φk.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      rwa [hfix] at this
    exact Subgroup.mem_map.mpr ⟨φk t, hmemT, rfl⟩
  have hM₂Q₀ : M₂ ≤ Q₀ := hlargest M₂ hM₂lePα hM₂norm hM₂isP
  have hdiv : ((T : Subgroup ↥M).map φ).index ∣ T.index :=
    ((T : Subgroup ↥M)).index_map_dvd hφsurj
  have hnotdvd : ¬ 2 ∣ ((T : Subgroup ↥M).map φ).index :=
    fun h => Sylow.not_dvd_index T (h.trans hdiv)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
  have hdvd2 : ((T : Subgroup ↥M).map φ).index ∣ 2 ^ k := by
    rw [← hk]; exact Subgroup.index_dvd_card _
  obtain ⟨j, _hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact h
    · exact absurd (by rw [hj]; exact dvd_pow_self 2 h.ne') hnotdvd
  have hindex1 : ((T : Subgroup ↥M).map φ).index = 1 := by
    rw [hj, hj0]; simp
  have htop : (T : Subgroup ↥M).map φ = ⊤ := Subgroup.index_eq_one.mp hindex1
  have hle : N ≤ M₂.map π := by
    intro n hn
    have hnT : (⟨n, hn⟩ : ↥N) ∈ (T : Subgroup ↥M).map φ := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨t, ht, htφ⟩ := Subgroup.mem_map.mp hnT
    have htM₂ : (t : G) ∈ M₂ := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(t : G), htM₂, ?_⟩
    have := congrArg (fun z : ↥N => (z : Q)) htφ
    simpa [φ] using this
  exact hle.trans (Subgroup.map_mono hM₂Q₀)

end CFSG.LocalAnalysis.WeakClosure81

end
