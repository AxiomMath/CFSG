module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
import CFSG.GroupTheory.SupCommute
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_rank {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ) (hn : 7 ≤ n)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    {y : G} (hy : y ∈ Bs) (hy1 : y ≠ 1) (hyK : ∀ k ∈ K, y * k = k * y) :
    (n + 1) / 2 = 4 ∧
      Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)) ∧
      Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  let S : Subgroup G := (halfTorus n).map ψ
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G)
  have hSle : S ≤ Bs := hψ.torus_le
  have hCle : C ≤ Bs := inf_le_left
  have hdisj : S ⊓ C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxC⟩ := hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hxS
    have hxC' : ψ t ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_inf.mp hxC).2
    rw [Subgroup.mem_centralizer_iff] at hxC'
    have hcomm : ∀ s : SpecialLinearGroup (Fin (n + 1)) F2, ψ t * ψ s = ψ s * ψ t := by
      intro s
      have hsK : ψ s ∈ K := by rw [← hψ.range]; exact ⟨s, rfl⟩
      exact (hxC' (ψ s) hsK).symm
    rw [eq_one_of_commute_range hψ.inj hcomm, map_one]
  have hcommSC : ∀ s ∈ S, ∀ c ∈ C, Commute s c := by
    intro s hs c hc
    exact commute_of_mem_of_isMulCommutative hBs.1 (hSle hs) (hCle hc)
  have hsup : Bs = S ⊔ C := by
    apply le_antisymm
    · intro b hb
      obtain ⟨t, ht, hact⟩ := hψ.act b hb
      have hψtS : ψ t ∈ S := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have hψtBs : ψ t ∈ Bs := hSle hψtS
      have hcBs : (ψ t)⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem hψtBs) hb
      have hcC : (ψ t)⁻¹ * b ∈ C := by
        refine Subgroup.mem_inf.mpr ⟨hcBs, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hconj : (ψ t)⁻¹ * b * l * ((ψ t)⁻¹ * b)⁻¹ = l := by
          have h1 : (ψ t)⁻¹ * b * l * ((ψ t)⁻¹ * b)⁻¹ =
              (ψ t)⁻¹ * (b * l * b⁻¹) * ψ t := by group
          rw [h1, hact l hl]; group
        have hcl : (ψ t)⁻¹ * b * l = l * ((ψ t)⁻¹ * b) := by
          have h := congrArg (fun z => z * ((ψ t)⁻¹ * b)) hconj
          simpa [mul_assoc] using h
        exact hcl.symm
      rw [show b = ψ t * ((ψ t)⁻¹ * b) from by group]
      exact Subgroup.mul_mem_sup hψtS hcC
    · exact sup_le hSle hCle
  have hcardS : Nat.card S = 3 ^ ((n + 1) / 2) := by
    rw [Subgroup.card_map_of_injective hψ.inj, card_halfTorus]
  have hcount : 3 ^ 5 = 3 ^ ((n + 1) / 2) * Nat.card C := by
    rw [← hcard, hsup, card_sup_eq_mul_of_commute S C hcommSC hdisj, hcardS]
  have hyC : y ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨hy, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hyK k hk).symm
  have horder : orderOf y = 3 := orderOf_eq_prime (hBs.2 y hy) hy1
  have hzle : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.mpr hyC
  have h3dvd : 3 ∣ Nat.card C := by
    have h := Subgroup.card_dvd_of_le hzle
    rwa [Nat.card_zpowers, horder] at h
  have hCpos : 0 < Nat.card C := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨⟨1, C.one_mem⟩⟩, inferInstance⟩
  have ha_ge : 3 ≤ Nat.card C := Nat.le_of_dvd hCpos h3dvd
  have hk_ge : 4 ≤ (n + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hk4 : (n + 1) / 2 = 4 := by
    by_contra hne
    have hk5le : 5 ≤ (n + 1) / 2 := by omega
    have hpow_ge : 3 ^ 5 ≤ 3 ^ ((n + 1) / 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 3) hk5le
    have hpow_le : 3 ^ ((n + 1) / 2) ≤ 3 ^ 5 := by
      nlinarith [hcount, ha_ge, Nat.zero_le (3 ^ ((n + 1) / 2))]
    have hEq : 3 ^ ((n + 1) / 2) = 3 ^ 5 := le_antisymm hpow_le hpow_ge
    have hk5 : (n + 1) / 2 = 5 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hEq
    have ha1 : Nat.card C = 1 := by
      rw [hk5] at hcount
      have h' : 3 ^ 5 * 1 = 3 ^ 5 * Nat.card C := by rw [mul_one]; exact hcount
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 5) h').symm
    omega
  have hcardC : Nat.card C = 3 := by
    have h := hcount
    rw [hk4] at h
    norm_num at h
    omega
  have hCeq : C = Subgroup.zpowers y := by
    have hcle : Nat.card C ≤ Nat.card (Subgroup.zpowers y) := by
      rw [hcardC, Nat.card_zpowers, horder]
    exact (Subgroup.eq_of_le_of_card_ge hzle hcle).symm
  exact ⟨hk4, hsup, hCeq⟩

end CFSG.StandardType

end
