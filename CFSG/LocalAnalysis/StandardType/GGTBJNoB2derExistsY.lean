module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_D_gen {G : Type} [Group G] [Finite G] {B D : Subgroup G} {x y : G}
    (hB : IsElemAbelian 3 B) (hDB : D ≤ B) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hx1 : x ≠ 1) (hyD : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) :
    ∀ d ∈ D, ∃ i j : ℤ, d = x ^ i * y ^ j := by
  classical
  haveI : IsMulCommutative ↥B := hB.1
  have hxB : x ∈ B := hDB hxD
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have horder : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcardzp : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, horder]
  have hzpD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hyB : y ∈ B := hDB hyD
  have hcomm : Commute x y := by
    show x * y = y * x
    have h := congrArg Subtype.val (mul_comm' (⟨y, hyB⟩ : ↥B) (⟨x, hxB⟩ : ↥B))
    simpa using h.symm
  let T : Subgroup G :=
    { carrier := {z | ∃ i j : ℤ, z = x ^ i * y ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        calc
          (x ^ i * y ^ j) * (x ^ k * y ^ l)
              = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
          _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by
                rw [((hcomm.symm).zpow_zpow j k).eq]
          _ = (x ^ i * x ^ k) * (y ^ j * y ^ l) := by group
          _ = x ^ (i + k) * y ^ (j + l) := by rw [← zpow_add, ← zpow_add]
      inv_mem' := by
        rintro a ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        have hc : Commute (y ^ (-j)) (x ^ (-i)) := (hcomm.symm).zpow_zpow (-j) (-i)
        calc
          (x ^ i * y ^ j)⁻¹ = y ^ (-j) * x ^ (-i) := by
            rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
          _ = x ^ (-i) * y ^ (-j) := hc.eq }
  have hT : Subgroup.closure ({x, y} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  have hxT : x ∈ T := hT (Subgroup.subset_closure (by simp))
  have hyT : y ∈ T := hT (Subgroup.subset_closure (by simp))
  let H : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hHleT : H ≤ T :=
    sup_le (Subgroup.zpowers_le.mpr hxT) (Subgroup.zpowers_le.mpr hyT)
  have hHle : H ≤ D := sup_le hzpD (Subgroup.zpowers_le.mpr hyD)
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hlt : Subgroup.zpowers x < H :=
    lt_of_le_of_ne le_sup_left (fun hEq => hyx (hEq ▸ hyH))
  have hcardH_dvd : Nat.card H ∣ 3 ^ 2 := by
    rw [← hDcard]
    exact Subgroup.card_dvd_of_le hHle
  have h3lt : 3 < Nat.card H := by
    have h := Subgroup.card_lt_of_lt hlt
    rwa [hcardzp] at h
  have hH9 : Nat.card H = 9 := by
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (show Nat.Prime 3 by norm_num)).mp hcardH_dvd
    have hk2 : k = 2 := by
      interval_cases k
      · rw [hk] at h3lt; norm_num at h3lt
      · rw [hk] at h3lt; norm_num at h3lt
      · rfl
    rw [hk, hk2]
    norm_num
  have hHD : H = D := Subgroup.eq_of_le_of_card_ge hHle (by rw [hDcard, hH9]; norm_num)
  intro d hdD
  exact hHleT (hHD.symm ▸ hdD)

theorem ggB2der_exists_y {G : Type} [Group G] [Finite G] {B D : Subgroup G} {x : G}
    (hB : IsElemAbelian 3 B) (hDB : D ≤ B) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hx1 : x ≠ 1) :
    ∃ y : ↥B, (y : G) ∈ D ∧ (y : G) ∉ Subgroup.zpowers x ∧
      ∀ d ∈ D, ∃ i j : ℤ, d = x ^ i * (y : G) ^ j := by
  classical
  have hxB : x ∈ B := hDB hxD
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hcardzp : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hnotle : ¬ D ≤ Subgroup.zpowers x := by
    intro hle
    have hdvd : Nat.card D ∣ Nat.card (Subgroup.zpowers x) := Subgroup.card_dvd_of_le hle
    rw [hDcard, hcardzp] at hdvd
    norm_num at hdvd
  obtain ⟨y₀, hy₀D, hy₀x⟩ : ∃ y₀ : G, y₀ ∈ D ∧ y₀ ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    exact hnotle fun z hz => h z hz
  exact ⟨⟨y₀, hDB hy₀D⟩, hy₀D, hy₀x, ggB2der_D_gen hB hDB hDcard hxD hx1 hy₀D hy₀x⟩

end CFSG.StandardType
