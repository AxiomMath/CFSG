module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

theorem g119_commutator_mem_of_sup_zpowers {G : Type*} [Group G] {A N : Subgroup G} (hNA : N ≤ A)
    (hnorm : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {a : G}
    (hA : N ⊔ Subgroup.zpowers a = A) {g₁ g₂ : G} (h₁ : g₁ ∈ A) (h₂ : g₂ ∈ A) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ N := by
  have haA : a ∈ A := hA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hnorm g hg h, fun hh => ?_⟩
    simpa [mul_assoc] using hnorm g⁻¹ (A.inv_mem hg) _ hh
  have : (N.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (hAN haA)
  have key : ∀ x : A, ∃ k : ℤ, QuotientGroup.mk' (N.subgroupOf A) x =
      (QuotientGroup.mk' (N.subgroupOf A) ⟨a, haA⟩) ^ k := by
    intro x
    have hx : (x : G) ∈ ((N ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
      rw [hA]
      exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N (Subgroup.zpowers a) hzN] at hx
    obtain ⟨n, hn, y, hy, hxy⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, ?_⟩
    have hx' : x = ⟨n, hNA hn⟩ * (⟨a, haA⟩ : A) ^ k := Subtype.ext (by simp [← hxy])
    have hn1 : QuotientGroup.mk' (N.subgroupOf A) ⟨n, hNA hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    rw [hx', map_mul, map_zpow, hn1, one_mul]
  obtain ⟨i, hi⟩ := key ⟨g₁, h₁⟩
  obtain ⟨j, hj⟩ := key ⟨g₂, h₂⟩
  have h1 : QuotientGroup.mk' (N.subgroupOf A)
      (⟨g₁, h₁⟩ * ⟨g₂, h₂⟩ * (⟨g₁, h₁⟩ : A)⁻¹ * (⟨g₂, h₂⟩ : A)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hi, hj]
    group
  have h2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  simpa using h2

theorem g119_le_of_perfect_of_sup_zpowers {G : Type*} [Group G] {A N P : Subgroup G} (hNA : N ≤ A)
    (hnorm : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {a : G} (hA : N ⊔ Subgroup.zpowers a = A)
    (hPA : P ≤ A) (hP : Group.IsPerfect ↥P) : P ≤ N := by
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ N := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact g119_commutator_mem_of_sup_zpowers hNA hnorm hA (hPA hg₁) (hPA hg₂)

theorem g119_mem_or_mul_mem_of_sup_zpowers {G : Type*} [Group G] {N : Subgroup G} {a : G}
    (ha : a * a = 1) (hnorm : ∀ n ∈ N, a * n * a⁻¹ ∈ N) {g : G}
    (hg : g ∈ N ⊔ Subgroup.zpowers a) : g ∈ N ∨ g * a ∈ N := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have haN : a ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hnorm h, fun hh => ?_⟩
    have := hnorm _ hh
    rwa [hinv, show a * (a * h * a) * a = (a * a) * h * (a * a) by group, ha, one_mul,
      mul_one] at this
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr haN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N (Subgroup.zpowers a) hzN]
    at hg
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rwa [zpow_mul, h2, one_zpow, mul_one]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, mul_assoc, ha, mul_one]
    exact hn

theorem g119_finrank_permCore {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) ↥(permCore n) = n - 1 := by
  let s : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i, LinearMap.proj i
  have hs : ∀ x, s x = ∑ i, x i := fun x => by simp [s]
  have hker : permCore n = LinearMap.ker s := by
    ext x
    rw [LinearMap.mem_ker, hs]
    exact Iff.rfl
  have hsurj : Function.Surjective s := fun c => by
    refine ⟨Pi.single ⟨0, hn⟩ c, ?_⟩
    rw [hs]
    simp
  have h := LinearMap.finrank_range_add_finrank_ker s
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  rw [hker]
  omega

theorem g119_four_le_finrank_range_of_ker {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ}
    (hn : 5 ≤ n) (β : ↥(permCore n) →ₗ[ZMod 2] M)
    (hker : ∀ u : ↥(permCore n), β u = 0 ↔
      (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) :
    4 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range β) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker β
  rw [g119_finrank_permCore (by omega)] at hrn
  by_cases hev : Even n
  · have hones : (fun _ : Fin n => (1 : ZMod 2)) ∈ permCore n := by
      show ∑ _i : Fin n, (1 : ZMod 2) = 0
      simpa using ZMod.natCast_eq_zero_iff_even.mpr hev
    have hle : LinearMap.ker β ≤ Submodule.span (ZMod 2) {(⟨_, hones⟩ : ↥(permCore n))} := by
      intro u hu
      rcases (hker u).mp hu with rfl | ⟨-, hu1⟩
      · exact Submodule.zero_mem _
      · rw [show u = ⟨_, hones⟩ from Subtype.ext (funext hu1)]
        exact Submodule.mem_span_singleton_self _
    have hfin : Module.finrank (ZMod 2) (LinearMap.ker β) ≤ 1 := by
      refine (Submodule.finrank_mono hle).trans ?_
      simpa using finrank_span_le_card (R := ZMod 2)
        ({(⟨_, hones⟩ : ↥(permCore n))} : Set ↥(permCore n))
    obtain ⟨r, hr⟩ := hev
    omega
  · have hbot : LinearMap.ker β = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro u hu
      rcases (hker u).mp hu with h | ⟨h, -⟩
      · exact h
      · exact absurd h hev
    rw [hbot, finrank_bot] at hrn
    omega

end G11

end CFSG.Quasithin
