module

public import CFSG.RankThree.PartOne.S12.Sec1322

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.Sec1322Fin
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

theorem gp_no_eight : ∀ g : Gp, g ^ 8 = 1 → g ^ 4 = 1 := by decide

theorem gp_six : ∀ g : Gp, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z0 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_noconj : ∀ s t : Gp, s * s = 1 → t * t = 1 → (∃ g : Gp, g * s * g⁻¹ = t) →
    (s * t) ^ 4 = 1 → (s * t) ^ 2 ≠ 1 → False := by decide

theorem d8_commuting : ∀ a b : DihedralGroup 4, a * a = 1 → b * b = 1 → a ≠ b → a * b = b * a →
    (∀ x : DihedralGroup 4, x * a = a * x) ∨ (∀ x : DihedralGroup 4, x * b = b * x) ∨
      ∃ x : DihedralGroup 4, x * a * x⁻¹ = b := by decide

theorem d8_no_three : ∀ g : DihedralGroup 4, g ^ 3 = 1 → g = 1 := by decide

theorem s3_no_commuting : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 →
    a ≠ b → a * b ≠ b * a := by decide

theorem d12_six : ∃ g : DihedralGroup 6, g ^ 6 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1 := by decide

theorem d16_eight : ∃ g : DihedralGroup 8, g ^ 8 = 1 ∧ g ^ 4 ≠ 1 := by decide

variable {G : Type} [Group G] [Finite G]

theorem exists_central_inverter {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (eX : reflectionGroup p E ≃* Gp) :
    ∃ z : MulAut E, z ∈ reflectionGroup p E ∧ (∀ e : E, z e = e⁻¹) ∧
      (∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1) ∧
      (∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z) ∧
      (∀ s ∈ reflectionGroup p E, ∀ t ∈ reflectionGroup p E, s * s = 1 → t * t = 1 →
        (∃ x ∈ reflectionGroup p E, x * s * x⁻¹ = t) → (s * t) ^ 4 = 1 → (s * t) ^ 2 ≠ 1 →
        False) := by
  classical
  let φ : Gp →* MulAut E := (reflectionGroup p E).subtype.comp eX.symm.toMonoidHom
  have hφ : ∀ g, φ g = ((eX.symm g : ↥(reflectionGroup p E)) : MulAut E) := fun _ => rfl
  have hφinj : Function.Injective φ := Subtype.val_injective.comp eX.symm.injective
  have hφX : ∀ g, φ g ∈ reflectionGroup p E := fun g => (eX.symm g).2
  have hφsurj : ∀ y ∈ reflectionGroup p E, ∃ g, φ g = y := fun y hy =>
    ⟨eX ⟨y, hy⟩, by simp [hφ]⟩
  set zM : MulAut E := φ z0 with hzM
  have hzX : zM ∈ reflectionGroup p E := hφX z0
  have hz2 : zM * zM = 1 := by rw [hzM, ← map_mul, (Sec1322.z0_props).1, map_one]
  have hz1 : zM ≠ 1 := fun h1 => (Sec1322.z0_props).2.1 (hφinj (h1.trans (map_one φ).symm))
  have hcen : ∀ y ∈ reflectionGroup p E, y * zM = zM * y := by
    intro y hy
    obtain ⟨g, rfl⟩ := hφsurj y hy
    rw [hzM, ← map_mul, ← map_mul, (Sec1322.z0_props).2.2 g]
  have huniq : ∀ y ∈ reflectionGroup p E, y * y = 1 → y ≠ 1 →
      (∀ x ∈ reflectionGroup p E, x * y = y * x) → y = zM := by
    intro y hy hy2 hy1 hyc
    obtain ⟨g, rfl⟩ := hφsurj y hy
    have hg : g = z0 :=
      Sec1322.central_unique g (hφinj (by rw [map_mul, hy2, map_one]))
        (fun hg => hy1 (by rw [hg, map_one]))
        (fun γ => hφinj (by rw [map_mul, map_mul]; exact hyc (φ γ) (hφX γ)))
    rw [hg]
  have hzinv : ∀ e : E, zM e = e⁻¹ := Sec1322.inverts_of_central h hF13 hzX hz2 hz1 hcen huniq
  refine ⟨zM, hzX, hzinv, ?_, ?_, ?_⟩
  · intro g hg h8
    obtain ⟨x, rfl⟩ := hφsurj g hg
    have e8 : x ^ 8 = 1 := hφinj (by rw [map_pow, h8, map_one])
    rw [← map_pow, gp_no_eight x e8, map_one]
  · intro g hg h6 h3 h2
    obtain ⟨x, rfl⟩ := hφsurj g hg
    have e6 : x ^ 6 = 1 := hφinj (by rw [map_pow, h6, map_one])
    have e3 : x ^ 3 ≠ 1 := fun h => h3 (by rw [← map_pow, h, map_one])
    have e2 : x ^ 2 ≠ 1 := fun h => h2 (by rw [← map_pow, h, map_one])
    rw [← map_pow, gp_six x e6 e3 e2]
  · intro s hs t ht hs2 ht2 hconj h4 h2
    obtain ⟨a, rfl⟩ := hφsurj s hs
    obtain ⟨b, rfl⟩ := hφsurj t ht
    obtain ⟨y, hy, hyst⟩ := hconj
    obtain ⟨c', rfl⟩ := hφsurj y hy
    have ha : a * a = 1 := hφinj (by rw [map_mul, hs2, map_one])
    have hb : b * b = 1 := hφinj (by rw [map_mul, ht2, map_one])
    have hab4 : (a * b) ^ 4 = 1 := hφinj (by rw [map_pow, map_mul, h4, map_one])
    have hab2 : (a * b) ^ 2 ≠ 1 := fun h' => h2 (by rw [← map_mul, ← map_pow, h', map_one])
    have hconj' : c' * a * c'⁻¹ = b := hφinj (by rw [map_mul, map_mul, map_inv, hyst])
    exact gp_noconj a b ha hb ⟨c', hconj'⟩ hab4 hab2

structure Inverter (p : ℕ) {G : Type} [Group G] (E : Subgroup G) (z : MulAut E) : Prop where
  mem : z ∈ reflectionGroup p E
  inv : ∀ e : E, z e = e⁻¹
  no_eight : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1
  six : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z
  noconj : ∀ s ∈ reflectionGroup p E, ∀ t ∈ reflectionGroup p E, s * s = 1 → t * t = 1 →
    (∃ x ∈ reflectionGroup p E, x * s * x⁻¹ = t) → (s * t) ^ 4 = 1 → (s * t) ^ 2 ≠ 1 → False

theorem exists_inverter {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (eX : reflectionGroup p E ≃* Gp) : ∃ z : MulAut E, Inverter p E z := by
  obtain ⟨z, hzX, hzinv, h8, h6, hnc⟩ := exists_central_inverter h hF13 eX
  exact ⟨z, ⟨hzX, hzinv, h8, h6, hnc⟩⟩

section Members

variable {p : ℕ} {B : Subgroup G} {c' : G} {J E : Subgroup G}

theorem inverter_not_mem_torusImage (h' : Sec12Hyp G p B c' J E) (hc'E : c' ∈ E) (hc'1 : c' ≠ 1)
    {z : MulAut E} (hz : ∀ e : E, z e = e⁻¹) : z ∉ torusImage E J := by
  intro hzJ
  obtain ⟨w, hwJ, hwN, hwz⟩ := Sec12Three.mem_torusImage_iff.1 hzJ
  have hp := h'.prime
  have hp2 : 3 < p := h'.three_lt
  have hconj : w * c' * w⁻¹ = c' := by
    have := Sec12Three.comm_c_L h' w hwJ
    rw [← this]
    group
  have hact : (z ⟨c', hc'E⟩ : E) = ⟨w * c' * w⁻¹, by
      have := (Subgroup.mem_normalizer_iff.1 hwN c').1 hc'E
      exact this⟩ := by
    rw [← hwz]
    rfl
  have h1 : (z ⟨c', hc'E⟩ : E) = ⟨c', hc'E⟩ := by
    rw [hact]
    exact Subtype.ext hconj
  rw [hz] at h1
  have h2 : c' * c' = 1 := by
    have h3 := congrArg Subtype.val h1
    simp only [Subgroup.coe_inv] at h3
    calc c' * c' = c'⁻¹ * c' := by rw [h3]
      _ = 1 := inv_mul_cancel c'
  have h3 : c' ^ 2 = 1 := by rw [pow_two]; exact h2
  have h4 : c' ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h' hc'E
  have h5 : c' ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨h3, h4⟩
  have hcop : Nat.gcd 2 p = 1 := by
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    exact this
  rw [hcop, pow_one] at h5
  exact hc'1 h5

theorem torusImage_le_reflectionGroup (hF' : Sec12Facts G p B c' J E) :
    torusImage E J ≤ reflectionGroup p E := by
  rw [hF'.three.1]
  exact Subgroup.closure_mono (fun x hx => hx.1)

end Members

end CFSG.RankThree.PartOne.K1320
