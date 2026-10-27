module

public import CFSG.Permutation.ProperSupportMaps

public section

namespace CFSG.Permutation.ProperSupportMaps

theorem commute_of_braid {H : Type*} [Group H] {Y : Subgroup H} {s g : H}
    (hs : s * s = 1) (hg : g * g = 1) (hbraid : s * g * s = g * s * g)
    (hsY : ∀ y ∈ Y, s * y = y * s) (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∀ y ∈ Y, g * y = y * g := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  intro y hy
  have hzY : g * y * g⁻¹ ∈ Y := hgY y hy
  have hsz : s * (g * y * g⁻¹) = (g * y * g⁻¹) * s := hsY _ hzY
  have hzg : (g * y * g⁻¹) * g = g * y := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hsgy : (s * g) * y = (g * y * g⁻¹) * (s * g) := by
    calc (s * g) * y = s * (g * y) := by group
      _ = s * ((g * y * g⁻¹) * g) := by rw [hzg]
      _ = (s * (g * y * g⁻¹)) * g := by group
      _ = ((g * y * g⁻¹) * s) * g := by rw [hsz]
      _ = (g * y * g⁻¹) * (s * g) := by group
  have hgsg : (g * s * g) * y = y * (g * s * g) := by
    have key : (g⁻¹ * s * g) * y = y * (g⁻¹ * s * g) := by
      calc (g⁻¹ * s * g) * y = g⁻¹ * ((s * g) * y) := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * (s * g)) := by rw [hsgy]
        _ = y * (g⁻¹ * s * g) := by group
    rwa [hg'] at key
  have hmul : ∀ a b : H, a * y = y * a → b * y = y * b → (a * b) * y = y * (a * b) := by
    intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have hs_comm : s * y = y * s := hsY y hy
  have hgs : s * (g * s * g) = g * s := by
    rw [show s * (g * s * g) = (s * g * s) * g by group, hbraid, mul_assoc, hg, mul_one]
  have h1 : (s * (g * s * g)) * y = y * (s * (g * s * g)) :=
    hmul s (g * s * g) hs_comm hgsg
  have h2 : (g * s) * y = y * (g * s) := by
    rw [hgs] at h1
    exact h1
  have h3 : (g * s * s) * y = y * (g * s * s) := hmul (g * s) s h2 hs_comm
  rwa [show g * s * s = g by rw [mul_assoc, hs, mul_one]] at h3

variable {I X H : Type*} [Fintype I] [DecidableEq I] [Group X] [Group H]
  {d : I} {B : Finset I → Subgroup X} {hB : Monotone B}
  {ρ : Equiv.Perm I →* X} {t : Equiv.Perm I →* H} {a : B (deletionSet d) →* H}

theorem cross_of_normalizes {u v c e : I} (hdu : d ≠ u) (hdv : d ≠ v) (hcd : c ≠ d)
    (hce : c ≠ e) (hed : e ≠ d) (huc : u ≠ c) (hue : u ≠ e) (hvc : v ≠ c) (hve : v ≠ e)
    (hcommon : ∀ σ : Equiv.Perm I, σ d = d →
      ∃ h : (ρ σ : X) ∈ B (deletionSet d), a ⟨ρ σ, h⟩ = t σ)
    (hbase : ∀ (σ : Equiv.Perm I) (x : B ({u, v} : Finset I)),
      σ u = u → σ v = v → ρ σ * (x : X) = (x : X) * ρ σ)
    (hnorm : ∀ x : B ({u, v} : Finset I), ∃ y : B ({u, v} : Finset I),
      t (Equiv.swap c d) *
          a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x) *
          (t (Equiv.swap c d))⁻¹ =
        a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) y)) :
    ∀ x : B ({u, v} : Finset I),
      t (Equiv.swap c d) *
          a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x) =
        a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x) *
          t (Equiv.swap c d) := by
  intro x
  have hle : ({u, v} : Finset I) ⊆ deletionSet d :=
    pair_subset_deletionSet hdu.symm hdv.symm
  let inc : B ({u, v} : Finset I) →* B (deletionSet d) := Subgroup.inclusion (hB hle)
  have hσd : Equiv.swap c e d = d := Equiv.swap_apply_of_ne_of_ne hcd.symm hed.symm
  have hσu : Equiv.swap c e u = u := Equiv.swap_apply_of_ne_of_ne huc hue
  have hσv : Equiv.swap c e v = v := Equiv.swap_apply_of_ne_of_ne hvc hve
  obtain ⟨hσB, hσa⟩ := hcommon (Equiv.swap c e) hσd
  have hcommY : ∀ x' : B ({u, v} : Finset I),
      t (Equiv.swap c e) * a (inc x') = a (inc x') * t (Equiv.swap c e) := by
    intro x'
    have hcommX : (ρ (Equiv.swap c e)) * (x' : X) = (x' : X) * ρ (Equiv.swap c e) :=
      hbase _ x' hσu hσv
    have hsub : (⟨ρ (Equiv.swap c e), hσB⟩ : B (deletionSet d)) * inc x' =
        inc x' * ⟨ρ (Equiv.swap c e), hσB⟩ := by
      ext
      simpa [inc, Subgroup.coe_inclusion] using hcommX
    calc t (Equiv.swap c e) * a (inc x')
        = a ⟨ρ (Equiv.swap c e), hσB⟩ * a (inc x') := by rw [hσa]
      _ = a (⟨ρ (Equiv.swap c e), hσB⟩ * inc x') := (map_mul a _ _).symm
      _ = a (inc x' * ⟨ρ (Equiv.swap c e), hσB⟩) := by rw [hsub]
      _ = a (inc x') * a ⟨ρ (Equiv.swap c e), hσB⟩ := map_mul a _ _
      _ = a (inc x') * t (Equiv.swap c e) := by rw [hσa]
  have hs : t (Equiv.swap c e) * t (Equiv.swap c e) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hg : t (Equiv.swap c d) * t (Equiv.swap c d) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hswap : Equiv.swap c e * Equiv.swap c d * Equiv.swap c e =
      Equiv.swap c d * Equiv.swap c e * Equiv.swap c d := by
    have h1 : Equiv.swap c e * Equiv.swap c d * Equiv.swap c e = Equiv.swap d e := by
      rw [Equiv.swap_comm c d, Equiv.swap_comm d e]
      exact Equiv.swap_mul_swap_mul_swap (x := d) (y := c) (z := e) hcd.symm hed.symm
    have h2 : Equiv.swap c d * Equiv.swap c e * Equiv.swap c d = Equiv.swap d e := by
      rw [Equiv.swap_comm c e]
      exact Equiv.swap_mul_swap_mul_swap (x := e) (y := c) (z := d) hce.symm hed
    rw [h1, h2]
  have hbraid : t (Equiv.swap c e) * t (Equiv.swap c d) * t (Equiv.swap c e) =
      t (Equiv.swap c d) * t (Equiv.swap c e) * t (Equiv.swap c d) := by
    calc t (Equiv.swap c e) * t (Equiv.swap c d) * t (Equiv.swap c e)
        = t (Equiv.swap c e * Equiv.swap c d * Equiv.swap c e) := by rw [map_mul, map_mul]
      _ = t (Equiv.swap c d * Equiv.swap c e * Equiv.swap c d) := by rw [hswap]
      _ = t (Equiv.swap c d) * t (Equiv.swap c e) * t (Equiv.swap c d) := by
            rw [map_mul, map_mul]
  have hsY : ∀ y ∈ (a.comp inc).range,
      t (Equiv.swap c e) * y = y * t (Equiv.swap c e) := by
    intro y hy
    obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hy
    exact hcommY x'
  have hgY : ∀ y ∈ (a.comp inc).range,
      t (Equiv.swap c d) * y * (t (Equiv.swap c d))⁻¹ ∈ (a.comp inc).range := by
    intro y hy
    obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨y', hy'⟩ := hnorm x'
    have harg : (a.comp inc) x' =
        a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x') := rfl
    rw [harg, hy']
    exact MonoidHom.mem_range.mpr ⟨y', rfl⟩
  have hmain := commute_of_braid (Y := (a.comp inc).range)
    (s := t (Equiv.swap c e)) (g := t (Equiv.swap c d)) hs hg hbraid hsY hgY
  exact hmain (a (inc x)) (MonoidHom.mem_range.mpr ⟨x, rfl⟩)

end CFSG.Permutation.ProperSupportMaps
