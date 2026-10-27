module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveBar
public import CFSG.LocalAnalysis.WeakClosure81.TwelveFix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem map_conj_map_eq_cj {G : Type} [Group G] (ρ : G →* LGL 2 V) (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map ρ = cj (ρ g) (A.map ρ) := by
  have h : ρ.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (ρ g)).toMonoidHom.comp ρ := by
    ext x
    simp [MulAut.conj_apply]
  rw [cj, Subgroup.map_map, Subgroup.map_map, h]

section Generation

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

private theorem b12_TwelvePartTwo_two_elt (h : Setting12Two A M n) {a : G} (ha : a ∈ A) :
    ∃ k : ℕ, a ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.A_two ⟨a, ha⟩
  exact ⟨k, by
    have h2 := congrArg (Subgroup.subtype A) hk
    simpa using h2⟩

private theorem b12_TwelvePartTwo_conj_pow (g a : G) (k : ℕ) :
    (g * a * g⁻¹) ^ 2 ^ k = g * a ^ 2 ^ k * g⁻¹ := by
  rw [conj_pow]

private theorem b12_TwelvePartTwo_conj_mem_ker (h : Setting12Two A M n) {a g : G}
    (haM : a ∈ M) (hg : g ∉ M) (hgaM : g * a * g⁻¹ ∈ M)
    (ha2 : ∃ k : ℕ, a ^ 2 ^ k = 1) : a ∈ CFSG.Quasithin.kerIn M ⊤ := by
  have hxMg : g * a * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, haM, rfl⟩
  have hx2 : ∃ k : ℕ, (g * a * g⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := ha2
    exact ⟨k, by rw [b12_TwelvePartTwo_conj_pow, hk]; simp⟩
  have hxK := h.mem_ker_of_mem_inf_conj hg hgaM hxMg hx2
  have hN : (CFSG.Quasithin.kerIn M ⊤).Normal := kerIn_top_normal12 M
  have hconj := hN.conj_mem (g * a * g⁻¹) hxK g⁻¹
  simpa [mul_assoc] using hconj

theorem Setting12Two.sup_conj_eq_top (h : Setting12Two A M n) {g : G} (hg : g ∉ M) :
    A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
  by_contra hH
  have hHleM : A ⊔ A.map (MulAut.conj g).toMonoidHom ≤ M :=
    h.unique_max _ le_sup_left hH
  exact h.not_le_ker fun a ha =>
    b12_TwelvePartTwo_conj_mem_ker h (h.A_le_M ha) hg
      (hHleM (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)))
      (b12_TwelvePartTwo_two_elt h ha)

theorem Setting12Two.zpowers_sup_conj_eq_top (h : Setting12Two A M n) {g a : G} (hg : g ∉ M)
    (ha : a ∈ A) (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) :
    Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
  let H : Subgroup G := Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom
  change H = ⊤
  have hcyc : CFSG.Quasithin.B6.conjSub g (CFSG.Quasithin.B6.conjSub g⁻¹ H) = H := by
    rw [← CFSG.Quasithin.B6.conjSub_mul, mul_inv_cancel, CFSG.Quasithin.B6.conjSub_one]
  by_contra htop
  have hAle : A ≤ CFSG.Quasithin.B6.conjSub g⁻¹ H := by
    intro x hx
    show x ∈ H.map (MulAut.conj g⁻¹).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
      group
  have hne : CFSG.Quasithin.B6.conjSub g⁻¹ H ≠ ⊤ := by
    intro heq
    apply htop
    rw [← hcyc, heq]
    exact OrderIso.map_top _
  have hHleM : CFSG.Quasithin.B6.conjSub g⁻¹ H ≤ M := h.unique_max _ hAle hne
  have hHle : H ≤ CFSG.Quasithin.B6.conjSub g M := by
    rw [← hcyc]
    exact (CFSG.Quasithin.B6.conjSub g).monotone hHleM
  have haMg : a ∈ M.map (MulAut.conj g).toMonoidHom :=
    hHle (show a ∈ H from Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  exact haK (h.mem_ker_of_mem_inf_conj hg (h.A_le_M ha) haMg
    (b12_TwelvePartTwo_two_elt h ha))

theorem Setting12Two.zpowers_conj_sup_eq_top (h : Setting12Two A M n) {g a : G} (hg : g ∉ M)
    (ha : a ∈ A) (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) :
    Subgroup.zpowers (g * a * g⁻¹) ⊔ A = ⊤ := by
  by_contra hH
  have hHleM : Subgroup.zpowers (g * a * g⁻¹) ⊔ A ≤ M :=
    h.unique_max _ le_sup_right hH
  have hgaM : g * a * g⁻¹ ∈ M :=
    hHleM (Subgroup.mem_sup_left (Subgroup.mem_zpowers (g * a * g⁻¹)))
  exact haK (b12_TwelvePartTwo_conj_mem_ker h (h.A_le_M ha) hg hgaM
    (b12_TwelvePartTwo_two_elt h ha))

end Generation

theorem twelveFive_partTwo {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}
    (h : Setting12Two A M n) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) {g : G} (hg : g ∉ M) :
    Conclusion121 ρ.range (A.map ρ) (ρ g)
      (fun a => ∃ a₀ ∈ A, a₀ ∉ CFSG.Quasithin.kerIn M ⊤ ∧ ρ a₀ = a) := by
  have hgen : ρ.range = A.map ρ ⊔ cj (ρ g) (A.map ρ) := by
    rw [MonoidHom.range_eq_map, ← Setting12Two.sup_conj_eq_top h hg, Subgroup.map_sup,
      map_conj_map_eq_cj]
  refine conclusion121_of_gen
    { g_mem := MonoidHom.mem_range.mpr ⟨g, rfl⟩, gen := hgen, quadratic := hq } ?_ ?_
  · intro a _ hPa
    obtain ⟨a₀, ha₀, ha₀K, rfl⟩ := hPa
    have hmap := congrArg (Subgroup.map ρ)
      (Setting12Two.zpowers_sup_conj_eq_top h hg ha₀ ha₀K)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_conj_map_eq_cj,
      Subgroup.map_top] at hmap
    exact hmap.symm
  · intro a _ hPa
    obtain ⟨a₀, ha₀, ha₀K, rfl⟩ := hPa
    have hmap := congrArg (Subgroup.map ρ)
      (Setting12Two.zpowers_conj_sup_eq_top h hg ha₀ ha₀K)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top] at hmap
    have hconj : (MulAut.conj (ρ g)) (ρ a₀) = ρ (g * a₀ * g⁻¹) := by
      simp [MulAut.conj_apply]
    rw [hconj]
    exact hmap.symm

end CFSG.LocalAnalysis.WeakClosure81
