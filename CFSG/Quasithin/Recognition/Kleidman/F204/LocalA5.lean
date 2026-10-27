module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.HA5Weyl

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem normalizer_kleinStd_iff_perm :
    ∀ x : Perm (Fin 5), Perm.sign x = 1 →
      ((∀ h : Perm (Fin 5), Perm.sign h = 1 → (h ∈ kleinSet ↔ x * h * x⁻¹ ∈ kleinSet)) ↔
        x 4 = 4) := by
  decide +kernel

theorem alt5_two_point_perm :
    ∀ x : Perm (Fin 5), Perm.sign x = 1 → x 4 ≠ 4 →
      ∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y 4 = 4 ∧ (x⁻¹ * y * x) 4 = 4 ∧ y ^ 3 = 1 ∧ y ≠ 1 := by
  decide +kernel


theorem sign_eq_one_of_alt5 (a : Alt5) : Perm.sign (a : Perm (Fin 5)) = 1 :=
  Perm.mem_alternatingGroup.mp a.2

theorem mem_normalizer_kleinStd (z : Alt5) :
    z ∈ Subgroup.normalizer (kleinStd : Set Alt5) ↔ (z : Perm (Fin 5)) 4 = 4 := by
  rw [Subgroup.mem_normalizer_iff, ← normalizer_kleinStd_iff_perm (z : Perm (Fin 5))
    (sign_eq_one_of_alt5 z)]
  constructor
  · intro h k hk
    have := h ⟨k, Perm.mem_alternatingGroup.mpr hk⟩
    rwa [mem_kleinStd, mem_kleinStd] at this
  · intro h k
    rw [mem_kleinStd, mem_kleinStd]
    exact h (k : Perm (Fin 5)) (sign_eq_one_of_alt5 k)

theorem alt5_two_point {T : Subgroup Alt5} (hT : Nat.card T = 4) {x : Alt5}
    (hx : x ∉ Subgroup.normalizer (T : Set Alt5)) :
    ∃ y : Alt5, y ∈ Subgroup.normalizer (T : Set Alt5) ∧
      x⁻¹ * y * x ∈ Subgroup.normalizer (T : Set Alt5) ∧ y ^ 3 = 1 ∧ y ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_conj_kleinStd T hT
  have hN : ∀ z : Alt5, z ∈ Subgroup.normalizer (T : Set Alt5) ↔
      g⁻¹ * z * g ∈ Subgroup.normalizer (kleinStd : Set Alt5) := by
    intro z
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h k
      have := h (g * k * g⁻¹)
      rw [hg, hg] at this
      have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
      have e2 : g⁻¹ * (z * (g * k * g⁻¹) * z⁻¹) * g = (g⁻¹ * z * g) * k * (g⁻¹ * z * g)⁻¹ := by
        group
      rwa [e, e2] at this
    · intro h k
      have := h (g⁻¹ * k * g)
      rw [hg, hg]
      have e2 : g⁻¹ * (z * k * z⁻¹) * g = (g⁻¹ * z * g) * (g⁻¹ * k * g) * (g⁻¹ * z * g)⁻¹ := by
        group
      rwa [e2]
  have hx' : (g⁻¹ * x * g : Alt5) ∉ Subgroup.normalizer (kleinStd : Set Alt5) := fun h => hx ((hN x).mpr h)
  rw [mem_normalizer_kleinStd] at hx'
  obtain ⟨y', hs, h4, hxy, h3, h1⟩ := alt5_two_point_perm ((g⁻¹ * x * g : Alt5) : Perm (Fin 5))
    (sign_eq_one_of_alt5 _) hx'
  set y'' : Alt5 := ⟨y', Perm.mem_alternatingGroup.mpr hs⟩ with hy''
  refine ⟨g * y'' * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    have : g⁻¹ * (g * y'' * g⁻¹) * g = y'' := by group
    rw [this, mem_normalizer_kleinStd]
    exact h4
  · rw [hN]
    have : g⁻¹ * (x⁻¹ * (g * y'' * g⁻¹) * x) * g = (g⁻¹ * x * g)⁻¹ * y'' * (g⁻¹ * x * g) := by
      group
    rw [this, mem_normalizer_kleinStd]
    exact hxy
  · have : (g * y'' * g⁻¹) ^ 3 = g * y'' ^ 3 * g⁻¹ := by
      rw [conj_pow]
    rw [this]
    have h3' : y'' ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [h3']
    group
  · intro h
    apply h1
    have : y'' = 1 := by
      have e : y'' = g⁻¹ * (g * y'' * g⁻¹) * g := by group
      rw [e, h]; group
    exact congrArg Subtype.val this

end CFSG.Quasithin.Kleidman.F204
