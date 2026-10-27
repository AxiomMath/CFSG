module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalA5

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem klein_sq_perm : ∀ k ∈ kleinSet, k * k = 1 := by decide +kernel

theorem klein_free_perm : ∀ x y : Perm (Fin 5), Perm.sign x = 1 → x 4 ≠ 4 → y ∈ kleinSet →
    (x⁻¹ * y * x) 4 = 4 → y = 1 := by
  decide +kernel

theorem alt5_klein_sq {T : Subgroup Alt5} (hT : Nat.card T = 4) {k : Alt5} (hk : k ∈ T) :
    k * k = 1 := by
  obtain ⟨g, hg⟩ := exists_conj_kleinStd T hT
  have h1 : g⁻¹ * k * g ∈ kleinStd := (hg k).mp hk
  have h2 : (g⁻¹ * k * g) * (g⁻¹ * k * g) = 1 :=
    Subtype.ext (klein_sq_perm _ h1)
  have : k * k = g * ((g⁻¹ * k * g) * (g⁻¹ * k * g)) * g⁻¹ := by group
  rw [this, h2]
  group

theorem alt5_klein_free {T : Subgroup Alt5} (hT : Nat.card T = 4) {x y : Alt5}
    (hx : x ∉ Subgroup.normalizer (T : Set Alt5)) (hy : y ∈ T)
    (hxy : x⁻¹ * y * x ∈ Subgroup.normalizer (T : Set Alt5)) : y = 1 := by
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
  set x' : Alt5 := g⁻¹ * x * g with hx'
  set y' : Alt5 := g⁻¹ * y * g with hy'
  have hx4 : (x' : Perm (Fin 5)) 4 ≠ 4 := by
    exact fun h => hx ((hN x).mpr ((mem_normalizer_kleinStd x').mpr h))
  have hyK : y' ∈ kleinStd := (hg y).mp hy
  have hxy4 : ((x'⁻¹ * y' * x' : Alt5) : Perm (Fin 5)) 4 = 4 := by
    have h := (hN _).mp hxy
    have e : g⁻¹ * (x⁻¹ * y * x) * g = x'⁻¹ * y' * x' := by
      rw [hx', hy']; group
    rw [e, mem_normalizer_kleinStd] at h
    exact h
  have key := klein_free_perm (x' : Perm (Fin 5)) (y' : Perm (Fin 5)) (sign_eq_one_of_alt5 _) hx4
    hyK (by simpa using hxy4)
  have hy1 : y' = 1 := Subtype.ext key
  have : y = g * y' * g⁻¹ := by rw [hy']; group
  rw [this, hy1]
  group

end CFSG.Quasithin.Kleidman.F204
