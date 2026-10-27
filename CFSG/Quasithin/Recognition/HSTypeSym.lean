module

public import CFSG.Quasithin.Recognition.HSTypeConj
public import CFSG.Quasithin.Recognition.HSTypeL12e

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem conj_inv_mem_Q_of_conj_mem_Q [Finite G] (h : HSSetting z V) {x : G}
    (hx : x * z * x⁻¹ ∈ hsQ z) : x⁻¹ * z * x ∈ hsQ z := by
  have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
  set y := x * z * x⁻¹ with hy
  have hyy : y * y = 1 := by
    rw [hy]
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
  have hy1 : y ≠ 1 := by
    intro h1
    apply h.z_ne_one
    calc z = x⁻¹ * y * x := by rw [hy]; group
      _ = 1 := by rw [h1]; group
  by_cases hyZ : y ∈ hsZQ z
  ·
    have hyz : y = z := h.eq_z_of_mem_ZQ hyZ hyy hy1
    have hxz : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * y * x := by rw [hyz]
        _ = z := by rw [hy]; group
    rw [hxz]
    exact h.mem_Q
  · obtain ⟨v, hvV, hvz⟩ := h.exists_mem_V_not_mem_zpowers
    have hv1 : v ≠ 1 := fun h1 => hvz (h1 ▸ (Subgroup.zpowers z).one_mem)
    have hvv : v * v = 1 := by
      have := h.elem.2 v hvV
      rwa [sq] at this
    have hvQ : v ∈ hsQ z := h.two.le hvV
    have hvZ : v ∉ hsZQ z := by
      intro hvZ
      exact hvz (h.eq_z_of_mem_ZQ hvZ hvv hv1 ▸ Subgroup.mem_zpowers z)
    obtain ⟨k, hk, hkyv⟩ := h.K_transitive hx hyy hyZ hvQ hvv hvZ
    obtain ⟨m, hm, hmz⟩ := h.exists_conj_eq_of_mem_V hvV hv1
    have hkz : k * z * k⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hk.1, mul_inv_cancel_right]
    set h' := x⁻¹ * (k⁻¹ * m) with hh'
    have hh'H : h' ∈ hsH z := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e1 : (k⁻¹ * m) * z * (k⁻¹ * m)⁻¹ = y := by
        calc (k⁻¹ * m) * z * (k⁻¹ * m)⁻¹ = k⁻¹ * (m * z * m⁻¹) * k := by group
          _ = k⁻¹ * (k * y * k⁻¹) * k := by rw [hmz, hkyv]
          _ = y := by group
      calc h' * z = x⁻¹ * ((k⁻¹ * m) * z * (k⁻¹ * m)⁻¹) * (k⁻¹ * m) := by rw [hh']; group
        _ = x⁻¹ * y * (k⁻¹ * m) := by rw [e1]
        _ = z * h' := by rw [hy, hh']; group
    have hmV : m⁻¹ * z * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp ((hsM V).inv_mem hm) z).mp h.mem_V
      simpa using this
    have e2 : x⁻¹ * z * x = h' * (m⁻¹ * z * m) * h'⁻¹ := by
      have e3 : m⁻¹ * z * m = m⁻¹ * (k * z * k⁻¹) * m := by rw [hkz]
      rw [e3, hh']
      group
    rw [e2]
    exact conj_mem_Q hh'H (h.two.le hmV)

theorem conj_mem_Q_iff [Finite G] (h : HSSetting z V) {x : G} :
    x * z * x⁻¹ ∈ hsQ z ↔ x⁻¹ * z * x ∈ hsQ z := by
  constructor
  · exact h.conj_inv_mem_Q_of_conj_mem_Q
  · intro hx
    have := h.conj_inv_mem_Q_of_conj_mem_Q (x := x⁻¹) (by simpa using hx)
    simpa using this

theorem mem_hsQ_conj_iff [Finite G] (h : HSSetting z V) (a b : G) :
    b * z * b⁻¹ ∈ hsQ (a * z * a⁻¹) ↔ a * z * a⁻¹ ∈ hsQ (b * z * b⁻¹) := by
  rw [hsQ_conj, hsQ_conj, mem_map_conj_iff, mem_map_conj_iff]
  have e1 : a⁻¹ * (b * z * b⁻¹) * a = (a⁻¹ * b) * z * (a⁻¹ * b)⁻¹ := by group
  have e2 : b⁻¹ * (a * z * a⁻¹) * b = (a⁻¹ * b)⁻¹ * z * (a⁻¹ * b) := by group
  rw [e1, e2]
  exact h.conj_mem_Q_iff

end HSSetting

end CFSG.Quasithin.HSType
