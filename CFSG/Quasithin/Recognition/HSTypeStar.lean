module

public import CFSG.Quasithin.Recognition.HSTypeL12f

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem isConj_z_mul_of_comm [Finite G] (h : HSSetting z V) {v : G} (hv : IsConj z v)
    (hvz : v * z = z * v) (hzv : z * v ≠ 1) : IsConj z (z * v) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hv
  have hzz : z * z = 1 := h.z_mul_z
  have hvv : v * v = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
  have hvH : v ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr hvz
  have hv1 : v ≠ 1 := fun h1 => h.z_ne_one (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hg, h1]; group)
  by_cases hvK : v ∈ hsK z
  ·
    have hvQ : v ∈ hsQ z := by
      rw [← hg]
      exact h.mem_Q_of_conj_mem_K (by rw [hg]; exact hvK)
    have hvZ : v ∉ hsZQ z := fun hZ => by
      have := h.eq_z_of_mem_ZQ hZ hvv hv1
      exact hzv (by rw [this, hzz])
    have hzvQ : z * v ∈ hsQ z := (hsQ z).mul_mem h.mem_Q hvQ
    have hzv2 : z * v * (z * v) = 1 := by
      calc z * v * (z * v) = z * (v * z) * v := by group
        _ = z * z * (v * v) := by rw [hvz]; group
        _ = 1 := by rw [hzz, hvv, one_mul]
    have hzvZ : z * v ∉ hsZQ z := fun hZ => by
      apply hvZ
      have hzZ : z ∈ hsZQ z := ⟨h.mem_Q, Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_singleton_iff.mp (h.Q_le_H hq))⟩
      have := (hsZQ z).mul_mem hzZ hZ
      rwa [← mul_assoc, hzz, one_mul] at this
    obtain ⟨c, hc⟩ := h.exists_conj_z_of_invol_Q hzvQ hzv2 hzvZ
    exact isConj_iff.mpr ⟨c, hc⟩
  ·
    have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm⟩
    obtain ⟨r, -, hr⟩ := h.exists_conj_eq_mul_of_invol hvH hvK hvv hzC
    refine hv.trans (isConj_iff.mpr ⟨r, ?_⟩)
    rw [← hr, hvz]

theorem star [Finite G] (h : HSSetting z V) (u v : G) (hu : IsConj z u) (hv : IsConj z v)
    (huv : u * v = v * u) (huv1 : u * v ≠ 1) : IsConj z (u * v) := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hu
  set v' := a⁻¹ * v * a with hv'
  have hv'c : IsConj z v' := hv.trans (isConj_iff.mpr ⟨a⁻¹, by rw [hv', inv_inv]⟩)
  have hcomm : v' * z = z * v' := by
    have e : a * z * a⁻¹ * v * (a * z * a⁻¹)⁻¹ = v := by
      rw [show a * z * a⁻¹ * v * (a * z * a⁻¹)⁻¹ = (a * z * a⁻¹ * v) * (a * z * a⁻¹)⁻¹ from rfl,
        huv, mul_inv_cancel_right]
    calc v' * z = a⁻¹ * (v * (a * z * a⁻¹)) * a := by rw [hv']; group
      _ = a⁻¹ * ((a * z * a⁻¹) * v) * a := by rw [huv]
      _ = z * v' := by rw [hv']; group
  have hne : z * v' ≠ 1 := fun h1 => huv1 (by
    calc a * z * a⁻¹ * v = a * (z * v') * a⁻¹ := by rw [hv']; group
      _ = 1 := by rw [h1]; group)
  have := h.isConj_z_mul_of_comm hv'c hcomm hne
  refine this.trans (isConj_iff.mpr ⟨a, ?_⟩)
  rw [hv']
  group

end HSSetting

end CFSG.Quasithin.HSType
