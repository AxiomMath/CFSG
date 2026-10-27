module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier

theorem on_exists_inv_of_fix_seven
    {α : MulAut Pv} (hα2 : α * α = 1) (hα1 : α ≠ 1) {y : Pv} (hy7 : y ^ 7 = 1) (hy1 : y ≠ 1)
    {u : Pv} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huy : u * y = y * u) (hαy : α y = y) :
    ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  obtain ⟨g, k, hk, rfl⟩ := on_exists_conj_pow_on7W_zero hy7 hy1 hu2 hu1 huy
  let β : MulAut Pv := MulAut.conj g⁻¹ * α * MulAut.conj g
  have hβapply : ∀ x : Pv, β x = g⁻¹ * α (g * x * g⁻¹) * g := by
    intro x
    simp only [β, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hβ2 : β * β = 1 := by
    simp only [β]
    rw [map_inv (MulAut.conj) g]
    calc (MulAut.conj g)⁻¹ * α * MulAut.conj g *
          ((MulAut.conj g)⁻¹ * α * MulAut.conj g)
        = (MulAut.conj g)⁻¹ * (α * α) * MulAut.conj g := by group
      _ = (MulAut.conj g)⁻¹ * 1 * MulAut.conj g := by rw [hα2]
      _ = 1 := by group
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    have hαeq : α = MulAut.conj g * β * MulAut.conj g⁻¹ := by
      simp only [β]
      rw [map_inv (MulAut.conj) g]
      group
    rw [hαeq, h, map_inv (MulAut.conj) g]
    group
  have hβfix : β (on7W 0 ^ k) = on7W 0 ^ k := by
    rw [hβapply, hαy]
    group
  have hβ0 : β (on7W 0) = on7W 0 := by
    have hcop : Nat.Coprime k (orderOf (on7W 0)) := by
      rw [orderOf_on7W 0]
      exact Nat.coprime_comm.mp (Nat.prime_seven.coprime_iff_not_dvd.mpr hk)
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp (CFSG.Quasithin.A4.mem_zpowers_pow_of_coprime hcop)
    calc β (on7W 0) = β ((on7W 0 ^ k) ^ n) := by rw [hn]
      _ = (β (on7W 0 ^ k)) ^ n := map_zpow β _ n
      _ = (on7W 0 ^ k) ^ n := by rw [hβfix]
      _ = on7W 0 := hn
  obtain ⟨z', hz', hz'inv⟩ := on_exists_inv_of_fix_on7W_zero hβ2 hβ1 hβ0
  have hαz : α (g * z' * g⁻¹) = (g * z' * g⁻¹)⁻¹ := by
    have h := hz'inv
    rw [hβapply] at h
    calc α (g * z' * g⁻¹) = g * (g⁻¹ * α (g * z' * g⁻¹) * g) * g⁻¹ := by group
      _ = g * z'⁻¹ * g⁻¹ := by rw [h]
      _ = (g * z' * g⁻¹)⁻¹ := by group
  exact ⟨g * z' * g⁻¹, hz'.conj g, hαz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
