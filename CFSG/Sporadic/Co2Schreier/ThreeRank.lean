module

public import CFSG.Sporadic.Co2Schreier.ThreeSylow
public import CFSG.Sporadic.Co2Schreier.ThreeSix

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Open

theorem eq_locZ_of_isElemAbelian_locC
    {F : Subgroup (Equiv.Perm (Fin 2300))} (hFC : F ≤ locC)
    (hF : IsElemAbelian 3 F) (h27 : Nat.card F = 3 ^ 3) {u : Equiv.Perm (Fin 2300)}
    (hu : u ∈ locC) (hu2 : orderOf u = 2)
    (huF : u ∈ Subgroup.centralizer (F : Set (Equiv.Perm (Fin 2300)))) : u = locZ := by
  obtain ⟨c, hc, hcF⟩ := exists_conj_le_locP0 hFC hF.isPGroup
  set F' := F.map (MulAut.conj c).toMonoidHom with hF'
  have hF'card : Nat.card F' = 27 := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj c).injective, h27]
    norm_num
  have hF'comm : IsMulCommutative F' := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    haveI := hF.1
    have hxy := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
    change (MulAut.conj c).toMonoidHom x * (MulAut.conj c).toMonoidHom y =
      (MulAut.conj c).toMonoidHom y * (MulAut.conj c).toMonoidHom x
    rw [← map_mul, ← map_mul]
    exact congrArg _ hxy
  set u' := c * u * c⁻¹ with hu'
  have hu'C : u' ∈ locC := locC.mul_mem (locC.mul_mem hc hu) (locC.inv_mem hc)
  have hu'2 : u' * u' = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2, pow_two] at h
    rw [hu']
    calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hcomm : ∀ m ∈ p0MarkedIdx, u' * eltE enumP0 m = eltE enumP0 m * u' := by
    intro m hm
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.1 (eltE_mem_of_le_locP0 hcF hF'comm hF'card hm)
    rw [← hxm]
    have hxu : x * u = u * x := (Subgroup.mem_centralizer_iff.1 huF x hx)
    change c * u * c⁻¹ * (c * x * c⁻¹) = c * x * c⁻¹ * (c * u * c⁻¹)
    calc c * u * c⁻¹ * (c * x * c⁻¹) = c * (u * x) * c⁻¹ := by group
      _ = c * (x * u) * c⁻¹ := by rw [hxu]
      _ = c * x * c⁻¹ * (c * u * c⁻¹) := by group
  have hmarked : ∀ m, m = 56 ∨ m = 1 ∨ m = 20 → m ∈ p0MarkedIdx := by
    rintro m (rfl | rfl | rfl) <;> rw [p0Marked_check] <;> decide
  have hQ : u' ∈ locQ := mem_locQ_of_commute hu'C hu'2 (hcomm 56 (hmarked 56 (by simp)))
    (hcomm 1 (hmarked 1 (by simp))) (hcomm 20 (hmarked 20 (by simp)))
  have hcz : c * locZ = locZ * c :=
    Subgroup.mem_centralizer_singleton_iff.1 (locC_le_centralizer hc)
  rcases eq_one_or_eq_locZ_of_mem_locQ hQ (hcomm 56 (hmarked 56 (by simp))) with h1 | hz
  · exfalso
    have : u = 1 := by
      have h' : c * u * c⁻¹ = 1 := h1
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = 1 := by rw [h']; group
    rw [this, orderOf_one] at hu2
    norm_num at hu2
  · have h' : c * u * c⁻¹ = locZ := hz
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = c⁻¹ * (locZ * c) := by rw [h']; group
      _ = c⁻¹ * (c * locZ) := by rw [hcz]
      _ = locZ := by group

end CFSG.Sporadic.Co2Schreier
