module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenMax

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

abbrev adj (i : Fin 5) : Equiv.Perm (Fin 6) := Equiv.swap i.castSucc i.succ

theorem adj01_eq : adj 0 * adj 1 = Equiv.swap 0 1 * Equiv.swap 1 2 := by decide

theorem map_conj_map_conj (K : Subgroup GL4) (a b : GL4) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (K : Subgroup GL4) : K.map (MulAut.conj (1 : GL4)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

section Cert

theorem exists_conj_range {ψ : Equiv.Perm (Fin 6) →* GL4} (hψ : ψ (adj 0 * adj 1) ≠ 1) :
    ∃ c : GL4, ψ.range = Sbar.map (MulAut.conj c).toMonoidHom :=
  Certificates.certificate899110.2.2.2.1 ψ (by rwa [adj01_eq] at hψ)

theorem max_of_ne {ψ : Equiv.Perm (Fin 6) →* GL4} (hψ : ψ (adj 0 * adj 1) ≠ 1)
    {H : Subgroup GL4} (hH : ψ.range ≤ H) : H = ψ.range ∨ H = ⊤ := by
  obtain ⟨c, hc⟩ := exists_conj_range hψ
  rw [hc] at hH ⊢
  have hK : Sbar ≤ H.map (MulAut.conj c⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨c * x * c⁻¹, hH ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hH' : H = (H.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  rcases sbar_max4 hK with h | h
  · left
    rw [hH', h]
  · right
    rw [hH', h, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective]

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
