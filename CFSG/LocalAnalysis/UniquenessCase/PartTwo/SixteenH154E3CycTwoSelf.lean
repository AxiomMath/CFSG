module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

theorem s16h_e3_CycTwoSelf_centralizer_le [Finite X] [Finite (MulAut X)]
    (F : s16h_CycFrame Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hDe : IsElemAbelian 3 D)
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = 3 ^ k) → a ∈ D)
    (hcent : ∀ c ∈ autSub (s16h_CycN Mb z) U,
      c ∈ Subgroup.centralizer (D : Set (MulAut ↥U)) → c ∈ D) :
    Subgroup.centralizer (F.core D : Set (MulAut X)) ⊓ Mb ≤ F.core D := by
  intro g hg
  have hzcore : z ∈ F.core D := F.z_mem_core D hzD
  have hzg : Commute z g := (Subgroup.mem_centralizer_iff.1 hg.1) z hzcore
  have hzpow : ∀ k : ℤ, g * z ^ k * g⁻¹ = z ^ k := by
    intro k
    have hk : Commute g (z ^ k) := (hzg.symm).zpow_right k
    calc g * z ^ k * g⁻¹ = (g * z ^ k) * g⁻¹ := by group
      _ = (z ^ k * g) * g⁻¹ := by rw [hk.eq]
      _ = z ^ k := by group
  have hzpow_inv : ∀ k : ℤ, g⁻¹ * z ^ k * g = z ^ k := by
    intro k
    have hk : Commute g⁻¹ (z ^ k) := ((hzg.symm).zpow_right k).inv_left
    calc g⁻¹ * z ^ k * g = (g⁻¹ * z ^ k) * g := by group
      _ = (z ^ k * g⁻¹) * g := by rw [hk.eq]
      _ = z ^ k := by group
  have hgN : g ∈ s16h_CycN Mb z := by
    refine ⟨hg.2, ?_⟩
    refine Subgroup.mem_set_normalizer_iff.2 fun h => ⟨?_, ?_⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [← hk, hzpow k]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have h' : h = z ^ k := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = g⁻¹ * z ^ k * g := by rw [← hk]
          _ = z ^ k := hzpow_inv k
      rw [h']
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hDcore : D ≤ autSub (F.core D) U := s16h_e3_CycTwoCoreA_le_autSub F hDA hDe hSyl
  refine ⟨hgN, fun m hm h => ?_⟩
  let k : ↥(s16h_CycN Mb z) := ⟨m⁻¹ * g * m, h⟩
  have hmem : F.rho k ∈ D := by
    refine hcent (F.rho k) ?_ ?_
    · rw [← F.rho_range]
      exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      obtain ⟨n, hncore, hnd⟩ := mem_autSub.1 (hDcore hd)
      let nN : ↥(s16h_CycN Mb z) := ⟨(n : MulAut X), F.core_le_N D hncore⟩
      have hden : resHom U n = F.rho nN := by
        refine MulEquiv.ext fun u => Subtype.ext ?_
        rw [resHom_apply, F.rho_apply]
      have hacomm : (m * (n : MulAut X) * m⁻¹) * g =
          g * (m * (n : MulAut X) * m⁻¹) :=
        (Subgroup.mem_centralizer_iff.1 hg.1) _ (F.conj_mem_core D hm hncore)
      have hxn : (n : MulAut X) * (m⁻¹ * g * m) =
          (m⁻¹ * g * m) * (n : MulAut X) := by
        calc (n : MulAut X) * (m⁻¹ * g * m)
            = m⁻¹ * ((m * (n : MulAut X) * m⁻¹) * g) * m := by group
          _ = m⁻¹ * (g * (m * (n : MulAut X) * m⁻¹)) * m := by rw [hacomm]
          _ = (m⁻¹ * g * m) * (n : MulAut X) := by group
      have hsub : nN * k = k * nN := by
        apply Subtype.ext
        exact hxn
      calc d * F.rho k = F.rho nN * F.rho k := by rw [← hnd, hden]
        _ = F.rho (nN * k) := (map_mul F.rho nN k).symm
        _ = F.rho (k * nN) := by rw [hsub]
        _ = F.rho k * F.rho nN := map_mul F.rho k nN
        _ = F.rho k * d := by rw [← hden, hnd]
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
