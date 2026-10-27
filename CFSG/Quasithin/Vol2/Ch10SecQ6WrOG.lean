module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrGam

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

theorem Y0_le_of_S0_lt {H : Subgroup SymFiveWrTwo} (hS : S0 ≤ H) (hne : H ≠ S0) : Y0 ≤ H := by
  have hT : wrT ∈ H := hS (wrT_mem_wrSub _)
  have hD : ∀ q, D8 ≤ coordSub H q := fun q σ hσ => hS (wrIota_mem_wrSub hσ q)
  obtain ⟨h, hh, hhS⟩ : ∃ h ∈ H, h ∉ S0 := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc hS)
  obtain ⟨q, hq⟩ : ∃ q, h.left q ∉ D8 := by
    by_contra hc
    push Not at hc
    exact hhS hc
  obtain ⟨h', hh', hr', hl'⟩ := exists_base hT hh
  obtain ⟨d, hd, hdx⟩ := exists_comm_not_mem (h.left q) hq
  have hdH : wrIota q d ∈ H := hS (wrIota_mem_wrSub hd q)
  have hK : coordSub H q ≠ D8 := by
    intro hK
    apply hdx
    rw [← hK, Subgroup.mem_comap]
    have hc := commutator_wrIota h'.left q d
    rw [← eq_wrBaseHom hr', hl'] at hc
    have he' : d * h.left q * d⁻¹ * (h.left q)⁻¹ = (h.left q * d * (h.left q)⁻¹ * d⁻¹)⁻¹ := by
      group
    have he : wrIota q (d * h.left q * d⁻¹ * (h.left q)⁻¹) =
        (wrIota q (h.left q * d * (h.left q)⁻¹ * d⁻¹))⁻¹ := by
      rw [he', map_inv]
    rw [he, ← hc]
    exact H.inv_mem (H.mul_mem (H.mul_mem (H.mul_mem hh' hdH) (H.inv_mem hh')) (H.inv_mem hdH))
  have hS4 : ∀ q', S4 ≤ coordSub H q' := by
    intro q'
    rcases eq_or_eq_zs_mul q q' with rfl | rfl
    · exact S4_le_of_D8_lt (hD q') hK
    · rw [coordSub_zs_mul hT]
      exact S4_le_of_D8_lt (hD q) hK
  have hbase : ∀ g ∈ Y0, g.right = 1 → g ∈ H := by
    intro g hg hr
    rw [eq_mul_wrIota hr]
    exact H.mul_mem (hS4 1 (hg 1)) (hS4 zs (hg zs))
  intro g hg
  rcases zmod2_cases g.right with hr | hr
  · exact hbase g hg hr
  · have h1 : g * wrT ∈ H := hbase _ (Y0.mul_mem hg (wrT_mem_wrSub _))
      (by rw [RegularWreathProduct.mul_right, hr]; decide)
    simpa using H.mul_mem h1 (H.inv_mem hT)

theorem exists_conj_S0 {S : Subgroup SymFiveWrTwo} (h2 : IsPGroup 2 S) (hi : ¬ 2 ∣ S.index) :
    ∃ g : SymFiveWrTwo, S = S0.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P0 := isPGroup_S0.toSylow not_two_dvd_index_S0
  let P1 := h2.toSylow hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SymFiveWrTwo P0 P1
  refine ⟨g, ?_⟩
  have h1 : ((g • P0 : Sylow 2 SymFiveWrTwo) : Subgroup SymFiveWrTwo) = S := by
    rw [hg]
    rfl
  rw [← h1, Sylow.coe_subgroup_smul]
  rfl

theorem exists_conj_le {S Y : Subgroup SymFiveWrTwo} (h2 : IsPGroup 2 S) (hi : ¬ 2 ∣ S.index)
    (hSY : S ≤ Y) (hne : S ≠ Y) : ∃ g : SymFiveWrTwo, Y0.map (MulAut.conj g).toMonoidHom ≤ Y := by
  obtain ⟨g, rfl⟩ := exists_conj_S0 h2 hi
  refine ⟨g, ?_⟩
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hY : Y = Y'.map (MulAut.conj g).toMonoidHom := by
    rw [hY', Subgroup.map_map, hcomp, Subgroup.map_id]
  have hS0 : S0 ≤ Y' := by
    rw [hY'] at *
    intro x hx
    refine ⟨MulAut.conj g x, hSY ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hne' : Y' ≠ S0 := by
    intro h
    apply hne
    rw [hY, h]
  rw [hY]
  exact Subgroup.map_mono (Y0_le_of_S0_lt hS0 hne')

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
