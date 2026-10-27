module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentGrp
import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotNormal

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem dentF2_conj_mem {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0) (hc : S0.card = 6) {d : X}
    (hd : d ∈ S.dentD S0) {f : X} (hf : f ∈ S.dentF2 S0) : d * f * d⁻¹ ∈ S.dentF2 S0 := by
  let G : Subgroup X := Subgroup.map (MulAut.conj d).toMonoidHom (S.dentF2 S0)
  have hGQ : G ≤ S.dentQ S0 := by
    intro x hx
    obtain ⟨y, hy, hx_eq⟩ := Subgroup.mem_map.1 hx
    have hyQ : y ∈ S.dentQ S0 := (Subgroup.mem_inf.1 hy).2
    rw [← hx_eq]
    simpa [MulAut.conj_apply] using S.dentQ_conj_mem hd hyQ
  have hGH : G ≤ S.H := hGQ.trans (S.dentQ_le_H h0)
  let M : Subgroup (Equiv.Perm (Fin 8)) := (G.subgroupOf S.H).map S.permHom
  have hM_bot : M = ⊥ := by
    apply perm_eq_bot_of_normal_of_exp_two S0 (by omega) (M := M)
    · intro m hm i hi
      obtain ⟨z, hz, hm_eq⟩ := Subgroup.mem_map.1 hm
      have hzG : (z : X) ∈ G := Subgroup.mem_subgroupOf.1 hz
      have hzQ : (z : X) ∈ S.dentQ S0 := hGQ hzG
      rw [← hm_eq]
      exact S.permHom_apply_eq_self_of_mem_dentQ hzQ hi
    · intro g hg m hm
      obtain ⟨z, hz, hm_eq⟩ := Subgroup.mem_map.1 hm
      have hzG : (z : X) ∈ G := Subgroup.mem_subgroupOf.1 hz
      obtain ⟨f', hf', hz_eq⟩ := Subgroup.mem_map.1 hzG
      obtain ⟨q, hqQ, hq_perm⟩ := S.exists_mem_dentQ_permHom_eq h0 hg
      let q' : X := d⁻¹ * (q : X) * d
      have hq'Q : q' ∈ S.dentQ S0 := by
        have hd_inv : d⁻¹ ∈ S.dentD S0 := (S.dentD S0).inv_mem hd
        simpa [q', MulAut.conj_apply, mul_assoc, inv_inv] using S.dentQ_conj_mem hd_inv hqQ
      have hf'' : q' * f' * q'⁻¹ ∈ S.dentF2 S0 := S.dentQ_conj_dentF2 h0 hq'Q hf'
      rw [Subgroup.mem_map]
      refine ⟨q * z * q⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        rw [Subgroup.mem_map]
        refine ⟨q' * f' * q'⁻¹, hf'', ?_⟩
        have hz_val : (z : X) = d * f' * d⁻¹ := by
          rw [← hz_eq]
          simp [MulAut.conj_apply]
        change d * (q' * f' * q'⁻¹) * d⁻¹ = (q : X) * (z : X) * (q : X)⁻¹
        rw [hz_val]
        change d * ((d⁻¹ * (q : X) * d) * f' * (d⁻¹ * (q : X) * d)⁻¹) * d⁻¹ =
          (q : X) * (d * f' * d⁻¹) * (q : X)⁻¹
        group
      · rw [← hm_eq, ← hq_perm]
        simp [map_mul, map_inv]
    · intro m hm
      obtain ⟨z, hz, hm_eq⟩ := Subgroup.mem_map.1 hm
      have hzG : (z : X) ∈ G := Subgroup.mem_subgroupOf.1 hz
      obtain ⟨f', hf', hz_eq⟩ := Subgroup.mem_map.1 hzG
      have hf'F1 : f' ∈ S.F1 := (Subgroup.mem_inf.1 hf').1
      have hf'_sq : f' * f' = 1 := S.F1_sq hf'F1
      have hz_sq : (z : X) * (z : X) = 1 := by
        have hz_val : (z : X) = d * f' * d⁻¹ := by
          rw [← hz_eq]
          simp [MulAut.conj_apply]
        rw [hz_val]
        calc
          (d * f' * d⁻¹) * (d * f' * d⁻¹) = d * f' * (d⁻¹ * d) * f' * d⁻¹ := by group
          _ = d * f' * f' * d⁻¹ := by simp [inv_mul_cancel]
          _ = d * (f' * f') * d⁻¹ := by group
          _ = d * 1 * d⁻¹ := by rw [hf'_sq]
          _ = 1 := by group
      have hz_sq_H : z * z = 1 := by
        apply Subtype.ext
        simpa using hz_sq
      have hm_sq : S.permHom z * S.permHom z = 1 := by
        rw [← map_mul, hz_sq_H, map_one]
      rw [← hm_eq]
      simpa using hm_sq
  have hfG : d * f * d⁻¹ ∈ G := by
    rw [Subgroup.mem_map]
    exact ⟨f, hf, by simp [MulAut.conj_apply]⟩
  have hyH : d * f * d⁻¹ ∈ S.H := hGH hfG
  let y : S.H := ⟨d * f * d⁻¹, hyH⟩
  have hyM : S.permHom y ∈ M := by
    rw [Subgroup.mem_map]
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hfG
  have hperm_y : S.permHom y = 1 := by
    rw [hM_bot] at hyM
    exact Subgroup.mem_bot.1 hyM
  have hyF1 : (y : X) ∈ S.F1 := (S.permHom_eq_one_iff_mem_F1 y).1 hperm_y
  have hyQ : (y : X) ∈ S.dentQ S0 := hGQ hfG
  exact Subgroup.mem_inf.2 ⟨hyF1, hyQ⟩

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
