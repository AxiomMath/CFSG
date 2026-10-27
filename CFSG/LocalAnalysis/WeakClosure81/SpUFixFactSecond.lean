module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

open scoped Pointwise

namespace SpUFixGeom

variable {L : Type} [Group L] {R : Subgroup L} {F V : Type} [Field F] [AddCommGroup V]
  [Module F V]

theorem exists_le_sylow_not_smul [Finite L] (G : SpUFixGeom L R F V) {Sy : Subgroup L}
    (hSy : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (R : Set L)) :
    ∃ u : V, u ≠ 0 ∧ G.β u u = 0 ∧ G.X u ≤ Sy ∧ ∀ c : F, u ≠ c • G.a := by
  obtain ⟨v, hvv, hav, hva⟩ := G.second
  have hv_ne : v ≠ 0 := fun h => hva 0 (by rw [h, zero_smul])
  have hXv_pgroup : IsPGroup 2 ↥(G.X v) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    refine fun y => ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using G.X_invol v hvv (y : L) y.2
  have hXv_le_N : G.X v ≤ Subgroup.normalizer (R : Set L) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy k hk
    have hk' : k ∈ G.X G.a := G.R_eq ▸ hk
    have hcomm : k * y = y * k := G.X_comm G.a v G.a_iso hvv hav k hk' y hy
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  obtain ⟨P, hP⟩ := hSy
  let N : Subgroup L := Subgroup.normalizer (R : Set L)
  have hPR : (P : Subgroup L) ≤ N := by
    change (P : Subgroup L) ≤ Subgroup.normalizer (R : Set L)
    rw [hP]
    exact hSyR
  let P' : Sylow 2 N := P.subtype hPR
  haveI : Finite (Sylow 2 N) := Sylow.finite_of_finiteIndex P'
  have hsub : IsPGroup 2 ((G.X v).subgroupOf N) := hXv_pgroup.comap_subtype
  obtain ⟨Q, hQ⟩ := hsub.exists_le_sylow
  obtain ⟨x', hx'⟩ := MulAction.exists_smul_eq N P' Q
  let x : L := (x' : L)
  have hXv_le : G.X v ≤ Sy.map (MulAut.conj x).toMonoidHom := by
    intro y hy
    have hyN : y ∈ N := hXv_le_N hy
    have hyQ : (⟨y, hyN⟩ : N) ∈ Q := hQ (by
      rw [Subgroup.mem_subgroupOf]
      exact hy)
    rw [← hx'] at hyQ
    change (⟨y, hyN⟩ : N) ∈ (MulAut.conj x' • (P' : Subgroup N) : Subgroup N) at hyQ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
    let s : N := (MulAut.conj x')⁻¹ • (⟨y, hyN⟩ : N)
    have hs : (s : L) ∈ Sy := by
      have h : s ∈ (P.subtype hPR : Subgroup N) := hyQ
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, hP] at h
      exact h
    refine ⟨(s : L), hs, ?_⟩
    simp only [MulAut.conj_apply, MulAut.conj_symm_apply, MulAut.inv_apply, MulAut.smul_def,
      MulEquiv.coe_toMonoidHom, Subgroup.coe_mul, Subgroup.coe_inv, x, s]
    group
  obtain ⟨M, hM_inj, hM_iso, hM_X, _⟩ := G.conj x⁻¹
  have hx'N : x ∈ N := x'.2
  have hx'inv : x⁻¹ ∈ N := N.inv_mem hx'N
  have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id L := by
    ext z
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hcancel : (Sy.map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom = Sy := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hMap_le : (G.X v).map (MulAut.conj x⁻¹).toMonoidHom ≤ Sy := by
    rw [← hcancel]
    exact Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hXv_le
  have hMa_eq : G.X (M G.a) = G.X G.a := by
    rw [← hM_X G.a G.a_iso, ← G.R_eq]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx'inv
  have hMa_ne : M G.a ≠ 0 := fun h => G.a_ne (hM_inj (h.trans (map_zero M).symm))
  have hMa_iso : G.β (M G.a) (M G.a) = 0 := (hM_iso G.a G.a).trans G.a_iso
  obtain ⟨c, hc⟩ :=
    G.X_inj G.a (M G.a) G.a_ne hMa_ne G.a_iso hMa_iso hMa_eq.symm
  have hc_ne : c ≠ 0 := by
    intro hc0
    exact hMa_ne (by rw [hc, hc0, zero_smul])
  refine ⟨M v, ?_, ?_, ?_, ?_⟩
  · intro hu
    exact hv_ne (hM_inj (hu.trans (map_zero M).symm))
  · exact (hM_iso v v).trans hvv
  · rw [← hM_X v hvv]
    exact hMap_le
  · intro c' hc'
    have hpt : (c' * c⁻¹) • G.a = v := by
      apply hM_inj
      calc M ((c' * c⁻¹) • G.a) = (c' * c⁻¹) • M G.a := LinearMap.map_smul M _ _
        _ = (c' * c⁻¹) • (c • G.a) := by rw [hc]
        _ = ((c' * c⁻¹) * c) • G.a := by rw [smul_smul]
        _ = c' • G.a := by rw [mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
        _ = M v := hc'.symm
    exact (hva (c' * c⁻¹)) hpt.symm

end SpUFixGeom

end CFSG.LocalAnalysis.WeakClosure81

end
