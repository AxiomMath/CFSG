module

public import CFSG.Sporadic.Fi22.LocalType
public import CFSG.Fischer.UnitaryTransport
public import CFSG.Sporadic.Fi22.Classes
import all CFSG.Fischer.F4
public import CFSG.Fischer.T46Unitary

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.F4.Native CFSG.Blueprint.Fischer CFSG.Fischer Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local irreducible] CFSG.F4.Native.uPts CFSG.Fischer.ptIdx CFSG.Fischer.uVec

noncomputable def localIso :
    LocalQuotient D a ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K) :=
  (quotientCenterCongr (MulEquiv.subgroupCongr localGroup_eq)).trans
    (caQuotEquiv.trans (suQuotEquiv.symm.trans psuEquiv))

noncomputable def tvSU (m : Fin 693) : SU0 :=
  ⟨tvGL (uVec m) (uVec_iso ptsFacts m.2), tvGL_mem_SU0 _⟩

theorem piSU_tvSU (m : Fin 693) : piSU (tvSU m) = tvPt m := by
  ext i
  rw [piSU_apply]
  show _ = (tvGU (uVec m) (uVec_iso ptsFacts m.2) • i).val
  rw [smul_val]
  rfl

theorem tvPt_mem_T46
    (u : Fin 693) : tvPt u ∈ T46 := by
  rw [← rho_ptE]; exact rho_mem_T46 _

theorem localIso_star
    (u : Fin 693) (f : LocalGroup D a) (hf : (f : J) = ptE u) :
    localIso (QuotientGroup.mk f) = QuotientGroup.mk (suEquiv (tvSU u)) := by
  unfold localIso
  rw [MulEquiv.trans_apply, quotientCenterCongr_mk, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : MulEquiv.subgroupCongr localGroup_eq f = ⟨ptE u, ptE_mem_Ca u⟩ := Subtype.ext hf
  rw [h1]
  have h2 : caQuotEquiv (QuotientGroup.mk ⟨ptE u, ptE_mem_Ca u⟩) = ⟨tvPt u, tvPt_mem_T46 u⟩ :=
    Subtype.ext (by rw [caQuotEquiv_mk, rho_ptE])
  rw [h2]
  have h3 : suQuotEquiv.symm ⟨tvPt u, tvPt_mem_T46 u⟩ = QuotientGroup.mk (tvSU u) := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [suQuotEquiv_mk, piSU_tvSU]
  rw [h3, psuEquiv_mk]

theorem ψV_add_smul (x w : W) (c : F4) : ψV (x + c • w) = ψV x + ψ c • ψV w := by
  funext i
  simp only [ψV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

theorem ψGL_tv_mulVec (w : W) (hw : hermStd w w = 0) (x : Blueprint.Fischer.V) :
    ((ψGL (tvGL w hw) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec x =
      x + hermitian 1 x (ψV w) • ψV w := by
  obtain ⟨x0, rfl⟩ := ψV_surjective x
  rw [ψGL_val, tvGL_val, mulVec_ψ, tvM_mulVec, ψV_add_smul, hermitian_ψ, herm_eq_std]

theorem ψV_ne_zero {w : W} (hw : w ≠ 0) : ψV w ≠ 0 := by
  intro h
  apply hw
  apply ψV_injective
  rw [h]
  funext i
  simp [ψV]

theorem hermitian_ψV_self (w : W) : hermitian 1 (ψV w) (ψV w) = ψ (hermStd w w) := by
  rw [hermitian_ψ, herm_eq_std]

theorem tvSU_mem (u : Fin 693) :
    (QuotientGroup.mk (suEquiv (tvSU u)) : PSU (1 : Matrix (Fin 6) (Fin 6) K)) ∈
      Transvections 1 := by
  refine ⟨suEquiv (tvSU u), rfl, ψV (uVec u), ψV_ne_zero (uVec_ne_zero ptsFacts u.2), ?_, ?_⟩
  · rw [hermitian_ψV_self, uVec_iso ptsFacts u.2, map_zero]
  · intro x
    rw [suEquiv_val]
    exact ψGL_tv_mulVec _ (uVec_iso ptsFacts u.2) x

private theorem cube_one : ∀ c : F4, c ≠ 0 → c ^ 2 * c = 1 := by decide

theorem tvM_smul {c : F4} (hc : c ≠ 0) (w : W) : tvM (c • w) = tvM w := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [tvM_mulVec, tvM_mulVec, hermStd_smul_right, smul_smul]
  congr 2
  calc c ^ 2 * hermStd x w * c = (c ^ 2 * c) * hermStd x w := by ring
    _ = hermStd x w := by rw [cube_one c hc, one_mul]

theorem transvection_preimage
    (q : PSU (1 : Matrix (Fin 6) (Fin 6) K))
    (hq : q ∈ Transvections 1) : ∃ u : Fin 693, q = QuotientGroup.mk (suEquiv (tvSU u)) := by
  obtain ⟨s', rfl, v, hv0, hviso, hact⟩ := hq
  obtain ⟨w0, rfl⟩ := ψV_surjective v
  have hw0 : w0 ≠ 0 := fun h => hv0 (by rw [h]; funext i; simp [ψV])
  have hiso : hermStd w0 w0 = 0 := by
    rw [hermitian_ψV_self] at hviso
    exact ψ.injective (by rw [hviso, map_zero])
  refine ⟨⟨ptIdx w0, ptIdx_lt ptsFacts hw0 hiso⟩, congrArg QuotientGroup.mk ?_⟩
  have hgl : (tvSU ⟨ptIdx w0, ptIdx_lt ptsFacts hw0 hiso⟩ : GL (Fin 6) F4) = tvGL w0 hiso := by
    apply Units.ext
    show tvM (uVec (ptIdx w0)) = tvM w0
    rw [uVec_ptIdx ptsFacts hw0 hiso]
    obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw0
    rw [hcw, tvM_smul hc]
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [hact x, suEquiv_val, hgl, ψGL_tv_mulVec]

theorem ptE_mem_localGroup
    (u : Fin 693) : (ptE u : J) ∈ LocalGroup D a :=
  Subgroup.subset_closure (ptE u).2

theorem localIso_image :
    localIso '' LocalImages D a = Transvections 1 := by
  ext q
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := ptE.surjective ⟨f, hf⟩
    rw [localIso_star u f (congrArg Subtype.val hu).symm]
    exact tvSU_mem u
  · intro hq
    obtain ⟨u, rfl⟩ := transvection_preimage q hq
    refine ⟨QuotientGroup.mk ⟨ptE u, ptE_mem_localGroup u⟩,
      ⟨⟨ptE u, ptE_mem_localGroup u⟩, (ptE u).2, rfl⟩, ?_⟩
    exact localIso_star u _ rfl

theorem f22_J :
    F22 J D :=
  ⟨pair_D, a, a_mem_D, 1, isNondegenerateHermitian_one, localIso, localIso_image⟩

end CFSG.Sporadic.Fi22
