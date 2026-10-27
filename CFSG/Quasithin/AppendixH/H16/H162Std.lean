module

public import CFSG.Quasithin.AppendixH.H16.H162Twist
public import CFSG.Quasithin.AppendixH.H16.OctadZ7
public import CFSG.Quasithin.AppendixH.H16.OctadZ8

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24 CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

private theorem rho_mem_octV5' (γ : ↥M24g) (hγ : (γ : S24) ∈ octStab octad0) {y : W11}
    (hy : y ∈ octV5) : rhoC11 AutPerm le_rfl γ y ∈ octV5 :=
  isActsInv_octV5 (fun v => rhoC11 AutPerm le_rfl γ v)
    ⟨rhoC11 AutPerm le_rfl γ, rhoCd_mem_imgCd γ.2 hγ, rfl⟩ y hy

private theorem conj_mem_fixO' {d k : S24} (hd : d ∈ octStab octad0) (hk : k ∈ fixO) :
    d * k * d⁻¹ ∈ fixO := by
  have hk' : k ∈ octStab octad0 := fixO_le_octStab_octad0 hk
  have hmem : (⟨k, hk'⟩ : ↥(octStab octad0)) ∈ (octFix octad0).subgroupOf (octStab octad0) :=
    Subgroup.mem_subgroupOf.2 (by rw [octFix_octad0]; exact hk)
  have h1 := (normal_octFix octad0).conj_mem (⟨k, hk'⟩ : ↥(octStab octad0)) hmem
    (⟨d, hd⟩ : ↥(octStab octad0))
  have h2 := Subgroup.mem_subgroupOf.1 h1
  rw [octFix_octad0] at h2
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2

theorem h162Z_koOne :
    H162Z (rhoC11 AutPerm le_rfl) octQ octV5 fixO (koPerm 1) := by
  have hfix : fixV (rImg (Γ := M24g) (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) =
      octWz := by
    change fixV (imgCd (Subgroup.zpowers (koPerm 1))) = octWz
    exact fixV_imgCd_zpowers_koOne
  have hW : octV5 ⊓ fixV (rImg (Γ := M24g) (rhoC11 AutPerm le_rfl)
      (Subgroup.zpowers (koPerm 1))) = octVz := by
    rw [hfix, octV5_inf_octWz]
  have hD : (cenM (Γ := M24g) (rhoC11 AutPerm le_rfl)
      (octV5 ⊓ fixV (rImg (Γ := M24g) (rhoC11 AutPerm le_rfl)
        (Subgroup.zpowers (koPerm 1))))).map M24g.subtype = dGrp :=
    cenMS_octV5_inf_fixV
  have hp : pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)) = fixO ⊔ dGrp :=
    pCoreOf_cent_koOne
  unfold H162Z
  refine ⟨clause3c_std, cenM_octWz, ⟨?_, ?_, ?_, ?_⟩, ?_, clause8_std⟩
  · rw [hW]; exact rk_octVz
  · rw [hD]; exact dGrp_isE2k
  · rw [hD]; exact pCoreOf_cent_koOne
  · intro element helement
    rw [hD]
    rw [hp] at helement
    rw [mem_fixO_sup_dGrp_iff] at helement
    exact helement
  · intro B hzB hB
    rw [hD] at hB
    exact clause7_std B hzB hB

theorem h162Z_std
    {z : S24} (hz : z ∈ fixO) (hz1 : z ≠ 1) :
    H162Z (rhoC11 AutPerm le_rfl) octQ octV5 fixO z := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff z).1 hz
  have ht : t ≠ 0 := by
    intro h
    exact hz1 (by rw [h, koPerm_zero])
  obtain ⟨m, hm, hmt⟩ := exists_octStab_conj_koPerm t ht
  let τ' : ↥M24g := ⟨m, octStab_octad0_le_AutPerm hm⟩
  let ρM : ↥M24g →* MulAut W11 := rhoC11 AutPerm le_rfl
  have hcongr : ∀ γ : ↥M24g,
      CFSG.Quasithin.H.congrHom (ρM τ'⁻¹) (ρM γ) = ρM (τ'⁻¹ * γ * τ') := by
    intro γ
    have h := congrHom_twist ρM ρM (MulEquiv.refl W11) (fun _ _ => rfl) τ' γ
    have heq : (ρM τ'⁻¹).trans (MulEquiv.refl W11) = ρM τ'⁻¹ := by
      ext x; simp
    rw [heq] at h
    exact h
  have hQ : ∀ x, octQ (ρM τ'⁻¹ x) = octQ x := by
    intro x
    exact octQ_rhoC11 τ'⁻¹ ((octStab octad0).inv_mem hm) x
  have hV₅ : octV5.map (ρM τ'⁻¹).toMonoidHom = octV5 := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact rho_mem_octV5' τ'⁻¹ ((octStab octad0).inv_mem hm) hy
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨ρM τ' y, rho_mem_octV5' τ' hm hy, ?_⟩
      show ρM τ'⁻¹ (ρM τ' y) = y
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hconj_fixO : conjSubg m fixO = fixO := by
    apply le_antisymm
    · intro x hx
      rw [mem_conjSubg_iff] at hx
      have hx' := conj_mem_fixO' hm hx
      have hx'' : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rwa [hx''] at hx'
    · intro x hx
      rw [mem_conjSubg_iff]
      simpa using conj_mem_fixO' ((octStab octad0).inv_mem hm) hx
  have hinv : conjSubg m⁻¹ fixO = fixO := by
    have h := conjSubg_inv_conjSubg m fixO
    rwa [hconj_fixO] at h
  have hKO : fixO = conjSubg ((τ' : S24)⁻¹) fixO := by
    show fixO = conjSubg m⁻¹ fixO
    exact hinv.symm
  have hzM : koPerm t ∈ M24g :=
    fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm
      ((mem_fixO_iff (koPerm t)).2 ⟨t, rfl⟩)
  have hz' : koPerm 1 = (τ' : S24)⁻¹ * koPerm t * (τ' : S24) := by
    show koPerm 1 = m⁻¹ * koPerm t * m
    rw [← hmt]
    group
  exact H162Z_of_twist ρM ρM (ρM τ'⁻¹) τ' hcongr hQ hV₅ hKO hzM hz' h162Z_koOne

end CFSG.ASVolI.H16
