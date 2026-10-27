module

public import CFSG.Quasithin.AppendixH.H16.OctadZKey
public import CFSG.Quasithin.AppendixH.H16.OctadZSyl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

theorem eq_one_or_eq_of_rk_one {K : Subgroup W11} (hK : rk ↥K = 1) {u : W11} (hu : u ∈ K)
    (hu1 : u ≠ 1) : ∀ y ∈ K, y = 1 ∨ y = u := by
  have hW11exp : ∀ v : W11, v ^ 2 = 1 := by
    intro v
    apply Multiplicative.ext
    rw [toAdd_pow, toAdd_one]
    exact CharTwo.two_nsmul v.toAdd
  have hcard : Nat.card ↥K = 2 := by
    have h := card_eq_two_pow hW11exp K
    rw [hK] at h
    simpa using h
  obtain ⟨y0, _hy0ne, hy0uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).1 hcard
  intro y hy
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    have hY : (⟨y, hy⟩ : ↥K) ≠ 1 := by
      intro h
      exact hy1 (by simpa using Subtype.ext_iff.mp h)
    have hU : (⟨u, hu⟩ : ↥K) ≠ 1 := by
      intro h
      exact hu1 (by simpa using Subtype.ext_iff.mp h)
    exact Subtype.ext_iff.mp ((hy0uniq _ hY).trans (hy0uniq _ hU).symm)

theorem clause8_std :
    ∀ g ∈ M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24),
      rk ↥(commOn (fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))))
          (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers g))) = 1 →
        g ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)) := by
  intro g hg hrk
  classical
  let γ : ↥AutPerm := ⟨g, hg.1⟩
  have hγ : (γ : S24) ∈ octStab octad0 := cent_koOne_le_octStab hg
  let Wz : Subgroup W11 := fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1)))
  have hWz : Wz = octWz := by
    show fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) = octWz
    rw [show rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1)) =
        imgCd (Subgroup.zpowers (koPerm 1)) from rfl]
    exact fixV_imgCd_zpowers_koOne
  let K : Subgroup W11 := commOn Wz (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers g))
  have hρmem : rhoC11 AutPerm le_rfl γ ∈ rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers g) := by
    unfold rImg
    exact Subgroup.mem_map.mpr
      ⟨γ, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers g), rfl⟩
  have hcomm_mem : ∀ w ∈ octWz,
      rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ K := by
    intro w hw
    have hwWz : w ∈ Wz := by rw [hWz]; exact hw
    exact Subgroup.subset_closure ⟨rhoC11 AutPerm le_rfl γ, hρmem, w, hwWz, rfl⟩
  have hmem_cen : ∀ w ∈ octVz, rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ octV5 := by
    intro w hw
    have hw5 : w ∈ octV5 := octVz_le_octV5 hw
    have hρw : rhoC11 AutPerm le_rfl γ w ∈ octV5 :=
      isActsInv_octV5 (fun v => rhoC11 AutPerm le_rfl γ v)
        ⟨rhoC11 AutPerm le_rfl γ, rhoCd_mem_imgCd γ.2 hγ, rfl⟩ w hw5
    exact octV5.mul_mem hρw (octV5.inv_mem hw5)
  by_cases hA : ∀ w ∈ octWz, rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ octV5
  · have hkey : g ∈ fixO ⊔ dGrp := key8 γ hγ hA
    rw [pCoreOf_cent_koOne]
    exact hkey
  · push Not at hA
    obtain ⟨w0, hw0, hw0V5⟩ := hA
    let u : W11 := rhoC11 AutPerm le_rfl γ w0 * w0⁻¹
    have huK : u ∈ K := hcomm_mem w0 hw0
    have hu5 : u ∉ octV5 := hw0V5
    have hu1 : u ≠ 1 := by
      intro h
      exact hu5 (by simpa [h] using octV5.one_mem)
    have hfixvz : ∀ w ∈ octVz, rhoC11 AutPerm le_rfl γ w = w := by
      intro w hw
      have hcK : rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ K := hcomm_mem w (octVz_le_octWz hw)
      have hc5 : rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ octV5 := hmem_cen w hw
      rcases eq_one_or_eq_of_rk_one (K := K) hrk huK hu1
        (rhoC11 AutPerm le_rfl γ w * w⁻¹) hcK with h | h
      · exact mul_inv_eq_one.mp h
      · have huV5 : u ∈ octV5 := by simpa [h] using hc5
        exact absurd huV5 hu5
    have hgd : g ∈ dGrp := mem_dGrp_of_fix_octVz ⟨g, hg.1⟩ hfixvz
    rw [pCoreOf_cent_koOne]
    exact (le_sup_right : dGrp ≤ fixO ⊔ dGrp) hgd

end CFSG.ASVolI.H16
