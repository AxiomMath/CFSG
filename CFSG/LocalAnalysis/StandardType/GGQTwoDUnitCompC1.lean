module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB4
public import CFSG.ClassicalInvolution.Phan.Defs
import CFSG.GH74.L5U5.IdentUnitary
import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType.QTwo

open CFSG CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem qtwoDB7_su_data
    {H J : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d)
    (hθ : ∃ θ : Su F0 2 1 d →* G, Function.Injective θ ∧ θ.range = J) (hJH : J ≤ H) :
    CFSG.IsQuasisimple (J.subgroupOf H) ∧
      3 ∣ Nat.card (↥(J.subgroupOf H) ⧸ Subgroup.center ↥(J.subgroupOf H)) := by
  obtain ⟨θ, hθ_inj, hθ_range⟩ := hθ
  have h_su : CFSG.IsQuasisimple (Su F0 2 1 d) :=
    CFSG.GH74.L5U5.isQuasisimple_su hF0 (by omega) (by intro h; simp at h; omega)
  let ε : Su F0 2 1 d ≃* J.subgroupOf H :=
    (MonoidHom.ofInjective (f := θ) hθ_inj).trans (MulEquiv.subgroupCongr hθ_range) |>.trans
      (Subgroup.subgroupOfEquivOfLe hJH).symm
  refine ⟨h_su.of_mulEquiv ε.symm, ?_⟩
  rw [← Nat.card_congr (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).toEquiv]
  exact qtwoDB7_three_dvd_su hF0 hd

theorem qtwoDB7_centerQuot_su
    {H J : Subgroup G} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d)
    (hθ : ∃ θ : Su F0 2 1 d →* G, Function.Injective θ ∧ θ.range = J) (hJH : J ≤ H) :
    Nonempty (↥((J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ⧸
        Subgroup.center ↥((J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ≃*
      Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d)) := by
  obtain ⟨θ, hθ_inj, hθ_range⟩ := hθ
  have h_su_data := qtwoDB7_su_data hF0 hd ⟨θ, hθ_inj, hθ_range⟩ hJH
  have hJ'_qs : CFSG.IsQuasisimple (J.subgroupOf H) := h_su_data.1
  have h3_J' : 3 ∣ Nat.card ((J.subgroupOf H) ⧸ Subgroup.center (J.subgroupOf H)) :=
    h_su_data.2

  let ε : Su F0 2 1 d ≃* J.subgroupOf H :=
    (MonoidHom.ofInjective (f := θ) hθ_inj).trans (MulEquiv.subgroupCongr hθ_range) |>.trans
      (Subgroup.subgroupOfEquivOfLe hJH).symm
  let e_S_J' : Su F0 2 1 d ⧸ Subgroup.center (Su F0 2 1 d) ≃*
      (J.subgroupOf H) ⧸ Subgroup.center (J.subgroupOf H) :=
    QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)

  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let J' := J.subgroupOf H
  let Jb := J'.map π
  let f : J' →* Jb := (π.comp J'.subtype).codRestrict Jb (fun x => ⟨x.val, x.2, rfl⟩)

  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx_mem, hx_eq⟩ := y.2
    refine ⟨⟨x, hx_mem⟩, ?_⟩
    exact Subtype.ext hx_eq

  have hker_le_center : f.ker ≤ Subgroup.center J' := by
    intro x hx
    have hπx : π x.val = 1 := by
      have h : ((f x : Jb) : H ⧸ CFSG.pPrimeCore 3 ↥H) = 1 := by
        simpa using congrArg Subtype.val hx
      have h_eq : ((f x : Jb) : H ⧸ CFSG.pPrimeCore 3 ↥H) = π x.val := rfl
      rwa [h_eq] at h
    have hx_R : x.val ∈ CFSG.pPrimeCore 3 ↥H := by
      rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥H)]
      exact MonoidHom.mem_ker.mpr hπx
    have hx_inf : x ∈ (J' ⊓ CFSG.pPrimeCore 3 ↥H).subgroupOf J' := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, hx_R⟩
    exact qtwoDB7_inf_core_le_center hJ'_qs h3_J' hx_inf

  have h_iso_J'_Jb : Nonempty (J' ⧸ Subgroup.center J' ≃* Jb ⧸ Subgroup.center Jb) :=
    qtwoDB7_centerQuot_of_surj hJ'_qs.1.commutator_eq_top f hf_surj hker_le_center

  obtain ⟨e_J'_Jb⟩ := h_iso_J'_Jb
  exact ⟨(e_S_J'.trans e_J'_Jb).symm⟩

end CFSG.StandardType.QTwo

end
