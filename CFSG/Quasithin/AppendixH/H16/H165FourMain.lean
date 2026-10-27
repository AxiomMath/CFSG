module

public import CFSG.Quasithin.AppendixH.H16.H165FourPat
public import CFSG.Quasithin.AppendixH.H16.H165FourZ
public import CFSG.Quasithin.AppendixH.H16.H165FourOct

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Monster.Code
open CFSG.ASVolI.ChH (cenMS)

@[expose] def h165E0 : Subgroup P24 :=
  kleinSubgroup h165Z0 h165D0 h165Z0_sq h165D0_sq h165D0_comm.symm

theorem mem_h165E0_iff (x : P24) :
    x ∈ h165E0 ↔ x = 1 ∨ x = h165Z0 ∨ x = h165D0 ∨ x = h165Z0 * h165D0 := Iff.rfl

theorem h165E0_le : h165E0 ≤ mog22plus := by
  intro x hx
  rcases (mem_h165E0_iff x).1 hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact h165Z0_mem
  · exact h165D0_mem
  · exact mul_mem h165Z0_mem h165D0_mem

theorem h165E0_isE2k : IsE2k 2 h165E0 :=
  isE2k_kleinSubgroup _ _ _ h165Z0_ne_one h165D0_ne_one h165D0_ne_Z0

theorem h165_cenMS_le : cenMS R (fixV (rImg R (Subgroup.zpowers h165Z0))) ≤ h165E0 := by
  intro g hg
  obtain ⟨hgΓ, hpair⟩ := h165_cen_pair hg
  rcases h165_pair_preserving hgΓ.1 hpair with rfl | rfl | rfl | rfl
  · exact (mem_h165E0_iff _).2 (Or.inl rfl)
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inl rfl))
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inr (Or.inl rfl)))
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))

theorem h165_le_cenMS : h165E0 ≤ cenMS R (fixV (rImg R (Subgroup.zpowers h165Z0))) := by
  intro g hg
  refine (mem_cenMS_iff R _ g).2 ⟨h165E0_le hg, fun w hw => ?_⟩
  rcases (mem_h165E0_iff g).1 hg with hg1 | hgZ | hgD | hgZD
  · have hsub : (⟨g, h165E0_le hg⟩ : ↥mog22plus) = 1 := Subtype.ext hg1
    rw [hsub]
    exact congrArg (fun f : MulAut W10 => f w) (map_one R)
  · have hsub : (⟨g, h165E0_le hg⟩ : ↥mog22plus) = ⟨h165Z0, h165Z0_mem⟩ :=
      Subtype.ext hgZ
    rw [hsub]
    exact (mem_fixV_rImg_zpowers R h165Z0_mem w).1 hw
  · have hsub : (⟨g, h165E0_le hg⟩ : ↥mog22plus) = ⟨h165D0, h165D0_mem⟩ :=
      Subtype.ext hgD
    rw [hsub]
    exact (h165_E0_fixes w hw).1
  · have hsub : (⟨g, h165E0_le hg⟩ : ↥mog22plus) = ⟨h165ZD0, h165ZD0_mem⟩ :=
      Subtype.ext (hgZD.trans h165ZD0_eq)
    rw [hsub]
    exact (h165_E0_fixes w hw).2

theorem h165_cenMS_eq :
    cenMS R (fixV (rImg R (Subgroup.zpowers h165Z0))) = h165E0 :=
  le_antisymm h165_cenMS_le h165_le_cenMS

theorem h165_normalizes_E0 {h e : P24}
    (hh : h ∈ mog22plus ⊓ Subgroup.centralizer ({h165Z0} : Set P24)) (he : e ∈ h165E0) :
    h * e * h⁻¹ ∈ h165E0 := by
  have hhz : h * h165Z0 = h165Z0 * h := by
    have h0 := (Subgroup.mem_centralizer_iff).1 hh.2 h165Z0 (by simp)
    exact h0.symm
  rw [← h165_cenMS_eq] at he ⊢
  exact conj_mem_cenMS_fixV R h165Z0_mem hh.1 hhz he

theorem h165_K0_le_twoResidual : ∀ k ∈ h165K0, k ∈ twoResidual (mog22plus ⊓
    Subgroup.centralizer ({h165Z0} : Set P24)) := by
  intro k hk
  let H : Subgroup P24 := mog22plus ⊓ Subgroup.centralizer ({h165Z0} : Set P24)
  have hY1H : h165Y1 ∈ H :=
    ⟨h165Y1_mem, (Subgroup.mem_centralizer_iff).2 (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h165Y1_comm)⟩
  have hY2H : h165Y2 ∈ H :=
    ⟨h165Y2_mem, (Subgroup.mem_centralizer_iff).2 (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h165Y2_comm)⟩
  have hY3H : h165Y3 ∈ H :=
    ⟨h165Y3_mem, (Subgroup.mem_centralizer_iff).2 (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h165Y3_comm)⟩
  have hy1 : h165Y1 ∈ twoResidual H :=
    mem_twoResidual_of_pow_eq_one hY1H (⟨1, rfl⟩ : Odd 3) h165Y1_cube
  have hy2 : h165Y2 ∈ twoResidual H :=
    mem_twoResidual_of_pow_eq_one hY2H (⟨1, rfl⟩ : Odd 3) h165Y2_cube
  have hy3 : h165Y3 ∈ twoResidual H :=
    mem_twoResidual_of_pow_eq_one hY3H (⟨1, rfl⟩ : Odd 3) h165Y3_cube
  change k ∈ twoResidual H
  simp only [h165K0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hy1
  · exact hy2
  · exact hy3
  · exact mul_mem hy2 hy1
  · exact mul_mem (inv_mem hy3) hy1
  · exact mul_mem hy3 (inv_mem hy1)
  · exact mul_mem (inv_mem hy2) hy1

theorem h165_cen_twoResidual_le : mog22plus ⊓ Subgroup.centralizer ((twoResidual (mog22plus ⊓
    Subgroup.centralizer ({h165Z0} : Set P24)) : Subgroup P24) : Set P24) ≤ h165E0 := by
  intro g hg
  have hpair : ∀ p, g p = p ∨ g p = h165Partner p :=
    h165_K0_comm_pair (fun k hk => by
      have hk2 : k ∈ twoResidual (mog22plus ⊓ Subgroup.centralizer ({h165Z0} : Set P24)) :=
        h165_K0_le_twoResidual k hk
      have hcomm := (Subgroup.mem_centralizer_iff).1 hg.2 k hk2
      exact hcomm.symm)
  rcases h165_pair_preserving hg.1.1 hpair with rfl | rfl | rfl | rfl
  · exact (mem_h165E0_iff _).2 (Or.inl rfl)
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inl rfl))
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inr (Or.inl rfl)))
  · exact (mem_h165E0_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))

theorem h165_le_cen_twoResidual : h165E0 ≤ mog22plus ⊓ Subgroup.centralizer ((twoResidual (mog22plus ⊓
    Subgroup.centralizer ({h165Z0} : Set P24)) : Subgroup P24) : Set P24) := by
  intro e he
  refine ⟨h165E0_le he, ?_⟩
  let H : Subgroup P24 := mog22plus ⊓ Subgroup.centralizer ({h165Z0} : Set P24)
  have hHE : ∀ h ∈ H, ∀ e ∈ h165E0, h * e * h⁻¹ ∈ h165E0 :=
    fun h hh e he => h165_normalizes_E0 hh he
  have hsq : ∀ h ∈ H, ∀ e ∈ h165E0, (h * h) * e = e * (h * h) := by
    intro h hh e he
    have hhz : h * h165Z0 = h165Z0 * h := by
      have h0 := (Subgroup.mem_centralizer_iff).1 hh.2 h165Z0 (by simp)
      exact h0.symm
    exact klein_sq_comm (E := h165E0) (fun x => mem_h165E0_iff x) h165D0_comm.symm h165Z0_sq
      h165D0_sq h165D0_ne_one h165D0_ne_Z0 (fun e he => h165_normalizes_E0 hh he) hhz e he
  change e ∈ Subgroup.centralizer ((twoResidual H : Subgroup P24) : Set P24)
  exact le_centralizer_twoResidual_of_sq H h165E0 hHE hsq he

theorem h165_cen_twoResidual_eq :
    mog22plus ⊓ Subgroup.centralizer ((twoResidual (mog22plus ⊓
      Subgroup.centralizer ({h165Z0} : Set P24)) : Subgroup P24) : Set P24) = h165E0 :=
  le_antisymm h165_cen_twoResidual_le h165_le_cen_twoResidual

theorem h165_Cen4_z0 : Cen4 R h165Z0 :=
  ⟨(h165_cenMS_eq).trans (h165_cen_twoResidual_eq).symm, by
    rw [h165_cenMS_eq]
    exact h165E0_isE2k⟩

theorem h165_Cen4_of_twoCentral
    {z : P24} (hz : z ∈ mog22plus) (hz2 : orderOf z = 2)
    (hc : ∃ S : Subgroup P24, IsSylowIn 2 S mog22plus ∧ ∀ s ∈ S, s * z = z * s) :
    Cen4 R z := by
  obtain ⟨g, hg, hgz⟩ := exists_conj_to_z0 hz hz2 hc
  let e : W10 ≃* W10 := (R ⟨g, hg⟩ : MulAut W10)
  have hΓ : conjSubg g mog22plus = mog22plus := by
    ext x
    rw [mem_conjSubg_iff]
    constructor
    · intro hx
      have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ mog22plus :=
        mul_mem (mul_mem hg hx) (inv_mem hg)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2
    · intro hx
      exact mul_mem (mul_mem (inv_mem hg) hx) hg
  obtain ⟨φ, hφ⟩ := exists_conjHom (c := g) hΓ
  have he : ∀ (x : ↥mog22plus) (v : W10), e (R x v) = R (φ x) (e v) := by
    intro x v
    show R ⟨g, hg⟩ (R x v) = R (φ x) (R ⟨g, hg⟩ v)
    have h1 : R ⟨g, hg⟩ (R x v) = R (⟨g, hg⟩ * x) v := by
      rw [← MulAut.mul_apply, ← map_mul]
    have h2 : R (φ x) (R ⟨g, hg⟩ v) = R (φ x * ⟨g, hg⟩) v := by
      rw [← MulAut.mul_apply, ← map_mul]
    have harg : (⟨g, hg⟩ : ↥mog22plus) * x = φ x * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hφ x]
      group
    rw [h1, h2, harg]
  have hstd : Cen4 R (g * z * g⁻¹) := by
    rw [hgz]
    exact h165_Cen4_z0
  exact (Cen4_of_transport g hΓ R R φ hφ e he z) hstd

theorem h165_four_main
    {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V) (c : P24)
    (hcΓ : conjSubg c Γ = mog22plus) (φ : ↥Γ →* ↥mog22plus)
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (e : V ≃* W10)
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = R (φ g) (e v)) {z : P24} (hz : z ∈ Γ)
    (hz2 : orderOf z = 2) (hzc : ∃ S : Subgroup P24, IsSylowIn 2 S Γ ∧ ∀ s ∈ S, s * z = z * s) :
    Cen4 ρ z := by
  have hz' : c * z * c⁻¹ ∈ mog22plus := by
    rw [← hcΓ, mem_conjSubg_iff]
    rw [show c⁻¹ * (c * z * c⁻¹) * c = z by group]
    exact hz
  have hz2' : orderOf (c * z * c⁻¹) = 2 := (orderOf_conj' c z).trans hz2
  have hc' : ∃ S : Subgroup P24, IsSylowIn 2 S mog22plus ∧
      ∀ s ∈ S, s * (c * z * c⁻¹) = (c * z * c⁻¹) * s := by
    obtain ⟨S, hS, hSc⟩ := isTwoCentral_conj hzc c
    exact ⟨S, by rwa [hcΓ] at hS, hSc⟩
  exact (Cen4_of_transport c hcΓ ρ R φ hφ e he z)
    (h165_Cen4_of_twoCentral hz' hz2' hc')

end CFSG.ASVolI.H16
