module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_six_swap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 2) (hp : (3 : ℕ) ∈ D.sig)
    (hLc : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥) {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (hJ₀ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₀) (hJ₁ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₁)
    (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = wTil ⊥ V hV L)
    (hfix₀ : J₀ ⊓ fixV (lBar ⊥ V hV L) = ⊥)
    (hE₀ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₀)
    (hE₁ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₁)
    (hψ₃ : ∀ n ∈ J₀, n ≠ 1 → ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ n = n)
    {z : MulAut (Vtil ⊥ V hV)} (hz3 : z ^ 3 = 1)
    (hzL : ∀ l ∈ lBar ⊥ V hV L, z * l = l * z)
    (hzW : (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁) (hzne : ∃ u ∈ J₀ ⊔ J₁, z u ≠ u)
    {t : MulAut (Vtil ⊥ V hV)} (htW : t ∈ barSub ⊥ V hV (E3.wClos V D.k D.T))
    (htne : (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom ≠ lBar ⊥ V hV L) :
    Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le
  have hWM := s16c13bcA_wBar_le_mbar D hV
  have hP2 := s16c13bcA_wBar_isPGroup D hV
  have hM2 : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ φ ∈ Mbar D.M ⊥ V hV,
      Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs
    exact hs
  have htM : t ∈ Mbar D.M ⊥ V hV := hWM htW
  have hpair := s16c13bc_conj_mem_pair htM htne hM2
  have hsq := s16c13bc_conj_sq htM htne hM2
  obtain ⟨g, hgM, hgne, hgcomm, hgfix⟩ := s16c13bcA_exists_other_conj D hV hH hs
  have hgt := (hpair g hgM).resolve_left hgne
  have hcommt : ⁅lBar ⊥ V hV L, (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    rw [← hgt]
    exact hgcomm
  have hfixt : ∀ b ∈ (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom,
      ∀ x ∈ wTil ⊥ V hV L, b x = x := by
    intro b hb x hx
    rw [← hgt] at hb
    exact hgfix b hb x hx
  obtain ⟨k, hkle, hk0, hkst⟩ := s16c13bcA_stable_member_le hJ₀ hJ₁ hinf hE₀ hE₁ hz3 hzL hzW hzne
    (N := barSub ⊥ V hV (E3.wClos V D.k D.T) ⊓
      Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))))
    (hP2.to_le inf_le_left) (fun w hw => (Subgroup.mem_inf.1 hw).2)
    (fun w hw => by
      rw [hsup]
      exact s16c13bcA_wTil_map_eq ⊥ V hV L
        (s16c13bcA_map_eq_of_mem_normalizer (Subgroup.mem_inf.1 hw).2))
  have hst : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L →
        (J₀.map (z ^ k).toMonoidHom).map w.toMonoidHom = J₀.map (z ^ k).toMonoidHom :=
    fun w hw hwn => hkst w (Subgroup.mem_inf.2 ⟨hw, s16c13bcA_mem_normalizer_of_map_eq hwn⟩)
  have hJW : J₀.map (z ^ k).toMonoidHom ≤ wTil ⊥ V hV L := hsup ▸ hkle
  obtain ⟨a, haJ, ha1, n, hn1, hnfix, hψn⟩ := s16c13bc_swap_fixed
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hP2 htW (fun w hw => hpair w (hWM hw)) hsq
    (fun w hw hwn => s16c13bc_conj_pair_stable htM htne hM2 (hWM hw) hwn) hJW hk0 hfixt
    (s16c13bcA_six_fixfree hfix₀ hzL k) hst
  obtain ⟨ψ, hψL, hψo, hψa⟩ := s16c13bcA_six_psi hψ₃ hzL haJ ha1
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hψ'B : t * ψ * t⁻¹ ∈ (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom := ⟨ψ, hψL, rfl⟩
  have hψ'o : orderOf (t * ψ * t⁻¹) = 3 := by
    have h1 := orderOf_injective (MulAut.conj t).toMonoidHom hinj ψ
    rw [hψo] at h1
    exact h1
  have hψ'1 : t * ψ * t⁻¹ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψ'o
    omega
  obtain ⟨hab, hne⟩ := s16c13bcA_pair_of_conj hcommt hLc hψL hψ'B hψ'1
  have hψ'M : t * ψ * t⁻¹ ∈ Mbar D.M ⊥ V hV :=
    (Mbar D.M ⊥ V hV).mul_mem ((Mbar D.M ⊥ V hV).mul_mem htM (hLM hψL))
      ((Mbar D.M ⊥ V hV).inv_mem htM)
  have htn : t n = n := hnfix t htW
  have htinv : t⁻¹ n = n := by
    calc t⁻¹ n = t⁻¹ (t n) := by rw [htn]
      _ = n := t.symm_apply_apply n
  have hψ'n : (t * ψ * t⁻¹) n = n := by
    calc (t * ψ * t⁻¹) n = t (ψ (t⁻¹ n)) := rfl
      _ = n := by rw [htinv, hψn ψ hψL hψa, htn]
  exact s16c13bcA_insp_of_pair D h hp (hLM hψL) hψ'M hψo hψ'o hab hne hn1 (mem_fixV.2 hnfix)
    (hψn ψ hψL hψa) hψ'n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
