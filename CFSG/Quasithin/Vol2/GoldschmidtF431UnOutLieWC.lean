module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieWB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCtr
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieW

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem wcl_coords_Pfx {y : Xg h} (hy : y ∈ Pfx h) :
    ∃ a b c d : K, h.bar a = a ∧ h.bar b = b ∧ h.bar c = c ∧ h.bar d = d ∧
      (y : GL (Fin 4) K) = miyamotoXGL h a b c d := by
  obtain ⟨a, b, c, d, hb, -, he⟩ := (mem_P h).1 hy.1
  have he' : (y : GL (Fin 4) K) = miyamotoXGL h a b c d := he
  have hfix := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) hy.2
  simp only [coe_miyamotoFieldAut_apply, he', glAut_miyamotoXGL, miyamotoBarEquiv_apply] at hfix
  obtain ⟨ha', hb', hc', hd'⟩ := (miyamotoXGL_inj h).1 hfix
  exact ⟨a, b, c, d, ha', hb', hc', hd', he'⟩

theorem wcl_center_Pfx {y₀ : Xg h} (hy₀ : y₀ ∈ Pfx h) (hc : ∀ u ∈ Pfx h, u * y₀ = y₀ * u) :
    ∃ c d : K, h.bar c = c ∧ h.bar d = d ∧ (y₀ : GL (Fin 4) K) = miyamotoXGL h 0 0 c d := by
  obtain ⟨a, b, c, d, ha, hb, hc', hd, he⟩ := wcl_coords_Pfx h hy₀
  have hb0 : h.bar (0 : K) = 0 := map_zero _
  have hb1 : h.bar (1 : K) = 1 := map_one _
  have hP1 := wcl_mem_P_of_bar h 1 0 0 0 hb1 hb0 hb0 hb0
  have hP2 := wcl_mem_P_of_bar h 0 1 0 0 hb0 hb1 hb0 hb0
  have e1 := congrArg (fun x : Xg h => (x : GL (Fin 4) K))
    (hc (wcl_xe h 1 0 0 0 hP1) (wcl_xe_mem_Pfx h _ _ _ _ hP1 hb1 hb0 hb0 hb0))
  have e2 := congrArg (fun x : Xg h => (x : GL (Fin 4) K))
    (hc (wcl_xe h 0 1 0 0 hP2) (wcl_xe_mem_Pfx h _ _ _ _ hP2 hb0 hb1 hb0 hb0))
  simp only [Subgroup.coe_mul, wcl_coe_xe, he] at e1 e2
  rw [miyamotoXGL_mul h hb0, miyamotoXGL_mul h hb, miyamotoXGL_inj] at e1
  rw [miyamotoXGL_mul h hb1, miyamotoXGL_mul h hb, miyamotoXGL_inj] at e2
  have hb' : b = 0 := by linear_combination (-1 : K) * e1.2.2.1
  have ha' : a = 0 := by linear_combination e2.2.2.1
  subst hb' ha'
  exact ⟨c, d, hc', hd, he⟩

theorem W_cls (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) (y : MulAut (Xg h))
    (hy : y ∈ spWf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h))
    (hk : ∃ k : MulAut (Xg h), k * cj h (z1X h) * k⁻¹ = y) :
    y ∈ Ssd h (ZX h) (fStab_ZX h) ⊥ := by
  have _hf := hf
  have hyc : y ∈ Ssd h (Pfx h) (fStab_Pfx h) ⊥ := by
    have h1 : y ∈ ⁅spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h),
        spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h)⁆ := hy.2
    rw [spTf_Ssd] at h1
    exact wcl_commutator_le h _ _ _ h1
  obtain ⟨y₀, hy₀, rfl⟩ := wcl_cj_of_mem_Ssd_bot h hyc
  have hcen : ∀ u ∈ Pfx h, u * y₀ = y₀ * u := by
    intro u hu
    have h1 := (mem_centerOf_iff.mp hy.1).2 (cj h u) (by rw [spTf_Ssd]; exact cj_mem_Ssd h hu)
    rw [← cj_mul, ← cj_mul] at h1
    exact (cj_inj h).1 h1
  obtain ⟨c, d, hc, hd, hye⟩ := wcl_center_Pfx h hy₀ hcen
  by_cases hc0 : c = 0
  · have hz : y₀ ∈ ZX h := by
      show (y₀ : GL (Fin 4) K) ∈ miyamotoZ h
      rw [hye]
      exact (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, hc0, hd⟩
    exact cj_mem_Ssd h hz
  · exfalso
    obtain ⟨k, hk⟩ := hk
    rw [aut_mul_cj_mul_inv h k (z1X h), cj_inj] at hk
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h k
    have hy₀s : y₀ = s * z1X h * s⁻¹ := by
      rw [← hk, hs, MulAut.mul_apply, fa_z1X, MulAut.conj_apply]
    have hy0 : (y₀ : GL (Fin 4) K) = (s : GL (Fin 4) K) * miyamotoZ1 K * (s : GL (Fin 4) K)⁻¹ := by
      have := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) hy₀s
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this
    have hA1 : (y₀ : GL (Fin 4) K) ∈ miyamotoA1 h := by
      rw [hye]
      exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩
    have hQ : miyamotoQA1 h (y₀ : GL (Fin 4) K) ≠ 0 := by
      rw [hye, miyamotoQA1_miyamotoXGL, hc, zero_mul, add_zero]
      exact mul_ne_zero hc0 hc0
    have horb : (y₀ : GL (Fin 4) K) ∈ {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h,
        g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y} := by
      rw [miyamoto_orbit_z2_I1N1 h]
      exact ⟨hA1, hQ⟩
    obtain ⟨g, -, hg⟩ := horb
    refine miyamotoZ1_not_conj_Z2 (K := K) (((g : GL (Fin 4) K) * (s : GL (Fin 4) K))⁻¹) ?_
    calc ((g * (s : GL (Fin 4) K))⁻¹)⁻¹ * miyamotoZ1 K * (g * (s : GL (Fin 4) K))⁻¹
        = g * ((s : GL (Fin 4) K) * miyamotoZ1 K * (s : GL (Fin 4) K)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * LocalAnalysis.miyamotoZ2 K * g) * g⁻¹ := by rw [← hy0, hg]
      _ = LocalAnalysis.miyamotoZ2 K := by group

end CFSG.Quasithin.H13.F431.Un.OL
