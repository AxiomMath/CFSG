module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCtr
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem IX_le_Pt : IX h ≤ Pt h := by
  intro g hg
  rw [Pt, Subgroup.mem_normalizer_iff]
  intro y
  have hn := miyamotoI_le_normalizer_unipotent h false true hg
  exact Subgroup.mem_normalizer_iff.1 hn (y : GL (Fin 4) K)

theorem Ssd_ZX_trans (hf : 2 ≤ f) (F : Subgroup (K ≃+* K)) (x : MulAut (Xg h))
    (hx : x ∈ Ssd h (ZX h) (fStab_ZX h) ⊥) (hx1 : x ≠ 1) :
    ∃ m ∈ Ssd h (Pt h) (fStab_Pt h) F, m * cj h (z1X h) * m⁻¹ = x := by
  obtain ⟨z₀, hz₀, φ, hφ, rfl⟩ := hx
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one] at hx1 ⊢
  have hz₀1 : z₀ ≠ 1 := fun e => hx1 (by rw [e, cj_one])
  have hcen := (miyamoto_two_one_two_centralizersG h (⊤ : Subgroup (Xg h)) (etaX h) hf).2.2.2
  have htr := (miyamoto_two_one_threeG h (⊤ : Subgroup (Xg h)) (etaX h) hf).2.2.2
  rw [hcen] at htr
  have hZ : ∀ w : Xg h, w ∈ ZX h → w ∈ miyamotoPull h ⊤ (etaX h) (miyamotoZ h) := fun w hw => by
    rw [← sg_eq_pull h]
    exact hw
  obtain ⟨g, hg, e⟩ := htr (z1X h) (hZ _ (z1X_mem_ZX h)) z₀ (hZ _ hz₀)
    (fun e1 => by
      have := orderOf_z1X h
      rw [e1, orderOf_one] at this
      exact absurd this (by norm_num)) hz₀1
  have hgI : g ∈ IX h := by
    have : g ∈ miyamotoIG h (⊤ : Subgroup (Xg h)) (etaX h) := hg
    rwa [show miyamotoIG h (⊤ : Subgroup (Xg h)) (etaX h) = IX h from (sg_eq_pull h _).symm] at this
  refine ⟨cj h g⁻¹, ⟨g⁻¹, (Pt h).inv_mem (IX_le_Pt h hgI), 1, Subgroup.one_mem _, by
    rw [fa_one, mul_one]⟩, ?_⟩
  have hc := congrArg (cj h) e
  rw [cj_mul, cj_mul, cj_inv] at hc
  rw [cj_inv, inv_inv]
  exact hc

end CFSG.Quasithin.H13.F431.Un.OL
