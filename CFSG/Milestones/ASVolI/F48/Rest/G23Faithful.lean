
module

public import CFSG.Milestones.ASVolI.F48.Rest.G23ModelPrelude
public import CFSG.Certificates.Kernel.G23F48.Frame
public import Certificates.Data.Kernel.G23F48.Frame

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.KC.G23F48
open scoped Matrix

theorem burnsideF48t_dv_unit (i : Fin 14) :
    burnsideF48t_dv (burnsideF48t_g23Unit i) = Pi.single i 1 := by
  funext j
  simp only [burnsideF48t_dv, burnsideF48t_g23Unit]
  rw [getElem!_ofFn_nat _ j.2]
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg (fun e => h (Fin.ext e)), Pi.single_eq_of_ne h]
    simp

@[expose] def burnsideF48t_frameV (FV : List (Array ℕ)) : Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  Matrix.of fun j i => burnsideF48t_dv FV[(i : ℕ)]! j

theorem burnsideF48t_frameOK_spec {FV : List (Array ℕ)} {W c : Array ℕ}
    (h : frameOK FV W c = true) :
    burnsideF48t_dm W * burnsideF48t_frameV FV = 1 ∧
      burnsideF48t_dm W *ᵥ burnsideF48t_dv FV[14]! = burnsideF48t_dv c ∧
      ∀ i, burnsideF48t_dv c i ≠ 0 := by
  simp only [frameOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨-, hcol⟩, hf⟩, hc⟩ := h
  refine ⟨?_, by rw [← burnsideF48t_dv_mulVec, hf], fun i => ?_⟩
  · ext j i
    have e := congrFun (burnsideF48t_dv_mulVec W FV[(i : ℕ)]!) j
    rw [hcol i i.2, burnsideF48t_dv_unit] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e' : (burnsideF48t_dm W *ᵥ burnsideF48t_dv FV[(i : ℕ)]!) j =
        ∑ k, burnsideF48t_dm W j k * burnsideF48t_frameV FV k i := rfl
    rw [← e', ← e, Pi.single_apply]
  · rcases hc i i.2 with h1 | h2
    · simp [burnsideF48t_dv, h1]
    · simp only [burnsideF48t_dv, h2]
      decide

section Faithful

open scoped Pointwise in
theorem burnsideF48t_g23_ker_smul {h : ↥burnsideF48t_g23R} (hh : burnsideF48t_g23ρ h = 1)
    (k : Fin 728) : ∃ l : ZMod 3, ((h : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) *ᵥ
      burnsideF48t_g23vec k = l • burnsideF48t_g23vec k := by
  have hs := burnsideF48t_resHom_spec (P := burnsideF48t_g23Pt) burnsideF48t_g23_Pt_injective
    burnsideF48t_g23_R_preserves h k
  have e : burnsideF48t_resHom burnsideF48t_g23_Pt_injective burnsideF48t_g23_R_preserves h k = k := by
    have := congrArg (fun σ : Equiv.Perm (Fin 728) => σ k) hh
    exact this
  rw [e] at hs
  have hm : (h : GL (Fin 14) (ZMod 3)) • burnsideF48t_g23vec k ∈ burnsideF48t_g23Pt k := by
    rw [hs]
    exact Set.smul_mem_smul_set (Set.mem_insert _ _)
  rw [Units.smul_def, Matrix.smul_eq_mulVec] at hm
  rcases hm with h1 | h2
  · exact ⟨1, by rw [h1, one_smul]⟩
  · exact ⟨2, h2⟩

theorem burnsideF48t_g23_center_R : Subgroup.center ↥burnsideF48t_g23R = ⊥ := by
  let σ : ZMod 3 ≃+* ZMod 3 := RingEquiv.refl _
  let e : ↥(adjointGroup .G2 (ZMod 3)) ≃* ↥burnsideF48t_g23R :=
    (Subgroup.equivMapOfInjective _ (glHom σ) (glHom_injective σ)).trans
      (MulEquiv.subgroupCongr (burnsideF48t_g23_map_adjointGroup σ))
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center ↥(adjointGroup .G2 (ZMod 3)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (e g)]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]

theorem burnsideF48t_g23_ρ_injective_of_frame {FI : ℕ → ℕ} {FV : List (Array ℕ)} {W c : Array ℕ}
    (hok : frameOK FV W c = true) (hFI : ∀ i < 15, FI i < 728)
    (hpts : ∀ i < 15, (burnsideF48t_g23Pts ())[FI i]! = FV[i]!) :
    Function.Injective burnsideF48t_g23ρ := by
  obtain ⟨hWV, hWu, hc⟩ := burnsideF48t_frameOK_spec hok
  rw [injective_iff_map_eq_one]
  intro h hh
  have hv : ∀ i (hi : i < 15), burnsideF48t_g23vec (⟨FI i, hFI i hi⟩ : Fin 728) =
      burnsideF48t_dv FV[i]! := fun i hi => by rw [burnsideF48t_g23vec, hpts i hi]
  let g : Matrix (Fin 14) (Fin 14) (ZMod 3) := ((h : GL (Fin 14) (ZMod 3)) : Matrix _ _ _)
  have hl : ∀ i : Fin 14, ∃ l : ZMod 3, g *ᵥ (fun j => burnsideF48t_frameV FV j i) =
      l • fun j => burnsideF48t_frameV FV j i := fun i => by
    obtain ⟨l, hl⟩ := burnsideF48t_g23_ker_smul hh ⟨FI i, hFI i (by omega)⟩
    rw [hv i (by omega)] at hl
    exact ⟨l, hl⟩
  obtain ⟨μ, hμ⟩ := burnsideF48t_g23_ker_smul hh ⟨FI 14, hFI 14 (by omega)⟩
  rw [hv 14 (by omega)] at hμ
  have hg : g = μ • 1 := eq_smul_one_of_frame hWV hc hWu
    (lam := fun i => Classical.choose (hl i)) (fun i => Classical.choose_spec (hl i)) hμ
  have hcen : h ∈ Subgroup.center ↥burnsideF48t_g23R := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Units.ext
    change ((x : GL (Fin 14) (ZMod 3)) : Matrix _ _ _) * g = g * ((x : GL (Fin 14) (ZMod 3)) : Matrix _ _ _)
    rw [hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  rw [burnsideF48t_g23_center_R, Subgroup.mem_bot] at hcen
  exact hcen

theorem burnsideF48t_g23_card_X_of_frame {FI : ℕ → ℕ} {FV : List (Array ℕ)} {W c : Array ℕ}
    (hok : frameOK FV W c = true) (hFI : ∀ i < 15, FI i < 728)
    (hpts : ∀ i < 15, (burnsideF48t_g23Pts ())[FI i]! = FV[i]!) :
    Nat.card ↥burnsideF48t_g23X = 4245696 := by
  rw [← burnsideF48t_g23_ρ_range, ← burnsideF48t_g23_card_R]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (burnsideF48t_g23_ρ_injective_of_frame hok hFI hpts)).toEquiv).symm

end Faithful

end CFSG.ASVolI
