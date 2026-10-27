module

public import CFSG.RankThree.GF2n.Smith81.S81UForm
public import CFSG.RankThree.GF2n.Smith81.S81VPlucker

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.RankThree.GF2n.Smith81.A5Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {b : Fin 3 → Fin 6 → F}
  {K : Type} [Field K]

theorem e3uVal_injective {e : K ≃+* Fσ σ} : Function.Injective (e3uVal : E3UWspace σ e → Cube F) := by
  intro w w' h
  exact Subtype.ext h

theorem e3uVal_smul {e : K ≃+* Fσ σ} (c : K) (w : E3UWspace σ e) :
    e3uVal (c • w) = ((e c : Fσ σ) : F) • e3uVal w :=
  rfl

theorem e3uVal_add {e : K ≃+* Fσ σ} (w w' : E3UWspace σ e) : e3uVal (w + w') = e3uVal w + e3uVal w' :=
  rfl

theorem e3uVal_P0 {e : K ≃+* Fσ σ} : e3uVal (e3uP0 σ e) = pt0 F := rfl

theorem e3u_R1M (hσ : IsUnitaryInvolution σ) (hf : Frame σ e3uT0Vec b) (e₀ e' : K ≃+* Fσ σ) (ψ : K ≃+* K)
    (he' : ∀ t, e' t = e₀ (ψ t)) (t : K) :
    e3uWact σ e' (uK hσ.invol hf (ψ t • n1K σ e₀))
        (e3uWact σ e' (sU hσ.invol hf) (e3uP0 σ e')) =
      e3uWact σ e' (sU hσ.invol hf) (e3uP0 σ e') + t • e3uP0 σ e' := by
  apply e3uVal_injective
  simp only [e3uVal_add, e3uVal_smul, e3uWact_val, e3uVal_P0, he']
  exact rho_uK_sU_pt0 hσ.invol hf e₀ (ψ t)

theorem e3u_spanM (hσ : IsUnitaryInvolution σ) (e' : K ≃+* Fσ σ) :
    Submodule.span K (Set.range fun g : SUid σ 6 => e3uWact σ e' g (e3uP0 σ e')) = ⊤ := by
  have key : ∀ x : Wform σ, (x : E3UWspace σ e') ∈
      Submodule.span K (Set.range fun g : SUid σ 6 => e3uWact σ e' g (e3uP0 σ e')) := by
    intro x
    have hx : x ∈ Submodule.span (Fσ σ)
        (Set.range fun g : SUid σ 6 => Wact σ g (U6Cube.pt0W σ)) := by
      rw [U6Cube.orbit_span_Fq hσ]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      have hc : e' (e'.symm c) = c := e'.apply_symm_apply c
      have heq : e'.symm c • (show E3UWspace σ e' from y) = c • y :=
        congrArg (fun r : Fσ σ => r • y) hc
      rw [← heq]
      exact Submodule.smul_mem _ _ hy
  rw [eq_top_iff]
  intro w _
  exact key w

theorem e3u_finrank (hσ : IsUnitaryInvolution σ) (e' : K ≃+* Fσ σ) : 20 ≤ finrank K (E3UWspace σ e') := by
  haveI : Module.Finite K (E3UWspace σ e') :=
    Module.Finite.of_fg_top (by
      rw [← e3u_spanM hσ e']
      exact Submodule.fg_span (Set.finite_range _))
  let B := Module.finBasis K (E3UWspace σ e')
  have hP : ∀ w : E3UWspace σ e', e3uVal w ∈
      Submodule.span F (Set.range fun i => e3uVal (B i)) := by
    intro w
    have hw : w ∈ Submodule.span K (Set.range B) := by
      rw [B.span_eq]
      exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [e3uVal_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [e3uVal_smul]
      exact Submodule.smul_mem _ _ hx
  have hsub : (U6Cube.Wsub σ : Set (Cube F)) ⊆
      (Submodule.span F (Set.range fun i => e3uVal (B i)) : Set (Cube F)) := by
    intro ξ hξ
    exact hP ((⟨ξ, U6Cube.mem_Wform_iff.mpr hξ⟩ : U6Cube.Wform σ) : E3UWspace σ e')
  have hspan : Submodule.span F (Set.range fun i => e3uVal (B i)) = ⊤ := by
    rw [eq_top_iff, ← U6Cube.span_Wsub hσ]
    exact Submodule.span_le.mpr hsub
  have hle : finrank F (Submodule.span F (Set.range fun i => e3uVal (B i))) ≤
      Fintype.card (Fin (finrank K (E3UWspace σ e'))) :=
    finrank_range_le_card (fun i => e3uVal (B i))
  rw [hspan, finrank_top, CFSG.RankThree.GF2n.Smith81.A5Cube.finrank_cube, Fintype.card_fin] at hle
  exact hle

end CFSG.RankThree.GF2n.Smith81.S81V
