module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL

public section

namespace CFSG.StandardType.LinTvA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.Assembly TableB TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_model_compat (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 2) ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ (A₀ : GL (Fin d) K) (φ' : SpecialLinearGroup (Fin d) K →* L'), Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧
      (∀ s, ψ (φ' s) = proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ s)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t := by
  classical
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one hpK
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := ggPGLTorality_holds (d := d) hp hp2 hpK _ hXA hXI (hcardX ▸ hr)
    (hcardX ▸ h3)
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover (slHasSections_of_five_le hd) ψ hψ hker hperf
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set φ' := φ.comp c₀.toMonoidHom with hφ'
  refine ⟨A₀, φ', hφs.comp c₀.surjective, ?_, fun s => hφ (c₀ s), ?_⟩
  · intro g hg
    have h1 : proj d K (c₀ g) = 1 := by
      rw [← hφ]
      change ψ (φ' g) = 1
      rw [hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  · intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have hBX : conjAut d K B ∈ inducedSub ψ A := ⟨a, ha, hφa⟩
    set D := A₀ * B * A₀⁻¹ with hD
    refine ⟨fun i => (D : Matrix (Fin d) (Fin d) K) i i, D,
      CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => by
        rw [hD, Units.val_mul, Units.val_mul]
        exact hA₀ B hBX i j hij, fun s => ?_⟩
    have h1 := act_of_lift_GL hperfSL hker hφ hφa (c₀ s)
    change a (φ (c₀ s)) = φ (c₀ (CatalogueBHigherLinearAction.slConjugation d K D s))
    rw [h1, hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
    congr 2
    group

end CFSG.StandardType.LinTvA

end
