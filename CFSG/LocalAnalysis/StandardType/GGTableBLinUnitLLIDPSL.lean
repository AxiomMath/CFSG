module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDCore

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGBstarTwoLocalSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ AB As : Subgroup (MulAut L'), AB ≤ As → IsElemAbelian p As →
      (∀ a ∈ AB, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      (∀ a ∈ As, ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card AB → p ^ 3 ≤ Nat.card AB →
      (∀ n : L', n ^ p = 1 → (∀ a ∈ AB, a n = n) → ∀ U : Subgroup L', U ≠ ⊥ → IsPGroup 2 U →
        (∀ a ∈ AB, ∀ u ∈ U, a u ∈ U) → (∀ u ∈ U, n * u * n⁻¹ ∈ U) → MulAut.conj n ∈ AB) →
      ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ a ∈ As, ∀ φ : MulAut R, (∀ l : L', φ (ψ l) = ψ (a l)) → ∀ u ∈ U, φ u ∈ U

theorem ggBstarTwoLocalSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGBstarTwoLocalSCr p r R' I') :
    GGBstarTwoLocalSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf AB As hle hA hAI hAs hr h3 hmax
  obtain ⟨U, hU, hU2, hUA⟩ := h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
    (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf AB As hle hA
    (fun a ha => by
      obtain ⟨φ, hφ, hφa⟩ := hAI a ha
      exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa l]⟩)
    (fun a ha => by
      obtain ⟨φ, hφa⟩ := hAs a ha
      exact ⟨MulAut.congr e φ, fun l => by simp [MulAut.congr_apply, hφa l]⟩)
    hr h3 hmax
  refine ⟨U.map e.symm.toMonoidHom, ?_, hU2.map _, ?_⟩
  · intro hbot
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have h1 : e.symm u ∈ U.map e.symm.toMonoidHom := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    simpa using congrArg e h1
  · rintro a ha φ hφa _ ⟨u, hu, rfl⟩
    refine ⟨MulAut.congr e φ u, hUA a ha (MulAut.congr e φ)
      (fun l => by simp [MulAut.congr_apply, hφa l]) u hu, ?_⟩
    simp [MulAut.congr_apply]

end CFSG.StandardType

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem toGL_slConjugation (A : GL (Fin d) K) (g : SpecialLinearGroup (Fin d) K) :
    SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation d K A g) =
      A * SpecialLinearGroup.toGL g * A⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation, Units.val_mul, Units.val_mul,
    SpecialLinearGroup.coe_GL_coe_matrix]

theorem exists_model' (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 2) ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ (A₀ : GL (Fin d) K) (φ' : SpecialLinearGroup (Fin d) K →* L'), Function.Surjective φ' ∧
      (∀ g, ψ (φ' g) = proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ g)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t := by
  classical
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
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
  refine ⟨A₀, φ.comp c₀.toMonoidHom, hφs.comp c₀.surjective, fun g => hφ (c₀ g), ?_⟩
  intro a ha
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

end CFSG.StandardType.LinUnitL

end
