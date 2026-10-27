module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

theorem GGTorusTBGroup.mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)}
    {I' : Set (MulAut R')} (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') {L' : Type}
    [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (h : GGTorusTBGroup p r R I L' ψ A) : GGTorusTBGroup p r R' I' L' (e.toMonoidHom.comp ψ) A := by
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := h
  refine ⟨e.surjective.comp hψ, ?_, hperf, hA, ?_, hr, h3, hsc⟩
  · exact (TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
    rw [MulEquiv.symm_apply_apply, hφa]

section PSL

variable {d p : ℕ} {K : Type} [Field K] [Finite K]

private theorem two_dvd_card_of_charP_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card K := by
  have := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff K 2 _).mp h0

theorem slHasSections_of_four_le [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) : SLHasSections d K := by
  rcases Nat.lt_or_ge 4 d with h5 | h4
  · exact slHasSections_of_five_le (by omega)
  · have hd4 : d = 4 := by omega
    have h2 : Nat.card K ≠ 2 := by
      intro hK2
      rw [hK2] at hpK
      norm_num at hpK
      have hge := hp.two_le
      omega
    have h34 : ¬(d = 3 ∧ Nat.card K = 4) := by omega
    have h43 : ¬(d = 4 ∧ Nat.card K = 3) := by
      rintro ⟨-, hK3⟩
      have h2' : 2 ∣ Nat.card K := two_dvd_card_of_charP_two
      omega
    exact slHasSections_of_card (by omega) h2 h34 h43

theorem not_ggTorusTBGroup_small (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hd3 : d ≤ 3) {r : ℕ} {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d K} {A : Subgroup (MulAut L')} :
    ¬ GGTorusTBGroup p r (projectiveSL d K) (Set.range (conjAut d K)) L' ψ A := by
  rintro ⟨hψ, hker, hperf, hA, hAI, -, h3, -⟩
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hlt := card_lt_of_torality hp hpK hd hd3 (ggPGLTorality_holds hp hp2 hpK) hX hXI
  rw [hcard] at hlt
  omega

theorem exists_actsDiag_model_of_tbGroup [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) {r : ℕ} (hr : d - 2 ≤ r) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d K} {A : Subgroup (MulAut L')}
    (hA : GGTorusTBGroup p r (projectiveSL d K) (Set.range (conjAut d K)) L' ψ A) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧ ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t := by
  classical
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr', h3, -⟩ := hA
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Nat.card K := two_dvd_card_of_charP_two
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hAe
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have h1 : p ^ (d - 2) ≤ Nat.card (inducedSub ψ A) := by
    rw [hcardX]
    exact (Nat.pow_le_pow_right hp.pos hr).trans hr'
  obtain ⟨A₀, hA₀⟩ := ggPGLTorality_holds (d := d) hp hp2 hpK _ hXA hXI h1 (hcardX ▸ h3)
  exact TypeANbrDvd.exists_actsDiag_model hperfSL (slHasSections_of_four_le hp hpK hd)
    hψ hker hperf hAI hA₀

end PSL

theorem ggTorusAutCardSCr_of_mulEquiv {p r N : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusAutCardSCr p r R' I' N) :
    GGTorusAutCardSCr p r R I N := by
  intro L' _ _ ψ A hA
  exact h L' (e.toMonoidHom.comp ψ) A (hA.mulEquiv e hI)

end CFSG.StandardType
