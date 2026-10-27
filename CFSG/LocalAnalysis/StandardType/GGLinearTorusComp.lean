module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Linear

theorem ggLinearTorusComponent_sl {G : Type} [Group G] [Finite G] {p m f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hnp : m + 1 = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (p - 1))
    (hEdiag : ∀ e ∈ E, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ e)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) {E₀ : Subgroup G} (hE₀ : E₀ ≤ E)
    {J : Subgroup G} (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) {e : G} (he : e ∈ E₀) :
    ∃ K : Subgroup G, IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {e}) ∧ J ≤ K ∧
      GGTypeAk f K := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hm : 2 ≤ m := by omega
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ := fun e he =>
    LinFusion.exists_mem_ggInducedPairs hm ψ hker (hEdiag e⁻¹ (E.inv_mem he))
  have hbig : p ^ ((m + 1) / p + 1) < Nat.card E := by
    rw [hcard, hnp, Nat.div_self hp.pos]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  obtain ⟨P, hP⟩ := LinTorus.exists_le_ggFrameTorus hp (by omega) (by rw [hF]; exact hpf) hker
    hE hbig hEA hEC
  have hker' := LinTorus.ker_comp_conjSL_le hker P⁻¹
  have hδ' : ∀ e ∈ E, ∃ d, (e, InnerDiagA.diagGL d) ∈
      LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) := fun e he => by
    obtain ⟨d, hd⟩ := hP he
    exact ⟨d, LinTorus.mem_ggInducedPairs_frame hd⟩
  choose! δ hδ using hδ'
  rw [← LinTorus.range_comp_conjSL ψ P⁻¹] at hJ ⊢
  exact LinTorus.exists_component_of_diag hF hf hp hker' (fun e he => hE.2 e he) hδ hE₀ hJ hidx
    he

end Linear

section Input

@[expose] def GGLinearTorusComponentTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    p.Prime → GGSixLinearCase p t n f →
    ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E = p ^ (p - 1) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
      E ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥ →
      ∀ E₀ : Subgroup G, E₀ ≤ E → ∀ J : Subgroup G,
        IsComponentOf J (G₀ ⊓ Subgroup.centralizer (E₀ : Set G)) →
        p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E →
          ∀ e ∈ E₀, e ≠ 1 → ∃ K : Subgroup G,
            IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) ∧ J ≤ K ∧ GGTypeAk f K

theorem ggLinearTorusComponentInput_of_tags (hL : GGLinearTorusComponentTag .PSL)
    (hU : GGLinearTorusComponentTag .PSU) : GGLinearTorusComponentInput := by
  intro G _ _ p t n f ψ G₀ hpres hp hlin
  rcases hlin.2.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hL G p n f ψ G₀ hpres hp hlin
  · exact hU G p n f ψ G₀ hpres hp hlin

theorem ggLinearTorusComponentTag_PSL : GGLinearTorusComponentTag .PSL := by
  intro G _ _ p n f ψ G₀ hpres hp hlin E hE hcard _ hEdiag hEC E₀ hE₀ J hJ hidx e he _
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpf : p ∣ 2 ^ f - 1 := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange] at hJ hEC ⊢
  exact ggLinearTorusComponent_sl hp hp5 hnp hadm.2.1 hpf hker hE hcard hEdiag hEC hE₀ hJ hidx he

theorem ggLinearTorusComponentInput_of_PSU (hU : GGLinearTorusComponentTag .PSU) :
    GGLinearTorusComponentInput :=
  ggLinearTorusComponentInput_of_tags ggLinearTorusComponentTag_PSL hU

theorem ggSixLinearJInput_of_PSU (hU : GGLinearTorusComponentTag .PSU) : GGSixLinearJInput :=
  ggSixLinearJInput_of_torus (ggLinearTorusComponentInput_of_PSU hU)

end Input

end CFSG.StandardType
