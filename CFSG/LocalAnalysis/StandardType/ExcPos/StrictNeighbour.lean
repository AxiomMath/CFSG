module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial

private theorem strictNbr_component_eq {X : Type*} [Group X] [Finite X] {J K₁ K₂ N : Subgroup X}
    (hJ : CFSG.Assembly.IsQuasisimple J) (h₁ : CFSG.Assembly.IsComponentOf K₁ N)
    (h₂ : CFSG.Assembly.IsComponentOf K₂ N) (hJ₁ : J ≤ K₁) (hJ₂ : J ≤ K₂) : K₁ = K₂ := by
  rcases isComponentOf_eq_or_commute h₁ h₂ with h | h
  · exact h
  · exact absurd (hJ₁.trans ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans
      (Subgroup.centralizer_le hJ₂))) (not_le_centralizer_self_of_isQuasisimple hJ)

theorem le_normalizer_of_isComponentOf_centralizer {X : Type*} [Group X] [Finite X]
    {B J K : Subgroup X} {e : X} (hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (heB : e ∈ B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) (hJ : CFSG.Assembly.IsQuasisimple J)
    (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) :
    B ≤ Subgroup.normalizer (K : Set X) := by
  have key : ∀ b ∈ B, conjSub b K = K := by
    intro b hb
    have hcent : (Subgroup.centralizer ({e} : Set X)).map (MulAut.conj b).toMonoidHom =
        Subgroup.centralizer {e} := by
      rw [map_conj_centralizer_singleton, hBcomm b hb e heB, mul_inv_cancel_right]
    have hKb : CFSG.Assembly.IsComponentOf (conjSub b K) (Subgroup.centralizer {e}) := by
      have := isComponentOf_map_conj hK b
      rwa [hcent] at this
    have hJb : J ≤ conjSub b K :=
      calc J = conjSub b J := (conjSub_eq_of_mem_normalizer (hBJ hb)).symm
        _ ≤ conjSub b K := Subgroup.map_mono hJK
    exact (strictNbr_component_eq hJ hK hKb hJK hJb).symm
  intro b hb
  exact mem_normalizer_of_conjSub_le (le_of_eq (key b hb)) (le_of_eq (key b⁻¹ (B.inv_mem hb)))

theorem not_le_centralizer_of_isComponentOf_inf {X : Type*} [Group X] [Finite X]
    {G₀ D J K : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hK : CFSG.Assembly.IsQuasisimple K) (hKG₀ : K ≤ G₀) (hJK : J ≤ K) (hKne : K ≠ J) :
    ¬ D ≤ Subgroup.centralizer (K : Set X) := by
  intro hD
  have hKH : K ≤ G₀ ⊓ Subgroup.centralizer (D : Set X) :=
    le_inf hKG₀ (Subgroup.le_centralizer_iff.1 hD)
  have hJK' : CFSG.Assembly.IsComponentOf J K := isComponentOf_of_le hJ hJK hKH
  have hKK : CFSG.Assembly.IsComponentOf K K := ⟨le_rfl, .refl K, hK⟩
  exact hKne (strictNbr_component_eq hJ.2.2 hJK' hKK le_rfl hJK).symm

theorem strictNeighbour_has_nontrivial_D_action
    {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) {e : X} (heD : e ∈ D) {K : Subgroup X}
    (hKG₀ : K ≤ G₀) (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}))
    (hJK : J ≤ K) (hKne : K ≠ J) :
    B₁ ≤ Subgroup.normalizer (K : Set X) ∧ ¬ D ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨-, -, -, -, -, -, -, -, hEA, -, hDB, -, hBJ, -, hJcomp, -⟩ := hH
  have hBcomm : ∀ b ∈ B₁, ∀ c ∈ B₁, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hEA.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  exact ⟨le_normalizer_of_isComponentOf_centralizer hBcomm (hDB heD) hBJ hJcomp.2.2 hKcomp hJK,
    not_le_centralizer_of_isComponentOf_inf hJcomp hKcomp.2.2 hKG₀ hJK hKne⟩

end CFSG.StandardType.LieKnownR2.ExcPos
