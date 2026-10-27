module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldCore
public import CFSG.RankThree.PartTwo.Sec21.Implications

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (descendAut conjAut fieldAut
  conjAut_mem_linearAutGroup)

theorem autElliptic_of_inndiag_mulEquiv {X : Type*} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (e : X ≃* SpecialLinearGroup (Fin 3) K)
    {E : Subgroup (MulAut X)} (hE3 : ∀ α ∈ E, α ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hdiag : ∀ α ∈ E, ∃ A : GL (Fin 3) K, ∀ x : X,
      ((e (α x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) *
          ((e x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    {x : X} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X) (hxE : ∀ α ∈ E, α x = x)
    {T : Subgroup (MulAut X)} (hT : IsPGroup 2 T)
    (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut X))) : AutElliptic X T := by
  set Φ := MulAut.congr e with hΦ
  refine autElliptic_of_map_congr e (autElliptic_of_inndiag hω (E := E.map Φ.toMonoidHom)
    (x := e x) ?_ ?_ ?_ ?_ ?_ ?_ (hT.map _) ?_)
  · rintro _ ⟨α, hα, rfl⟩
    change Φ α ^ 3 = 1
    rw [← map_pow, hE3 α hα, map_one]
  · rw [Subgroup.card_map_of_injective Φ.injective]
    exact hE9
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨A, hA⟩ := hdiag α hα
    refine ⟨A, MulEquiv.ext fun h => Subtype.ext ?_⟩
    change ((e (α (e.symm h)) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [hA, MulEquiv.apply_symm_apply, slConjugation_matrix]
  · rw [← map_pow, hx3, map_one]
  · intro h
    exact hxZ ((mem_center_iff_of_mulEquiv e x).mp h)
  · exact (fixed_map_congr_iff e E x).mpr hxE
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨α, hα, rfl⟩
    change Φ α * Φ t = Φ t * Φ α
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hTE ht)) α hα]

theorem inndiag_of_not_field {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    {K : Type} [Field K] [Finite K] (e : lBar L ≃* SpecialLinearGroup (Fin 3) K)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hnf : ∀ a ∈ A, ¬ CFSG.RankThree.PartTwo.KFacts.InducesKindSL 3 K L a .field) :
    ∀ α ∈ Sec4.autThetaQuot A L, ∃ g : GL (Fin 3) K, ∀ z : lBar L,
      ((e (α z) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) *
          ((e z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  intro α hα
  obtain ⟨a, ha, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hα
  set β : MulAut (SpecialLinearGroup (Fin 3) K) :=
    CFSG.RankThree.PartTwo.KFacts.inducedAutHom L e ⟨a, ha⟩ with hβ
  have hβ3 : β ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.KFacts.inducedAutHom_pow_eq_one L e ha (hA3 a haA)
  have hβz : ∀ z : lBar L, e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) z) =
      β (e z) := by
    intro z
    change _ = e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) (e.symm (e z)))
    rw [MulEquiv.symm_apply_apply]
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField.exists_isConjBy_or_conj_fieldAut β
      hβ3 with ⟨g, hg⟩ | ⟨σ, H, hσ, hβH⟩
  · exact ⟨g, fun z => by rw [hβz]; exact hg (e z)⟩
  · exfalso
    apply hnf a haA
    refine ⟨e, ha, fieldAut 3 K σ, ⟨σ, rfl⟩, ?_, conjAut 3 K H, conjAut_mem_linearAutGroup H,
      ?_⟩
    · intro h1
      have hσ1 : σ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hσ
        norm_num at hσ
      apply CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField.slFieldAut_ne_one hσ1
      apply CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := K) le_rfl
      rw [map_one]
      exact h1
    · change descendAut 3 K β = _
      rw [hβH, map_mul, map_mul, map_inv]
      rfl

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
