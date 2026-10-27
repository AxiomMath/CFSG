module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksIso
import CFSG.LocalAnalysis.StandardType.GGQ2LinGLDerived
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksQuasi

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix

theorem blockGroup_extension_zero {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2) :
    blockGroup ζ t ε (PlaneRaw.Code.extension 0) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h1 := (Subgroup.mem_inf.mp hg).1.1
  have hP : (planeIdem t ε (PlaneRaw.Code.extSupport (0 : PlaneRaw.V t)) false :
      Matrix (LinIdx t ε) (LinIdx t ε) K) = 0 := by
    ext ((i | i) | k) ((j | j) | l) <;>
      simp [planeIdem, PlaneRaw.Code.extSupport, Matrix.diagonal_apply]
  rw [hP, sub_zero, mul_one] at h1
  exact Subgroup.mem_bot.mpr (Units.ext h1)

theorem relIndex_ycode_extension {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {ε : Fin 2}
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {e : PlaneRaw.V t}
    (he : 2 ≤ (PlaneRaw.Code.extSupport e).card) :
    (Ycode ζ t ε (PlaneRaw.Code.extension e)).relIndex
      (blockGroup ζ t ε (PlaneRaw.Code.extension e)) = 3 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (PlaneRaw.Code.extSupport e).card by omega)
  have hne : e ≠ 0 := fun h => (PlaneRaw.mem_extSupport e i).mp hi (by rw [h]; rfl)
  obtain ⟨L, _, _, _, hL, ⟨φ⟩⟩ := exists_blockGroup_extension_mulEquiv ζ t ε hK hζ hne
  have h := relIndex_commutator_of_mulEquiv_gl he (fun _ => by rw [hL]; norm_num) φ
  rw [hL] at h
  exact h

theorem linMarkedYcode_holds : LinMarkedYcode := by
  intro K _ _ _ ζ t ε hK hζ c hc
  cases c with
  | zero S =>
    have hS : 3 ≤ 2 * S.card + ε.val := hc
    obtain ⟨φ⟩ := nonempty_blockGroup_zero_mulEquiv ζ t ε S
    exact largeEvenMarking_commutator_of_mulEquiv_gl (f := 1) (hK.trans (pow_one 2).symm) le_rfl
      (by omega) (fun h => absurd h (by omega)) φ
  | extension e =>
    obtain ⟨he, hs⟩ := hc
    have hs' : 2 ≤ (PlaneRaw.Code.extSupport e).card := hs
    obtain ⟨L, _, _, _, hL, ⟨φ⟩⟩ := exists_blockGroup_extension_mulEquiv ζ t ε hK hζ he
    exact largeEvenMarking_commutator_of_mulEquiv_gl (f := 2) hL (by norm_num) hs'
      (fun _ => le_rfl) φ

theorem linIsQuasisimpleYcode_holds : LinIsQuasisimpleYcode := by
  intro K _ _ _ ζ t ε hK hζ c hc
  obtain ⟨hperf, lab, -, hraw⟩ := linMarkedYcode_holds ζ t ε hK hζ c hc
  obtain ⟨R, _, -, -, hsimple, hna, θ, -⟩ :=
    largeEvenRawDatum_exists ((largeEvenRawDatum_legacy lab _).mpr hraw)
  have : IsSimpleGroup R := hsimple
  exact ⟨⟨hperf⟩, θ.isSimpleGroup, nonabelian_of_mulEquiv θ.symm hna⟩

theorem linNotIsComponentOfYcode_holds : LinNotIsComponentOfYcode := by
  intro K _ _ _ ζ t ε hK hζ c hc X
  cases c with
  | zero S =>
    have hS : ¬ 3 ≤ 2 * S.card + ε.val := hc
    obtain ⟨φ⟩ := nonempty_blockGroup_zero_mulEquiv ζ t ε S
    refine not_isComponentOf_commutator_of_mulEquiv_gl ?_ φ X
    rcases Nat.lt_or_ge (2 * S.card + ε.val) 2 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hK⟩
  | extension e =>
    by_cases he : e = 0
    · subst he
      have h0 : Ycode ζ t ε (PlaneRaw.Code.extension (0 : PlaneRaw.V t)) =
          ⁅(⊥ : Subgroup (GL (LinIdx t ε) K)), ⊥⁆ := by
        rw [Ycode, blockGroup_extension_zero]
      rw [h0]
      exact SpBlocks.not_isComponentOf_commutator_bot X
    · have h1 : (PlaneRaw.Code.extSupport e).card ≤ 1 := by
        by_contra h
        exact hc ⟨he, by omega⟩
      obtain ⟨L, _, _, _, hL, ⟨φ⟩⟩ := exists_blockGroup_extension_mulEquiv ζ t ε hK hζ he
      exact not_isComponentOf_commutator_of_mulEquiv_gl (Or.inl h1) φ X

end CFSG.StandardType.GGQ2Frame.LinBlocks
