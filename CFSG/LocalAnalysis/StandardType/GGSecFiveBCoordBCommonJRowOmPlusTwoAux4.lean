module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux3
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndElt
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneShapes

public section

namespace CFSG.StandardType.CommonJOmPlusTwo

open CFSG.Assembly CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.OrthBlocks
  CFSG.StandardType.GGQ2Frame.PlaneRaw

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggCommonJOmPlusTwo_sparse (hK : Nat.card K = 2) :
    ∀ f : Fin 4 → Multiplicative (ZMod 3), f ≠ 1 → GGCoordSparse f →
      ∃ K' : Subgroup ↥(omegaQ (K := K) 4 1),
        IsComponentOf K' (Subgroup.centralizer
          ({(ggCommonJOmPlusTwo_tau hK 4 f)} : Set ↥(omegaQ (K := K) 4 1))) ∧
        (∀ K'' : Subgroup ↥(omegaQ (K := K) 4 1),
          IsComponentOf K'' (Subgroup.centralizer
            ({(ggCommonJOmPlusTwo_tau hK 4 f)} : Set ↥(omegaQ (K := K) 4 1))) → K'' = K') ∧
        (ggCommonJOmPlusTwo_tau hK 4).range ⊓
            Subgroup.centralizer (K' : Set ↥(omegaQ (K := K) 4 1)) =
          Subgroup.zpowers (ggCommonJOmPlusTwo_tau hK 4 f) ∧
        7 ∣ Nat.card K' := by
  classical
  intro f hf hsparse
  obtain ⟨a, ha⟩ := hsparse
  have hfa : f a ≠ 1 := by
    intro h1
    apply hf
    funext j
    by_cases hja : j = a
    · simp [hja, h1]
    · exact ha j hja
  let F' : PlaneRaw.V 4 := fun i => (f i).toAdd
  let S : Finset (Fin 4) := Finset.univ.filter fun i => F' i = 0
  let τ := ggCommonJOmPlusTwo_tau hK 4
  let K' : Subgroup ↥(omegaQ (K := K) 4 1) := oYcode (otc_zeta K) 4 1 (.zero S)
  have hS : S = Finset.univ.erase a := by
    ext i
    simp only [S, F', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro hia
      rw [hia] at hi
      exact hfa (toAdd_eq_zero.mp hi)
    · rintro ⟨hia, -⟩
      exact toAdd_eq_zero.mpr (ha i hia)
  have hScard : S.card = 3 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  have hocc0 : PlaneRaw.occurs (Submodule.span (ZMod 3) {F'}) (.zero S) := by
    intro i
    constructor
    · intro hi u
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.2
      rw [← hc]
      have hfi : F' i = 0 := by simpa [S] using (Finset.mem_filter.mp hi).2
      change (c • F') i = 0
      simp [Pi.smul_apply, smul_eq_mul, hfi]
    · intro h
      change i ∈ Finset.filter (fun i => F' i = 0) Finset.univ
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, h ⟨F', Submodule.mem_span_singleton_self _⟩⟩
  have hadm : PlaneRaw.admissible (.orthogonal 1) (.zero S) := by
    refine Or.inr ⟨?_, ?_⟩ <;> rw [hScard] <;> norm_num
  have hcomp : ∀ K'' : Subgroup ↥(omegaQ (K := K) 4 1),
      IsComponentOf K'' (Subgroup.centralizer ({τ f} : Set ↥(omegaQ (K := K) 4 1))) →
        K'' = K' := by
    intro K'' hK''
    obtain ⟨c, hc, hocc, rfl⟩ := ggCommonJOmPlusTwo_components hK f hK''
    cases c with
    | zero T =>
        have hT : T = S := by
          ext i
          rw [show i ∈ T ↔ ∀ u : ↥(Submodule.span (ZMod 3) {F'}),
            (u : PlaneRaw.V 4) i = 0 from hocc i]
          rw [show i ∈ S ↔ ∀ u : ↥(Submodule.span (ZMod 3) {F'}),
            (u : PlaneRaw.V 4) i = 0 from hocc0 i]
        rw [hT]
    | extension e =>
        exfalso
        obtain ⟨he, χ, hχne, hχ, hχzero⟩ := hocc
        obtain ⟨hae, h4⟩ := hc
        have hsub : PlaneRaw.Code.extSupport e ⊆ {a} := by
          intro i hi
          by_contra hia
          have hfi : F' i = 0 := by
            have h1 : f i = 1 := ha i (by simpa using hia)
            simpa [F'] using congrArg Multiplicative.toAdd h1
          have hz : PlaneRaw.evalRestr (Submodule.span (ZMod 3) {F'}) i = 0 := by
            ext u
            change (u : PlaneRaw.V 4) i = 0
            obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.2
            rw [← hc]
            change (c • F') i = 0
            simp [Pi.smul_apply, smul_eq_mul, hfi]
          have h1 := hχ i (by simpa using hi)
          have hz' : e i • χ = 0 := by rw [← h1, hz]
          have hei : e i ≠ 0 := by simpa using hi
          rcases smul_eq_zero.mp hz' with h | h
          · exact hei h
          · exact hχne h
        have hcardle : (PlaneRaw.Code.extSupport e).card ≤ 1 := by
          have := Finset.card_le_card hsub
          simpa using this
        omega
  have hcardcent : Nat.card ↥(PlaneRaw.cent (.orthogonal 1) (.zero S)) = 3 := by
    change Nat.card ↥(PlaneRaw.centZero S) = 3
    have hcard' : Nat.card ↥(PlaneRaw.centZero S) = Nat.card (ZMod 3) :=
      Nat.card_congr
        { toFun := fun v => v.1 a
          invFun := fun c => ⟨c • PlaneRaw.unitVec 4 a, by
            rw [PlaneRaw.mem_centZero]
            intro i hi
            have hia : i ≠ a := (Finset.mem_erase.mp (hS ▸ hi)).1
            simp [PlaneRaw.unitVec, Pi.smul_apply, hia]⟩
          left_inv := fun v => by
            apply Subtype.ext
            funext i
            by_cases hia : i = a
            · subst hia
              simp [PlaneRaw.unitVec]
            · have hv2 := v.2
              rw [PlaneRaw.mem_centZero] at hv2
              have hvi : v.1 i = 0 :=
                hv2 i (by rw [hS]; exact Finset.mem_erase.mpr ⟨hia, Finset.mem_univ i⟩)
              simp [PlaneRaw.unitVec, Pi.smul_apply, hia, hvi]
          right_inv := fun c => by simp [PlaneRaw.unitVec] }
    rw [hcard', Nat.card_zmod]
  have hcardinf : Nat.card ↥(τ.range ⊓
      Subgroup.centralizer (K' : Set ↥(omegaQ (K := K) 4 1))) = 3 := by
    change Nat.card ↥(τ.range ⊓ Subgroup.centralizer
      (oYcode (otc_zeta K) 4 1 (.zero S) :
        Set ↥(omegaQ (K := K) 4 1))) = 3
    rw [(ggCommonJOmPlusTwo_position hK f (.zero S) hadm hocc0).1]
    exact hcardcent
  have hx3 : ∀ x : Multiplicative (ZMod 3), x ^ 3 = 1 := by decide
  have hf3 : f ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply]
    exact hx3 (f i)
  have hordertau : orderOf (τ f) = 3 := by
    rw [orderOf_injective τ (ggCommonJOmPlusTwo_tau_injective hK 4) f]
    exact orderOf_eq_prime hf3 hf
  have hcardzp : Nat.card ↥(Subgroup.zpowers (τ f)) = 3 := by
    rw [Nat.card_zpowers, hordertau]
  have hK' : IsComponentOf K' (Subgroup.centralizer
      ({(ggCommonJOmPlusTwo_tau hK 4 f)} : Set ↥(omegaQ (K := K) 4 1))) := by
    rw [ggCommonJOmPlusTwo_centralizer_span (K := K) hK 4 f]
    exact (orthIsComponentOfCentralizerTorusSetIff_holds (otc_zeta K) 4 1 hK
      (otc_zeta_injective K) (Submodule.span (ZMod 3) {F'}) K').mpr
      ⟨.zero S, hadm, hocc0, rfl⟩
  have hle : Subgroup.zpowers (τ f) ≤ τ.range ⊓
      Subgroup.centralizer (K' : Set ↥(omegaQ (K := K) 4 1)) := by
    refine Subgroup.zpowers_le_of_mem ⟨⟨f, rfl⟩, ?_⟩
    change τ f ∈ Subgroup.centralizer (K' : Set ↥(omegaQ (K := K) 4 1))
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK'.1 hg)
  have heq : τ.range ⊓ Subgroup.centralizer (K' : Set ↥(omegaQ (K := K) 4 1)) =
      Subgroup.zpowers (τ f) := by
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardinf, hcardzp])).symm
  have hseven : 7 ∣ Nat.card K' := by
    let ψ := oYcodeMulEquivOmegaQ (ζ := otc_zeta K) hK 4 1 S hadm
    have hcard : Nat.card K' = Nat.card (CFSG.RankThree.Classical2.orthDerived
        (planeQForm K 3 1)) := by
      calc Nat.card K' = Nat.card ↥(omegaQ (K := K) S.card 1) := Nat.card_congr ψ.toEquiv
        _ = Nat.card ↥(omegaQ (K := K) 3 1) := by rw [hScard]
        _ = Nat.card (CFSG.RankThree.Classical2.orthDerived (planeQForm K 3 1)) := by
            rw [show omegaQ (K := K) 3 1 = LargeEvenOmega ⇑(planeQForm K 3 1) by
              unfold omegaQ
              rw [← coe_planeQForm]]
            exact Nat.card_congr
              (TableBOrth.omegaEquivOrthDerived (planeQForm K 3 1)).toEquiv
    rw [hcard]
    exact CFSG.StandardType.IOneOrthEnd.seven_dvd_card_orthDerived
      (W := Fin (3 + 1) ⊕ Fin (3 + 1) → K) (R := planeQForm K 3 1)
      (by simpa using hK : Nat.card K = 2 ^ 1) nondegenerate_planeQForm (by
        simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum])
  exact ⟨K', hK', hcomp, heq, hseven⟩

end CFSG.StandardType.CommonJOmPlusTwo

end
