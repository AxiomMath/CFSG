module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5U42
public import CFSG.GroupTheory.ExtraspecialCentralInner
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem centerOf_facts_of_isQ8D8 {E Q : Subgroup H} (h : IsQ8D8 ↥Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set H)) :
    IsElemSec (centerOf Q) Q ∧ (centerOf Q).relIndex Q = 16 ∧
      E ≤ Subgroup.normalizer (centerOf Q : Set H) ∧
      (∀ z ∈ centerOf Q, ∀ e ∈ E, z * e = e * z) ∧
      (∀ z ∈ centerOf Q, z ^ 2 = 1) := by
  have hfacts := isQ8D8_extraspecial_facts h
  refine ⟨hfacts.2.2.1, hfacts.2.2.2, ?_, ?_, ?_⟩
  · intro x hx
    exact CFSG.GroupTheory.mem_normalizer_inf_centralizer (hEQ hx) (hEQ hx)
  · intro z hz
    exact commute_of_mem_centerOf_of_card_two hEQ hfacts.2.1 hz
  · intro z hz
    have h := pow_card_eq_one' (G := ↥(centerOf Q)) (x := ⟨z, hz⟩)
    rw [hfacts.2.1] at h
    simpa using congrArg (fun x : ↥(centerOf Q) => (x : H)) h

theorem f112sa_ker_right_j2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hJ : S3A5J2Hyp L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ f112saP2' L1 L2 S, ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  obtain ⟨hsec, hidx, hK₀n, hK₀c, hK₀2⟩ :=
    centerOf_facts_of_isQ8D8 hJ.q8d8_right
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S))
  have hcB : c ∈ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S) hcS
  obtain ⟨hc2, hcQ⟩ := f112sa_two_elem_normalizer_QA hF hcS
  have hQB : pCoreOf 2 (f112saP2' L1 L2 S) ≤ bigB L1 L2 S :=
    (f112sa_QA_le_T hF).trans (inf_le_right.trans (f112sa_K_le_bigB L1 L2 S))
  have hT3 : ∀ x ∈ bigB L1 L2 S, (∀ t ∈ S ⊓ f112saK L1 L2 S, x * t = t * x) →
      ∃ z ∈ (S ⊓ f112saK L1 L2 S) ⊓
          Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H),
        ∀ y ∈ f112saP1' L1 L2 S, x * y * x⁻¹ = z * y * z⁻¹ :=
    fun x hx hxT => f112sa_exists_center_conj_eq_P1' hF hx hxT
  have hcore : ∀ x ∈ bigB L1 L2 S,
      (∀ y ∈ f112saP1' L1 L2 S, x * y = y * x) →
      (∀ y ∈ f112saP2' L1 L2 S, x * y = y * x) → x = 1 := by
    intro x hxB hx1 hx2
    have hmem : x ∈ bigB L1 L2 S ⊓
        Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
        Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
      ⟨⟨hxB, Subgroup.mem_centralizer_iff.mpr fun y hy => (hx1 y hy).symm⟩,
        Subgroup.mem_centralizer_iff.mpr fun y hy => (hx2 y hy).symm⟩
    rw [f112sa_core_free hF] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact CFSG.GroupTheory.mem_of_commutatorElement_mem_of_isExtraspecial
    (B := bigB L1 L2 S) (E₁ := f112saP1' L1 L2 S) (L := f112saP2' L1 L2 S)
    (Q := pCoreOf 2 (f112saP2' L1 L2 S)) (T := S ⊓ f112saK L1 L2 S) (c := c)
    (isQ8D8_extraspecial_facts hJ.q8d8_right).1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    (f112sa_irred hF h1 h2 hsec (le_of_eq hidx) hK₀n hK₀c hK₀2)
    (le_commutator_sup_pCoreOf_of_isL2Quot le_rfl (f112sa_isL2Quot_P2' hF h1 h2))
    hK₀c (f112sa_T_sylow_P2' hF.toW).1 (f112sa_centerOf_T_le_P2' hF.toW) hQB hT3 hcore hc2 hcB
      hcQ hcL

private theorem f112sa_indec_right_j2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hJ : S3A5J2Hyp L1 L2 S) :
    ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoRes L2⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S) := by
  obtain ⟨hsec, hidx, hK₀n, hK₀c, hK₀2⟩ :=
    centerOf_facts_of_isQ8D8 hJ.q8d8_right
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S))
  have h := f112sa_indec_sup hF h1 h2 hsec (le_of_eq hidx) hK₀n hK₀c hK₀2
  refine le_antisymm (le_sup_left.trans h.le) ?_
  refine CFSG.GroupTheory.le_of_le_sup_of_le_commutator
    (Q := pCoreOf 2 (f112saP2' L1 L2 S))
    (M := ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoRes L2⁆)
    (K₀ := centerOf (pCoreOf 2 (f112saP2' L1 L2 S)))
    (le_sup_left.trans h.le) h.ge ?_ ?_
  · intro k hk q hq
    exact hK₀c k hk q (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)
  · exact (CFSG.GroupTheory.commutator_eq_inf_centralizer_of_isExtraspecial
      (isQ8D8_extraspecial_facts hJ.q8d8_right).1).ge

theorem s3a5ModuleFacts_of_j2Hyp {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hJ : S3A5J2Hyp L1 L2 S) : S3A5ModuleFacts L1 L2 S :=
  ⟨fun c hc hcL => f112sa_ker_right_j2 hF h1 h2 hJ hc hcL,
    f112sa_indec_right_j2 hF h1 h2 hJ, fun d hd hd3 e he hed => by
      have he1 : e ∈ (⊥ : Subgroup H) :=
        hJ.nat_left d hd hd3 e he (by
          rw [show ⁅e, d⁆ = 1 by rw [commutatorElement_def, hed]; group]
          exact Subgroup.one_mem _)
      rw [Subgroup.mem_bot.mp he1]
      exact Subgroup.one_mem _⟩

end CFSG.Quasithin.F112R.St84
