module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFourOne
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFourTwo

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open CFSG.StandardType.SevOm
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] in
private theorem splitFour_zero_cases (hQ : (polarBilin Q).Nondegenerate)
    (F : SevOm.Frame Q p E r) (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (s : Multiplicative (Fin r → ZMod p)) (hsp4 : finrank K (fixedSpace (F.ι s)) = 4) :
    (∃ k, toAdd s k = 0 ∧ ∀ j, j ≠ k → toAdd s j ≠ 0) ∨
      ∃ k l, k ≠ l ∧ toAdd s k = 0 ∧ toAdd s l = 0 := by
  rcases splitFour_zero_card hQ F hU hV s hsp4 with h1 | h2
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
    have hkm := Finset.mem_singleton_self k
    rw [← hk] at hkm
    refine Or.inl ⟨k, (Finset.mem_filter.mp hkm).2, fun j hj hj0 => hj ?_⟩
    have hjm : j ∈ Finset.univ.filter (fun j => toAdd s j = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj0⟩
    rw [hk] at hjm
    exact Finset.mem_singleton.mp hjm
  · obtain ⟨k, l, hkl, hkl'⟩ := Finset.card_eq_two.mp h2
    have hkm : k ∈ ({k, l} : Finset (Fin r)) := Finset.mem_insert_self k {l}
    have hlm : l ∈ ({k, l} : Finset (Fin r)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self l)
    rw [← hkl'] at hkm hlm
    exact Or.inr ⟨k, l, hkl, (Finset.mem_filter.mp hkm).2, (Finset.mem_filter.mp hlm).2⟩

theorem exists_mem_of_splitFour (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) {e : ℕ}
    (hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) →
      y * y' = y' * y)
    (hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    (s : Multiplicative (Fin r → ZMod p)) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {F.ι s}))
    (hJX : J ≤ supportedBlock Q (F.ι s) (X - 1))
    (hsp : OmNonsplit.SplitFour (Q.comp (fixedSpace (F.ι s)).subtype))
    (hK : 4 ≤ Nat.card K) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hx : OddOrderIsometry Q p (F.ι s) := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have hsp4 : finrank K (fixedSpace (F.ι s)) = 4 := hsp.1
  rcases (SevOmSmall.fixed_case_small_odd hx (isComponentOf_isometryCentralizer hJ) hJX).2 with
    hodd | ⟨-, -, -⟩
  · exact exists_mem_of_odd_mem hQ hp hp2 hEΩ F hU hV hz s (by omega) hodd
  have hRnd : (QuadraticMap.polarBilin (Q.comp (fixedSpace (F.ι s)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  obtain ⟨T₁, T₂, hsup, -, -, hcommT, hc₁, hc₂, ⟨ψ₁, hψ₁, hr₁⟩, ⟨ψ₂, hψ₂, hr₂⟩, hoddO⟩ :=
    splitFour_factors hRnd hsp (by omega) (by omega)
  have hinf : T₁ ⊓ T₂ = ⊥ := splitFour_inf_eq_bot hcommT hψ₁ hr₁
  rcases splitFour_zero_cases hQ F hU hV s hsp4 with ⟨k, hk, hothers⟩ | ⟨k, l, hkl, hk, hl⟩
  · exact (splitFour_one_coord_false hQ hp hp2 hEΩ F hU hmax s hx hk hothers hsup hcommT
      hψ₁ hr₁ hψ₂ hr₂ hoddO).elim
  obtain ⟨hTJc, hTJq⟩ := splitFour_TJ_isComponent F s hx hJ hJX
  rcases eq_left_or_right_of_splitFour hsup hc₁ hc₂ hTJq hTJc.2.1 with hTJ | hTJ
  · exact splitFour_two_coord_exists hQ hp hp2 hEΩ F hcomm hz s hx hk hl hkl hsup.symm hinf
      hcommT hψ₂ hr₂ hoddO hTJ
  · exact splitFour_two_coord_exists hQ hp hp2 hEΩ F hcomm hz s hx hk hl hkl
      (by rw [sup_comm]; exact hsup.symm) (by rw [inf_comm]; exact hinf)
      (fun a ha b hb => (hcommT b hb a ha).symm) hψ₁ hr₁ hoddO hTJ

end CFSG.StandardType.OrthTorusGen
