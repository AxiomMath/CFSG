module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfField
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFramesHalf

open ExcFrames


theorem exists_weylFrame_half_of_ext {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K L : Type} [Field K] [Finite K]
    [CharP K 2] [Field L] [Finite L] [CharP L 2] (ι : K →+* L) (hK : Nat.card K = 2 ^ f)
    (hL : Nat.card L = 2 ^ (2 * f)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {G : Type} [Group G] (χ : adjointGroup τ K →* G)
    (hχ : Function.Injective χ) {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hBs : IsElemAbelian p Bs) (hr : p ^ τ.rank ≤ Nat.card Bs) :
    ∃ ι' : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι' ∧ ι'.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι' (Multiplicative.ofAdd s) * g⁻¹ =
            ι' (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  have hp : p.Prime := Fact.out
  have hpL : p ∣ Nat.card L - 1 := by
    have hq : 1 ≤ Nat.card K := Finite.card_pos
    have e : Nat.card L - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      rw [hL, pow_mul', ← hK, ← Nat.sq_sub_sq, one_pow]
    rw [e]
    exact hpq.mul_right _
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) hpL
  have hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L := by
    rcases hτ with rfl | hτ'
    · exact fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a
    · exact TableBExc.full_of_E7_E8 hτ'
  have hE : IsElemAbelian p ((Bs.comap χ).map (adjBaseChange (τ := τ) ι)) :=
    isElemAbelian_map_frame _ (isElemAbelian_comap_frame χ hχ hBs)
  have hEc : Nat.card ((Bs.comap χ).map (adjBaseChange (τ := τ) ι)) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective (adjBaseChange_injective ι),
      card_comap_of_le_range χ hχ hBsR]
  have hT : ∃ c : adjointGroup τ L, ((Bs.comap χ).map (adjBaseChange ι)).map
      (MulAut.conj c).toMonoidHom = TableBExc.torusPow τ L p := by
    rcases hτ with rfl | hτ'
    · have hT4 : GGF4ToralRankInput L p := by
        by_cases hp3 : p = 3
        · subst hp3
          exact TableBF4.ggF4ToralRankInput_three hpL
        · exact TableBF4.ggF4ToralRankInput_of_five_le hp
            (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hpL
      exact hT4 _ hE (by rw [hEc]; exact hr)
    · exact IOneRest.ggExcToralRankInput_E7E8 hτ' hp hp2 hpL _ hE (by rw [hEc]; exact hr)
  obtain ⟨c, hc⟩ := hT
  refine exists_weylFrame_half ι hfull (isUnit_det_symmetrizedCartan hτ hp2) hζo χ hχ c hBsR hc
    fun α hα => ?_
  obtain ⟨a, σ, hσp, hα'⟩ := exists_normalForm hτ hf hK hp hp2 α hα
  obtain ⟨σ', hσ'p, hext⟩ := exists_ext_ringAut ι hf hK hL hp hp2 hσp
  obtain ⟨y, hy⟩ := exists_conj_of_normalForm ι hσ'p hext α a hα' c
  refine ⟨y, fun x hx => hy x ?_⟩
  rw [← hc]
  exact ⟨adjBaseChange ι x, ⟨x, hx, rfl⟩, rfl⟩

theorem exists_weylFrame_half_of_card {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {G : Type} [Group G] (χ : adjointGroup τ K →* G)
    (hχ : Function.Injective χ) {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hBs : IsElemAbelian p Bs) (hr : p ^ τ.rank ≤ Nat.card Bs) :
    ∃ ι' : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι' ∧ ι'.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι' (Multiplicative.ofAdd s) * g⁻¹ =
            ι' (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  have : CharP (FiniteField.Extension K 2 2) 2 :=
    charP_of_injective_algebraMap (algebraMap K (FiniteField.Extension K 2 2)).injective 2
  have hL : Nat.card (FiniteField.Extension K 2 2) = 2 ^ (2 * f) := by
    rw [FiniteField.natCard_extension, hK, ← pow_mul, mul_comm]
  exact exists_weylFrame_half_of_ext hτ hf (algebraMap K (FiniteField.Extension K 2 2)) hK hL
    hp2 hpq χ hχ hBsR hBs hr

end ExcFramesHalf

end CFSG.StandardType
