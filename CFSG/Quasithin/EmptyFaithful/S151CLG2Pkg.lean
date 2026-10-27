module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2Step
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsG24Good
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParG2

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

section G2


theorem goodLocal_parabolic_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (j : Fin 2) :
    GoodLocal ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  set C := adjointGroup Tag.G2 K with hC
  have hP₀C : parabolicSubgroup Tag.G2 K {G2.i0} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : parabolicSubgroup Tag.G2 K {G2.i1} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hQ₀C : parabolicRadical Tag.G2 K {G2.i0} ≤ C :=
    ((parabolicRadical_le_posUnipotent {G2.i0}).trans
      (posUnipotent_le_parabolicSubgroup {G2.i0})).trans hP₀C
  have hQ₁C : parabolicRadical Tag.G2 K {G2.i1} ≤ C :=
    ((parabolicRadical_le_posUnipotent {G2.i1}).trans
      (posUnipotent_le_parabolicSubgroup {G2.i1})).trans hP₁C
  rcases G2.fin_two_cases (g2Index j) with hj | hj <;> rw [hj]
  · refine ParabolicFacts.goodLocal (Q := (parabolicRadical Tag.G2 K {G2.i0}).subgroupOf C) ?_
    refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact G2.parabolicFacts_zero hK hf
  · refine ParabolicFacts.goodLocal (Q := (parabolicRadical Tag.G2 K {G2.i1}).subgroupOf C) ?_
    refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact G2.parabolicFacts_one hK hf

theorem exists_pkg_good_of_equiv {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C]
    (e : Y ≃* C) {U₀ : Subgroup C} {P₀ : Fin 2 → Subgroup C} (h : Rk2.Rank2Pkg C U₀ P₀)
    (hgood : ∀ j, GoodLocal (P₀ j)) (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rk2.Rank2Pkg Y U P ∧ ∀ j, GoodLocal (P j) := by
  have h1 := h.map e.symm
  have hU₁ := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ :=
    (isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : (U₀.map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨fun j => ((P₀ j).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom, ?_,
    fun j => ?_⟩
  · have := h1.map (MulAut.conj k)
    rwa [hconj] at this
  · exact ((hgood j).map e.symm).map (MulAut.conj k)

theorem rankTwoPar_g2 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 2 n Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, RankTwoPar Y U P := by
  obtain ⟨hf, K, hF, hFin, hCh, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  obtain ⟨P, hPkg, hgood⟩ := exists_pkg_good_of_equiv e (Rk2.rank2Pkg_g2 hK hf)
    (fun j => goodLocal_parabolic_g2 hK hf j) hU₀ hU
  refine ⟨P, hPkg, ?_, hgood⟩
  intro α hα j
  obtain ⟨Q₁, Q₂, -, hmax, -, -, -, hinv⟩ := (even_G2_model_two_extensions hY).2.2.2 U hU
  rcases (hmax (P j) (hPkg.le j)).1 (hPkg.covBy j) with h | h
  · rw [h]
    exact (hinv α hα).1
  · rw [h]
    exact (hinv α hα).2

end G2

end CFSG.Quasithin.CLG2
