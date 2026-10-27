module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCaseB
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtMonomial
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSpecial
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableOrth

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

theorem exists_isOrthOvergroup_four (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp3 : p ≠ 3)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hT5 : TFDegThree p) : ∃ K, IsOrthOvergroup p G H K := by
  have hs3 : SplitSupport B 3 := by
    have h := hD.split.2.2.1
    rwa [h4] at h
  have htf : QTwoLin.TransvectionFree B :=
    fun g hg => hD.setting.rGroup.2 g (hD.split.1 hg)
  have hd₁ : p = 3 → ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := fun h3 => absurd h3 hp3
  have hVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B :=
    HardMathSupport.Kantor79.commutatorSpace_mono hD.split.2.2.2.2
  rcases hT5 hp U h4 B hD.split.2.1 htf hs3 with
    ⟨horth, -⟩ | ⟨g, hg, ζ, hζ, hgv⟩ | ⟨hcard, hdm, hp7⟩ |
      ⟨hcard, -, hp5, Q, hQ, hBQ⟩ | ⟨f, i₀, i₁, ζ, hi, hB⟩
  · exact exists_isOrthOvergroup_of_isOrthType_movedGroup hp hD hirr₁ hd₁ horth
  · exact (false_of_mem_smul hp hD hg hζ fun v hv => hgv v (hVB hv)).elim
  · exact (false_of_card_movedGroup_eq_336 hp hD h4 hp7 hcard hdm).elim
  · exact exists_isOrthOvergroup_of_card_movedGroup_eq_120 hp hD h4 hp5 hirr₁ hcard
      ⟨Q, hQ, hBQ⟩
  · by_cases hζ2 : ζ * ζ = 1
    · refine exists_isOrthOvergroup_of_le_g2mmn (f := f) (i₀ := i₀) (i₁ := i₁) (ζ := ζ)
        hp hD h4 hirr₁ hi hζ2 ?_
      rcases hB with hB | hB
      · rw [hB]
        exact gmmn_le_g2mmn f i₀ i₁ ζ
      · rw [hB]
    · exact (false_of_monomial_of_mul_self_ne_one hp hD h4 hirr₁ hi hζ2 hB).elim

theorem exists_isOrthOvergroup_four_special (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp5 : p = 5)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) (hT5 : TFDegThree p) :
    ∃ K, IsOrthOvergroup p G H K := by
  have hs3 : SplitSupport B 3 := by
    have h := hD.split.2.2.1
    rwa [h4] at h
  have htf : QTwoLin.TransvectionFree B :=
    fun g hg => hD.setting.rGroup.2 g (hD.split.1 hg)
  have hVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B :=
    HardMathSupport.Kantor79.commutatorSpace_mono hD.split.2.2.2.2
  rcases hT5 hp U h4 B hD.split.2.1 htf hs3 with
    ⟨horth, -⟩ | ⟨g, hg, ζ, hζ, hgv⟩ | ⟨hcard, hdm, hp7⟩ |
      ⟨hcard, -, hp5', Q, hQ, hBQ⟩ | ⟨f, i₀, i₁, ζ, hi, hB⟩
  · exact exists_isOrthOvergroup_special_of_isOrthType hp hD h4 hp5 hr hT horth
  · exact (false_of_mem_smul hp hD hg hζ fun v hv => hgv v (hVB hv)).elim
  · exact (false_of_card_movedGroup_eq_336 hp hD h4 hp7 hcard hdm).elim
  · exact absurd hp5 hp5'
  · rcases hB with hB | hB
    · exact exists_isOrthOvergroup_special_of_eq_gmmn (f := f) (i₀ := i₀) (i₁ := i₁) (ζ := ζ)
        hp hD h4 hp5 hr hT hi hB
    · exact exists_isOrthOvergroup_special_of_eq_g2mmn (f := f) (i₀ := i₀) (i₁ := i₁) (ζ := ζ)
        hp hD h4 hp5 hr hT hi hB

theorem exists_isOrthOvergroup_of_five_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h5 : 5 ≤ Module.finrank (ZMod p) U)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hd₁ : p = 3 → ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hT4 : TFOrthCorankOne p (Module.finrank (ZMod p) U - 1)) :
    ∃ K, IsOrthOvergroup p G H K := by
  have htf : QTwoLin.TransvectionFree B :=
    fun g hg => hD.setting.rGroup.2 g (hD.split.1 hg)
  have hsY : SplitSupport (reflStab p H h) (Module.finrank (ZMod p) U - 1 - 1) := by
    have h := splitSupport_reflStab hp hD.setting.four_le hD.setting.five_le_of_eq_three
      hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 hD.mem hD.isRefl hirr₁
    rwa [show Module.finrank (ZMod p) U - 1 - 1 = Module.finrank (ZMod p) U - 2 by omega]
  have hoY := isOrthType_movedGroup_reflStab hp hD.setting.four_le
    hD.setting.five_le_of_eq_three hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 hD.mem hD.isRefl
  rcases hT4 (by omega) U B (reflStab p H h) hD.split.2.2.2.2 hD.split.2.1 htf
      hD.split.2.2.1 (reflGen_reflSubgroupIn H _) hsY hoY hd₁ with
    ⟨horthB, -⟩ | ⟨-, -, hψ, x, hx, hxV⟩
  · exact exists_isOrthOvergroup_of_isOrthType_movedGroup hp hD hirr₁ hd₁ horthB
  · exact exists_isOrthOvergroup_of_mem_map_ne hp hD
      (exists_eq_mul_of_irredOnSection hp hD hirr₁ hψ) hx hxV

theorem exists_isOrthOvergroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hT4 : TFOrthCorankOne p (Module.finrank (ZMod p) U - 1)) (hT5 : TFDegThree p) :
    ∃ K, IsOrthOvergroup p G H K := by
  have hm3 : 3 ≤ Module.finrank (ZMod p) U - 1 := by
    have := hD.setting.four_le
    omega
  have hfin : Module.finrank (ZMod p) U = Module.finrank (ZMod p) U - 1 + 1 := by omega
  rcases tfOrthStabilizer hp (m := Module.finrank (ZMod p) U - 1) hm3 U hfin H
      hD.setting.sub.1 hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 hD.setting.sub.2.2.1
      hD.setting.sub.2.2.2.2 h hD.mem hD.isRefl with ⟨-, hirr₁, hd₁⟩ | ⟨hm, hp5, r, e, s, hr, hT⟩
  · by_cases h4 : Module.finrank (ZMod p) U = 4
    · have hp3 : p ≠ 3 := by
        intro h3
        have := hD.setting.five_le_of_eq_three h3
        omega
      exact exists_isOrthOvergroup_four hp hD h4 hp3 hirr₁ hT5
    · have h5 : 5 ≤ Module.finrank (ZMod p) U := by
        have := hD.setting.four_le
        omega
      exact exists_isOrthOvergroup_of_five_le hp hD h5 hirr₁ hd₁ hT4
  · have h4 : Module.finrank (ZMod p) U = 4 := by omega
    exact exists_isOrthOvergroup_four_special hp hD h4 hp5 hr hT hT5

end CFSG.StandardType.ZS

end
