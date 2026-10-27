module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCaseA
public import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

theorem exists_isIsom_basisSumSq_of_le_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1)
    (hB : movedGroup B ≤ g2mmn p f i₀ i₁ ζ) :
    ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      Q₂.comp (HardMathSupport.Kantor79.commutatorSpace B).subtype = basisSumSq f ∧
      ∀ g ∈ B, IsIsom p Q₂ g := by
  have hs : SplitSupport B (Module.finrank (ZMod p) U - 1) := hD.split.2.2.1
  have hn : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by
    have h4 := hD.setting.four_le
    omega
  obtain ⟨e, he, he0⟩ := hs.exists_mem_centralizerSpace_ne_zero hn
  obtain ⟨Q₂, hQ₂, hcomp, -, hBQ⟩ := exists_isIsom_of_isIsom_movedGroup hp hs
    (polarBilin_basisSumSq_nondegenerate f hp)
    (fun g hg => isIsom_basisSumSq_of_mem_g2mmn f hi hζ (hB hg))
    he he0 (c := 1) one_ne_zero
  exact ⟨Q₂, hQ₂, hcomp, hBQ⟩

theorem exists_isOrthOvergroup_of_le_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1)
    (hB : movedGroup B ≤ g2mmn p f i₀ i₁ ζ) : ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨Q₂, hQ₂, -, hBQ₂⟩ := exists_isIsom_basisSumSq_of_le_g2mmn hp hD hi hζ hB
  have hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g := ⟨Q₂, hQ₂, hBQ₂⟩
  have hζ2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hζ)
  have hlcm : Nat.lcm 2 (orderOf ζ) = 2 := Nat.lcm_eq_left hζ2
  have hcard : Nat.card (g2mmn p f i₀ i₁ ζ) = 48 := by
    rw [card_g2mmn hp (by norm_num) f hi ζ, hlcm]
    norm_num
  have hdvd' : Nat.card (movedGroup B) ∣ 48 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hB
  have hp3 : p ≠ 3 := by
    intro h3
    have h5 := hD.setting.five_le_of_eq_three h3
    omega
  refine exists_isOrthOvergroup_of_not_dvd_card hp hD h4 hirr₁ ?_ hψ
  intro hd
  have hp48 : p ∣ 48 := hd.trans hdvd'
  have hpr : p.Prime := Fact.out
  rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hp48
  rcases hpr.dvd_mul.mp hp48 with h | h
  · exact hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp h)

end CFSG.StandardType.ZS

end
