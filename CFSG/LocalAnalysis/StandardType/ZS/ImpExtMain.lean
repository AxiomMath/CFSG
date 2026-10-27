module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtN4Std
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4End
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDegEnd

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma polar_phiForm_apply (f : Module.Basis (Fin 4) (ZMod p) U) (m : U) (j : Fin 4) :
    QuadraticMap.polarBilin (phiForm f) m (f j) =
      (2 : ZMod p) * (if j = 3 then (-1 : ZMod p) else 1) * f.repr m j := by
  rw [QuadraticMap.polarBilin_apply_apply]
  fin_cases j <;>
  · simp only [phiForm, QuadraticMap.comp_apply, QuadraticMap.polar,
      QuadraticMap.weightedSumSquares_apply, map_add, Fin.sum_univ_four]
    simp
    ring

theorem isOrthType_of_forall_isIsom_phiForm (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : ∀ g, g ∈ G ↔ IsIsom p (phiForm f) g) :
    IsOrthType p G := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  refine ⟨phiForm f, ?_, Or.inl hG⟩
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro m hm
  apply f.forall_coord_eq_zero_iff.mp
  intro j
  rw [Module.Basis.coord_apply]
  have h2 : (2 : ZMod p) * (if j = 3 then (-1 : ZMod p) else 1) * f.repr m j = 0 := by
    rw [← polar_phiForm_apply]
    exact hm (f j)
  have hw : (if j = 3 then (-1 : ZMod p) else 1) ≠ 0 := by
    split_ifs with h
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpge2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    exact hp (le_antisymm hp2 hpge2)
  exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero h2ne hw)

private lemma two_ne_zero_of_prime_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpge2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  exact hp (le_antisymm hp2 hpge2)

namespace ImpExtSetting

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}

theorem finrank_eq_four_of_impExt (hp : p ≠ 2) (S : ImpExtSetting G H d)
    (I : ImpExtInputs G H) : Module.finrank (ZMod p) U = 4 := by
  obtain ⟨e, j₀, j₁, ζ, hne, hmono⟩ := S.exists_standardBasis hp
  let Std : ImpExtStd G H d e j₀ j₁ ζ := ⟨S, hne, hmono⟩
  obtain ⟨hl, _, _⟩ := Std.impExtRowM hp I
  have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
  omega

theorem eq_weylN4_or_weylEN4_or_weylF4_or_orth (hp : p ≠ 2) (S : ImpExtSetting G H d)
    (I : ImpExtInputs G H) :
    Module.finrank (ZMod p) U = 4 ∧
      ((∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
          G = basisClosure f (weylN4Mats t)) ∨
        (∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
          G = basisClosure f (weylEN4Mats t)) ∨
        (∃ f : Module.Basis (Fin 4) (ZMod p) U, G = basisClosure f weylF4Mats) ∨
        (p = 3 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U, ∀ g, g ∈ G ↔ IsIsom p (phiForm f) g)) := by
  obtain ⟨e, j₀, j₁, ζ, hne, hmono⟩ := S.exists_standardBasis hp
  let Std : ImpExtStd G H d e j₀ j₁ ζ := ⟨S, hne, hmono⟩
  obtain ⟨_, hm, hk⟩ := Std.impExtRowM hp I
  have hn : Module.finrank (ZMod p) U = 4 := finrank_eq_four_of_impExt hp S I
  refine ⟨hn, ?_⟩
  rcases hmono with hmono | hmono
  · exact Or.inl (Std.eq_weylN4 hp hn (hm hmono) hmono)
  · rcases hk hmono with hζ2 | hζ4
    · rcases Std.eq_weylF4_or_eq_isIsom hp I hn hζ2 hmono with hF4 | horth
      · exact Or.inr (Or.inr (Or.inl hF4))
      · exact Or.inr (Or.inr (Or.inr horth))
    · exact Or.inr (Or.inl (Std.eq_weylEN4 hp hn hζ4 hmono))

end ImpExtSetting

end CFSG.StandardType.ZS

end
