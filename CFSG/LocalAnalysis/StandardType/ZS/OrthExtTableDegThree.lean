module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Main
import CFSG.LocalAnalysis.StandardType.ZS.AmbivalentForm
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtWitt
import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix

public section

namespace CFSG.StandardType.ZS

open CFSG.StandardType.ZS.DimThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem exists_basis_eq_gmmn_or_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) (h3 : 3 ≤ n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : ReflGen p A) (hA : AbsIrred p A) (himp : Quasithin.SimsG4.IsImprimitiveOnV A) :
    ∃ (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ), i₀ ≠ i₁ ∧
      (A = gmmn p f i₀ i₁ ζ ∨ A = g2mmn p f i₀ i₁ ζ) := by
  obtain ⟨b, hmon⟩ := CFSG.StandardType.ggRC_monomial_of_imprimitive
    (n := n) hn A hA hgen himp
  obtain ⟨b', hmon', hperm', -⟩ :=
    CFSG.StandardType.ggRC_monomial_frame hp b A hA hgen hmon
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have h' : (0 : ℕ) = 1 := by simpa [i₀, i₁] using congrArg Fin.val h
    omega
  by_cases hsign : ∃ i, diagMap p b' (fun j => if j = i then -1 else 1) ∈ A
  · obtain ⟨ζ, -, hAeq⟩ := eq_g2mmn_of_permMap_mem hp b' hgen hmon' hperm' hsign hi
    exact ⟨b', i₀, i₁, ζ, hi, Or.inr hAeq⟩
  · have hsign' : ∀ i, diagMap p b' (fun j => if j = i then -1 else 1) ∉ A := by
      intro i hi_mem
      exact hsign ⟨i, hi_mem⟩
    obtain ⟨ζ, hAeq⟩ := eq_gmmn_of_permMap_mem hp b' hgen hmon' hperm' hsign' hi
    exact ⟨b', i₀, i₁, ζ, hi, Or.inl hAeq⟩

theorem not_transvectionFree_of_mem_iff_det [Module.Finite (ZMod p) U]
    (h2 : 2 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) :
    ¬ QTwoLin.TransvectionFree A := by
  intro htf
  let b := Module.finBasis (ZMod p) U
  let i₀ : Fin (Module.finrank (ZMod p) U) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank (ZMod p) U) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have h' : (0 : ℕ) = 1 := by simpa [i₀, i₁] using congrArg Fin.val h
    omega
  have hv0 : b i₀ ≠ 0 := Module.Basis.ne_zero b i₀
  have hψ0 : b.coord i₁ ≠ 0 := by
    intro h0
    have h1 : b.coord i₁ (b i₁) = 1 := by
      simp [Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [h0] at h1
    exact zero_ne_one h1
  have hψv : b.coord i₁ (b i₀) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Ne.symm hi]
  have hdet : LinearEquiv.det (LinearEquiv.transvection hψv) = 1 :=
    LinearEquiv.transvection.det_eq_one hψv
  have hmem : LinearEquiv.transvection hψv ∈ A := (hA _).mpr (Or.inl hdet)
  have htrans : QTwoLin.IsTransvectionLin (LinearEquiv.transvection hψv) :=
    ⟨b i₀, b.coord i₁, hv0, hψ0, hψv, LinearEquiv.transvection.apply hψv⟩
  exact htf _ hmem htrans

private theorem tfDegThree_imprimitive (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (h3 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3)
    (hRY : ReflGen p (movedGroup X)) (hIY : AbsIrred p (movedGroup X))
    (himp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)) :
    ∃ (f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
      (i₀ i₁ : Fin 3) (ζ : (ZMod p)ˣ), i₀ ≠ i₁ ∧
      (movedGroup X = gmmn p f i₀ i₁ ζ ∨ movedGroup X = g2mmn p f i₀ i₁ ζ) := by
  let W := HardMathSupport.Kantor79.commutatorSpace X
  let _ : Module.Finite (ZMod p) W := Module.Finite.of_injective W.subtype W.subtype_injective
  exact exists_basis_eq_gmmn_or_g2mmn hp h3 (le_refl 3) hRY hIY himp

private theorem tfDegThree_J34 {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ34 : ExcData p .J34 (movedGroup X)) :
    Nat.card (movedGroup X) = 336 ∧ DMax p (movedGroup X) 4 ∧ p ≠ 7 := by
  obtain ⟨hadm, -, hcard, -, hdmax, -⟩ := hJ34
  exact ⟨by simpa [ExcRow.ord] using hcard, by simpa [ExcRow.dmax] using hdmax,
    by simpa [ExcRow.admissible] using hadm⟩

private theorem tfDegThree_J35 {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ35 : ExcData p .J35 (movedGroup X) ∧ ∃ g ∈ movedGroup X, ∃ ζ : ZMod p,
      ζ * ζ ≠ 1 ∧ ∀ v, g v = ζ • v) :
    ∃ g ∈ X, ∃ ζ : ZMod p, ζ * ζ ≠ 1 ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, g v = ζ • v := by
  obtain ⟨-, g, hgY, ζ, hζ, hgv⟩ := hJ35
  let W := HardMathSupport.Kantor79.commutatorSpace X
  let hW : ∀ h ∈ X, ∀ w ∈ W, h w ∈ W := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have hgY' : g ∈ (restrictHom X W hW).range := by
    change g ∈ movedGroup X
    exact hgY
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hgY'
  refine ⟨(x : U ≃ₗ[ZMod p] U), x.2, ζ, hζ, ?_⟩
  intro v hv
  have h := congrArg (fun w : W => (w : U)) (hgv ⟨v, hv⟩)
  rw [← hx] at h
  simpa [restrictHom_apply] using h

private theorem tfDegThree_H3 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (h4 : Module.finrank (ZMod p) U = 4)
    (hs : SplitSupport X 3) (hIY : AbsIrred p (movedGroup X))
    (hH3 : ExcData p .H3 (movedGroup X) ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧
      ∀ g ∈ movedGroup X, ∃ k ∈ movedGroup X, k * g * k⁻¹ = g⁻¹) :
    Nat.card (movedGroup X) = 120 ∧ DMax p (movedGroup X) 5 ∧ p ≠ 5 ∧
      ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
        ∀ g ∈ X, IsIsom p Q g := by
  obtain ⟨hdata, hp10, hinv⟩ := hH3
  obtain ⟨-, -, hcard, -, hdmax, -⟩ := hdata
  have hcard' : Nat.card (movedGroup X) = 120 := by simpa [ExcRow.ord] using hcard
  have hdmax' : DMax p (movedGroup X) 5 := by simpa [ExcRow.dmax] using hdmax
  have hp5 : p ≠ 5 := by rintro rfl; norm_num at hp10
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp10
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two hp
  have h3 : (3 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_three hp3
  have h5 : (5 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_five hp5
  have h120 : (120 : ZMod p) ≠ 0 := by
    have hfac : (120 : ZMod p) = 2 ^ 3 * 3 * 5 := by norm_num
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h2) h3) h5
  have hcardZ : (Nat.card (movedGroup X) : ZMod p) ≠ 0 := by
    rw [hcard']; exact h120
  let W := HardMathSupport.Kantor79.commutatorSpace X
  let _ : Module.Finite (ZMod p) W := Module.Finite.of_injective W.subtype W.subtype_injective
  have h3W : Module.finrank (ZMod p) W = 3 := hs.2.1
  obtain ⟨ψ, hψnd, hψY⟩ :=
    exists_isIsom_of_isConj_inv hp hIY hcardZ (by rw [h3W]; norm_num) hinv
  have hCdim : Module.finrank (ZMod p) (centralizerSpace X) = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hs.1
    rw [hs.2.1, h4] at hsum
    omega
  have hCne : centralizerSpace X ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hCdim
    exact zero_ne_one hCdim
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
  have hs' : SplitSupport X (Module.finrank (ZMod p) U - 1) := by
    simpa [h4] using hs
  obtain ⟨Q, hQnd, -, -, hQX⟩ :=
    exists_isIsom_of_isIsom_movedGroup hp hs' hψnd hψY he he0 (c := 1) one_ne_zero
  exact ⟨hcard', hdmax', hp5, Q, hQnd, hQX⟩


theorem tfDegThree : TFDegThree p := by
  intro hp U _ _ _ h4 X hR htf hs
  let Y := movedGroup X
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_injective V.subtype V.subtype_injective
  have hRY : ReflGen p Y := reflGen_movedGroup hR
  have hIY : AbsIrred p Y := absIrred_of_reflGen hRY (irred_movedGroup_of_splitSupport hs)
  have htfY : QTwoLin.TransvectionFree Y := transvectionFree_movedGroup hs htf
  have h3 : Module.finrank (ZMod p) V = 3 := hs.2.1
  by_cases hprim : Quasithin.SimsG4.IsImprimitiveOnV Y
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (tfDegThree_imprimitive hp h3 hRY hIY hprim))))
  · rcases rows_of_finrank_eq_three hp h3 hRY hIY hprim with hSL | hOrth | hH3 | hJ34 | hJ35
    · exact (not_transvectionFree_of_mem_iff_det (by rw [h3]; norm_num) hSL htfY).elim
    · exact Or.inl ⟨hOrth, hprim⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (tfDegThree_H3 hp h4 hs hIY ⟨hH3.1, hH3.2.1, hH3.2.2.1⟩))))
    · exact Or.inr (Or.inr (Or.inl (tfDegThree_J34 hJ34.1)))
    · exact Or.inr (Or.inl (tfDegThree_J35 hJ35))

end CFSG.StandardType.ZS

end
