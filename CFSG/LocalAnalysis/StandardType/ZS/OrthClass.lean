module

public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.OrthOrderBound
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModel

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem zs_isIsom_mul {Q : QuadraticForm (ZMod p) U} {g h : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) (hh : IsIsom p Q h) : IsIsom p Q (g * h) := by
  intro v
  rw [LinearEquiv.mul_apply, hg, hh]

private theorem zs_isIsom_inv {Q : QuadraticForm (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) : IsIsom p Q g⁻¹ := by
  intro v
  have h := hg (g⁻¹ v)
  rw [show g (g⁻¹ v) = v by simp] at h
  exact h.symm

theorem ggOrthType_of_orth {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ A ↔ IsIsom p Q g) : GGOrthType A := by
  refine ⟨Q, hQ, fun g hg => (hA g).mp hg, ?_⟩
  intro g h hg hh
  rw [hA]
  exact zs_isIsom_mul (zs_isIsom_mul (zs_isIsom_mul hg hh) (zs_isIsom_inv hg))
    (zs_isIsom_inv hh)

theorem ggOrthType_of_orthClass [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = Subgroup.closure (ClassRefl p Q c)) :
    GGOrthType A := by
  rw [hA]
  exact ⟨Q, hQ, fun g hg => isIsom_of_mem_closure_classRefl hg,
    fun g h hg hh => commutator_mem_closure_classRefl hp h5 hQ hc hg hh⟩

theorem pow_le_card_of_ggOrthType [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) (h5 : 5 ≤ n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : GGOrthType A) : p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A := by
  obtain ⟨Q, hQ, -, hcomm⟩ := hA
  exact pow_le_card_of_commutator_isometry_mem hp hn h5 hQ A hcomm

private lemma zs_e6_finrank {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {u : Fin 6 → V}
    {φ : Fin 6 → Module.Dual (ZMod 3) V}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hspan : Submodule.span (ZMod 3) (Set.range u) = ⊤)
    (hker : ⨅ i, LinearMap.ker (φ i) = ⊥) :
    Module.finrank (ZMod 3) V = 5 := by
  have hrel : Fintype.linearCombination (ZMod 3) u E6QTwo.cartanE6KernelVec = 0 := by
    have hz : Fintype.linearCombination (ZMod 3) u E6QTwo.cartanE6KernelVec ∈
        ⨅ i, LinearMap.ker (φ i) := by
      rw [Submodule.mem_iInf]
      intro i
      exact LinearMap.mem_ker.mpr (by
        rw [E6QTwo.apply_linearCombination_eq_cartanE6ModThree hK i E6QTwo.cartanE6KernelVec]
        exact congrFun E6QTwo.cartanE6ModThree_mulVec_cartanE6KernelVec i)
    rwa [hker, Submodule.mem_bot] at hz
  have hker_ne : LinearMap.ker (Fintype.linearCombination (ZMod 3) u) ≠ ⊥ := by
    intro hbot
    have hmem : E6QTwo.cartanE6KernelVec ∈
        LinearMap.ker (Fintype.linearCombination (ZMod 3) u) := LinearMap.mem_ker.mpr hrel
    rw [hbot, Submodule.mem_bot] at hmem
    exact E6QTwo.cartanE6KernelVec_ne_zero hmem
  have hle : Module.finrank (ZMod 3) V ≤ 5 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination (ZMod 3) u)
    rw [Fintype.range_linearCombination, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hsum
    have hker1 : 1 ≤ Module.finrank (ZMod 3)
        (LinearMap.ker (Fintype.linearCombination (ZMod 3) u)) := by
      obtain ⟨x, hxmem, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hker_ne
      have hmono : Submodule.span (ZMod 3) {x} ≤
          LinearMap.ker (Fintype.linearCombination (ZMod 3) u) := by
        rw [Submodule.span_le]
        rintro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxmem
      have h := Submodule.finrank_mono hmono
      rwa [finrank_span_singleton hx0] at h
    have : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range u)) ≤ 5 := by omega
    rwa [hspan, finrank_top] at this
  have hge : 5 ≤ Module.finrank (ZMod 3) V := by
    have h := E6QTwo.five_le_finrank_span hK
    rwa [hspan, finrank_top] at h
  exact le_antisymm hle hge

private lemma zs_e6_form {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {u : Fin 6 → V}
    {φ : Fin 6 → Module.Dual (ZMod 3) V}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod 3)) (hV : Nat.card V = 3 ^ 5) :
    ∃ (B : LinearMap.BilinForm (ZMod 3) V) (Q : QuadraticForm (ZMod 3) V),
      (∀ i v, B (u i) v = φ i v) ∧ (∀ x y, B x y = B y x) ∧ B.Nondegenerate ∧
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ (∀ v, Q v = B v v) ∧
      (∀ x y, QuadraticMap.polar Q x y = 2 * B x y) := by
  obtain ⟨B, hB⟩ := E6QTwo.exists_bilinForm hK hV
  have hsymm : ∀ x y, B x y = B y x := E6QTwo.bilinForm_symm hK hV hB
  have hBnd : B.Nondegenerate :=
    ⟨fun x hx => E6QTwo.bilinForm_nondegenerate hK hV hB hx,
     fun y hy => E6QTwo.bilinForm_nondegenerate hK hV hB fun x => by
       rw [← hsymm x y]; exact hy x⟩
  let Q : QuadraticForm (ZMod 3) V := B.toQuadraticMap
  have hQval : ∀ v, Q v = B v v := fun v => LinearMap.BilinMap.toQuadraticMap_apply B v
  have hpolarQ : ∀ x y, QuadraticMap.polar Q x y = 2 * B x y := by
    intro x y
    rw [QuadraticMap.polar, hQval (x + y), hQval x, hQval y]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
    rw [hsymm y x]
    ring
  have hpQ : (QuadraticMap.polarBilin Q).Nondegenerate := by
    have hflip : B.flip = B := LinearMap.ext fun x => LinearMap.ext fun y => (hsymm x y).symm
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, show LinearMap.flip B = B from hflip]
    constructor
    · intro x hx
      refine hBnd.1 x fun y => ?_
      have h2 : (2 : ZMod 3) * B x y = 0 := by
        simpa only [LinearMap.add_apply, two_mul] using hx y
      exact (mul_eq_zero.mp h2).resolve_left (by decide)
    · intro y hy
      refine hBnd.2 y fun x => ?_
      have h2 : (2 : ZMod 3) * B x y = 0 := by
        simpa only [LinearMap.add_apply, two_mul] using hy x
      exact (mul_eq_zero.mp h2).resolve_left (by decide)
  exact ⟨B, Q, hB, hsymm, hBnd, hpQ, hQval, hpolarQ⟩

private lemma zs_e6_classRefl {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {u : Fin 6 → V}
    {φ : Fin 6 → Module.Dual (ZMod 3) V} {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    {B : LinearMap.BilinForm (ZMod 3) V} {Q : QuadraticForm (ZMod 3) V}
    (hφ : ∀ i, φ i (u i) = 2) (hK : ∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (u i) v = φ i v)
    (hpQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQval : ∀ v, Q v = B v v)
    (hpolarQ : ∀ x y, QuadraticMap.polar Q x y = 2 * B x y)
    (hAeq : A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) :
    A = Subgroup.closure (ClassRefl 3 Q 2) := by
  apply le_antisymm
  · rw [hAeq]
    refine (Subgroup.closure_le (Subgroup.closure (ClassRefl 3 Q 2))).mpr fun _ hr => ?_
    obtain ⟨i, rfl⟩ := hr
    exact Subgroup.subset_closure ⟨
      (isRefl_iff (p := 3) (U := V) (by norm_num) (Module.reflection (hφ i))).mpr
        ⟨u i, φ i, hφ i, rfl⟩,
      fun v => by
        rw [hQval (Module.reflection (hφ i) v), hQval v]
        exact E6QTwo.bilinForm_reflection hK hV hB hφ i v v,
      u i, by rw [hQval, hB i (u i), hφ i], Module.reflection_apply_self (hφ i)⟩
  · refine (Subgroup.closure_le A).mpr fun t ht => ?_
    obtain ⟨a, hQa, rfl⟩ :=
      (mem_classRefl_iff (p := 3) (U := V) (by norm_num) hpQ
        (by decide : (2 : ZMod 3) ≠ 0) t).mp ht
    have hQa_ne : Q a ≠ 0 := by rw [hQa]; decide
    have hBaa : B a a = 2 := by rw [← hQval]; exact hQa
    obtain ⟨g, hgA, hgapp⟩ := E6QTwo.exists_mem_e6Weyl_reflection hK hV hB hφ hBaa
    rw [hAeq]
    have hgt : g = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
      ext w
      rw [hgapp w, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa_ne,
        hpolarQ a w, hQa, mul_div_cancel_left₀ (B a w) (by decide : (2 : ZMod 3) ≠ 0)]
    rw [← hgt]
    exact hgA

theorem isCartanModel_E6_three_classRefl {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : IsCartanModel 3 (CartanMatrix.E 6) A) :
    Module.finrank (ZMod 3) V = 5 ∧ ∃ Q : QuadraticForm (ZMod 3) V,
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ A = Subgroup.closure (ClassRefl 3 Q 2) := by
  obtain ⟨u, φ, hφ, hK, hspan, hker, hAeq⟩ := hA
  have hfin : Module.finrank (ZMod 3) V = 5 := zs_e6_finrank hK hspan hker
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod 3) u) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  have _ : Module.Finite (ZMod 3) V :=
    Module.Finite.of_surjective (Fintype.linearCombination (ZMod 3) u) hsurj
  let _ : Finite V := Finite.of_surjective _ hsurj
  have hV : Nat.card V = 3 ^ 5 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hfin] at h
    exact h
  obtain ⟨B, Q, hB, -, -, hpQ, hQval, hpolarQ⟩ := zs_e6_form hK hV
  exact ⟨hfin, Q, hpQ, zs_e6_classRefl hφ hK hV hB hpQ hQval hpolarQ hAeq⟩

theorem ggOrthType_of_isCartanModel_E6 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : IsCartanModel 3 (CartanMatrix.E 6) A) :
    Module.finrank (ZMod 3) V = 5 ∧ GGOrthType A := by
  obtain ⟨hfin, Q, hpQ, hAcl⟩ := isCartanModel_E6_three_classRefl hA
  have _ : Module.Finite (ZMod 3) V := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  refine ⟨hfin, Q, hpQ, fun g hg => ?_, fun g h hg hh => ?_⟩
  · rw [hAcl] at hg
    exact isIsom_of_mem_closure_classRefl hg
  · rw [hAcl] at ⊢
    exact commutator_mem_closure_classRefl (p := 3) (U := V) (by norm_num) (by rw [hfin])
      hpQ (by decide : (2 : ZMod 3) ≠ 0) hg hh

end CFSG.StandardType.ZS

end
