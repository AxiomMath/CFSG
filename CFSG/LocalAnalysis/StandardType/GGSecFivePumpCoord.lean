module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCoordPair
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem coord_linInd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W] {k : ℕ} (hk : 2 ≤ k) {x : Fin k → W}
    {f : Fin k → Module.Dual (ZMod p) W} (hP : ∀ i j, f i (x j) = (cartanD k i j : ZMod p)) :
    LinearIndependent (ZMod p) x := by
  have hdet : (Matrix.of fun i j => f i (x j)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j => f i (x j)) =
        (cartanD k).map (fun c : ℤ => (c : ZMod p)) := by
      ext i j
      simp [Matrix.map_apply, hP]
    rw [hmap, ← Int.cast_det (cartanD k), cartanD_eq, CartanMatrix.D_det hk, Int.cast_ofNat,
      show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero (zmod_two_ne_zero hp2) (zmod_two_ne_zero hp2)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : (Matrix.of fun i j => f i (x j)).mulVec g = 0 := by
    ext i
    have hi := congrArg (f i) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) i

private theorem coord_gram {k : ℕ} (hk : 2 ≤ k) (a b : Fin k) :
    ggDDot (toStdD k (Pi.single b 1)) (toStdD k (Pi.single a 1)) = cartanD k a b := by
  have hs : weylAction (isFiniteType_cartanD k)
      ((coxeterMatrix (isFiniteType_cartanD k)).simple a) = reflection (cartanD k) a := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      weylAction_simple (isFiniteType_cartanD k) a
  have h := (ggDReflRoot_simple k a).action hk (Pi.single b 1)
  rw [hs, reflection_apply_coroot, coroot_single, toStdD_sub, toStdD_smul, ggDReflect] at h
  have hα : toStdD k (Pi.single a 1) ≠ 0 := by
    rw [← toStdD_zero k, (toStdD_injective k).ne_iff]
    exact fun h0 => one_ne_zero (Pi.single_eq_zero_iff.1 h0)
  exact (smul_left_injective ℤ hα (sub_right_injective h)).symm

private theorem coord_equivariant {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {k : ℕ} {ρ : ggWeylD k →* MulAut ↥Bs} {x : Fin k → V} {f : Fin k → Module.Dual (ZMod p) V}
    (hx : ∀ a v, ggLin (p := p) ι (ρ ((coxeterMatrix (isFiniteType_cartanD k)).simple a)) v =
      v - f a v • x a)
    (hxf : ∀ a b, f a (x b) = (cartanD k a b : ZMod p)) (w : ggWeylD k) (u : Fin k → ℤ) :
    ggLin (p := p) ι (ρ w) (Fintype.linearCombination ℤ x u) =
      Fintype.linearCombination ℤ x (weylAction (isFiniteType_cartanD k) w u) := by
  revert u
  refine (coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.simple_induction
    (p := fun w => ∀ u, ggLin (p := p) ι (ρ w) (Fintype.linearCombination ℤ x u) =
      Fintype.linearCombination ℤ x (weylAction (isFiniteType_cartanD k) w u)) w
    (fun a u => ?_) (fun u => ?_) fun w w' hw hw' u => ?_
  · rw [weylAction_simple, reflection_apply_coroot, map_sub, map_smul,
      Fintype.linearCombination_apply_single, one_smul, CoxeterMatrix.toCoxeterSystem_simple, hx]
    congr 1
    rw [Fintype.linearCombination_apply, map_sum, coroot_apply,
      ← Int.cast_smul_eq_zsmul (ZMod p)]
    congr 1
    push_cast
    exact Finset.sum_congr rfl fun b _ => by
      rw [map_zsmul, hxf]
      exact (zsmul_eq_mul _ _).trans (mul_comm _ _)
  · simp
  · rw [map_mul ρ, map_mul (ggLin (p := p) ι), LinearEquiv.mul_apply, hw', hw,
      weylAction_mul_apply]

theorem ggDk_exists_coord {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {k : ℕ} (hk : 4 ≤ k)
    (hcard : Nat.card Bs = p ^ k) {ρ : ggWeylD k →* MulAut ↥Bs} (hρ : Function.Injective ρ)
    (hrefl : ∀ a, GGIsReflection p (ρ ((coxeterMatrix (isFiniteType_cartanD k)).simple a))) :
    ∃ θ : Additive ↥Bs ≃+ (Fin k → ZMod p), ∀ (t : ggWeylD k) (η : Fin k → ℤ),
      GGDReflRoot k t η → ∀ b : ↥Bs, θ (Additive.ofMul (ρ t b)) =
        θ (Additive.ofMul b) - (∑ a, θ (Additive.ofMul b) a * (η a : ZMod p)) •
          fun a => (η a : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hk2 : 2 ≤ k := by omega
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite ↥Bs := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp.pos k).ne')
  haveI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) V = k := by
    have h1 : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ι, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
        Nat.card_zmod]
    rw [hcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  obtain ⟨x, f, hx, hxf⟩ := ggDk_exists_cartanPairing hp2 ι hk hρ hrefl
  let βV := basisOfLinearIndependentOfCardEqFinrank' (K := ZMod p) x (coord_linInd hp2 hk2 hxf)
    (by rw [Fintype.card_fin, hdim])
  have hxb : ∀ b, βV b = x b := fun b => by simp [βV]
  let r : Fin k → Fin k → ZMod p := fun b c => (toStdD k (Pi.single b 1) c : ZMod p)
  let rf : Fin k → Module.Dual (ZMod p) (Fin k → ZMod p) :=
    fun a => ∑ c, r a c • LinearMap.proj c
  have hrf : ∀ a b, rf a (r b) = (cartanD k a b : ZMod p) := fun a b => by
    rw [← coord_gram hk2 a b, ggDDot, Int.cast_sum]
    simp only [rf, r, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => by rw [Int.cast_mul]; exact mul_comm _ _
  let βS := basisOfPiSpaceOfLinearIndependent (coord_linInd (W := Fin k → ZMod p) hp2 hk2 hrf)
  let Θ : V ≃ₗ[ZMod p] (Fin k → ZMod p) := βV.equiv βS (Equiv.refl _)
  have hΘx : ∀ b, Θ (x b) = r b := fun b => by
    rw [← hxb b]
    simp [Θ, βS]
  have hΘ : ∀ u : Fin k → ℤ,
      Θ (Fintype.linearCombination ℤ x u) = fun c => (toStdD k u c : ZMod p) := fun u => by
    have hT : toStdD k u = ∑ b, u b • toStdD k (Pi.single b 1) := by
      conv_lhs => rw [pi_eq_sum_univ' u]
      rw [← AddMonoidHom.mk'_apply (toStdD k) (toStdD_add k), map_sum]
      simp only [AddMonoidHom.mk'_apply, toStdD_smul]
    rw [Fintype.linearCombination_apply, map_sum, hT]
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, hΘx]
    exact zsmul_eq_mul (r b c) (u b)
  have hsurj : ∀ v : V, ∃ u : Fin k → ℤ, Fintype.linearCombination ℤ x u = v := fun v =>
    ⟨fun b => ((βV.repr v b).val : ℤ), by
      conv_rhs => rw [← βV.sum_repr v]
      rw [Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hxb b, ← Int.cast_smul_eq_zsmul (ZMod p), Int.cast_natCast, ZMod.natCast_zmod_val]⟩
  refine ⟨ι.trans Θ.toAddEquiv, fun t η ht b => ?_⟩
  obtain ⟨u, hu⟩ := hsurj (ι (Additive.ofMul b))
  have h1 : ι (Additive.ofMul (ρ t b)) =
      Fintype.linearCombination ℤ x (weylAction (isFiniteType_cartanD k) t u) := by
    rw [← ggLin_apply_ofMul (p := p) ι, ← hu, coord_equivariant ι hx hxf]
  have h2 : (ι.trans Θ.toAddEquiv) (Additive.ofMul (ρ t b)) =
      fun c => (ggDReflect η (toStdD k u) c : ZMod p) := by
    rw [AddEquiv.trans_apply, h1]
    exact (hΘ (weylAction (isFiniteType_cartanD k) t u)).trans (by rw [ht.action hk2])
  have h3 : (ι.trans Θ.toAddEquiv) (Additive.ofMul b) = fun c => (toStdD k u c : ZMod p) := by
    rw [AddEquiv.trans_apply, ← hu]
    exact hΘ u
  rw [h2, h3]
  funext c
  simp only [ggDReflect_apply, ggDDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end CFSG.StandardType

end
