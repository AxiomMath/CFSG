module

public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusDescent

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (cartanFunctional)

theorem qplus_torus_data_of_isAlgClosure (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ f + 1) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] :
    ∃ (θ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K)
      (n : Fin τ.rank → adjointGroup τ K), Function.Injective θ ∧ (∀ i, orderOf (n i) = 2) ∧
      ∀ i v, n i * θ (.ofAdd v) * (n i)⁻¹ =
        θ (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity 2 L f hf).1 τ
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L 2 f := ⟨_, rfl⟩
  rw [← hFrdef] at hS
  have hFr2 : ∀ c, Fr c = c ^ 2 ^ f := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr2, hK]
  obtain ⟨g, hg⟩ := hLang ⟨qplusZ τ L, qplusZ_mem⟩
  have hgF : Units.map (entrywiseHom Fr) (g : ModGL τ L) = (g : ModGL τ L) * qplusZ τ L := by
    rw [← hS g]
    have h1 : S g = g * ⟨qplusZ τ L, qplusZ_mem⟩ := by rw [hg, mul_inv_cancel_left]
    rw [h1]
    rfl
  have hfix : ∀ x : ModGL τ L,
      qplusZ τ L * Units.map (entrywiseHom Fr) x * (qplusZ τ L)⁻¹ = x →
      Units.map (entrywiseHom Fr) ((g : ModGL τ L) * x * (g : ModGL τ L)⁻¹) =
        (g : ModGL τ L) * x * (g : ModGL τ L)⁻¹ := by
    intro x hx
    rw [map_mul, map_mul, map_inv, hgF]
    calc (g : ModGL τ L) * qplusZ τ L * Units.map (entrywiseHom Fr) x *
          ((g : ModGL τ L) * qplusZ τ L)⁻¹ =
        (g : ModGL τ L) * (qplusZ τ L * Units.map (entrywiseHom Fr) x * (qplusZ τ L)⁻¹) *
          (g : ModGL τ L)⁻¹ := by group
      _ = (g : ModGL τ L) * x * (g : ModGL τ L)⁻¹ := by rw [hx]
  obtain ⟨ζ, hζ⟩ := qplus_exists_zeta L hp (by omega)
  let θL : Multiplicative (Fin τ.rank → ZMod p) →* ModGL τ L :=
    { toFun := fun v => qplusTheta τ ζ v.toAdd
      map_one' := qplusTheta_zero hζ
      map_mul' := fun v w => qplusTheta_add hζ v.toAdd w.toAdd }
  have hθL : ∀ v, θL (Multiplicative.ofAdd v) = qplusTheta τ ζ v := fun v => rfl
  have hθinj : Function.Injective θL := (injective_iff_map_eq_one θL).2 fun v hv =>
    toAdd_eq_zero.1 (qplusTheta_eq_one hζ hτ hp3 hv)
  let ιK : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hιK : Function.Injective ιK :=
    (baseChangeGL_injective (algebraMap K L)).comp (adjointGroup τ K).subtype_injective
  have hH : ∀ x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)), x ∈ ιK.range := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨⟨u, hu⟩, rfl⟩
  have hconj_mem : ∀ x ∈ adjointGroup τ L,
      (g : ModGL τ L) * x * (g : ModGL τ L)⁻¹ ∈ adjointGroup τ L := fun x hx =>
    mul_mem (mul_mem g.2 hx) (inv_mem g.2)
  have hΘ : ∀ v, ((MulAut.conj (g : ModGL τ L)).toMonoidHom.comp θL) v ∈ ιK.range := by
    intro v
    have h1 : (g : ModGL τ L) * qplusTheta τ ζ v.toAdd * (g : ModGL τ L)⁻¹ ∈ ιK.range :=
      hH _ (qplus_frobenius_fixed_mem hτ Fr hFr (hconj_mem _ (qplusTheta_mem ζ _))
        (hfix _ (qplusZ_conj_map_qplusTheta hτ Fr hFr2 hζ hpq _)))
    exact h1
  obtain ⟨θK, hθK⟩ := qplus_exists_hom_of_range ιK hιK
    ((MulAut.conj (g : ModGL τ L)).toMonoidHom.comp θL) hΘ
  have hFn : ∀ i, Units.map (entrywiseHom Fr) (weylElt τ L i 1) = weylElt τ L i 1 := fun i => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_weylElt_one]
  have hn : ∀ i, ∃ u : adjointGroup τ K,
      ιK u = (g : ModGL τ L) * weylElt τ L i 1 * (g : ModGL τ L)⁻¹ := fun i =>
    hH _ (qplus_frobenius_fixed_mem hτ Fr hFr (hconj_mem _ (weylElt_mem_adjointGroup i 1))
      (hfix _ (by rw [hFn i, qplusZ_comm hτ i, mul_inv_cancel_right])))
  choose n hn using hn
  refine ⟨θK, n, ?_, fun i => ?_, fun i v => ?_⟩
  · intro v w h
    have h1 : ιK (θK v) = ιK (θK w) := by rw [h]
    rw [hθK, hθK] at h1
    exact hθinj ((MulAut.conj (g : ModGL τ L)).injective h1)
  · have h1 : orderOf (ιK (n i)) = orderOf (n i) := orderOf_injective ιK hιK (n i)
    have h2 : orderOf ((g : ModGL τ L) * weylElt τ L i 1 * (g : ModGL τ L)⁻¹) =
        orderOf (weylElt τ L i 1) :=
      orderOf_injective (MulAut.conj (g : ModGL τ L)).toMonoidHom
        (MulAut.conj (g : ModGL τ L)).injective (weylElt τ L i 1)
    rw [← h1, hn i, h2]
    exact qplus_orderOf_weylElt i
  · apply hιK
    have hrel : weylElt τ L i 1 * θL (.ofAdd v) * (weylElt τ L i 1)⁻¹ =
        θL (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) := by
      rw [hθL, hθL]
      exact weylElt_conj_qplusTheta hζ i v
    have e1 : ιK (θK (.ofAdd v)) = (g : ModGL τ L) * θL (.ofAdd v) * (g : ModGL τ L)⁻¹ :=
      hθK _
    have e2 : ιK (θK (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1))) =
        (g : ModGL τ L) * θL (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) *
          (g : ModGL τ L)⁻¹ := hθK _
    rw [map_mul, map_mul, map_inv, e1, e2, hn i, ← hrel]
    group

theorem even_E7_E8_qplus_rational_reflection_torus (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ f + 1) :
    ∃ (θ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K)
      (n : Fin τ.rank → adjointGroup τ K), Function.Injective θ ∧ (∀ i, orderOf (n i) = 2) ∧
      ∀ i v, n i * θ (.ofAdd v) * (n i)⁻¹ =
        θ (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) :=
  qplus_torus_data_of_isAlgClosure τ hτ hf K hK hp hp3 hpq (AlgebraicClosure K)

end CFSG.RankThree.PartOne.KE
