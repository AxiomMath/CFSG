module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Alternating.Transvections
import CFSG.RankThree.OrthogonalInvolutions.Witt
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.SevenFour
import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions.PartThree

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U] {Q : QuadraticForm K U}
variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V] {b : LinearMap.BilinForm L V}
  {φ : U → V}

omit [Module L V] in
theorem bilin_add_smul_add_smul [CharP L 2] [Module L V] {b : LinearMap.BilinForm L V}
    (hb : ∀ v, b v v = 0) (a x y : V) : b (x + b x a • a) (y + b y a • a) = b x y := by
  have hskew : b a y = b y a := by
    have h := hb (a + y)
    simp only [map_add, LinearMap.add_apply, hb a, hb y, zero_add, add_zero] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb a,
    hskew, mul_zero, add_zero]
  linear_combination (b x a * b y a) * h2

theorem bilin_reflect_eq [CharP L 2] (hb : ∀ v, b v v = 0)
    (hconj : ∀ w x, Q w = 1 → Q x = 1 → φ (reflect Q w x) = φ x + b (φ x) (φ w) • φ w)
    {w x y : U} (hw : Q w = 1) (hx : Q x = 1) (hy : Q y = 1) :
    b (φ (reflect Q w x)) (φ (reflect Q w y)) = b (φ x) (φ y) := by
  rw [hconj w x hw hx, hconj w y hw hy, bilin_add_smul_add_smul hb]

theorem bilin_apply_of_mem_closure [CharP L 2] (hb : ∀ v, b v v = 0)
    (hconj : ∀ w x, Q w = 1 → Q x = 1 → φ (reflect Q w x) = φ x + b (φ x) (φ w) • φ w)
    {g : U ≃ₗ[K] U} (hg : g ∈ Subgroup.closure (reflect Q '' {w | Q w = 1})) {x y : U}
    (hx : Q x = 1) (hy : Q y = 1) : b (φ (g x)) (φ (g y)) = b (φ x) (φ y) := by
  have hle : Subgroup.closure (reflect Q '' {w | Q w = 1}) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, -, rfl⟩
    exact reflect_mem_orthogonalGroup Q w
  induction hg using Subgroup.closure_induction generalizing x y with
  | mem g hg =>
    obtain ⟨w, hw, rfl⟩ := hg
    exact bilin_reflect_eq hb hconj hw hx hy
  | one => rfl
  | mul g h _ hh ihg ihh =>
    have hhx : Q (h x) = 1 := by rw [map_of_mem (hle hh), hx]
    have hhy : Q (h y) = 1 := by rw [map_of_mem (hle hh), hy]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ihg hhx hhy, ihh hx hy]
  | inv g hg ihg =>
    have hm := inv_mem (hle hg)
    have hgx : Q (g⁻¹ x) = 1 := by rw [map_of_mem hm, hx]
    have hgy : Q (g⁻¹ y) = 1 := by rw [map_of_mem hm, hy]
    have h := ihg hgx hgy
    have hx' : g (g⁻¹ x) = x := g.apply_symm_apply x
    have hy' : g (g⁻¹ y) = y := g.apply_symm_apply y
    rw [hx', hy'] at h
    exact h.symm

theorem bilin_eq_of_polar_eq [CharP K 2] [CharP L 2] [FiniteDimensional K U]
    (hQ : Q.polarBilin.Nondegenerate) (hb : ∀ v, b v v = 0)
    (hconj : ∀ w x, Q w = 1 → Q x = 1 → φ (reflect Q w x) = φ x + b (φ x) (φ w) • φ w)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (reflect Q '' {w | Q w = 1}))
    {x y x' y' : U} (hx : Q x = 1) (hy : Q y = 1) (hx' : Q x' = 1) (hy' : Q y' = 1)
    (hxy : x ≠ y) (hxy' : x' ≠ y') (h : polar Q x y = polar Q x' y') :
    b (φ x) (φ y) = b (φ x') (φ y') := by
  have hpol0 : ∀ z : U, polar Q z z = 0 := fun z => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hyx : polar Q y x = polar Q y' x' := by rw [polar_comm, h, polar_comm]
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ ![x, y] ![x', y'] (PartFour.linearIndependent_pair_of_map_eq_one hx hy hxy)
    (PartFour.linearIndependent_pair_of_map_eq_one hx' hy' hxy')
    (fun i => by fin_cases i <;> simp [hx, hy, hx', hy'])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [hpol0, h, hyx])
  have h0 : g x = x' := by simpa using hgu 0
  have h1 : g y = y' := by simpa using hgu 1
  rw [← h0, ← h1, bilin_apply_of_mem_closure hb hconj (hgen hg) hx hy]

theorem exists_pair_polar_eq [Finite K] [CharP K 2] [FiniteDimensional K U]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K U) (c : K) :
    ∃ x y : U, Q x = 1 ∧ Q y = 1 ∧ x ≠ y ∧ polar Q x y = c := by
  have hpartner : ∀ x : U, x ≠ 0 → ∃ y, polar Q x y ≠ 0 := by
    intro x hx
    by_contra! h
    exact hx (hQ.1 x fun y => by rw [polarBilin_apply_apply]; exact h y)
  obtain ⟨a, ha⟩ : ∃ a : U, a ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  obtain ⟨a', ha'⟩ := hpartner a ha
  obtain ⟨x, -, -, hx⟩ := PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ hV ha' 0 0 1
  have hx0 : x ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hx
    exact zero_ne_one hx
  obtain ⟨x', hx'⟩ := hpartner x hx0
  obtain ⟨y, hyx, hyx', hy⟩ :=
    PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ hV hx' c (polar Q x x' + 1) 1
  refine ⟨x, y, hx, hy, fun h => ?_, by rw [polar_comm]; exact hyx⟩
  rw [← h] at hyx'
  exact one_ne_zero (left_eq_add.mp hyx')

theorem exists_ringHom_bilin_eq [Finite K] [CharP K 2] [CharP L 2] [FiniteDimensional K U]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K U) (hb : ∀ v, b v v = 0)
    (hconj : ∀ w x, Q w = 1 → Q x = 1 → φ (reflect Q w x) = φ x + b (φ x) (φ w) • φ w)
    (hcomm : ∀ x y, Q x = 1 → Q y = 1 → (b (φ x) (φ y) = 0 ↔ polar Q x y = 0))
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (reflect Q '' {w | Q w = 1})) :
    ∃ σ : K →+* L, ∀ x y, Q x = 1 → Q y = 1 → b (φ x) (φ y) = σ (polar Q x y) := by
  have hpol0 : ∀ z : U, polar Q z z = 0 := fun z => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  choose px py hpx hpy hpne hpc using exists_pair_polar_eq hQ hV
  let ψ : K → L := fun c => b (φ (px c)) (φ (py c))
  have h0 : ψ 0 = 0 := (hcomm _ _ (hpx 0) (hpy 0)).mpr (hpc 0)
  have key : ∀ x y, Q x = 1 → Q y = 1 → b (φ x) (φ y) = ψ (polar Q x y) := by
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy
      rw [hb, hpol0, h0]
    · exact bilin_eq_of_polar_eq hQ hb hconj hgen hx hy (hpx _) (hpy _) hxy (hpne _) (hpc _).symm
  have hfe : ∀ a c β : K, β ≠ 0 → ψ (a + β * c) = ψ a + ψ β * ψ c := by
    intro a c β hβ
    obtain ⟨x, y, hx, hy, -, hxy⟩ := exists_pair_polar_eq hQ hV β
    obtain ⟨z, hza, hzc, hz⟩ :=
      PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ hV (hxy ▸ hβ) a c 1
    have hxz : polar Q x z = a := by rw [polar_comm]; exact hza
    have hyz : polar Q y z = c := by rw [polar_comm]; exact hzc
    have hrefl : reflect Q y x = x + β • y := by
      rw [reflect_apply (show Q y ≠ 0 by rw [hy]; exact one_ne_zero), hy, div_one,
        polar_comm Q y x, hxy, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
    have hx1 : Q (reflect Q y x) = 1 := by
      rw [map_of_mem (reflect_mem_orthogonalGroup Q y), hx]
    have hpz : polar Q (reflect Q y x) z = a + β * c := by
      rw [hrefl, polar_add_left, polar_smul_left, hxz, hyz, smul_eq_mul]
    calc ψ (a + β * c) = b (φ (reflect Q y x)) (φ z) := by rw [key _ _ hx1 hz, hpz]
      _ = b (φ x) (φ z) + b (φ x) (φ y) * b (φ y) (φ z) := by
        rw [hconj y x hy hx]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      _ = ψ a + ψ β * ψ c := by
        rw [key _ _ hx hz, key _ _ hx hy, key _ _ hy hz, hxz, hxy, hyz]
  have hne1 : ψ 1 ≠ 0 := fun h =>
    one_ne_zero ((hpc 1).symm.trans ((hcomm _ _ (hpx 1) (hpy 1)).mp h))
  have h1 : ψ 1 = 1 := by
    have h := hfe 0 1 1 one_ne_zero
    rw [zero_add, mul_one, h0, zero_add] at h
    exact mul_left_cancel₀ hne1 (h.symm.trans (mul_one _).symm)
  have hadd : ∀ a c : K, ψ (a + c) = ψ a + ψ c := by
    intro a c
    have h := hfe a c 1 one_ne_zero
    rwa [one_mul, h1, one_mul] at h
  have hmul : ∀ β c : K, ψ (β * c) = ψ β * ψ c := by
    intro β c
    by_cases hβ : β = 0
    · rw [hβ, zero_mul, h0, zero_mul]
    · have h := hfe 0 c β hβ
      rwa [zero_add, h0, zero_add] at h
  exact ⟨⟨⟨⟨ψ, h1⟩, hmul⟩, h0, hadd⟩, key⟩

theorem span_setOf_map_eq_one [Finite K] [CharP K 2] [FiniteDimensional K U]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K U) :
    Submodule.span K {x : U | Q x = 1} = ⊤ := by
  rw [eq_top_iff]
  intro u _
  by_cases hu : u = 0
  · rw [hu]
    exact Submodule.zero_mem _
  obtain ⟨u', hu'⟩ : ∃ u', polar Q u u' ≠ 0 := by
    by_contra! h
    exact hu (hQ.1 u fun y => by rw [polarBilin_apply_apply]; exact h y)
  obtain ⟨x, hxu, -, hx⟩ := PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ hV hu' (Q u) 0 1
  have hxu1 : Q (x + u) = 1 := by
    rw [QuadraticMap.map_add Q x u, hx, hxu, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h := (Submodule.span K {x : U | Q x = 1}).sub_mem (Submodule.subset_span hxu1)
    (Submodule.subset_span hx)
  rwa [add_sub_cancel_left] at h

omit [Module L V] in
theorem bilin_comm_of_alt [CharP L 2] [Module L V] {b : LinearMap.BilinForm L V}
    (hb : ∀ v, b v v = 0) (v w : V) : b v w = b w v := by
  have h := hb (v + w)
  simp only [map_add, LinearMap.add_apply, hb v, hb w, zero_add, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

theorem exists_semilinear_of_bilin_eq [Finite K] [CharP K 2] [CharP L 2] [FiniteDimensional K U]
    [FiniteDimensional L V] (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K U)
    (hb : ∀ v, b v v = 0) (hbnd : ∀ v, (∀ w, b v w = 0) → v = 0)
    (hcard : Nat.card K = Nat.card L) (hdim : finrank L V = finrank K U) (σ : K →+* L)
    (hσ : ∀ x y, Q x = 1 → Q y = 1 → b (φ x) (φ y) = σ (polar Q x y)) :
    ∃ Φ : U → V, Function.Bijective Φ ∧ (∀ u u', Φ (u + u') = Φ u + Φ u') ∧
      (∀ (a : K) u, Φ (a • u) = σ a • Φ u) ∧ (∀ u u', b (Φ u) (Φ u') = σ (polar Q u u')) ∧
      ∀ x, Q x = 1 → Φ x = φ x := by
  classical
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent K {x : U | Q x = 1}
  let bas : Basis B K U := Basis.mk hBli (by
    rw [Subtype.range_coe, hBspan, span_setOf_map_eq_one hQ hV])
  have hbas : ∀ i, Q (bas i) = 1 := fun i => by
    rw [Basis.mk_apply]
    exact hBsub i.2
  have : Finite U := Module.finite_of_finite K
  have : Fintype B := Fintype.ofFinite B
  let Φ : U → V := fun u => ∑ i, σ (bas.repr u i) • φ (bas i)
  have hsum : ∀ u, Φ u = ∑ i, σ (bas.repr u i) • φ (bas i) := fun u => rfl
  have hadd : ∀ u u', Φ (u + u') = Φ u + Φ u' := by
    intro u u'
    simp only [hsum, map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (a : K) u, Φ (a • u) = σ a • Φ u := by
    intro a u
    simp only [hsum, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul,
      Finset.smul_sum]
  have hpair : ∀ u x, Q x = 1 → b (Φ u) (φ x) = σ (polar Q u x) := by
    intro u x hx
    have hu : polar Q u x = ∑ i, bas.repr u i * polar Q (bas i) x := by
      conv_lhs => rw [← bas.sum_repr u]
      rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, polarBilin_apply_apply]
    rw [hu]
    show b (∑ i, σ (bas.repr u i) • φ (bas i)) (φ x) = _
    rw [map_sum b, LinearMap.sum_apply, map_sum σ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hσ _ _ (hbas i) hx, map_mul]
  have hiso : ∀ u u', b (Φ u) (Φ u') = σ (polar Q u u') := by
    intro u u'
    have hu : polar Q u u' = ∑ j, bas.repr u' j * polar Q u (bas j) := by
      conv_lhs => rw [← bas.sum_repr u']
      rw [← polarBilin_apply_apply, map_sum]
      simp only [map_smul, smul_eq_mul, polarBilin_apply_apply]
    rw [hu]
    show b (Φ u) (∑ j, σ (bas.repr u' j) • φ (bas j)) = _
    rw [map_sum (b (Φ u)), map_sum σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hpair u _ (hbas j), map_mul]
  have hinj : Function.Injective Φ := by
    intro u u' h
    have hΦ0 : Φ (u - u') = 0 := by
      have h1 := hadd (u - u') u'
      rw [sub_add_cancel, h] at h1
      exact add_eq_right.mp h1.symm
    have h0 : ∀ w, polar Q (u - u') w = 0 := by
      intro w
      apply σ.injective
      rw [map_zero, ← hiso, hΦ0, map_zero, LinearMap.zero_apply]
    exact sub_eq_zero.mp (hQ.1 _ fun w => by rw [polarBilin_apply_apply]; exact h0 w)
  have : Finite L := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have : Finite V := Module.finite_of_finite L
  have hcardUV : Nat.card U = Nat.card V := by
    have : Fintype K := Fintype.ofFinite K
    have : Fintype L := Fintype.ofFinite L
    have : Fintype U := Fintype.ofFinite U
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := K) (V := U), Module.card_eq_pow_finrank (K := L) (V := V),
      hdim, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcardUV.ge
  refine ⟨Φ, hbij, hadd, hsmul, hiso, fun x hx => ?_⟩
  have h0 : ∀ v, b (Φ x - φ x) v = 0 := by
    intro v
    obtain ⟨u, rfl⟩ := hbij.2 v
    rw [map_sub, LinearMap.sub_apply, hiso, bilin_comm_of_alt hb (φ x), hpair u x hx, polar_comm,
      sub_self]
  exact sub_eq_zero.mp (hbnd _ h0)

theorem exists_quadraticForm_of_semilinear (σ : K →+* L) (hσ : Function.Bijective σ) {Φ : U → V}
    (hΦ : Function.Bijective Φ) (hadd : ∀ u u', Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (a : K) u, Φ (a • u) = σ a • Φ u)
    (hiso : ∀ u u', b (Φ u) (Φ u') = σ (polar Q u u')) :
    ∃ Q' : QuadraticForm L V, (∀ v w, polar Q' v w = b v w) ∧ ∀ u, Q' (Φ u) = σ (Q u) := by
  let e := Equiv.ofBijective Φ hΦ
  let τ := RingEquiv.ofBijective σ hσ
  have he : ∀ u, e u = Φ u := fun u => rfl
  have hτ : ∀ a, τ a = σ a := fun a => rfl
  have hesmul : ∀ (a : L) v, e.symm (a • v) = τ.symm a • e.symm v := by
    intro a v
    apply e.injective
    rw [Equiv.apply_symm_apply, he, hsmul, ← hτ, RingEquiv.apply_symm_apply, ← he,
      Equiv.apply_symm_apply]
  have headd : ∀ v w, e.symm (v + w) = e.symm v + e.symm w := by
    intro v w
    apply e.injective
    rw [Equiv.apply_symm_apply, he, hadd, ← he, ← he, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  let Q' : QuadraticForm L V :=
    { toFun := fun v => σ (Q (e.symm v))
      toFun_smul := fun a v => by
        rw [hesmul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul, map_mul, ← hτ,
          RingEquiv.apply_symm_apply]
      exists_companion' := ⟨b, fun v w => by
        rw [headd, QuadraticMap.map_add Q, map_add, map_add, ← hiso, ← he, ← he,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩ }
  have hQ' : ∀ v, Q' v = σ (Q (e.symm v)) := fun v => rfl
  refine ⟨Q', fun v w => ?_, fun u => ?_⟩
  · rw [QuadraticMap.polar, hQ', hQ', hQ', headd, QuadraticMap.map_add Q, map_add, map_add,
      ← hiso, ← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ring
  · rw [hQ', ← he, Equiv.symm_apply_apply]

theorem mem_closure_symplecticTransvection_of_semilinear [CharP K 2] [CharP L 2]
    (hb : b.IsAlt) (σ : K →+* L) (hσ : Function.Bijective σ) {Φ : U → V}
    (hΦ : Function.Bijective Φ) (hadd : ∀ u u', Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (a : K) u, Φ (a • u) = σ a • Φ u)
    (hiso : ∀ u u', b (Φ u) (Φ u') = σ (polar Q u u')) {Q' : QuadraticForm L V}
    (hQ' : ∀ u, Q' (Φ u) = σ (Q u))
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (reflect Q '' {w | Q w = 1}))
    {g : LinearMap.GeneralLinearGroup L V} (hg : ∀ v, Q' ((g : V →ₗ[L] V) v) = Q' v) :
    g ∈ Subgroup.closure {t | ∃ a, Q' a = 1 ∧
      t = CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb a 1} := by
  set e := Equiv.ofBijective Φ hΦ with hedef
  set τ := RingEquiv.ofBijective σ hσ with hτdef
  have he : ∀ u, e u = Φ u := fun u => rfl
  have hτ : ∀ a, τ a = σ a := fun a => rfl
  have hΦe : ∀ v, Φ (e.symm v) = v := fun v => by rw [← he, Equiv.apply_symm_apply]
  have heΦ : ∀ u, e.symm (Φ u) = u := fun u => by rw [← he, Equiv.symm_apply_apply]
  have hesmul : ∀ (a : L) v, e.symm (a • v) = τ.symm a • e.symm v := by
    intro a v
    apply e.injective
    rw [Equiv.apply_symm_apply, he, hsmul, ← hτ, RingEquiv.apply_symm_apply, hΦe]
  have headd : ∀ v w, e.symm (v + w) = e.symm v + e.symm w := by
    intro v w
    apply e.injective
    rw [Equiv.apply_symm_apply, he, hadd, hΦe, hΦe]
  set S := {t : LinearMap.GeneralLinearGroup L V | ∃ a, Q' a = 1 ∧
    t = CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb a 1} with hSdef
  have key : ∀ h ∈ Subgroup.closure (reflect Q '' {w | Q w = 1}),
      ∃ t ∈ Subgroup.closure S, ∀ v, (t : V →ₗ[L] V) v = Φ (h (e.symm v)) := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem h hh =>
      obtain ⟨w, hw, rfl⟩ := hh
      have hw' : Q' (Φ w) = 1 := by rw [hQ', hw, map_one]
      refine ⟨CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb (Φ w) 1,
        Subgroup.subset_closure ⟨Φ w, hw', rfl⟩, fun v => ?_⟩
      have hrefl : reflect Q w (e.symm v) = e.symm v + polar Q w (e.symm v) • w := by
        rw [reflect_apply (show Q w ≠ 0 by rw [hw]; exact one_ne_zero), hw, div_one,
          sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
      calc (CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb (Φ w) 1 :
            V →ₗ[L] V) v = v + b v (Φ w) • Φ w := by
              rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
        _ = Φ (e.symm v) + σ (polar Q w (e.symm v)) • Φ w := by
              rw [← hiso, hΦe, bilin_comm_of_alt hb]
        _ = Φ (reflect Q w (e.symm v)) := by rw [hrefl, hadd, hsmul]
    | one =>
      refine ⟨1, Subgroup.one_mem _, fun v => ?_⟩
      rw [Units.val_one, Module.End.one_apply]
      exact (hΦe v).symm
    | mul h₁ h₂ _ _ ih₁ ih₂ =>
      obtain ⟨t₁, ht₁, h1⟩ := ih₁
      obtain ⟨t₂, ht₂, h2⟩ := ih₂
      refine ⟨t₁ * t₂, Subgroup.mul_mem _ ht₁ ht₂, fun v => ?_⟩
      rw [Units.val_mul, Module.End.mul_apply, h2, h1, heΦ, LinearEquiv.mul_apply]
    | inv h _ ih =>
      obtain ⟨t, ht, h1⟩ := ih
      refine ⟨t⁻¹, Subgroup.inv_mem _ ht, fun v => ?_⟩
      have h2 : (t : V →ₗ[L] V) (Φ (h⁻¹ (e.symm v))) = v := by
        rw [h1, heΦ]
        show Φ (h (h.symm (e.symm v))) = v
        rw [LinearEquiv.apply_symm_apply, hΦe]
      have h3 := congrArg (((t⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V)) h2
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply] at h3
      exact h3.symm
  have hgi : ∀ v,
      (g : V →ₗ[L] V) (((g⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V) v) = v :=
    fun v => by
      have := congrArg (fun f : V →ₗ[L] V => f v) (Units.mul_inv g)
      simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hig : ∀ v, ((g⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V) ((g : V →ₗ[L] V) v) = v :=
    fun v => by
      have := congrArg (fun f : V →ₗ[L] V => f v) (Units.inv_mul g)
      simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  let G' : U ≃ₗ[K] U :=
    { toFun := fun u => e.symm ((g : V →ₗ[L] V) (Φ u))
      invFun := fun u =>
        e.symm (((g⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V) (Φ u))
      map_add' := fun u u' => by
        show e.symm ((g : V →ₗ[L] V) (Φ (u + u'))) =
          e.symm ((g : V →ₗ[L] V) (Φ u)) + e.symm ((g : V →ₗ[L] V) (Φ u'))
        rw [hadd, map_add, headd]
      map_smul' := fun a u => by
        show e.symm ((g : V →ₗ[L] V) (Φ (a • u))) = a • e.symm ((g : V →ₗ[L] V) (Φ u))
        rw [hsmul, map_smul, hesmul, ← hτ, RingEquiv.symm_apply_apply]
      left_inv := fun u => by
        show e.symm (((g⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V)
          (Φ (e.symm ((g : V →ₗ[L] V) (Φ u))))) = u
        rw [hΦe, hig, heΦ]
      right_inv := fun u => by
        show e.symm ((g : V →ₗ[L] V)
          (Φ (e.symm (((g⁻¹ : LinearMap.GeneralLinearGroup L V) : V →ₗ[L] V) (Φ u))))) = u
        rw [hΦe, hgi, heΦ] }
  have hG' : G' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro u
    apply σ.injective
    show σ (Q (e.symm ((g : V →ₗ[L] V) (Φ u)))) = σ (Q u)
    rw [← hQ', hΦe, hg, hQ']
  obtain ⟨t, ht, htv⟩ := key G' (hgen hG')
  have htg : t = g := Units.ext (LinearMap.ext fun v => by
    rw [htv]
    show Φ (e.symm ((g : V →ₗ[L] V) (Φ (e.symm v)))) = (g : V →ₗ[L] V) v
    rw [hΦe, hΦe])
  rw [← htg]
  exact ht

theorem exists_quadraticForm_of_marked [Finite K] [CharP K 2] [CharP L 2] [FiniteDimensional K U]
    [FiniteDimensional L V] (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K U)
    (hb : ∀ v, b v v = 0) (hbnd : ∀ v, (∀ w, b v w = 0) → v = 0)
    (hcard : Nat.card K = Nat.card L) (hdim : finrank L V = finrank K U)
    (hconj : ∀ w x, Q w = 1 → Q x = 1 → φ (reflect Q w x) = φ x + b (φ x) (φ w) • φ w)
    (hcomm : ∀ x y, Q x = 1 → Q y = 1 → (b (φ x) (φ y) = 0 ↔ polar Q x y = 0))
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (reflect Q '' {w | Q w = 1})) :
    ∃ Q' : QuadraticForm L V, (∀ v w, polar Q' v w = b v w) ∧
      (∀ v, Q' v = 1 ↔ ∃ x, Q x = 1 ∧ φ x = v) ∧
      ∀ g : LinearMap.GeneralLinearGroup L V, (∀ v, Q' ((g : V →ₗ[L] V) v) = Q' v) →
        g ∈ Subgroup.closure {t | ∃ a, Q' a = 1 ∧
          t = CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb a 1} := by
  obtain ⟨σ, hσ⟩ := exists_ringHom_bilin_eq hQ hV hb hconj hcomm hgen
  obtain ⟨Φ, hΦ, hadd, hsmul, hiso, hΦφ⟩ :=
    exists_semilinear_of_bilin_eq hQ hV hb hbnd hcard hdim σ hσ
  have : Finite L := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hσb : Function.Bijective σ := σ.injective.bijective_of_nat_card_le hcard.ge
  obtain ⟨Q', hpol, hQ'⟩ := exists_quadraticForm_of_semilinear σ hσb hΦ hadd hsmul hiso
  refine ⟨Q', hpol, fun v => ⟨fun hv => ?_, ?_⟩, fun g hg =>
    mem_closure_symplecticTransvection_of_semilinear hb σ hσb hΦ hadd hsmul hiso hQ' hgen hg⟩
  · obtain ⟨u, rfl⟩ := hΦ.2 v
    have hu : Q u = 1 := σ.injective (by rw [← hQ', hv, map_one])
    exact ⟨u, hu, (hΦφ u hu).symm⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hΦφ x hx, hQ', hx, map_one]

end CFSG.OddTranspositions.PartThree
