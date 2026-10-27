module

public import CFSG.RankThree.GF2n.Smith81.S81YGenQ
public import CFSG.RankThree.GF2n.Smith81.S81YGenOdd
public import CFSG.RankThree.GF2n.Smith81.S81YGenPt
public import CFSG.RankThree.GF2n.Smith81.Sec212Lanes

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def HasGDat (M Q Z B : Subgroup G) (z : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
    (ψ : M₀.E ≃ₗ[K] V) (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)) (Γ : Subgroup (V ≃ₗ[K] V))
    (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V)) (IsRt : (V ≃ₗ[K] V) → Prop),
    GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z

structure GoodCase (P : Subgroup G → Subgroup G → Subgroup G → Subgroup G → Prop) : Prop where
  conj : ∀ M Q Z B, P M Q Z B → ∀ h : G,
    P (conjSubgroup h M) (conjSubgroup h Q) (conjSubgroup h Z) (conjSubgroup h B)
  dat : ∀ M Q Z B, P M Q Z B → ∀ z ∈ Z, z ≠ 1 → HasGDat M Q Z B z
  point : ∀ M Q Z B, P M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

section Main

variable [Finite G]


variable {P : Subgroup G → Subgroup G → Subgroup G → Subgroup G → Prop}

theorem lin213_left_Q_gen (hP : GoodCase P) {M Q Z B : Subgroup G} (hPM : P M Q Z B) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) {x y : G} (hxc : IsConj z x) (hyc : IsConj z y) (hxQ : x ∈ Q)
    (hyM : y ∈ M) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  obtain ⟨K, _, _, _, γ, M₀, V, _, _, ψ, φ, Γ, p₀, U₀, IsRt, Dt⟩ := hP.dat M Q Z B hPM z hz hz1
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  by_cases hyQ : y ∈ Q
  · rcases sq_eq_one_or_inZClass_of_mem_Q H (Q.mul_mem hxQ hyQ) with h | h
    · exact lin213_concl_of H (Or.inl h)
    · exact lin213_concl_of H (Or.inr (Or.inl h))
  · exact concl_Q_left_gen Dt hxc hxQ hyc hyM hyQ

theorem lin213_main_gen (hP : GoodCase P) {M Q Z B : Subgroup G} (hPM : P M Q Z B) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) {x y : G} (hxc : IsConj z x) (hxM : x ∈ M) (hyc : IsConj z y)
    (hyM : y ∈ M) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  obtain ⟨K, _, _, _, γ, M₀, V, _, _, ψ, φ, Γ, p₀, U₀, IsRt, Dt⟩ := hP.dat M Q Z B hPM z hz hz1
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  by_cases hxQ : x ∈ Q
  · exact lin213_left_Q_gen hP hPM hz hz1 hxc hyc hxQ hyM
  by_cases hyQ : y ∈ Q
  · refine lin213_concl_conj x⁻¹ ?_
    have e : x⁻¹ * (x * y) * x⁻¹⁻¹ = y * x := by group
    rw [e]
    exact lin213_left_Q_gen hP hPM hz hz1 hyc hxc hyQ hxM
  obtain ⟨r, hxr, hr⟩ := Dt.acts_root hxc hxM hxQ
  obtain ⟨s, hys, hs⟩ := Dt.acts_root hyc hyM hyQ
  by_cases hA : Odd (orderOf (r * s)) ∧ r * s ≠ 1
  · exact lin213_concl_of H (Or.inr (Or.inr
      (odd_orderOf_mul_gen Dt hxc hxM hxQ hyc hyM hyQ hr hs hxr hys hA.1 hA.2)))
  have hAx : ∀ X : Subgroup G, Sit M Q Z X x →
      ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ A ≤ QB X := fun X hs' => by
    obtain ⟨A, hA1, hA2, hA3, hA4, -, -⟩ := smith29_of_exists hs' (hP.point M Q Z B hPM X x hs')
    exact ⟨A, hA1, hA2, hA3, hA4⟩
  obtain ⟨D, hDZ, hxD, hyD⟩ := exists_point_centralized_gen Dt hxc hxM hxQ hyc hyM hyQ hr hs hxr
    hys hA hAx
  obtain ⟨h, hDh, hQD, hND⟩ := hDZ.QB_eq H
  subst hDh
  have hPM' := hP.conj M Q Z B hPM h
  have hz' : h * z * h⁻¹ ∈ conjSubgroup h Z := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hz
  have hz1' : h * z * h⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [this, h1]
    group
  have hzz' : IsConj z (h * z * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
  have hxc' : IsConj (h * z * h⁻¹) x := hzz'.symm.trans hxc
  have hyc' : IsConj (h * z * h⁻¹) y := hzz'.symm.trans hyc
  have hxQ' : x ∈ conjSubgroup h Q := by rw [← hQD]; exact hxD
  have hyM' : y ∈ conjSubgroup h M := by
    rw [← hND]
    exact IsZConjugate.mem_normalizer_of_commute H hDZ hz1' hz'
      (show Commute y (h * z * h⁻¹) from
        (show Commute (h * z * h⁻¹) y from Subgroup.mem_centralizer_iff.mp hyD _ hz').symm)
  obtain ⟨K', _, _, _, γ', M₀', V', _, _, ψ', φ', Γ', p₀', U₀', IsRt', Dt'⟩ :=
    hP.dat _ _ _ _ hPM' (h * z * h⁻¹) hz' hz1'
  have H' : StrothHyp (conjSubgroup h M) (conjSubgroup h Q) (conjSubgroup h Z) := Dt'.ctx.hyp
  obtain ⟨hc1, hc2⟩ := lin213_left_Q_gen hP hPM' hz' hz1' hxc' hyc' hxQ' hyM'
  refine ⟨hc1, fun h4 => ?_⟩
  exact E3LRoot.inZClass_of_isConj hz hz1
    (hzz'.trans (E3LRoot.isConj_of_inZClass H' hz' hz1' (hc2 h4)))

theorem smith213_of_good (hP : GoodCase P) {M Q Z B : Subgroup G} (hPM : P M Q Z B) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)) := by
  obtain ⟨K, _, _, _, γ, M₀, V, _, _, ψ, φ, Γ, p₀, U₀, IsRt, Dt⟩ := hP.dat M Q Z B hPM z hz hz1
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  refine isRootInvolutionSet_of_lin213Prop H hz hz1 ?_
  intro x y hxM hyM hxZ hyZ
  exact lin213_main_gen hP hPM hz hz1 (E3LRoot.isConj_of_inZClass H hz hz1 hxZ) hxM
    (E3LRoot.isConj_of_inZClass H hz hz1 hyZ) hyM

end Main

end CFSG.RankThree.GF2n.Smith81.RootGen
