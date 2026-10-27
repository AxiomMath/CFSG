module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.AUTSL
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgOM_neg_mem_roots {U : Type*} [Group U] (D : UniversalRootDatum U)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : -γ ∈ D.roots :=
  (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem γ hγ

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def irgOM_modelIso :
    spinGroup (quadMinus n K b c) ⧸ Subgroup.center (spinGroup (quadMinus n K b c)) ≃*
      matrixDerived (Qm n hn4 b c) :=
  (QuotientGroup.quotientMulEquivOfEq (AutOm.ker_spinModelMinus hn4 hirr).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (AutOm.spinModelMinus_surjective hn4 hirr))

theorem irgOM_modelIso_mk (x : spinGroup (quadMinus n K b c)) :
    irgOM_modelIso hn4 hirr
        (QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c))) x) =
      AutOm.spinModelMinus hn4 hirr x := by
  change irgOM_modelIso hn4 hirr (QuotientGroup.mk x) = AutOm.spinModelMinus hn4 hirr x
  rw [irgOM_modelIso, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  have e : (QuotientGroup.quotientKerEquivOfSurjective (AutOm.spinModelMinus hn4 hirr)
        (AutOm.spinModelMinus_surjective hn4 hirr)).symm
        (AutOm.spinModelMinus hn4 hirr x) =
      (QuotientGroup.mk x : spinGroup (quadMinus n K b c) ⧸
        (AutOm.spinModelMinus hn4 hirr).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [← e, MulEquiv.apply_symm_apply]

end Model

section Preserve

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ} (hn4 : 4 ≤ n) {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hcard : Nat.card K = 2 ^ f)

include hirr hcard in
theorem irgOM_model_preserve (β : MulAut (matrixDerived (Qm n hn4 b c))) :
    ∃ g : matrixDerived (Qm n hn4 b c),
      (∀ γ ∈ (minusDatum n hirr).roots, ∀ z ∈ (minusDatum n hirr).rootGroup γ,
        ∃ z' ∈ (minusDatum n hirr).rootGroup γ,
          g⁻¹ * β (AutOm.spinModelMinus hn4 hirr z) * g = AutOm.spinModelMinus hn4 hirr z') ∧
      (∀ γ ∈ (minusDatum n hirr).roots, ∀ z' ∈ (minusDatum n hirr).rootGroup γ,
        ∃ z ∈ (minusDatum n hirr).rootGroup γ,
          g⁻¹ * β (AutOm.spinModelMinus hn4 hirr z) * g = AutOm.spinModelMinus hn4 hirr z') := by
  obtain ⟨_, ⟨h, rfl⟩, k, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hcard β
  haveI : Fintype K := Fintype.ofFinite K
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hcard
    have h2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  refine ⟨h, ?_, ?_⟩
  · intro γ hγ z hz
    obtain ⟨z', hz', e⟩ := OrdPGraphOmega.frobAut_pow_mem_rootGroup hn4 hirr hγ k hz
    exact ⟨z', hz', by rw [MulAut.mul_apply, MulAut.conj_apply, e]; group⟩
  · intro γ hγ z' hz'
    obtain ⟨z, hz, e⟩ :=
      OrdPGraphOmega.frobAut_pow_mem_rootGroup hn4 hirr hγ (2 * f * k - k) hz'
    refine ⟨z, hz, ?_⟩
    have hk_le : k ≤ 2 * f * k := by
      calc k = 1 * k := (one_mul k).symm
        _ ≤ 2 * f * k := Nat.mul_le_mul_right k (by omega)
    have hexp : k + (2 * f * k - k) = 2 * f * k := by omega
    have hpow : (AutOm.frobAut hn4 hirr ^ k) (AutOm.spinModelMinus hn4 hirr z) =
        AutOm.spinModelMinus hn4 hirr z' := by
      have h1 : (AutOm.frobAut hn4 hirr ^ k)
          ((AutOm.frobAut hn4 hirr ^ (2 * f * k - k))
            (AutOm.spinModelMinus hn4 hirr z')) = AutOm.spinModelMinus hn4 hirr z' := by
        rw [← MulAut.mul_apply, ← pow_add, hexp, pow_mul,
          AutOm.frobAut_pow_two_mul hn4 hirr hcard, one_pow]
        rfl
      rw [← e]
      exact h1
    rw [MulAut.mul_apply, MulAut.conj_apply, hpow]
    group

end Preserve

private theorem irgOM_subgroup_map_eq {G L M : Type*} [Group G] [Group L] [Group M]
    (H : Subgroup G) (f : L →* M) (g : G →* L) (h : G →* M)
    (hF : ∀ x ∈ H, ∃ y ∈ H, f (g x) = h y)
    (hB : ∀ y ∈ H, ∃ x ∈ H, f (g x) = h y) :
    (H.map g).map f = H.map h := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', e⟩ := hF x' hx'
    exact ⟨y', hy', e.symm⟩
  · rintro y ⟨y', hy', rfl⟩
    obtain ⟨x, hx, e⟩ := hB y' hy'
    exact ⟨g x, ⟨x, hx, rfl⟩, e⟩

private theorem irgOM_theta_conj {G A C : Type*} [Group G] [Group A] [Group C]
    (θ : MulAut A) (Φ : A ≃* C) (π : G →* C) (mk : G →* A) (βa : MulAut C)
    (hΦmk : ∀ x, Φ (mk x) = π x) (hβa : ∀ y, Φ (θ y) = βa (Φ y))
    {g h : C} {u' ufin : G} (hh : h = g⁻¹ * βa (π u') * g) (hu : π ufin = g * h)
    {z z' : G} (hEq : g⁻¹ * βa (π z) * g = π z') :
    θ (mk (u' * z * u'⁻¹)) = mk (ufin * z' * ufin⁻¹) := by
  have hθ : θ (mk (u' * z * u'⁻¹)) = Φ.symm (βa (π (u' * z * u'⁻¹))) := by
    rw [← hΦmk (u' * z * u'⁻¹), ← hβa (mk (u' * z * u'⁻¹))]
    simp
  rw [hθ]
  refine Φ.injective ?_
  rw [MulEquiv.apply_symm_apply, hΦmk (ufin * z' * ufin⁻¹)]
  have hβu : βa (π u') = g * h * g⁻¹ := by rw [hh]; group
  have hβz : βa (π z) = g * π z' * g⁻¹ := by rw [← hEq]; group
  have hπu : π (u' * z * u'⁻¹) = π u' * π z * π u'⁻¹ := by rw [map_mul, map_mul, map_inv]
  have hπfin : π (ufin * z' * ufin⁻¹) = π ufin * π z' * π ufin⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hπu, hπfin]
  simp only [map_mul, map_inv]
  rw [hu, hβu, hβz]
  group

section Main

theorem irgOM_pairAut_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (θ : MulAut (spinGroup (quadMinus n K b c) ⧸
      Subgroup.center (spinGroup (quadMinus n K b c))))
    {β' : Fin (minusDatum n hirr).rank → ℤ} (hβ' : β' ∈ (minusDatum n hirr).roots)
    (hlong : GGLongRoot (minusDatum n hirr) β') (u' : spinGroup (quadMinus n K b c)) :
    ∃ u : spinGroup (quadMinus n K b c),
      (ggRootSub (minusDatum n hirr)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c)))) β' u').map
          θ.toMonoidHom =
        ggRootSub (minusDatum n hirr)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c)))) β' u ∧
      (ggRootSub (minusDatum n hirr)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c)))) (-β') u').map
          θ.toMonoidHom =
        ggRootSub (minusDatum n hirr)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c)))) (-β') u := by
  set mk : spinGroup (quadMinus n K b c) →*
      (spinGroup (quadMinus n K b c) ⧸ Subgroup.center (spinGroup (quadMinus n K b c))) :=
    QuotientGroup.mk' (Subgroup.center (spinGroup (quadMinus n K b c))) with hmkdef
  set Φ := irgOM_modelIso hn4 hirr with hΦdef
  set π := AutOm.spinModelMinus hn4 hirr with hπdef
  have hΦmk : ∀ x : spinGroup (quadMinus n K b c), Φ (mk x) = π x := by
    intro x
    rw [hmkdef]
    exact irgOM_modelIso_mk hn4 hirr x
  set βa : MulAut (matrixDerived (Qm n hn4 b c)) := Φ.symm.trans (θ.trans Φ) with hβadef
  have hβa : ∀ y, Φ (θ y) = βa (Φ y) := fun y => by
    simp [hβadef, MulEquiv.trans_apply]
  obtain ⟨g, hfwd, hbwd⟩ := irgOM_model_preserve hn4 hirr hcard βa
  obtain ⟨g', hg'⟩ := AutOm.spinModelMinus_surjective hn4 hirr g
  set h : matrixDerived (Qm n hn4 b c) := g⁻¹ * βa (π u') * g with hhdef
  obtain ⟨u, hu⟩ := AutOm.spinModelMinus_surjective hn4 hirr h
  set ufin : spinGroup (quadMinus n K b c) := g' * u with hufindef
  have hπufin : π ufin = g * h := by
    rw [hufindef, map_mul, hg', hu]
  have key : ∀ (z z' : spinGroup (quadMinus n K b c)),
      g⁻¹ * βa (π z) * g = π z' →
      θ (mk ((MulAut.conj u') z)) = mk ((MulAut.conj ufin) z') := by
    intro z z' hEq
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact irgOM_theta_conj θ Φ π mk βa hΦmk hβa hhdef hπufin hEq
  refine ⟨ufin, ?_, ?_⟩
  · have hF : ∀ x ∈ (minusDatum n hirr).rootGroup β',
        ∃ y ∈ (minusDatum n hirr).rootGroup β',
          θ (mk ((MulAut.conj u') x)) = mk ((MulAut.conj ufin) y) := by
      intro x hx
      obtain ⟨y, hy, hEq⟩ := hfwd β' hβ' x hx
      exact ⟨y, hy, key x y hEq⟩
    have hB : ∀ y ∈ (minusDatum n hirr).rootGroup β',
        ∃ x ∈ (minusDatum n hirr).rootGroup β',
          θ (mk ((MulAut.conj u') x)) = mk ((MulAut.conj ufin) y) := by
      intro y hy
      obtain ⟨x, hx, hEq⟩ := hbwd β' hβ' y hy
      exact ⟨x, hx, key x y hEq⟩
    simpa only [ggRootSub, Subgroup.map_map] using
      irgOM_subgroup_map_eq ((minusDatum n hirr).rootGroup β') θ.toMonoidHom
        (mk.comp (MulAut.conj u').toMonoidHom) (mk.comp (MulAut.conj ufin).toMonoidHom) hF hB
  · have hneg : -β' ∈ (minusDatum n hirr).roots := irgOM_neg_mem_roots _ hβ'
    have hF : ∀ x ∈ (minusDatum n hirr).rootGroup (-β'),
        ∃ y ∈ (minusDatum n hirr).rootGroup (-β'),
          θ (mk ((MulAut.conj u') x)) = mk ((MulAut.conj ufin) y) := by
      intro x hx
      obtain ⟨y, hy, hEq⟩ := hfwd (-β') hneg x hx
      exact ⟨y, hy, key x y hEq⟩
    have hB : ∀ y ∈ (minusDatum n hirr).rootGroup (-β'),
        ∃ x ∈ (minusDatum n hirr).rootGroup (-β'),
          θ (mk ((MulAut.conj u') x)) = mk ((MulAut.conj ufin) y) := by
      intro y hy
      obtain ⟨x, hx, hEq⟩ := hbwd (-β') hneg y hy
      exact ⟨x, hx, key x y hEq⟩
    simpa only [ggRootSub, Subgroup.map_map] using
      irgOM_subgroup_map_eq ((minusDatum n hirr).rootGroup (-β')) θ.toMonoidHom
        (mk.comp (MulAut.conj u').toMonoidHom) (mk.comp (MulAut.conj ufin).toMonoidHom) hF hB

end Main

end CFSG.StandardType.RCKRP
