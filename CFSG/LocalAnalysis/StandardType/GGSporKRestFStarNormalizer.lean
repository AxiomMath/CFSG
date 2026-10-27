module

public import CFSG.GroupTheory.Fitting.MulEquiv
public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_fstar_of_normalizer_maximal {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p K)
    (hmax : ∀ Y : Subgroup K, Subgroup.normalizer ((S₀ : Subgroup K) : Set K) ≤ Y →
      Y = Subgroup.normalizer ((S₀ : Subgroup K) : Set K) ∨ Y = ⊤)
    (hF : IsPGroup p ↥(CFSG.generalizedFitting ↥(Subgroup.normalizer ((S₀ : Subgroup K) : Set K)))) :
    ∀ (S : Sylow p K) (Y : Subgroup K), Y ≠ ⊤ →
      Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ Y →
        IsPGroup p ↥(CFSG.generalizedFitting ↥Y) := by
  intro S Y hY hNY
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ S
  let c : K ≃* K := MulAut.conj g⁻¹
  let Y' : Subgroup K := Y.map c.toMonoidHom
  have hcomp : c.toMonoidHom.comp (↑(MulAut.conj g) : K →* K) = MonoidHom.id K := by
    ext x
    show c ((MulAut.conj g) x) = x
    simp only [c, MulAut.conj_apply]
    group
  have hSmap : (S : Subgroup K).map c.toMonoidHom = S₀ := by
    have hg_sub : ((g • S₀ : Sylow p K) : Subgroup K) = (S : Subgroup K) :=
      congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hg
    rw [← hg_sub, Sylow.coe_subgroup_smul, ← TauCeti.map_conj_eq_conj_smul g (S₀ : Subgroup K),
      Subgroup.map_map, hcomp, Subgroup.map_id]
  have hNeq : (Subgroup.normalizer ((S : Subgroup K) : Set K)).map c.toMonoidHom =
      Subgroup.normalizer ((S₀ : Subgroup K) : Set K) := by
    rw [Subgroup.map_equiv_normalizer_eq (S : Subgroup K) c, hSmap]
  have hNle : Subgroup.normalizer ((S₀ : Subgroup K) : Set K) ≤ Y' := by
    rw [← hNeq]
    exact Subgroup.map_mono hNY
  have hcomp_symm : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id K := by
    ext x
    exact c.symm_apply_apply x
  have hmapY : Y'.map c.symm.toMonoidHom = Y := by
    show (Y.map c.toMonoidHom).map c.symm.toMonoidHom = Y
    rw [Subgroup.map_map, hcomp_symm, Subgroup.map_id]
  have htop : (⊤ : Subgroup K).map c.symm.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 c.symm.surjective
  have hY'ne : Y' ≠ ⊤ := by
    intro h
    apply hY
    rw [← hmapY, h, htop]
  rcases hmax Y' hNle with h | h
  · let N : Subgroup K := Subgroup.normalizer ((S₀ : Subgroup K) : Set K)
    have hF' : IsPGroup p ↥(CFSG.generalizedFitting ↥N) := hF
    have he : ↥Y ≃* ↥N :=
      (Subgroup.equivMapOfInjective Y c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr h)
    have hgf : (CFSG.generalizedFitting ↥Y).map he.toMonoidHom = CFSG.generalizedFitting ↥N :=
      CFSG.WholeGroup.generalizedFitting_map_mulEquiv he
    let eGF : ↥(CFSG.generalizedFitting ↥Y) ≃* ↥(CFSG.generalizedFitting ↥N) :=
      (Subgroup.equivMapOfInjective (CFSG.generalizedFitting ↥Y) he.toMonoidHom
        he.injective).trans (MulEquiv.subgroupCongr hgf)
    exact IsPGroup.of_equiv hF' eGF.symm
  · exact absurd h hY'ne

end CFSG.StandardType.SporadicShape
