module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem conjSL_eq_slConjugation {m : ℕ} {K : Type} [Field K]
    (A : GL (Fin (m + 1)) K) (s : SpecialLinearGroup (Fin (m + 1)) K) :
    InnerDiagA.conjSL (m := m) (F := K) A s =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) K A s := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]

private theorem range_subtype_comp {m : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] {L' : Subgroup M}
    {φ' : SpecialLinearGroup (Fin (m + 1)) K →* L'} (hφs : Function.Surjective φ') :
    (L'.subtype.comp φ').range = L' := by
  rw [← MonoidHom.map_range L'.subtype φ',
    MonoidHom.range_eq_top_of_surjective φ' hφs, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_block_of_isComponentOf_centralizer_SL
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ')
    (hker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (hdiag : ∀ e : E, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    {D' : Subgroup M} (hD' : D' ≤ E) {J' : Subgroup M}
    (hJ : IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M))) :
    ∃ I₀ : Finset (Fin d), 2 ≤ I₀.card ∧
      J' = (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀).map
        (L'.subtype.comp φ') := by
  classical
  have hd_ne : d ≠ 0 := by
    intro hd
    haveI : Subsingleton (Fin d) := by rw [hd]; exact Fin.subsingleton_zero
    haveI : Subsingleton (SpecialLinearGroup (Fin d) K) :=
      Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    haveI : Subsingleton L' := ⟨fun x y => by
      obtain ⟨s, rfl⟩ := hφs x
      obtain ⟨t, rfl⟩ := hφs y
      rw [Subsingleton.elim s t]⟩
    have hJsub : J' ≤ L' := hJ.1.trans inf_le_left
    haveI : Subsingleton J' := (Subgroup.inclusion_injective hJsub).subsingleton
    haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJ.2.2.2
    have hJnontriv : Nontrivial J' :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).nontrivial
    obtain ⟨a, b, hab⟩ := hJnontriv
    exact hab (Subsingleton.elim a b)
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := Nat.exists_eq_add_one_of_ne_zero hd_ne
  let ψ : SpecialLinearGroup (Fin (m + 1)) K →* M := L'.subtype.comp φ'
  let b : D' → M := fun e => (e : M)
  choose t ht using fun e : D' => hdiag (⟨(e : M), hD' e.2⟩ : E)
  let dd : D' → Fin (m + 1) → Kˣ := fun e j => Units.mk0 (t e j) ((ht e).ne_zero j)
  have hker' : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact scalars_le_center (m + 1) K (hker x (Subtype.ext (by simpa [ψ] using hx)))
  have hb : ∀ e : D', (b e, InnerDiagA.diagGL (dd e)) ∈ LinFusion.ggInducedPairs ψ := by
    intro e
    rw [LinFusion.mem_ggInducedPairs]
    intro u
    let D := Classical.choose (ht e)
    have hDmat : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = diagonal (t e) :=
      (Classical.choose_spec (ht e)).1
    have hact := (Classical.choose_spec (ht e)).2
    have hDd : InnerDiagA.diagGL (dd e) = D := by
      apply Units.ext
      rw [InnerDiagA.coe_diagGL, hDmat]
      congr 1
    have hL : (e : M) * ((φ' u : L') : M) * (e : M)⁻¹ =
        ((L'.normalizerMonoidHom ⟨(e : M), hE (hD' e.2)⟩) (φ' u) : M) := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hR : ((φ' (InnerDiagA.conjSL (InnerDiagA.diagGL (dd e)) u) : L') : M) =
        ((L'.normalizerMonoidHom ⟨(e : M), hE (hD' e.2)⟩) (φ' u) : M) := by
      rw [hact u, conjSL_eq_slConjugation, hDd]
    show (e : M) * ((φ' u : L') : M) * (e : M)⁻¹ =
      ((φ' (InnerDiagA.conjSL (InnerDiagA.diagGL (dd e)) u) : L') : M)
    rw [hL, hR]
  have hL' : CFSG.Assembly.IsComponentOf J' (ψ.range ⊓ Subgroup.centralizer (Set.range b)) := by
    have hrange : ψ.range = L' := by
      change (L'.subtype.comp φ').range = L'
      exact range_subtype_comp hφs
    have hbr : Set.range b = (D' : Set M) := Subtype.range_coe
    rw [hrange, hbr]
    exact hJ
  obtain ⟨i, hi⟩ :=
    LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf
      (F := K) (m := m) (ι := D') (G := M) (ψ := ψ) (d := dd) (b := b) hker' hb hL'
  obtain ⟨h2, -⟩ :=
    LinSemisimple.two_le_card_of_isQuasisimple_le (F := K) (m := m) (ψ := ψ) hJ.2.2 hi.le
  exact ⟨LinSemisimple.eigClass dd i, h2, hi⟩

end CFSG.StandardType
