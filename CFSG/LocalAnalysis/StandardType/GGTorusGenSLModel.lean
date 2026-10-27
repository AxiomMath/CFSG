module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem exists_tbGroup_of_position
    {d p : ℕ} {K : Type} [Field K] [Finite K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* projectiveSL d K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hp : p.Prime)
    (hpos : GGTableBPosition p L' E (Set.range (conjAut d K)) θ hE)
    (hr : p ^ (d - 1) ≤ Nat.card E) :
    GGTorusTBGroup p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) L'
      (ggQuotHom θ) (ggGamma L' hE).range := by
  refine ⟨ggQuotHom_surjective θ, (ker_ggQuotHom θ).le, hpos.1,
    TableBBridge.isElemAbelian_range_gamma hpos,
    TableBBridge.induces_range_gamma hpos, ?_,
    TableBBridge.pow_three_le_card_range hpos hp,
    TableBBridge.ggTorusSelfCent_range hpos⟩
  have h := TableBBridge.pow_pred_le_card_range hpos hp (r := d - 1) (by simpa using hr)
  rwa [show d - 1 - 1 = d - 2 by omega] at h

theorem exists_model_of_position_PSL
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* projectiveSL d K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E (Set.range (conjAut d K)) θ hE)
    (hr : p ^ (d - 1) ≤ Nat.card E) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧
      ∀ e : E, ∃ t : Fin d → K,
        TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t := by
  classical
  have htb := exists_tbGroup_of_position (d := d) (p := p) (K := K) (M := M) (L' := L') (E := E)
    (θ := θ) (hE := hE) hp hpos hr
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup (d := d) (p := p) (K := K) hp hpK hd
      (r := d - 2) (le_refl _) htb
  refine ⟨φ', hφ's, hφ'ker, ?_⟩
  intro e
  obtain ⟨t, ht⟩ := hdiag (ggGamma L' hE e) ⟨e, rfl⟩
  have hgg : ggGamma L' hE e = L'.normalizerMonoidHom ⟨e, hE e.2⟩ := rfl
  exact ⟨t, hgg ▸ ht⟩

end CFSG.StandardType
