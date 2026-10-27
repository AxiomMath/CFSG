module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem exists_tbGroup_of_position_gamma
    {d p : ℕ} {K : Type} [Field K] [Finite K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* projectiveSL d K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hp : p.Prime)
    (hpos : GGTableBPosition p L' E (Set.range (conjAut d K)) θ hE)
    (hr : p ^ (d - 2) ≤ Nat.card (ggGamma L' hE).range) :
    GGTorusTBGroup p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) L'
      (ggQuotHom θ) (ggGamma L' hE).range :=
  ⟨ggQuotHom_surjective θ, (ker_ggQuotHom θ).le, hpos.1,
    TableBBridge.isElemAbelian_range_gamma hpos,
    TableBBridge.induces_range_gamma hpos, hr,
    TableBBridge.pow_three_le_card_range hpos hp,
    TableBBridge.ggTorusSelfCent_range hpos⟩

private theorem actsDiag_comp_ggQuotHom
    {d : ℕ} {K : Type} [Field K] [Finite K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* projectiveSL d K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    {φ' : SpecialLinearGroup (Fin d) K →* L'}
    {a : Subgroup.normalizer (L' : Set M)} {t : Fin d → K}
    (h : TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom a) t) :
    TypeANbrDvd.ActsDiag ((ggQuotHom θ).comp φ') (ggLAut L' θ a) t := by
  obtain ⟨D, hD, hact⟩ := h
  refine ⟨D, hD, fun s => ?_⟩
  show ggLAut L' θ a (ggQuotHom θ (φ' s)) =
    ggQuotHom θ (φ' (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      d K D s))
  rw [ggQuotHom_apply, ggLAut_apply, ggQuotHom_apply, hact]

theorem exists_model_of_position_PSL_gamma
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* projectiveSL d K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E (Set.range (conjAut d K)) θ hE)
    (hr : p ^ (d - 2) ≤ Nat.card (ggGamma L' hE).range) :
    ∃ φ : SpecialLinearGroup (Fin d) K →* projectiveSL d K, Function.Surjective φ ∧
      (∀ g, φ g = 1 → g ∈ scalars d K) ∧
      ∀ e : E, ∃ t : Fin d → K,
        TypeANbrDvd.ActsDiag φ (ggLAut L' θ ⟨e, hE e.2⟩) t := by
  classical
  have htb := exists_tbGroup_of_position_gamma (d := d) (p := p) (K := K) (M := M) (L' := L')
    (E := E) (θ := θ) (hE := hE) hp hpos hr
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup (d := d) (p := p) (K := K) hp hpK hd
      (r := d - 2) (le_refl _) htb
  refine ⟨(ggQuotHom θ).comp φ', (ggQuotHom_surjective θ).comp hφ's, ?_, ?_⟩
  ·
    intro g hg
    have hz : φ' g ∈ Subgroup.center L' := by
      rw [← ker_ggQuotHom θ]
      simpa using hg
    have hconj : ∀ y, φ' (g * y * g⁻¹) = φ' y := by
      intro y
      have h1 : φ' g * φ' y = φ' y * φ' g :=
        (Subgroup.mem_center_iff.mp hz (φ' y)).symm
      rw [map_mul, map_mul, map_inv]
      calc φ' g * φ' y * (φ' g)⁻¹ = (φ' y * φ' g) * (φ' g)⁻¹ := by rw [h1]
        _ = φ' y := by group
    obtain ⟨c, hc⟩ := TypeANbrDvd.exists_scalar_of_map_conj_eq hφ'ker hconj
    exact (TypeA.mem_scalars_of_coe_eq_scalar (d := d) (by omega) hc).2
  ·
    intro e
    obtain ⟨t, ht⟩ := hdiag (ggGamma L' hE e) ⟨e, rfl⟩
    have hgg : ggGamma L' hE e = L'.normalizerMonoidHom ⟨e, hE e.2⟩ := rfl
    have ht' : TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t := hgg ▸ ht
    exact ⟨t, actsDiag_comp_ggQuotHom (θ := θ) (hE := hE) ht'⟩

end CFSG.StandardType
