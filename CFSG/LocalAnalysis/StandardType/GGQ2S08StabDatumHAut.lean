module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumAllAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08x1a_psi_lift_closure {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    {σ : MulAut ↥Bs} (hσ : σ ∈ Subgroup.closure (Set.range M.simple)) :
    ∃ Φ' ∈ Subgroup.closure (Set.range (ggQ2s08x1p_psi hS hBsN M)),
      ∀ b : ↥Bs, Φ' ((ggGamma L hBsN).rangeRestrict b) =
        (ggGamma L hBsN).rangeRestrict (σ b) := by
  induction hσ using Subgroup.closure_induction with
  | mem ψ hψ =>
      obtain ⟨i, rfl⟩ := hψ
      exact ⟨ggQ2s08x1p_psi hS hBsN M i, Subgroup.subset_closure ⟨i, rfl⟩,
        fun b => ggQ2s08x1p_psi_compat hS hBsN M i b⟩
  | one =>
      exact ⟨1, Subgroup.one_mem _, fun _ => rfl⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨Φa, hΦa, hpa⟩ := iha
      obtain ⟨Φb, hΦb, hpb⟩ := ihb
      exact ⟨Φa * Φb, Subgroup.mul_mem _ hΦa hΦb,
        fun c => by
          rw [MulAut.mul_apply, hpb c, hpa (b c)]
          rfl⟩
  | inv a _ iha =>
      obtain ⟨Φa, hΦa, hpa⟩ := iha
      refine ⟨Φa⁻¹, Subgroup.inv_mem _ hΦa, fun c => ?_⟩
      have h : Φa ((ggGamma L hBsN).rangeRestrict (a.symm c)) =
          (ggGamma L hBsN).rangeRestrict c := by
        simpa using hpa (a.symm c)
      rw [← h]
      exact MulEquiv.symm_apply_apply Φa _

theorem ggQ2s08x1p_hAut_le_of_norm {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    (hnorm : ∀ l : ↥L, (MulAut.conj l : MulAut ↥L) ∈
      Subgroup.normalizer (((ggGamma L hBsN).range : Subgroup (MulAut ↥L)) : Set (MulAut ↥L)) →
        (l : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range ≤
      Subgroup.closure (Set.range (ggQ2s08x1p_psi hS hBsN M)) := by
  intro Φ hΦ
  obtain ⟨g, hgH, hgnorm, hgval⟩ := mem_ggAutomizer_iff.mp hΦ
  obtain ⟨l, hl_eq⟩ := MonoidHom.mem_range.mp hgH
  have hconj_mem : (MulAut.conj l : MulAut ↥L) ∈
      Subgroup.normalizer (((ggGamma L hBsN).range : Subgroup (MulAut ↥L)) :
        Set (MulAut ↥L)) := by
    rwa [hl_eq]
  have hl : (l : G) ∈ Subgroup.normalizer (Bs : Set G) := hnorm l hconj_mem
  let σ : MulAut ↥Bs := ggConjAut Bs hl
  have hσ : σ ∈ Subgroup.closure (Set.range M.simple) := by
    rw [← M.automizer_L]
    exact ggConjAut_mem_ggAutomizer l.2 hl
  obtain ⟨Φ', hΦ'closure, hΦ'prop⟩ := ggQ2s08x1a_psi_lift_closure hS hBsN M hσ
  have hkey : ∀ b : ↥Bs, (MulAut.conj l : MulAut ↥L) * ggGamma L hBsN b *
      (MulAut.conj l)⁻¹ = ggGamma L hBsN (σ b) := by
    intro b
    have hgb : (l : G) * (b : G) * (l : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hl b).mp b.2
    have h1 : (MulAut.conj l : MulAut ↥L) =
        L.normalizerMonoidHom ⟨(l : G), Subgroup.le_normalizer l.2⟩ :=
      MulEquiv.ext fun l' => Subtype.ext rfl
    rw [h1, ggGamma_conj_normalizer L hBsN ⟨(l : G), Subgroup.le_normalizer l.2⟩ b hgb]
    exact congrArg (ggGamma L hBsN)
      (show (⟨(l : G) * (b : G) * (l : G)⁻¹, hgb⟩ : ↥Bs) = σ b from rfl)
  have hΦeq : Φ = Φ' := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    rw [hgval ((ggGamma L hBsN).rangeRestrict b), hΦ'prop b,
      MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, ← hl_eq]
    exact hkey b
  rw [hΦeq]
  exact hΦ'closure

end CFSG.StandardType

end
