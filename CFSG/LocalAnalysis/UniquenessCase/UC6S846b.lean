module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barAut (L : Subgroup G) : MulAut ↥L →* MulAut (Bar2 L) where
  toFun φ := QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) φ
    (CFSG.pCore_map_iso 2 φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def rhoL (L : Subgroup G) : ↥(normalizer (L : Set G)) →* MulAut (Bar2 L) :=
  (barAut L).comp (Subgroup.normalizerMonoidHom L)

theorem rhoL_mk (L : Subgroup G) (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    rhoL L m (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.normalizerMonoidHom L m x) := rfl

theorem rhoL_mk_coe (L : Subgroup G) (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    ((Subgroup.normalizerMonoidHom L m x : ↥L) : G) = (m : G) * (x : G) * (m : G)⁻¹ := by
  simp

theorem rhoL_inner (L : Subgroup G) (l : G) (hl : l ∈ L) :
    rhoL L ⟨l, Subgroup.le_normalizer hl⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : Bar2 L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [rhoL_mk]
    show QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨l, _⟩ x) = _
    have : Subgroup.normalizerMonoidHom L ⟨l, Subgroup.le_normalizer hl⟩ x = ⟨l, hl⟩ * x * ⟨l, hl⟩⁻¹ := by
      apply Subtype.ext
      simp
    rw [this]
    simp [MulAut.conj_apply]

theorem rhoL_fix_iff (L : Subgroup G) (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    rhoL L m (QuotientGroup.mk x) = QuotientGroup.mk x ↔
      (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L := by
  rw [rhoL_mk, QuotientGroup.eq_iff_div_mem]
  have hcoe : (((Subgroup.normalizerMonoidHom L m x) / x : ↥L) : G) =
      (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ := by
    rw [Subgroup.coe_div, rhoL_mk_coe, div_eq_mul_inv]
  constructor
  · intro h
    exact ⟨_, h, hcoe⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = (Subgroup.normalizerMonoidHom L m x) / x := Subtype.ext (by
      rw [hcoe]; exact hyx)
    rw [← this]
    exact hy

theorem normalizer_le_normalizer_pCoreOf (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g' ∈ normalizer (L : Set G), ∀ x ∈ pCoreOf 2 L, g' * x * g'⁻¹ ∈ pCoreOf 2 L := by
    intro g' hg' x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.normalizerMonoidHom L ⟨g', hg'⟩ y, ?_, by simp⟩
    have hfix : (CFSG.pCore 2 ↥L).map (Subgroup.normalizerMonoidHom L ⟨g', hg'⟩).toMonoidHom =
        CFSG.pCore 2 ↥L := CFSG.pCore_map_iso 2 _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this

theorem isPGroup_pCoreOf (L : Subgroup G) : IsPGroup 2 (pCoreOf 2 L) := by
  unfold pCoreOf
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
