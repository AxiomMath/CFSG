module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreAutomizer

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem ggLieDP_isRoot_ggGraphLat
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .F4 ∨ t = .twistedE6)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) :
    IsRoot (langTag t) (ggGraphLat t γ) := by
  rcases ht with rfl | rfl | rfl
  · change IsRoot (langTag .E6) γ
    exact hγ
  · change IsRoot (langTag .F4) γ
    exact hγ
  · change IsRoot (langTag .twistedE6) (permLattice (TwistTag.perm .E6) γ)
    exact hγ.permLattice (TwistTag.cartan_perm .E6)

theorem ggLieDP_map_ggPhi_rootSubgroup
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .F4 ∨ t = .twistedE6) (f : ℕ)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) :
    (rootSubgroup (langTag t) GGL γ).map (ggPhi t f) =
      rootSubgroup (langTag t) GGL (ggGraphLat t γ) := by
  rcases ht with rfl | rfl | rfl
  · ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).1 hy
      refine (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).2 ⟨c ^ 2 ^ f, ?_⟩
      exact (ggPhi_pinnedX_untw (t := .E6) (Or.inr (Or.inl rfl)) f hγ c).symm
    · intro hx
      obtain ⟨e, rfl⟩ := (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).1 hx
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := GGL) e (n := 2 ^ f)
        (pow_pos (by norm_num) f)
      refine Subgroup.mem_map.2 ⟨pinnedX Tag.E6 GGL γ c,
        (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).2 ⟨c, rfl⟩, ?_⟩
      rw [← hc]
      exact ggPhi_pinnedX_untw (t := .E6) (Or.inr (Or.inl rfl)) f hγ c
  · ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := Tag.F4) (R := GGL) (α := γ)).1 hy
      refine (mem_rootSubgroup (τ := Tag.F4) (R := GGL) (α := γ)).2 ⟨c ^ 2 ^ f, ?_⟩
      exact (ggPhi_pinnedX_untw (t := .F4) (Or.inl rfl) f hγ c).symm
    · intro hx
      obtain ⟨e, rfl⟩ := (mem_rootSubgroup (τ := Tag.F4) (R := GGL) (α := γ)).1 hx
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := GGL) e (n := 2 ^ f)
        (pow_pos (by norm_num) f)
      refine Subgroup.mem_map.2 ⟨pinnedX Tag.F4 GGL γ c,
        (mem_rootSubgroup (τ := Tag.F4) (R := GGL) (α := γ)).2 ⟨c, rfl⟩, ?_⟩
      rw [← hc]
      exact ggPhi_pinnedX_untw (t := .F4) (Or.inl rfl) f hγ c
  · ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).1 hy
      refine (mem_rootSubgroup (τ := Tag.E6) (R := GGL)
        (α := ggGraphLat .twistedE6 γ)).2 ⟨c ^ 2 ^ f, ?_⟩
      exact (ggPhi_pinnedX_twistedE6 f hγ c).symm
    · intro hx
      obtain ⟨e, rfl⟩ := (mem_rootSubgroup (τ := Tag.E6) (R := GGL)
        (α := ggGraphLat .twistedE6 γ)).1 hx
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := GGL) e (n := 2 ^ f)
        (pow_pos (by norm_num) f)
      refine Subgroup.mem_map.2 ⟨pinnedX Tag.E6 GGL γ c,
        (mem_rootSubgroup (τ := Tag.E6) (R := GGL) (α := γ)).2 ⟨c, rfl⟩, ?_⟩
      rw [← hc]
      exact ggPhi_pinnedX_twistedE6 f hγ c

private theorem ggLieDP_map_conj_rootSubgroup
    {τ : Tag} {w : WeylGroup τ} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (rootSubgroup τ GGL δ).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) GGL w)).toMonoidHom =
      rootSubgroup τ GGL (w • δ) := by
  have h2 : (2 : GGL) = 0 := by
    haveI : CharP GGL 2 := inferInstance
    exact_mod_cast CharP.cast_eq_zero GGL 2
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := τ) (R := GGL) (α := δ)).1 hy
    refine (mem_rootSubgroup (τ := τ) (R := GGL) (α := w • δ)).2 ⟨c, ?_⟩
    change pinnedX τ GGL (w • δ) c =
      canonicalRep (coxeterSystem τ) GGL w * pinnedX τ GGL δ c *
        (canonicalRep (coxeterSystem τ) GGL w)⁻¹
    exact (canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hδ c).symm
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := τ) (R := GGL) (α := w • δ)).1 hx
    refine Subgroup.mem_map.2 ⟨pinnedX τ GGL δ c,
      (mem_rootSubgroup (τ := τ) (R := GGL) (α := δ)).2 ⟨c, rfl⟩, ?_⟩
    change canonicalRep (coxeterSystem τ) GGL w * pinnedX τ GGL δ c *
        (canonicalRep (coxeterSystem τ) GGL w)⁻¹ = pinnedX τ GGL (w • δ) c
    exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hδ c

theorem isSteinbergEnd_ggPhi
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ) :
    IsSteinbergEnd (langTag t) GGL (2 ^ f) (ggPhi t f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · refine ⟨ggFrobT f, fun c => ggFrobT_apply f c, 1, Or.inl rfl, ?_⟩
    intro g
    change Units.map (entrywiseHom (ggFrobT f)) g =
      1 * Units.map (entrywiseHom (ggFrobT f)) g * 1⁻¹
    simp only [one_mul, mul_one, inv_one]
  · refine ⟨ggFrobT f, fun c => ggFrobT_apply f c, 1, Or.inl rfl, ?_⟩
    intro g
    change Units.map (entrywiseHom (ggFrobT f)) g =
      1 * Units.map (entrywiseHom (ggFrobT f)) g * 1⁻¹
    simp only [one_mul, mul_one, inv_one]
  · refine ⟨ggFrobT f, fun c => ggFrobT_apply f c, 1, Or.inl rfl, ?_⟩
    intro g
    change Units.map (entrywiseHom (ggFrobT f)) g =
      1 * Units.map (entrywiseHom (ggFrobT f)) g * 1⁻¹
    simp only [one_mul, mul_one, inv_one]
  · refine ⟨ggFrobT f, fun c => ggFrobT_apply f c, 1, Or.inl rfl, ?_⟩
    intro g
    change Units.map (entrywiseHom (ggFrobT f)) g =
      1 * Units.map (entrywiseHom (ggFrobT f)) g * 1⁻¹
    simp only [one_mul, mul_one, inv_one]
  · refine ⟨ggFrobT f, fun c => ggFrobT_apply f c,
      diagramAt (langTag .twistedE6) GGL TwistTag.E6 rfl,
      Or.inr ⟨TwistTag.E6, rfl, rfl⟩, ?_⟩
    intro g
    change twistHom TwistTag.E6 GGL (ggFrobT f) g =
      diagramAt (langTag .twistedE6) GGL TwistTag.E6 rfl *
        Units.map (entrywiseHom (ggFrobT f)) g *
        (diagramAt (langTag .twistedE6) GGL TwistTag.E6 rfl)⁻¹
    simp only [twistHom, MonoidHom.comp_apply, MulAut.conj_apply]
    rfl

theorem ggLie_frobRootMap_eq_on_roots
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .F4 ∨ t = .twistedE6) {f : ℕ} (hf : 1 ≤ f)
    (hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ f) (ggPhi t f)) (w : WeylGroup (langTag t))
    (g : ModGL (langTag t) GGL) (hg : g ∈ adjointGroup (langTag t) GGL)
    (hlang : ggPhi t f g = g * canonicalRep (coxeterSystem (langTag t)) GGL w)
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)}
    (hρ : FrobRootMap (langDatumOfPosition hΦ w g hg hlang) ρ)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) :
    ρ γ = w • ggGraphLat t γ := by
  let D : LangDatum (langTag t) GGL := langDatumOfPosition hΦ w g hg hlang
  have hφroot : IsRoot (langTag t) (ggGraphLat t γ) := ggLieDP_isRoot_ggGraphLat ht hγ
  have hstep : (rootSubgroup (langTag t) GGL γ).map D.step =
      rootSubgroup (langTag t) GGL (w • ggGraphLat t γ) := by
    have hsplit : (rootSubgroup (langTag t) GGL γ).map D.step =
        ((rootSubgroup (langTag t) GGL γ).map (ggPhi t f)).map
          (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL w)).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hsplit, ggLieDP_map_ggPhi_rootSubgroup ht f hγ,
      ggLieDP_map_conj_rootSubgroup hφroot]
  have hρ' : (rootSubgroup (langTag t) GGL γ).map D.step =
      rootSubgroup (langTag t) GGL (ρ γ) := hρ.map_rootSubgroup γ hγ
  have hroots : IsRoot (langTag t) (ρ γ) := (hρ.isRoot_iff γ).2 hγ
  exact rootSubgroup_injective_of_isRoot hroots (IsRoot.smul hφroot w)
    (hρ'.symm.trans hstep)

end CFSG.StandardType.LieCore
