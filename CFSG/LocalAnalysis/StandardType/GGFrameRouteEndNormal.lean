module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

theorem subgroupOf_centralizer_normal_of_sStar {G : Type} [Group G] [Finite G]
    {B : Subgroup G} {x : G} {L : Subgroup G} (hSstar : LargeEvenSStar 3 B x L)
    (hS : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  have hcompA : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hSstar.2.2.2.1
  have hcompO : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_iff_open.mp hcompA
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup 3 S → IsCyclic S :=
    hSstar.2.2.2.2
  obtain ⟨S, hSle, hSp, hSnc⟩ := hS
  have hconj : ∀ c ∈ Subgroup.centralizer ({x} : Set G),
      L.map (MulAut.conj c).toMonoidHom = L := by
    intro c hc
    by_contra hne
    have hLcO : CFSG.Open.IsComponentOf (L.map (MulAut.conj c).toMonoidHom)
        (Subgroup.centralizer ({x} : Set G)) :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcompO hc
    have hcomm : ⁅L, L.map (MulAut.conj c).toMonoidHom⁆ = ⊥ :=
      CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hcompO hLcO (fun h => hne h.symm)
    have hcent : L.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer (L : Set G) := by
      have h2 : ⁅L.map (MulAut.conj c).toMonoidHom, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]; exact hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    let T : Subgroup G := S.map (MulAut.conj c).toMonoidHom
    have hTp : IsPGroup 3 T := hSp.map (MulAut.conj c).toMonoidHom
    have hTle : T ≤ Subgroup.centralizer (L : Set G) :=
      (Subgroup.map_mono hSle).trans hcent
    haveI : IsCyclic T := hcyc T hTle hTp
    have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
    exact hSnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective S (MulAut.conj c).toMonoidHom hinj).toMonoidHom
      (Subgroup.equivMapOfInjective S (MulAut.conj c).toMonoidHom hinj).injective)
  refine Subgroup.Normal.mk fun n hn g => ?_
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : G) ∈ Subgroup.centralizer ({x} : Set G) := g.2
  have hmap := hconj (g : G) hg
  have hmem : (MulAut.conj (g : G)) (n : G) ∈ L.map (MulAut.conj (g : G)).toMonoidHom :=
    ⟨(n : G), hn, rfl⟩
  rw [hmap] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem subgroupOf_centralizer_normal_of_noncyclic {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hS : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
  subgroupOf_centralizer_normal_of_sStar hR.1.1.2.2.2.2.2.2.1 hS

theorem conj_mem_ggAutomizer_of_fix {G : Type} [Group G] {Bs H L : Subgroup G} {x : G}
    (hxBs : x ∈ Bs) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (t : MulAut ↥Bs) (ht : t ∈ ggAutomizer H Bs)
    (htx : ∀ b : ↥Bs, (b : G) = x → ((t b : ↥Bs) : G) = x) :
    ∀ a ∈ ggAutomizer L Bs, t * a * t⁻¹ ∈ ggAutomizer L Bs := by
  intro a ha
  obtain ⟨g, _hgH, hgN, ht_apply⟩ := mem_ggAutomizer_iff.mp ht
  obtain ⟨l, hlL, hlN, ha_apply⟩ := mem_ggAutomizer_iff.mp ha
  have hgCx : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := htx ⟨x, hxBs⟩ rfl
    rw [ht_apply ⟨x, hxBs⟩] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hlCx : l ∈ Subgroup.centralizer ({x} : Set G) := hLx hlL
  have hglg : g * l * g⁻¹ ∈ L := by
    let C := Subgroup.centralizer ({x} : Set G)
    have hmem : (⟨l, hlCx⟩ : ↥C) ∈ L.subgroupOf C := hlL
    have hconj_mem :
        (⟨g, hgCx⟩ : ↥C) * (⟨l, hlCx⟩ : ↥C) * (⟨g, hgCx⟩ : ↥C)⁻¹ ∈ L.subgroupOf C :=
      hLn.conj_mem ⟨l, hlCx⟩ hmem ⟨g, hgCx⟩
    rw [Subgroup.mem_subgroupOf] at hconj_mem
    simpa using hconj_mem
  have hglN : g * l * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN)
  refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, hglg, hglN, fun b => ?_⟩
  have ht_inv_apply : ∀ b : ↥Bs, ((t⁻¹ b : ↥Bs) : G) = g⁻¹ * b * g :=
    inv_apply_of_forall ht_apply
  rw [MulAut.mul_apply, MulAut.mul_apply, ht_apply (a (t⁻¹ b)),
    ha_apply (t⁻¹ b), ht_inv_apply b]
  group

end CFSG.StandardType.FrameRoute

end
