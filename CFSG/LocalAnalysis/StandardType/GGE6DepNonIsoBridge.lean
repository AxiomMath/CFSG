module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepNbrFacts
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem toAdd_phi_mem_hypE6 {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) {Z : Subgroup ↥L}
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup ↥L}
    {w : Fin 6 → ↥L} (hwith : GGE6ThreeWeylModelWith Z (ggGamma L hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5) (a : ↥(ggGamma L hBsN).range) :
    Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6 := by
  have hΦinj : Function.Injective Φ := hwith.1
  have hΦne : Φ.range ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (ggGamma L hBsN).range = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv
    have h2 : Nat.card Φ.range = Nat.card (Multiplicative (Fin 6 → ZMod 3)) := by
      rw [htop, Subgroup.card_top]
    have h3 : Nat.card (Multiplicative (Fin 6 → ZMod 3)) = 3 ^ 6 := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := Fin 6 → ZMod 3)), Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have : (3 : ℕ) ^ 5 = 3 ^ 6 := by rw [← hcard, h1, h2, h3]
    norm_num at this
  exact (hwith.2.1.resolve_left hΦne (Multiplicative.toAdd (Φ a))).mp (by
    rw [ofAdd_toAdd]
    exact ⟨a, rfl⟩)

theorem ggE6Dep_nonIso_of_prop {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hnbr : GGNbr 3 B x D J y K)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hyBs : y ∈ Bs)
    {R : Type} [Group R] {I : Set (MulAut R)} (hP : GGE6DepNonIsoProp R I) (ψ : ↥L →* R)
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup ↥L}
    {w : Fin 6 → ↥L} (hTB : GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5)
    (hwith : GGE6ThreeWeylModelWith ψ.ker (ggGamma L hBsN).range Φ T w) :
    E6Dep.norm6 (E6Dep.coordF.mulVec (Multiplicative.toAdd
      (Φ ((ggGamma L hBsN).rangeRestrict ⟨y, hyBs⟩)))) ≠ 0 := by
  classical
  intro hnorm
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨-, hxy, -, -⟩ := ggE6Dep_nbr_facts hcfg hnbr
  obtain ⟨a, ha⟩ : ∃ a : ↥(ggGamma L hBsN).range,
      a = (ggGamma L hBsN).rangeRestrict ⟨y, hyBs⟩ := ⟨_, rfl⟩
  rw [← ha] at hnorm
  have hac : (a : MulAut ↥L) = ggGamma L hBsN ⟨y, hyBs⟩ := by rw [ha]; rfl
  have ha1 : a ≠ 1 := by
    intro h1
    apply hxy
    rw [← hcfg.bstar_inf_centralizer_L]
    refine ⟨hyBs, (ggGamma_eq_one_iff L hBsN ⟨y, hyBs⟩).mp ?_⟩
    rw [← hac, h1]
    rfl
  have hmem := toAdd_phi_mem_hypE6 hBsN hwith hcard a
  have hne0 : Multiplicative.toAdd (Φ a) ≠ 0 := by
    intro h0
    apply ha1
    apply hwith.1
    rw [map_one]
    exact toAdd_eq_zero.mp h0
  have hIso : GGE6IsoPt (Multiplicative.toAdd (Φ a)) := ⟨hmem, hne0, hnorm⟩
  have hstd := hcfg.2.2.1
  have hJlayer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := hstd.2.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hstd.2.2.2.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hnbr.2.1, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have hfix : (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)).map L.subtype =
      L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBsN ⟨y, hyBs⟩
  have hinj : Function.Injective L.subtype := Subgroup.subtype_injective L
  have hJ0 : IsComponentOf (J.comap L.subtype) (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)) := by
    refine (isComponentOf_comap_of_injective L.subtype hinj ?_).1
    rw [hfix]
    exact hJcomp
  obtain ⟨J', hJ', hne⟩ := hP ↥L ψ (ggGamma L hBsN).range hTB hcard Φ T w hwith a hIso
    (J.comap L.subtype) (by rw [hac]; exact hJ0)
  rw [hac] at hJ'
  have hK' : IsComponentOf (J'.map L.subtype) (L ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [← hfix]
    exact isComponentOf_map_of_injective L.subtype hinj hJ'
  have hle : J'.map L.subtype ≤ J := by
    have h1 : J'.map L.subtype ≤ LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
      le_sSup hK'
    rw [← hJlayer] at h1
    exact h1
  have heq : J'.map L.subtype = J :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hK' hJcomp hle
  apply hne
  have h2 := congrArg (Subgroup.comap L.subtype) heq
  rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h2

end CFSG.StandardType

end
