module

public import CFSG.Quasithin.EmptyFaithful.S153NBdGen
public import CFSG.Quasithin.EmptyFaithful.S153NDef
public import CFSG.Quasithin.Background.S1567Z4

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Core

variable {G : Type} [Group G] [Finite G]

theorem bridgeD_core {C Te M K : Subgroup G} (hSE : IsSylowTwoOf (Te ⊓ C) C)
    (hJTe : thompsonJ Te ≤ Te) (hJC : thompsonJ Te ≤ C)
    (hPJ : ∀ P : Subgroup G, thompsonJ Te ≤ P → P ≤ Te →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (thompsonJ Te : Set G))
    (hN : Subgroup.normalizer (thompsonJ Te : Set G) ≤ M) (hTM : Te ≤ M) (hKM : K ≤ M)
    {W : Type} [CommGroup W] (φ : ↥C →* MulAut W) (hker : φ.ker = K.subgroupOf C) (w : W)
    (hstab : ∀ c : ↥C, φ c ∈ stabAt φ.range w ↔ (c : G) ∈ M) :
    ∀ N : Subgroup (MulAut W), N ≤ φ.range → (N.subgroupOf φ.range).Normal →
      (∀ A : Subgroup G, IsMaxElemAbelian Te A → (A.subgroupOf C).map φ ≤ N) →
      φ.range = N ⊔ stabAt φ.range w ∧ ∃ S : Subgroup (MulAut W), IsSylowTwoOf S N ∧
        Subgroup.normalizer (S : Set (MulAut W)) ⊓ N ≤ stabAt φ.range w := by
  intro N hNr hNn hA
  set IN : Subgroup G := (N.comap φ).map C.subtype with hIN
  have hINC : IN ≤ C := Subgroup.map_subtype_le _
  have hmemIN : ∀ g : G, g ∈ IN ↔ ∃ h : g ∈ C, φ ⟨g, h⟩ ∈ N := by
    intro g
    simp only [hIN, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
    · rintro ⟨h, hg⟩
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hINsub : IN.subgroupOf C = N.comap φ :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hINnorm : C ≤ Subgroup.normalizer (IN : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hINC).1 ?_
    rw [hINsub]
    exact BridgeD.normal_comap_of_normal_subgroupOf_range φ hNn
  have hSI : IsSylowTwoOf (Te ⊓ IN) IN := by
    have h := A4.isSylowTwoOf_inf_normal hSE hINC hINnorm
    rwa [inf_assoc, inf_eq_right.mpr hINC] at h
  have hJIN : thompsonJ Te ≤ IN := by
    refine iSup₂_le fun A hAm => ?_
    intro a ha
    have haC : a ∈ C := hJC ((le_iSup₂_of_le A hAm le_rfl : A ≤ thompsonJ Te) ha)
    rw [hmemIN]
    exact ⟨haC, hA A hAm (Subgroup.mem_map.2 ⟨⟨a, haC⟩, ha, rfl⟩)⟩
  have hJSI : thompsonJ Te ≤ Te ⊓ IN := le_inf hJTe hJIN
  have hnSI : Subgroup.normalizer ((Te ⊓ IN : Subgroup G) : Set G) ≤ M :=
    (hPJ _ hJSI inf_le_left).trans hN
  have hSIC : Te ⊓ IN ≤ C := inf_le_right.trans hINC
  have hP : IsSylowTwoOf ((Te ⊓ IN).subgroupOf C) (N.comap φ) := by
    rw [← hINsub]
    exact BridgeD.isSylowTwoOf_subgroupOf hSI hINC
  have hker' : φ.ker ≤ M.subgroupOf C := by
    intro x hx
    rw [hker] at hx
    exact hKM hx
  have hPQ : (Te ⊓ IN).subgroupOf C ≤ M.subgroupOf C := fun x hx =>
    hTM (Subgroup.mem_subgroupOf.mp hx).1
  have hNP : Subgroup.normalizer (((Te ⊓ IN).subgroupOf C : Subgroup ↥C) : Set ↥C) ≤
      M.subgroupOf C := by
    intro m hm
    have h1 : m ∈ (Subgroup.normalizer ((Te ⊓ IN : Subgroup G) : Set G)).subgroupOf C := by
      rw [Subgroup.subgroupOf_normalizer_eq hSIC]
      exact hm
    exact hnSI h1
  obtain ⟨h1, h2, h3⟩ :=
    BridgeD.frattini_transfer φ hNr (stabAt_le _ _) hNn hP (fun c => hstab c) hker' hPQ hNP
  exact ⟨h1, _, h2, h3⟩

end Core

section Bridge

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem bridgeD_frattini (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hN : Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ≤ M) {W : Type} [CommGroup W]
    (φ : ↥(Subgroup.centralizer (E : Set G)) →* MulAut W)
    (hker : φ.ker = (S1567.K167 T M E).subgroupOf (Subgroup.centralizer (E : Set G))) (w : W)
    (hstab : ∀ c : ↥(Subgroup.centralizer (E : Set G)), φ c ∈ stabAt φ.range w ↔ (c : G) ∈ M) :
    ∀ N : Subgroup (MulAut W), N ≤ φ.range → (N.subgroupOf φ.range).Normal →
      (∀ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A →
        (A.subgroupOf (Subgroup.centralizer (E : Set G))).map φ ≤ N) →
      φ.range = N ⊔ stabAt φ.range w ∧ ∃ S : Subgroup (MulAut W), IsSylowTwoOf S N ∧
        Subgroup.normalizer (S : Set (MulAut W)) ⊓ N ≤ stabAt φ.range w := by
  obtain ⟨hJTE, -, -, hPJ, -, -⟩ := S1567.commJ_data h113 k
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hSE : IsSylowTwoOf (TE153 T E ⊓ Subgroup.centralizer (E : Set G))
      (Subgroup.centralizer (E : Set G)) :=
    A4.isSylowTwoOf_inf_normal k.r2.sylow_GE hCN (S1567.normalizer_le_normalizer_CE E)
  have hJC : thompsonJ (TE153 T E) ≤ Subgroup.centralizer (E : Set G) :=
    (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66).trans (Subgroup.centralizer_le k.L.le_V)
  exact bridgeD_core hSE hJTE hJC hPJ hN (inf_le_left.trans k.c.hyp.T_le)
    ((S1567.K167_le_M_inf_normalizer k).trans inf_le_left) φ hker w hstab

end Bridge

end CFSG.Quasithin.S153N
