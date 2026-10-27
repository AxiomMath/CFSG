module

public import CFSG.Quasithin.Background.F918V5GRank
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918V5G

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf {K M : Subgroup G} (hK : IsComponentOf K M) :
    CFSG.IsComponent (K.subgroupOf M) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hK.1).symm hq, ?_⟩
  have h := A3.subnormal_comap M.subtype hK.2.1
  rw [show M.comap M.subtype = ⊤ from Subgroup.subgroupOf_self M] at h
  exact A3.subnormal_top_iff.mp h

theorem isComponentOf_eq_or_commute [Finite G] {K K' M : Subgroup G} (hK : IsComponentOf K M)
    (hK' : IsComponentOf K' M) : K = K' ∨ ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf hK)
      (isComponent_subgroupOf hK') with h | h
  · left
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hK.1,
      inf_of_le_left hK'.1] at this
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rw [inf_of_le_left hK'.1] at h1
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hx) y hy).symm

theorem isComponentOf_map_conj {K M : Subgroup G} (hK : IsComponentOf K M) {m : G}
    (hm : m ∈ M) : IsComponentOf (K.map (MulAut.conj m).toMonoidHom) M := by
  have hM : M.map (MulAut.conj m).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hm)
  refine ⟨?_, ?_, ?_⟩
  · calc K.map (MulAut.conj m).toMonoidHom ≤ M.map (MulAut.conj m).toMonoidHom :=
        Subgroup.map_mono hK.1
      _ = M := hM
  · have := A3.subnormal_map (MulAut.conj m).toMonoidHom hK.2.1
    rwa [hM] at this
  · have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
    exact A3.isQuasisimple_iff_open.mp (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective) hq)

theorem map_conj_eq_of_pRank_le_one [Finite G] {M Y K : Subgroup G} (hK : IsComponentOf K M)
    (hn : HasNoncentral3 K) (hKY : K ≤ Y)
    (hYK : ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom ≤ Y)
    (hr : CFSG.Assembly.pRank 3 Y ≤ 1) :
    ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom = K := by
  intro m hm
  by_contra hne
  rcases isComponentOf_eq_or_commute hK (isComponentOf_map_conj hK hm) with h | hcomm
  · exact hne h.symm
  · have := two_le_pRank_of_commuting hKY (hYK m hm) hcomm hn (hn.map_conj m)
    omega

end F918V5G

end CFSG.Quasithin
