module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5b
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12Stmt

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_self {Q : Subgroup G} (h : Group.IsPerfect ↥Q) : ⁅Q, Q⁆ = Q := by
  have h1 := Group.isPerfect_def.mp h
  rw [commutator_def] at h1
  calc ⁅Q, Q⁆ = (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q).map Q.subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (⊤ : Subgroup ↥Q).map Q.subtype := by rw [h1]
    _ = Q := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem le_of_relIndex_eq_two {H M L : Subgroup G} (hMH : M ≤ H) (hθ : L = thetaOf M)
    (hM : M = H ⊓ Subgroup.normalizer (L : Set G)) (h2 : M.relIndex H = 2) : H ≤ M := by
  intro g hg
  have hn : (M.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two h2
  have hconj : ∀ x ∈ M, g * x * g⁻¹ ∈ M := by
    intro x hx
    have := hn.conj_mem ⟨x, hMH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    conv_lhs => rw [hθ]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxM, hx3⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, hθ]
    refine Subgroup.subset_closure ⟨hconj x hxM, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hx3
  have heq : L.map (MulAut.conj g).toMonoidHom = L := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  rw [hM]
  exact ⟨hg, hgN⟩

omit [Finite G] in
theorem mem_centerOf {K : Subgroup G} {t : G} (hK : K ≤ Subgroup.centralizer ({t} : Set G))
    (ht : t ∈ K) : t ∈ centerOf K := by
  refine ⟨ht, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hK hk)

variable {T L V : Subgroup G} {t : G}

namespace D127

variable (d : D127 G T L V t)
include d

theorem hypC28 (h12212 : Stmt12_2_12) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))) :
    HypC28 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) (Lt L t) V := by
  obtain ⟨-, h2⟩ := h12212 G T L V d.hyp.hyp t d.mem d.ne_one hsyl (d.pCoreOf_autOn_eq_bot hTV)
  have hLtN := d.lt_le_normalizer
  have hperf : autOn (Lt L t) V = perfectCore (autOn (Lt L t) V) := by
    have hp : Group.IsPerfect ↥(autOn (Lt L t) V) := by
      have hs : Function.Surjective
          (((conjAct V).comp (Subgroup.inclusion hLtN)).rangeRestrict) :=
        MonoidHom.rangeRestrict_surjective _
      have hr : ((conjAct V).comp (Subgroup.inclusion hLtN)).range = autOn (Lt L t) V := by
        ext φ
        rw [A4.mem_autOn_iff hLtN]
        exact ⟨fun ⟨l, hl⟩ => ⟨l, hl⟩, fun ⟨l, hl⟩ => ⟨l, hl⟩⟩
      have := d.perfect
      have := Group.IsPerfect.ofSurjective hs
      rwa [hr] at this
    exact (perfectCore_eq_self_of_perfect (commutator_eq_self hp)).symm
  have h := h2 hperf d.comm_eq
  rwa [perfectCore_eq_self_of_perfect (commutator_eq_self d.perfect)] at h

end D127

end CFSG.Quasithin.H13.S127.L5
