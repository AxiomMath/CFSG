module

public import CFSG.Quasithin.H13.A5S132
public import CFSG.Quasithin.H13.NParamRootFourLift
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Comp

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_alt_five : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hnc : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup (alternatingGroup (Fin 5)) :=
      { (inferInstance : Group ↥(alternatingGroup (Fin 5))) with mul_comm := fun a b => h a b }
    have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 5))
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [h60] at hp
    exact absurd hp (by norm_num)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

omit [Finite G] in
theorem range_eq_top_of_not_isSolvable {X : Type*} [Group X]
    (f : X →* ↥(alternatingGroup (Fin 5))) (hker : Group.IsSolvable ↥f.ker)
    (hX : ¬ Group.IsSolvable X) : f.range = ⊤ := by
  by_contra h
  apply hX
  have hs : Group.IsSolvable ↥f.range :=
    SteinbergBM.alternating_five_proper_subgroup_solvable (by simp) (lt_top_iff_ne_top.mpr h)
  refine Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict ?_
  intro x hx
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker] at hx ⊢
  exact congrArg Subtype.val hx

theorem commutator_le_solvableRadical {H L K : Subgroup G} (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (hne : L ≠ K) : ⁅L, K⁆ ≤ (CFSG.solvableRadical ↥H).map H.subtype := by
  classical
  have hHL : L ≤ H := le_of_mem_cComp hL
  have hHK : K ≤ H := le_of_mem_cComp hK
  set N : Subgroup ↥H := CFSG.solvableRadical ↥H with hN
  have hNs : Group.IsSolvable N := A3.solvableRadical_isSolvable
  have hbij := cComp_quotient_bijOn N hNs
  have hL' : L.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hL
  have hK' : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  have hLc : (L.subgroupOf H).map (QuotientGroup.mk' N) ∈
      {X : Subgroup (↥H ⧸ N) | CFSG.IsComponent X} := by
    rw [← (cComp_part_five (G := ↥H)).1]
    exact hbij.mapsTo hL'
  have hKc : (K.subgroupOf H).map (QuotientGroup.mk' N) ∈
      {X : Subgroup (↥H ⧸ N) | CFSG.IsComponent X} := by
    rw [← (cComp_part_five (G := ↥H)).1]
    exact hbij.mapsTo hK'
  have hne' : (L.subgroupOf H).map (QuotientGroup.mk' N) ≠
      (K.subgroupOf H).map (QuotientGroup.mk' N) := by
    intro h
    apply hne
    have := hbij.injOn hL' hK' h
    rw [← Subgroup.map_subgroupOf_eq_of_le hHL, ← Subgroup.map_subgroupOf_eq_of_le hHK, this]
  have hcomm := (CFSG.LocalCores.distinct_components_commute hLc hKc).resolve_left hne'
  rw [Subgroup.commutator_le]
  intro l hl k hk
  have hl' : (⟨l, hHL hl⟩ : ↥H) ∈ L.subgroupOf H := hl
  have hk' : (⟨k, hHK hk⟩ : ↥H) ∈ K.subgroupOf H := hk
  have h1 : ⁅QuotientGroup.mk' N (⟨l, hHL hl⟩ : ↥H), QuotientGroup.mk' N (⟨k, hHK hk⟩ : ↥H)⁆ ∈
      ⁅(L.subgroupOf H).map (QuotientGroup.mk' N), (K.subgroupOf H).map (QuotientGroup.mk' N)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hl')
      (Subgroup.mem_map_of_mem _ hk')
  rw [hcomm, Subgroup.mem_bot] at h1
  have h2 : (⁅(⟨l, hHL hl⟩ : ↥H), (⟨k, hHK hk⟩ : ↥H)⁆ : ↥H) ∈ N := by
    have h3 : (QuotientGroup.mk' N) ⁅(⟨l, hHL hl⟩ : ↥H), (⟨k, hHK hk⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp h3
  exact ⟨_, h2, rfl⟩

end Comp

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem le_normalizer_of_cComp (h1222 : Stmt12_2_2) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥) : T ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hTH hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩
  obtain ⟨K', hK'⟩ := (Set.toFinite {X : Subgroup G | quasithinIsLocal T X ∧ K ≤ X}).exists_maximal
    ⟨K, hKloc, le_rfl⟩
  have hKK' : K ≤ K' := hK'.1.2
  have hK'max : quasithinIsMaximalLocal T K' :=
    ⟨hK'.1.1, fun X hX hK'X => le_antisymm (hK'.2 ⟨hX, hKK'.trans hK'X⟩ hK'X) hK'X⟩
  have hZK' : ⁅quasithinOmegaOneCenter T, K'⁆ ≠ ⊥ := fun h =>
    hZK (le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKK'))
  have hK'f : quasithinIsFaithfulLocal T K' :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hK'max.1 hZK'
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff K' _).1 (S.h13.a5 S.a5 K' hK'f)
  have hq : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_alt_five
  have hTK' : T ≤ Subgroup.normalizer (K' : Set G) := by
    rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
    · exact absurd h S.not_alt12_2_2
    · exact (h K' hK'max hK'f hq).1
  by_contra hTK
  obtain ⟨t, htT, htN⟩ := Set.not_subset.mp hTK
  set Kt : Subgroup G := conjSub t K with hKtdef
  have hKt : Kt ∈ cComp H := conjSub_mem_cComp_of_mem hKc (hTH htT)
  have hne : K ≠ Kt := by
    intro h
    apply htN
    refine E1.LiftS5.mem_normalizer_of_conj_le fun k hk => ?_
    rw [h]
    exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hKtK' : Kt ≤ K' := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_normalizer_iff.mp (hTK' htT) k).mp (hKK' hk)
  set Φ : ↥K' →* ↥(alternatingGroup (Fin 5)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K')) with hΦ
  have hΦker : Φ.ker = CFSG.pCore 2 ↥K' := by
    ext x
    simp [hΦ]
  have hsurj : ∀ X : Subgroup G, X ∈ cComp H → ∀ hX : X ≤ K', ∀ σ : alternatingGroup (Fin 5),
      ∃ x : ↥X, Φ (Subgroup.inclusion hX x) = σ := by
    intro X hXc hX σ
    have hker : Group.IsSolvable ↥(Φ.comp (Subgroup.inclusion hX)).ker := by
      rw [← MonoidHom.comap_ker, hΦker]
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K').comap (Subgroup.inclusion hX)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥K')).comap_of_injective _
          (Subgroup.inclusion_injective hX)
      have := hp.isNilpotent
      infer_instance
    have htop := range_eq_top_of_not_isSolvable _ hker (not_isSolvable_of_mem_cComp hXc)
    have hσ : σ ∈ (Φ.comp (Subgroup.inclusion hX)).range := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := hσ
    exact ⟨x, hx⟩
  have hcK' : ⁅K, Kt⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact K'.mul_mem (K'.mul_mem (K'.mul_mem (hKK' ha) (hKtK' hb)) (K'.inv_mem (hKK' ha)))
      (K'.inv_mem (hKtK' hb))
  have hcs : Group.IsSolvable ↥⁅K, Kt⁆ := by
    have hR : Group.IsSolvable ↥((CFSG.solvableRadical ↥H).map H.subtype) := by
      have : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) := A3.solvableRadical_isSolvable
      have h1 : Group.IsSolvable ↥((H.subtype.comp (CFSG.solvableRadical ↥H).subtype).range) :=
        Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
      rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (commutator_le_solvableRadical hKc hKt hne))
  set g : ↥⁅K, Kt⁆ →* ↥(alternatingGroup (Fin 5)) := Φ.comp (Subgroup.inclusion hcK') with hg
  have hgsurj : Function.Surjective g := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← commutator_alternatingGroup_eq_top (α := Fin 5) (by simp),
      commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨x, rfl⟩ := hsurj K hKc hKK' a
    obtain ⟨y, rfl⟩ := hsurj Kt hKt hKtK' b
    refine ⟨⟨⁅(x : G), (y : G)⁆, Subgroup.commutator_mem_commutator x.2 y.2⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, ← map_commutatorElement]
    rfl
  exact E1.LiftS5.not_isSolvable_alt (Group.isSolvable_of_surjective hgsurj)

end Setting

@[expose] def Res1328a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : Setting G T L V)
    (H K : Subgroup G), IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → K ∈ cComp H →
    H = K ⊔ T → T ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
    E1.LiftS5.RootFourLiftQuot T K

end CFSG.Quasithin.H13.A5
