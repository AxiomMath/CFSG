module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.Vol2.Ch3E213MOLB10
public import CFSG.Quasithin.Vol2.Ch3E213MOL3

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem card_zOf_eq {X : Type} [Group X] {K S : Subgroup X} (hSK : S ≤ K) :
    Nat.card ↥(E2P.zOf S) = Nat.card ↥(E2P.zOf (S.subgroupOf K)) := by
  have hmap : (E2P.zOf (S.subgroupOf K)).map K.subtype = E2P.zOf S := by
    ext x
    simp only [Subgroup.mem_map, E2P.zOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, ⟨hyS, hyc⟩, rfl⟩
      refine ⟨hyS, fun h hh => ?_⟩
      have := hyc ⟨h, hSK hh⟩ hh
      exact congrArg Subtype.val this
    · rintro ⟨hxS, hxc⟩
      refine ⟨⟨x, hSK hxS⟩, ⟨hxS, fun h hh => ?_⟩, rfl⟩
      exact Subtype.ext (hxc h.1 hh)
  rw [← hmap, Subgroup.card_subtype]

theorem exists_sylow_of_isSylowTwoOf {X : Type} [Group X] {K S : Subgroup X}
    (h : IsSylowTwoOf S K) : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = S.subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsPGroup.toSylow (h.2.1.comap_subtype) h.2.2, rfl⟩

theorem isSylowTwoOf_top {X : Type} [Group X] {K S : Subgroup X}
    (h : IsSylowTwoOf S K) : IsSylowTwoOf (S.subgroupOf K) ⊤ := by
  refine ⟨le_top, h.2.1.comap_subtype, ?_⟩
  have : ((S.subgroupOf K).subgroupOf ⊤).index = (S.subgroupOf K).index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [this]
  exact h.2.2

theorem center_eq_bot_of_isPSL_three_three {K : Type} [Group K] (h : IsPSL 3 3 1 K) :
    Subgroup.center K = ⊥ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hsimp : IsSimpleGroup K :=
    CFSG.Quasithin.Ch3E213M.OL.isSimpleGroup_of_L3U3 hp le_rfl (Or.inr h)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
    have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 3) (by norm_num)
      (Or.inl le_rfl)
    have hKperf : Group.IsPerfect K :=
      Group.IsPerfect.ofSurjective (G := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
        (f := ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).trans
          e.symm).toMonoidHom) ((MulEquiv.surjective _))
    have hc := hKperf.commutator_eq_top
    rw [(commutator_eq_bot_iff_center_eq_top K).mpr h0] at hc
    have := hsimp.toNontrivial
    exact bot_ne_top hc


theorem f0_holds :
    ∀ (X : Type) [Group X] [Finite X] (K S : Subgroup X) (p : ℕ), p.Prime → p ≠ 2 →
      IsL3U3 p ↥K → IsSylowTwoOf S K → Nat.card ↥(E2P.zOf S) = 2 := by
  intro X _ _ K S p hp hp2 hK hS
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hS
  rw [card_zOf_eq hS.1]
  by_cases hp3 : p = 3
  · subst hp3
    have hL : IsPSL 3 3 1 ↥K := by
      rcases hK with ⟨h4, _⟩ | ⟨_, h⟩
      · omega
      · exact h
    have hS' := isSylowTwoOf_top hS
    obtain ⟨Q, hQ⟩ := exists_sylow_of_isSylowTwoOf hS'
    have hLtop : IsPSL 3 3 1 ↥(⊤ : Subgroup ↥K) := IsPSL.of_mulEquiv Subgroup.topEquiv.symm hL
    have hcen : Subgroup.centralizer ((⊤ : Subgroup ↥K) : Set ↥K) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ]
      exact center_eq_bot_of_isPSL_three_three hL
    obtain ⟨z, hz, hzS, -⟩ := CFSG.Quasithin.Ch3E213M.OLB.kFactL33NoQuadFour_holds ↥K ⊤
      Subgroup.normal_top hLtop hcen Q
    rw [hQ] at hzS
    rw [card_zOf_eq (le_top : S.subgroupOf K ≤ ⊤)]
    rw [hzS, Nat.card_zpowers, hz]
  · have hp5 : 5 ≤ p := by
      have h3 := hp.two_le
      have : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    obtain ⟨z, hz, hzS, -⟩ := CFSG.Quasithin.Ch3E213M.OLA.kFactL3U3OuterInv_holds ↥K p hp hp5 hK P
    rw [hP] at hzS
    rw [hzS, Nat.card_zpowers, hz]
