module

public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.A4Bridge
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G]

theorem eq_oTwoUpper_of_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) : L = oTwoUpper L := by
  rw [eq_oTwoUpper_iff_forall_normal]
  intro N hNL hN hpow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (N.subgroupOf L).Normal := hN
  have hp : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  have hnil : Group.IsNilpotent (↥L ⧸ N.subgroupOf L) := hp.isNilpotent
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  by_contra hne
  have hne' : N.subgroupOf L ≠ ⊤ := fun h => hne (le_antisymm hNL (Subgroup.subgroupOf_eq_top.mp h))
  have : Nontrivial (↥L ⧸ N.subgroupOf L) := QuotientGroup.nontrivial_iff.mpr hne'
  exact Group.IsPerfect.not_isSolvable (G := ↥L ⧸ N.subgroupOf L) inferInstance

theorem isFaithfulLocal_iff_isXf {T L : Subgroup G} :
    quasithinIsFaithfulLocal T L ↔ quasithinIsLocal T L ∧ IsXf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hloc, hO2, hFs, hV⟩
    refine ⟨hloc, ⟨hloc.2.1.1, (eq_oTwoUpper_iff_forall_normal L).mpr hO2, ?_⟩, hV⟩
    exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mp hFs
  · rintro ⟨hloc, ⟨-, hO2, hF⟩, hV⟩
    exact ⟨hloc, (eq_oTwoUpper_iff_forall_normal L).mp hO2,
      (quasithinGenFitting_eq_pCoreOf_iff L 2).mpr hF, hV⟩

theorem isSylowTwoOf_of_sylow_le (T : Sylow 2 G) {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) :
    IsSylowTwoOf (T : Subgroup G) H :=
  isSylowTwoOf_of_quasithinIsSylowTwo ⟨T.isPGroup', T.not_dvd_index⟩ hTH

theorem isFaithfulLocal_of_commutator_ne_bot (hEven : quasithinEvenCharacteristic G)
    (T : Sylow 2 G) {H L V : Subgroup G} (hH : InH (T : Subgroup G) H) (hL : L ∈ cComp H)
    (hV : IsTwoReducedIn H V) (hne : ⁅V, L⁆ ≠ ⊥) : quasithinIsFaithfulLocal (T : Subgroup G) L := by
  refine isFaithfulLocal_iff_isXf.mpr
    ⟨isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_sylow_le T hH.1) hH.2 hL, ?_⟩
  exact A4.isXf_of_isTwoReducedIn (charTwo_of_inH hEven T hH)
    (eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hL)) (subnormal_of_mem_cComp hL) hV hne

theorem lemma_1_2_10 (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {H L : Subgroup G}
    (hH : InH (T : Subgroup G) H) (hL : L ∈ cComp H) (hchief : NoncentralTwoChiefFactorsInO2 L) :
    List.TFAE [quasithinIsFaithfulLocal (T : Subgroup G) L,
      ∃ V, IsTwoReducedIn H V ∧ ⁅V, L⁆ ≠ ⊥, ⁅twoReducedJoin H, L⁆ ≠ ⊥] := by
  have hloc : quasithinIsLocal (T : Subgroup G) L :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_sylow_le T hH.1) hH.2 hL
  have h411 := a4_11 (charTwo_of_inH hEven T hH) (eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hL))
    (subnormal_of_mem_cComp hL) hchief
  have hiff : quasithinIsFaithfulLocal (T : Subgroup G) L ↔ IsXf L :=
    ⟨fun h => (isFaithfulLocal_iff_isXf.mp h).2, fun h => isFaithfulLocal_iff_isXf.mpr ⟨hloc, h⟩⟩
  tfae_have 1 ↔ 2 := by
    rw [hiff]
    exact h411.out 1 2
  tfae_have 2 ↔ 3 := h411.out 2 3
  tfae_finish

end CFSG.Quasithin
