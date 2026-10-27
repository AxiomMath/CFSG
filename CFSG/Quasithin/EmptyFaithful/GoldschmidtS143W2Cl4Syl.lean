module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompX
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem isSylowTwoOf_Tw_inf_comp (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x)) : IsSylowTwoOf (Tw T d x ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal h.hSyl hL.1 (normalizer_of_component h hf hL)

theorem card_Tw_inf_comp (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x))
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1) :
    Nat.card ↥(Tw T d x ⊓ L) = 32 := by
  have hS := isSylowTwoOf_Tw_inf_comp h hf hL
  obtain ⟨h1, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound ↥L 3 3 1 hmod
  have hcard : Nat.card ↥L = 6048 := by
    have h2 : (Nat.card ↥L : ℤ) = 6048 := by
      have h' := h1
      norm_num [Finset.prod_Icc_succ_top] at h'
      omega
    exact_mod_cast h2
  obtain ⟨n, hn⟩ := hS.2.1.exists_card_eq
  have hprod : Nat.card ↥(Tw T d x ⊓ L) * ((Tw T d x ⊓ L).subgroupOf L).index = 6048 := by
    have h3 := Subgroup.card_mul_index ((Tw T d x ⊓ L).subgroupOf L)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hcard] at h3
  have hodd := hS.2.2
  have hpos : 0 < ((Tw T d x ⊓ L).subgroupOf L).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hn] at hprod ⊢
  have hle : 2 ^ n ≤ 6048 := by
    rw [← hprod]
    exact Nat.le_mul_of_pos_right _ hpos
  have hn13 : n < 13 := by
    by_contra hge
    have : 2 ^ 13 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hge)
    omega
  interval_cases n <;> omega

end InspW2

end S143

end CFSG.Quasithin
