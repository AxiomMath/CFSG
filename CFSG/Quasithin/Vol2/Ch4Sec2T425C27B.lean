module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases
public import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27

variable {G : Type} [Group G] [Finite G]

structure Ctx (H R M K J : Subgroup G) : Prop extends Hyp27 H R M K where
  J_le : J ≤ M ⊓ K
  J_norm : M ⊓ K ≤ Subgroup.normalizer (J : Set G)
  nonsolv : ¬ Group.IsSolvable J
  rank : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card J → CFSG.Open.pRank p K ≤ 1

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J)
include c

theorem J_le_K : J ≤ K := c.J_le.trans inf_le_right

theorem J_le_normalizer :
    J ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
  c.J_le_K.trans (le_sup_left.trans (le_normalizer_omegaOneCenterOf_pCoreOf (K ⊔ R)))

variable (hC27 : ASC27Statement G)
include hC27

theorem c27_one :
    pCoreOf 2 (K ⊔ R) ≤
        (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
        pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  (hC27 H R M K _ c.hyp c.comp c.quasi c.charTwo c.not_le c.norm rfl).1

theorem cases : SBc17.C27Cases H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  SBc17.asc27_cases hC27 c.hyp c.comp c.quasi c.charTwo c.not_le c.norm rfl

theorem star : StarHyp R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  ⟨c.norm, c.toHyp27.isPGroup, c.quasi, (c.c27_one hC27).2.2, (c.c27_one hC27).2.1,
    c.toHyp27.pCoreOf_sup_le, c.toHyp27.not_le_centralizer⟩

theorem isSolvable_of_autOn
    (h : Group.IsSolvable (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) :
    Group.IsSolvable J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  set f := InternalSec.autOnHom c.J_le_normalizer with hf
  have hJK := c.J_le_K
  let ι : ↥f.ker →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp
      ((Subgroup.inclusion hJK).comp f.ker.subtype)
  have hcen : ∀ j : ↥f.ker, ι j ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro j
    have hjC : ((j : ↥J) : G) ∈ Subgroup.centralizer (V : Set G) :=
      (InternalSec.mem_ker_autOnHom c.J_le_normalizer _).mp j.2
    have hjZ := (c.star hC27).inf_centralizer_le ⟨hJK (j : ↥J).2, hjC⟩
    obtain ⟨y, hy, hye⟩ := hjZ
    have hy' : y = Subgroup.inclusion hJK (j : ↥J) := Subtype.ext hye
    rw [hy'] at hy
    exact hy
  let ι' : ↥f.ker →* ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := ι.codRestrict _ hcen
  have hZs : Group.IsSolvable ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have hker : Group.IsSolvable ↥f.ker := by
    refine isSolvable_of_ker ι' ?_
    have hp : IsPGroup 2 ↥ι'.ker := by
      intro z
      have hz1 : ι z = 1 := congrArg Subtype.val z.2
      have hzO : Subgroup.inclusion hJK ((z : ↥f.ker) : ↥J) ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff _).mp hz1
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, hzO⟩
      refine ⟨n, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
      simpa using congrArg (fun w : ↥(CFSG.pCore 2 ↥K) => ((w : ↥K) : G)) hn
    have : Group.IsNilpotent ↥ι'.ker := hp.isNilpotent
    infer_instance
  exact isSolvable_of_ker f hker

theorem not_isSolvable_autOn :
    ¬ Group.IsSolvable (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :=
  fun h => c.nonsolv (c.isSolvable_of_autOn hC27 h)

theorem not_le_of_isSolvable {X : Subgroup (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))}
    (hX : Group.IsSolvable X) (hJX : autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤ X) :
    False :=
  c.not_isSolvable_autOn hC27
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJX)
      (Subgroup.inclusion_injective _))

omit hC27 in
theorem card_autOn_dvd :
    Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∣ Nat.card J :=
  ⟨_, card_eq_card_autOn_mul c.J_le_normalizer⟩

theorem false_of_two_three
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) →
      r = 2 ∨ r = 3) : False :=
  c.not_isSolvable_autOn hC27 (isSolvable_of_prime_dvd Nat.prime_two Nat.prime_three h)

theorem three_dvd {s : ℕ} (hs : s.Prime)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) →
      r = 2 ∨ r = 3 ∨ r = s) :
    3 ∣ Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) := by
  by_contra h3
  refine c.not_isSolvable_autOn hC27 (isSolvable_of_prime_dvd Nat.prime_two hs fun r hr hrd => ?_)
  rcases h r hr hrd with h2 | h3' | hrs
  · exact Or.inl h2
  · exact absurd (h3' ▸ hrd) h3
  · exact Or.inr hrs

omit hC27 in
theorem rank_three (h3 : 3 ∣ Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) :
    CFSG.Open.pRank 3 K ≤ 1 :=
  c.rank 3 Nat.prime_three (by norm_num) (h3.trans c.card_autOn_dvd)

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
