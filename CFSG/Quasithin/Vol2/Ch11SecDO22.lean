module

import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mem_oTwoTwoPrime_iff {K : Subgroup G} (y : ↥K) :
    (y : G) ∈ oTwoTwoPrime K ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) y ∈ CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K) := by
  unfold oTwoTwoPrime preimageModTwoCore
  constructor
  · rintro ⟨y', hy', hyy'⟩
    rwa [Subtype.ext hyy'] at hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem oTwoTwoPrime_le (K : Subgroup G) : oTwoTwoPrime K ≤ K :=
  Subgroup.map_subtype_le _

theorem pCoreOf_subgroupOf (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

theorem pCoreOf_le_oTwoTwoPrime (K : Subgroup G) : pCoreOf 2 K ≤ oTwoTwoPrime K := by
  rintro _ ⟨y, hy, rfl⟩
  show (y : G) ∈ oTwoTwoPrime K
  rw [mem_oTwoTwoPrime_iff]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
  exact Subgroup.one_mem _

variable [Finite G]

theorem odd_card_oddCore (X : Type) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) :=
  CFSG.ComponentClassification.OddCore.odd_card X

theorem mem_pCoreOf_of_mem_oTwoTwoPrime {K : Subgroup G} {x : G} (hx : x ∈ oTwoTwoPrime K)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hodd := odd_card_oddCore (↥K ⧸ CFSG.pCore 2 ↥K)
  have h1 : (⟨π y, hy⟩ : ↥(CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K))) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    have : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hord : orderOf (⟨π y, hy⟩ : ↥(CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K))) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))) (orderOf_dvd_natCard _)
  have h2 : π y = 1 := by
    have := orderOf_eq_one_iff.mp hord
    simpa using congrArg Subtype.val this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨y, h2, rfl⟩

theorem le_pCoreOf_of_le_oTwoTwoPrime {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSP : S ≤ oTwoTwoPrime K) : S ≤ pCoreOf 2 K := fun x hx => by
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  exact mem_pCoreOf_of_mem_oTwoTwoPrime (hSP hx) (k := k)
    (by simpa using congrArg Subtype.val hk)

theorem odd_relIndex_oTwoTwoPrime (K : Subgroup G) :
    ¬ 2 ∣ (pCoreOf 2 K).relIndex (oTwoTwoPrime K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oTwoTwoPrime K with hP
  set Q := pCoreOf 2 K with hQ
  have hQ2 : IsPGroup 2 (Q.subgroupOf P) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCoreOf_le_oTwoTwoPrime K)).symm
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hSQ : (S : Subgroup ↥P).map P.subtype ≤ Q :=
    le_pCoreOf_of_le_oTwoTwoPrime (S.isPGroup'.map _) (Subgroup.map_subtype_le _)
  have hSeq : (S : Subgroup ↥P) = Q.subgroupOf P := le_antisymm (fun x hx => by
    have := hSQ ⟨x, hx, rfl⟩
    exact this) hS
  have := S.not_dvd_index
  rwa [hSeq] at this

theorem isSolvable_oTwoTwoPrime (K : Subgroup G) : Group.IsSolvable ↥(oTwoTwoPrime K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oTwoTwoPrime K with hP
  set Q := pCoreOf 2 K with hQ
  have hQP : Q ≤ P := pCoreOf_le_oTwoTwoPrime K
  have : (Q.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    ((oTwoTwoPrime_le K).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
  have hQ2 : IsPGroup 2 (Q.subgroupOf P) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have : Group.IsNilpotent ↥(Q.subgroupOf P) := hQ2.isNilpotent
  have : Group.IsSolvable (↥P ⧸ Q.subgroupOf P) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (odd_relIndex_oTwoTwoPrime K))
  exact Group.isSolvable_of_ker_le_range (Q.subgroupOf P).subtype
    (QuotientGroup.mk' (Q.subgroupOf P)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

omit [Finite G] in
theorem normalizer_le_normalizer_oTwoTwoPrime (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoTwoPrime K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oTwoTwoPrime K,
      g * x * g⁻¹ ∈ oTwoTwoPrime K := by
    intro g hg x hx
    have hgK : ∀ a ∈ K, g * a * g⁻¹ ∈ K := fun a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hgK' : ∀ a ∈ K, g⁻¹ * a * g ∈ K := fun a ha => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) a).mp ha
      simpa using this
    let c : ↥K ≃* ↥K :=
      { toFun := fun a => ⟨g * a * g⁻¹, hgK a a.2⟩
        invFun := fun a => ⟨g⁻¹ * a * g, hgK' a a.2⟩
        left_inv := fun a => Subtype.ext (by simp [mul_assoc])
        right_inv := fun a => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hc : (CFSG.pCore 2 ↥K).map c.toMonoidHom = CFSG.pCore 2 ↥K :=
      Subgroup.characteristic_iff_map_eq.mp
        (by exact CFSG.LieType.BorelTits.pCore_characteristic 2) c
    let cb := QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) c hc
    have hX : (CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K)).map cb.toMonoidHom =
        CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Subgroup.characteristic_iff_map_eq.mp
        (CFSG.ComponentClassification.OddCore.characteristic _) cb
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (c y) ∈
        CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [← hX]
      exact ⟨_, hy, rfl⟩
    exact (mem_oTwoTwoPrime_iff (c y)).mpr hy'
  intro g hg
  refine mem_normalizer_of_conj (key g hg) (fun x hx => ?_)
  have := key g⁻¹ (Subgroup.inv_mem _ hg) x hx
  simpa using this

end CFSG.Quasithin.Vol2.Ch11.SecD
