module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223JCount
public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot
public import CFSG.Quasithin.EmptyFaithful.Der6DAux
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCrit
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

variable {G : Type} [Group G] [Finite G]

structure P4Fact (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I X : Subgroup G) : Prop where
  theta : thetaOf I = X
  K_le : oTwoUpper H ≤ X
  X_normal : I ≤ Subgroup.normalizer (X : Set G)
  sylow : IsSylowTwoOf (sOf152 T Mc M B₀ ⊓ X) X
  K_inf_M : IsPGroup 2 ↥(oTwoUpper H ⊓ M)
  card_Y : Nat.card ↥(oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X)) =
    9 * Nat.card ↥(sOf152 T Mc M B₀ ⊓ X)
  solv_Y : Group.IsSolvable ↥(oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X))
  rank_Y : CFSG.Open.pRank 3 (oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) : Subgroup G) = 2
  Y_le : oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤
    X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace P4Ctx

theorem sylowH (c : P4Ctx T Mc M H B₀ I X) : IsSylowTwoOf T H :=
  S152N.isSylowTwoOf_hStar c.setting c.hstar

theorem pow_three_of_odd (c : P4Ctx T Mc M H B₀ I X) {x : G} (hx : x ∈ oTwoUpper H)
    (hodd : Odd (orderOf x)) : x ^ 3 = 1 := by
  obtain ⟨φ⟩ := c.quotH
  have h1 : x ^ 3 ∈ pCoreOf 2 H := C1Pack12.pow_three_mem_pCoreOf φ hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨x ^ 3, h1⟩
  have hj' : (x ^ 3) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hr : (x ^ 3) ^ orderOf x = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hcop : Nat.Coprime (2 ^ j) (orderOf x) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have hd : orderOf (x ^ 3) ∣ Nat.gcd (2 ^ j) (orderOf x) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hr)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem K_le_theta (c : P4Ctx T Mc M H B₀ I X) : oTwoUpper H ≤ thetaOf I := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hx.1 hx.2
  have h3 := c.pow_three_of_odd hxK hx.2
  by_cases h1 : x = 1
  · rw [h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨c.K_le_I hxK, orderOf_eq_prime h3 h1⟩

theorem relIndex_K (c : P4Ctx T Mc M H B₀ I X) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
  obtain ⟨φ⟩ := c.quotH
  exact C1Pack12.relIndex_pCoreOf_oTwoUpper φ

theorem A_le_T (_c : P4Ctx T Mc M H B₀ I X) : sOf152 T Mc M B₀ ⊓ X ≤ T :=
  inf_le_left.trans S_le_T152

theorem A_isPGroup (c : P4Ctx T Mc M H B₀ I X) : IsPGroup 2 ↥(sOf152 T Mc M B₀ ⊓ X) :=
  c.setting.qtfe.sylow.1.to_le c.A_le_T

theorem A_le_normalizer_K (c : P4Ctx T Mc M H B₀ I X) :
    sOf152 T Mc M B₀ ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  c.A_le_T.trans (c.sylowH.1.trans (le_normalizer_oTwoUpper H))

theorem K_inf_A (c : P4Ctx T Mc M H B₀ I X) (hK : oTwoUpper H ≤ X) :
    oTwoUpper H ⊓ (sOf152 T Mc M B₀ ⊓ X) = pCoreOf 2 (oTwoUpper H) := by
  obtain ⟨φ⟩ := c.quotH
  have hpK := S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  apply le_antisymm
  · intro y hy
    rw [hpK]
    exact ⟨hy.1, Der6D.inf_le_pCoreOf' c.sylowH φ hy.1 (c.A_le_T hy.2)⟩
  · intro y hy
    have hyK : y ∈ oTwoUpper H := pCoreOf_le 2 (oTwoUpper H) hy
    have hyP : y ∈ pCoreOf 2 H := ((hpK ▸ hy : y ∈ oTwoUpper H ⊓ pCoreOf 2 H)).2
    have hyT : y ∈ T := c.sylowH.pCoreOf_le hyP
    have hyS : y ∈ sOf152 T Mc M B₀ := by
      rw [← inf_T_I152 c.setting c.hstar c.min.1 c.inputs]
      exact ⟨hyT, c.K_le_I hyK⟩
    exact ⟨hyK, hyS, hK hyK⟩

theorem card_K_sup_A (c : P4Ctx T Mc M H B₀ I X) (hK : oTwoUpper H ≤ X) :
    Nat.card ↥(oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X)) =
      9 * Nat.card ↥(sOf152 T Mc M B₀ ⊓ X) := by
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    c.A_le_normalizer_K
  rw [c.K_inf_A hK] at hcard
  have hK9 : Nat.card ↥(oTwoUpper H) = Nat.card ↥(pCoreOf 2 (oTwoUpper H)) * 9 := by
    rw [card_eq_card_pCoreOf_mul_relIndex (oTwoUpper H), c.relIndex_K]
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (oTwoUpper H)) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hcard, hK9]
  ring

theorem exists_E9 (c : P4Ctx T Mc M H B₀ I X) :
    ∃ E : Subgroup G, E ≤ oTwoUpper H ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  obtain ⟨φ⟩ := c.quotH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPH, hP9⟩ := He4.exists_subgroup_card_nine (pCoreOf_isPGroup 2 H)
    (S15223.card_H φ)
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hPK : P ≤ oTwoUpper H := He4.le_oTwoUpper_of_isPGroup_three hPH hP3
  refine ⟨P, hPK, ⟨?_, fun x hx => ?_⟩, by rw [hP9]; norm_num⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP9]; norm_num)
  · obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf x) := by
      have hd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
    exact c.pow_three_of_odd (hPK hx) hodd

end P4Ctx

theorem P4Ctx.facts (hθ : ThetaEqComponent) (c : P4Ctx T Mc M H B₀ I X)
    (hr : CFSG.Open.pRank 3 (X : Subgroup G) = 2) (hty : IsRankTwoListType X) :
    P4Fact T Mc M H B₀ I X := by
  have htheta : thetaOf I = X := hθ G I X c.hyp.sqtk c.comp c.quasi hr hty
  have hKX : oTwoUpper H ≤ X := htheta ▸ c.K_le_theta
  have hAX : sOf152 T Mc M B₀ ⊓ X ≤ X := inf_le_right
  have hY_le : oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤
      X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) :=
    sup_le (le_inf hKX c.K_le_centralizer)
      (le_inf inf_le_right (inf_le_left.trans c.S_le_centralizer))
  have hcard := c.card_K_sup_A hKX
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp c.A_isPGroup
  refine ⟨htheta, hKX, ?_, S153D.isSylowTwoOf_inf_of_isSubnormal
    (subnormal_of_mem_cComp c.comp) c.sylow, ?_, hcard, ?_, ?_, hY_le⟩
  · intro g hg
    have := S153D.normalizer_le_normalizer_thetaOf I (Subgroup.le_normalizer hg)
    rwa [htheta] at this
  · refine c.setting.qtfe.sylow.1.to_le (fun x hx => ?_)
    have h := c.inputs.hN.eq_inf
    rw [h]
    exact ⟨hx.2, oTwoUpper_le H hx.1⟩
  · exact E6.Spor.isSolvable_of_card_two_pow_mul_three_pow (a := a) (b := 2)
      (by rw [hcard, ha]; ring)
  · apply le_antisymm
    · exact CFSG.SectionRank.pRank_mono (by norm_num) (hY_le.trans inf_le_left) |>.trans hr.le
    · obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
      exact le_pRank Nat.prime_three (hEK.trans le_sup_left) hE hE9

end S15223P4

end CFSG.Quasithin
