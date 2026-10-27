module

public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.S153D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S1417

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_central_two_power {L : Subgroup G} {z : ↥L ⧸ CFSG.pCore 2 ↥L}
    (hz : z ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) {a : ℕ} (ha : z ^ 2 ^ a = 1) : z = 1 := by
  have hN : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let P : Subgroup ↥L := (Subgroup.zpowers z).comap π
  have hnormZ : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : z ^ k ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.zpow_mem _ hz k
    have h := Subgroup.mem_center_iff.mp hc g
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers z k⟩
  have hPn : P.Normal := hnormZ.comap π
  have hPp : IsPGroup 2 P := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : π (x ^ 2 ^ a) = 1 := by
      rw [map_pow]
      have hk' : π x = z ^ k := hk.symm
      rw [hk', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have h2 : x ^ 2 ^ a ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (G := ↥L) (p := 2) ⟨x ^ 2 ^ a, h2⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hle : P ≤ CFSG.pCore 2 ↥L := by
    exact CFSG.LieType.BorelTits.le_pCore 2 hPn hPp
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  exact (QuotientGroup.eq_one_iff l).mpr (hle (Subgroup.mem_zpowers _))

theorem sqtkGroup_quot_pCore {X : Type} [Group X] [Finite X] (hX : SQTKGroup X) :
    SQTKGroup (X ⧸ CFSG.pCore 2 X) :=
  ⟨sqt_quotient_two_group hX.1 (CFSG.pCore 2 X) CFSG.pCore_isPGroup, kGroup_quotient hX.2 _⟩

theorem nonempty_quot_mulEquiv_autOn (hcover : AsA36NoOddCover) {L W : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G)) (hH : IsL345Type ↥(autOn L W)) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L W)) := by
  have hcent := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
    (exists_autOnQuot_ne_one hLN hker hnt)
  have hodd : ∀ x ∈ (autOnQuot hLN hker).ker, Odd (orderOf x) := by
    intro x hx
    have hxc : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hcent hx
    by_contra hnodd
    obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp hnodd
    have hpos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
    have hc0 : 0 < c := by omega
    have hy2 : (x ^ c) ^ 2 ^ 1 = 1 := by
      rw [← pow_mul, pow_one]
      have : c * 2 = orderOf x := by omega
      rw [this, pow_orderOf_eq_one]
    have hy : x ^ c = 1 := eq_one_of_central_two_power (Subgroup.pow_mem _ hxc c) hy2
    have hd := Nat.le_of_dvd hc0 (orderOf_dvd_of_pow_eq_one hy)
    omega
  have hinj : Function.Injective (autOnQuot hLN hker) :=
    hcover _ _ hq hsq (autOnQuot hLN hker) (autOnQuot_surjective hLN hker) hodd hH
  exact ⟨MulEquiv.ofBijective (autOnQuot hLN hker) ⟨hinj, autOnQuot_surjective hLN hker⟩⟩

end CFSG.Quasithin.S153D
