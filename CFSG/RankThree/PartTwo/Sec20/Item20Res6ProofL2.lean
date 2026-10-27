module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofCover
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KFactL2PerfectSelfNormalizing : Prop :=
  ∀ (m : ℕ) (Y : Type) [Group Y] [Finite Y],
    Nonempty (Y ≃* projSL 2 (GaloisField 2 m)) →
    ∀ K : Subgroup Y, K ≠ ⊤ → K ≠ ⊥ → Group.IsPerfect K →
      Subgroup.normalizer (K : Set Y) = K

@[expose] def Step204FinalL2Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
          ¬ yTwenty X c ⊓ M ≤ kTwenty M c ⊔ oThreePrimeYR M X T c

theorem step204FinalL2_of (hKF : KFactL2PerfectSelfNormalizing) (hYK : Step204YAlphaNe)
    (hZ : Step204FinalL2Z) : Step204FinalL2 := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm ⟨m, ⟨e⟩⟩
  apply hZ G A M L N c T i j P hset X hX hXM hm ⟨m, ⟨e⟩⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set W := Y ⊔ R with hW
  set O' := oThreePrimeYR M X T c with hO'
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hKW : K ≤ W := hKY.trans le_sup_left
  have hYW : Y ≤ W := le_sup_left
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hc := Res6.orderOf_c_of_setting204 hset
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W) with hπ
  set Yb := yAlpha M X T c with hYb
  have hYbdef : Yb = (Y.subgroupOf W).map π := rfl
  set Kb := (K.subgroupOf W).map π with hKb
  have hKbY : Kb ≤ Yb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hKY (Subgroup.mem_subgroupOf.mp hx))
  have hpull : ∀ w : ↥W, π w ∈ Kb → (w : G) ∈ K ⊔ O' := by
    intro w hw
    obtain ⟨k, hk, hkw⟩ := hw
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkw
    have hO : ((k⁻¹ * w : ↥W) : G) ∈ O' := ⟨_, hkw, rfl⟩
    have e1 : (w : G) = (k : G) * ((k⁻¹ * w : ↥W) : G) := by
      simp
    rw [e1]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) hO
  set Kb' : Subgroup ↥Yb := Kb.subgroupOf Yb with hKb'
  have hKb'top : Kb' ≠ ⊤ := by
    intro htop
    apply hYK G A M L N c T i j P hset X hX hXM hm
    intro y hy
    have hyb : π ⟨y, hYW hy⟩ ∈ Yb := ⟨⟨y, hYW hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have : (⟨π ⟨y, hYW hy⟩, hyb⟩ : ↥Yb) ∈ Kb' := by rw [htop]; exact Subgroup.mem_top _
    exact hpull ⟨y, hYW hy⟩ (Subgroup.mem_subgroupOf.mp this)
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcb : π ⟨c, hKW hcK⟩ ∈ Kb := ⟨⟨c, hKW hcK⟩, Subgroup.mem_subgroupOf.mpr hcK, rfl⟩
  have hKb'bot : Kb' ≠ ⊥ := by
    intro hbot
    have hmem : (⟨π ⟨c, hKW hcK⟩, hKbY hcb⟩ : ↥Yb) ∈ Kb' := Subgroup.mem_subgroupOf.mpr hcb
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : π ⟨c, hKW hcK⟩ = 1 := congrArg Subtype.val hmem
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcO : c ∈ O' := ⟨_, h1, rfl⟩
    have hdvd : orderOf c ∣ Nat.card O' := by
      rw [← Subgroup.orderOf_mk c hcO]
      exact orderOf_dvd_natCard _
    rw [hc] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Res6.coprime_card_inSubgroup_pPrimeCore 3 W) hdvd
  have hKperf : Group.IsPerfect ↥K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  have hKb'perf : Group.IsPerfect ↥Kb' := by
    set f : ↥K →* ↥Kb' :=
      { toFun := fun k => ⟨⟨π ⟨k, hKW k.2⟩,
            hKbY ⟨⟨k, hKW k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩⟩,
          Subgroup.mem_subgroupOf.mpr ⟨⟨k, hKW k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          simp only [OneMemClass.coe_one]
          exact map_one π
        map_mul' := by
          intro a b
          apply Subtype.ext
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          rw [← map_mul]
          rfl } with hf
    refine Group.IsPerfect.ofSurjective (f := f) ?_
    rintro ⟨⟨z, hzY⟩, hz⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_subgroupOf.mp hz
    refine ⟨⟨w, Subgroup.mem_subgroupOf.mp hw⟩, ?_⟩
    rfl
  have hN := hKF m ↥Yb ⟨e⟩ Kb' hKb'top hKb'bot hKb'perf
  intro y hy
  have hyb : π ⟨y, hYW hy.1⟩ ∈ Yb := ⟨⟨y, hYW hy.1⟩, Subgroup.mem_subgroupOf.mpr hy.1, rfl⟩
  have hyN : (⟨π ⟨y, hYW hy.1⟩, hyb⟩ : ↥Yb) ∈ Subgroup.normalizer (Kb' : Set ↥Yb) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, hKb', Subgroup.mem_subgroupOf] at hz ⊢
    obtain ⟨k, hk, hkz⟩ := hz
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hyk : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hMK hy.2) k).mp hkK
    refine ⟨⟨y, hYW hy.1⟩ * k * ⟨y, hYW hy.1⟩⁻¹, Subgroup.mem_subgroupOf.mpr hyk, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hkz]
  rw [hN, hKb', Subgroup.mem_subgroupOf] at hyN
  exact hpull ⟨y, hYW hy.1⟩ hyN

end CFSG.RankThree.PartTwo.Sec20
