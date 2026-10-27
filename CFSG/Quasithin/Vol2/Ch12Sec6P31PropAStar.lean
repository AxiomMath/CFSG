module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl

public section

namespace CFSG.Quasithin.H13.P31A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Generic

variable {H : Subgroup G}

theorem isSolvable_star {X : Subgroup G} (hX : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥(star H X) := by
  have h1 : Group.IsSolvable ↥(X.subgroupOf H) := by
    let f : ↥(X.subgroupOf H) →* ↥X :=
      { toFun := fun x => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥X => (z : G)) h))
  let f : ↥(X.subgroupOf H) →* HStar H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (X.subgroupOf H).subtype
  have hrange : f.range = star H X := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange]
  exact Group.isSolvable_of_surjective (f := f.rangeRestrict)
    (MonoidHom.rangeRestrict_surjective f)

theorem star_commutator {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    star H ⁅X, Y⁆ = ⁅star H X, star H Y⁆ := by
  have hXY : ⁅X, Y⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hX ha) (hY hb)) (H.inv_mem (hX ha)))
      (H.inv_mem (hY hb))
  have hsub : (⁅X, Y⁆ : Subgroup G).subgroupOf H =
      ⁅X.subgroupOf H, Y.subgroupOf H⁆ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_subgroupOf_eq_of_le hXY]
  unfold S126.star
  rw [hsub, Subgroup.map_commutator]

theorem star_eq_closure_three {X : Subgroup G} (hXH : X ≤ H)
    (hX : X = Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1}) :
    star H X = Subgroup.closure {x : HStar H | x ∈ star H X ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} := by
  set T : Set (↥H) := {x | (x : G) ∈ X ∧ ∃ k : ℕ, (x : G) ^ (3 ^ k) = 1} with hT
  have hXT : X.subgroupOf H = Subgroup.closure T := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hXH]
    have himg : H.subtype '' T = {x : G | x ∈ X ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hXH hx.1⟩, hx, rfl⟩
    rw [himg]
    exact hX
  have hstar_eq : star H X =
      Subgroup.closure ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) '' T) := by
    unfold S126.star
    rw [hXT, MonoidHom.map_closure]
  rw [hstar_eq]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro y ⟨x, hxT, rfl⟩
    refine Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨x, hxT, rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := hxT.2
    exact ⟨k, by
      rw [← map_pow, show x ^ (3 ^ k) = 1 from Subtype.ext (by simpa using hk), map_one]⟩
  · rw [Subgroup.closure_le]
    intro y hy
    exact hy.1

theorem star_le_pCoreOf {N X : Subgroup G} (hNX : N ≤ X) (hXH : X ≤ H)
    (hN : IsPGroup 2 ↥N) (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    star H N ≤ pCoreOf 2 (star H X) := by
  have hNH : N ≤ H := hNX.trans hXH
  refine le_pCoreOf_of_le_normalizer 2 (star_mono hNX) ?_ ?_
  · exact S126P31.star_le_normalizer_star hNH hXH hXN
  · exact S126P31.isPGroup_star hN hNH

end Generic

section Finite

variable [Finite G] {H : Subgroup G}

theorem mk_not_mem_pCoreOf {g : ↥H} (hg : ∀ k : ℕ, (g : G) ^ (2 ^ k) ≠ 1)
    (Y : Subgroup (HStar H)) :
    (QuotientGroup.mk g : HStar H) ∉ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hx
  obtain ⟨y, hy, hq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨y, hy⟩
  have hyq : (y : HStar H) ^ 2 ^ k = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 Y) => (z : HStar H)) hk
    simpa using this
  have hgq : (QuotientGroup.mk g : HStar H) ^ 2 ^ k = 1 := by
    rw [← hq]
    exact hyq
  have hgcore' : ((g ^ 2 ^ k : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← F126.mkH_eq_one_iff]
    simpa using hgq
  have hgcore : (g ^ 2 ^ k : ↥H) ∈ CFSG.pCore 2 ↥H :=
    (Subgroup.mem_map_iff_mem H.subtype_injective).mp hgcore'
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨g ^ 2 ^ k, hgcore⟩
  have hgj : (g ^ 2 ^ k) ^ 2 ^ j = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => (z : ↥H)) hj
    simpa using this
  refine hg (k + j) ?_
  have hpow : (g : ↥H) ^ 2 ^ (k + j) = 1 := by
    calc (g : ↥H) ^ 2 ^ (k + j) = (g : ↥H) ^ (2 ^ k * 2 ^ j) := by rw [pow_add]
      _ = ((g : ↥H) ^ 2 ^ k) ^ 2 ^ j := by rw [pow_mul]
      _ = 1 := hgj
  exact congrArg Subtype.val hpow

theorem star_isPGroup_max {T : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 ↥T)
    (hmax : ∀ S : Subgroup G, IsPGroup 2 ↥S → T ≤ S → S = T) :
    IsPGroup 2 ↥(star H T) ∧
      ∀ S : Subgroup (HStar H), IsPGroup 2 ↥S → star H T ≤ S → S = star H T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨S126P31.isPGroup_star hT hTH, fun S hS hle => ?_⟩
  have hpre : IsPGroup 2 ↥(pre H S) := by
    intro r
    obtain ⟨hrH, hrS⟩ := mem_pre.1 r.2
    obtain ⟨k, hk⟩ := hS ⟨QuotientGroup.mk ⟨(r : G), hrH⟩, hrS⟩
    have hk' : (QuotientGroup.mk ⟨(r : G), hrH⟩ : HStar H) ^ 2 ^ k = 1 :=
      congrArg Subtype.val hk
    have hrq : ((r : G) ^ 2 ^ k) ∈ pCoreOf 2 H := by
      have h1 : (QuotientGroup.mk ((⟨(r : G), hrH⟩ : ↥H) ^ 2 ^ k) : HStar H) = 1 := by
        rw [QuotientGroup.mk_pow]
        exact hk'
      exact F126.mkH_eq_one_iff.1 h1
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨(r : G) ^ 2 ^ k, hrq⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hTR : T ≤ pre H S := fun t ht =>
    mem_pre.2 ⟨hTH ht, hle (mk_mem_star (h := ⟨t, hTH ht⟩) ht)⟩
  have hRT : pre H S = T := hmax (pre H S) hpre hTR
  calc S = star H (pre H S) := (star_pre S).symm
    _ = star H T := by rw [hRT]

end Finite

theorem isSylowTwoOf_inf_subgroupOf {X : Type} [Group X] [Finite X] {T K : Subgroup X}
    [K.Normal] (hT : IsPGroup 2 ↥T)
    (hmax : ∀ S : Subgroup X, IsPGroup 2 ↥S → T ≤ S → S = T) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 X :=
    { toSubgroup := T
      isPGroup' := hT
      is_maximal' := fun {P} hP hTP => hmax P hP hTP }
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hK : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
  refine ⟨le_top, A4.isPGroup_subgroupOf_of_le hK.1 hK.2.1, ?_⟩
  show ¬ 2 ∣ ((T ⊓ K).subgroupOf K).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hK.2.2

section Setting

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V] {H K : Subgroup G}

theorem T_le_H (F : Frame126 T L V) (hHK : S126.IsHK T L F.V1 H K) : T ≤ H := by
  rw [hHK.2.2]
  exact le_sup_right.trans le_sup_right

theorem L1_le_H (F : Frame126 T L V) (hHK : S126.IsHK T L F.V1 H K) :
    S126.Li L F.V1 ≤ H := by
  rw [hHK.2.2]
  change L₁Of L F.V1 ≤ conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T)
  exact le_sup_left.trans le_sup_right

theorem normal_star_K (F : Frame126 T L V) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hK₀ : conjClosure K T = K) : (star H K).Normal := by
  have h : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hK₀]
    exact h918.K₀_normal
  exact S126P31.normal_star h

theorem commutator_star_K (F : Frame126 T L V) (h918 : HypF918 T V L F.V1 F.V5 H K) :
    ⁅star H K, star H K⁆ = star H K := by
  have hK : K ≤ H := le_of_mem_cComp h918.K_cComp
  rw [← star_commutator hK hK, perfect_of_mem_cComp h918.K_cComp]

theorem commutator_star_K_eq_top (F : Frame126 T L V)
    (h918 : HypF918 T V L F.V1 F.V5 H K) :
    commutator ↥(star H K) = ⊤ :=
  S126P31.commutator_eq_top_of_perfect (commutator_star_K F h918)

theorem odd_card_center_star_K (F : Frame126 T L V)
    (h918 : HypF918 T V L F.V1 F.V5 H K) :
    Odd (Nat.card ↥(Subgroup.center ↥(star H K))) := by
  by_contra hodd
  have heven : Even (Nat.card ↥(Subgroup.center ↥(star H K))) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center ↥(star H K))) 2 (even_iff_two_dvd.mp heven)
  have hsub : (star H K).IsSubnormal :=
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp))
  have hO2 : ∀ N : Subgroup (HStar H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hn hp => S126P31.eq_bot_of_isPGroup hn hp
  have hzpow : (z : ↥(star H K)) ^ 2 ^ 1 = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz] at h
    simpa using congrArg (fun w : ↥(Subgroup.center ↥(star H K)) => (w : ↥(star H K))) h
  have hzone : (z : ↥(star H K)) = 1 :=
    S126P31.eq_one_of_central_two_element hO2 hsub z.2 hzpow
  have hz1 : z = 1 := Subtype.ext hzone
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem isPGroup_star_T (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hHK : S126.IsHK T L F.V1 H K) : IsPGroup 2 ↥(star H T) :=
  S126P31.isPGroup_star hH.hyp.sylow.1 (T_le_H F hHK)

theorem star_T_max (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hHK : S126.IsHK T L F.V1 H K) :
    ∀ S : Subgroup (HStar H), IsPGroup 2 ↥S → star H T ≤ S → S = star H T := by
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hH.hyp.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hH.hyp.sylow.2
  have hmax : ∀ S : Subgroup G, IsPGroup 2 ↥S → T ≤ S → S = T := by
    intro S hS hTS
    have hle := (A4.isSylowTwoOf_iff_maximal.mp hTsyl).2.2 S le_top hS hTS
    exact le_antisymm hle hTS
  exact (star_isPGroup_max (T_le_H F hHK) hH.hyp.sylow.1 hmax).2

end Setting

end CFSG.Quasithin.H13.P31A
