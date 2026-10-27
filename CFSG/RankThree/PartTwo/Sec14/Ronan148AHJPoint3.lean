module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AHJPoint2
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem dvd_card_of_le_sup148 {N L T : Subgroup G} (hNT : N ≤ Subgroup.normalizer (T : Set G))
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) (hN : N ⊔ T ≤ L ⊔ T) {m : ℕ}
    (hm : m * Nat.card ↥(N ⊓ T) ∣ Nat.card N) (hT : 0 < Nat.card T)
    (hNT0 : 0 < Nat.card ↥(N ⊓ T)) : m ∣ Nat.card L := by
  have h1 := Sec6.card_sup_mul_card_inf hNT
  have h2 := Sec6.card_sup_mul_card_inf hLT
  have h3 : Nat.card ↥(N ⊔ T) ∣ Nat.card ↥(L ⊔ T) := Subgroup.card_dvd_of_le hN
  have h4 : m * Nat.card T ∣ Nat.card ↥(N ⊔ T) := by
    obtain ⟨k, hk⟩ := hm
    refine ⟨k, ?_⟩
    have : Nat.card ↥(N ⊔ T) * Nat.card ↥(N ⊓ T) =
        m * Nat.card T * k * Nat.card ↥(N ⊓ T) := by
      rw [h1, hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hNT0 this
  have h5 : m * Nat.card T * Nat.card ↥(L ⊓ T) ∣ Nat.card L * Nat.card T := by
    rw [← h2]
    exact Nat.mul_dvd_mul_right (h4.trans h3) _
  have h6 : m * Nat.card ↥(L ⊓ T) ∣ Nat.card L := by
    rw [show m * Nat.card T * Nat.card ↥(L ⊓ T) = m * Nat.card ↥(L ⊓ T) * Nat.card T by ring]
      at h5
    exact Nat.dvd_of_mul_dvd_mul_right hT h5
  exact (dvd_mul_right m _).trans h6

theorem card_img148_mul_dvd {A Y : Subgroup G} [(ker148 A Y).Normal] {N T : Subgroup G}
    (hN : N ≤ Y ⊔ A) (hNT : N ⊓ T ≤ pPrimeCoreOf 3 Y) :
    Nat.card (img148 A Y N) * Nat.card ↥(N ⊓ T) ∣ Nat.card N := by
  set f : ↥N →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hN) with hf
  have hcard := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = img148 A Y N := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : Nat.card ↥(N ⊓ T) ∣ Nat.card f.ker := by
    have hle : T.subgroupOf N ≤ f.ker := by
      intro n hn
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      change ((Subgroup.inclusion hN n : ↥(Y ⊔ A)) : G) ∈ pPrimeCoreOf 3 Y
      exact hNT ⟨n.2, hn⟩
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(T.subgroupOf N) = Nat.card ↥(N ⊓ T) := by
      rw [← Subgroup.inf_subgroupOf_left T N]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← h2]
    exact h1
  rw [← hcard, hrange, mul_comm]
  exact Nat.mul_dvd_mul_right hker _

theorem not_seven_dvd_card_inf_centralizer
    {A B Lb : Subgroup G} {b d : G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) :
    ¬ 7 ∣ Nat.card ↥(Lb ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hd3 : d ^ 3 = 1 := hA.1.2 d (hB.1 hdB)
  obtain ⟨-, -, -, ⟨φ⟩, hd, S, hdS, hSd⟩ := hc
  set P := CFSG.pCore 2 ↥Lb with hP
  set π : ↥Lb →* ↥Lb ⧸ P := QuotientGroup.mk' P with hπ
  set z : ↥Lb ⧸ P := π ⟨d, hd⟩ with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hmem : (⟨d, hd⟩ : ↥Lb) ∈ P := (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Lb)) ⟨⟨d, hd⟩, hmem⟩
    have hk' : (⟨d, hd⟩ : ↥Lb) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd3' : (⟨d, hd⟩ : ↥Lb) ^ 3 = 1 := Subtype.ext hd3
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    have h1 : (⟨d, hd⟩ : ↥Lb) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hk', hd3'⟩
    rw [hcop, pow_one] at h1
    exact hd1 (congrArg Subtype.val h1)
  have hzS : ∃ P' : Sylow 3 (↥Lb ⧸ P), z ∈ (P' : Subgroup (↥Lb ⧸ P)) ∧
      (P' : Subgroup (↥Lb ⧸ P)) ≤ Subgroup.centralizer ({z} : Set (↥Lb ⧸ P)) := by
    refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective P), ⟨⟨d, hd⟩, hdS, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsd := Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)
    change π s * π ⟨d, hd⟩ = π ⟨d, hd⟩ * π s
    rw [← map_mul, ← map_mul, hsd]
  have hC := KFacts.KS14.j2_centralizer_isTripleCover h415 ⟨φ⟩ hz1 hzS
  have hC1080 := HJRes2.card_of_isTripleCover_six hC
  set M : Subgroup ↥Lb := (Subgroup.centralizer ({d} : Set G)).subgroupOf Lb with hM
  have hMcard : Nat.card M = Nat.card ↥(Lb ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [hM, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  set f : ↥M →* ↥Lb ⧸ P := π.comp M.subtype with hf
  have hcard := Subgroup.card_ker_mul_card_range f
  have hrange : f.range ≤ Subgroup.centralizer ({z} : Set (↥Lb ⧸ P)) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm : ((m : ↥Lb) : G) ∈ Subgroup.centralizer ({d} : Set G) := m.2
    have hmd := Subgroup.mem_centralizer_singleton_iff.mp hm
    change π m * π ⟨d, hd⟩ = π ⟨d, hd⟩ * π m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmd
  have hr : Nat.card f.range ∣ 1080 := hC1080 ▸ Subgroup.card_dvd_of_le hrange
  have hk2 : IsPGroup 2 f.ker := by
    intro x
    have hx : f x = 1 := x.2
    have hxP : ((x : ↥M) : ↥Lb) ∈ P := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Lb)) ⟨_, hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨k, hk⟩ := hk2.exists_card_eq
  intro h7
  rw [← hMcard, ← hcard, hk] at h7
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
    omega
  · have := h.trans hr
    norm_num at this

theorem false_of_member_of_j2
    {A L : Subgroup G} {c : G} {Y : Subgroup G} [(ker148 A Y).Normal]
    {B Lb : Subgroup G} {a b d : G} (hOne : Desc143X.One A c L a b d B Lb)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (hdY : d ∈ Y)
    (φ : ↥(img148 A Y Y) ≃* CFSG.Blueprint.NativeSporadic.J2)
    {X : Subgroup G} (hXa : X ∈ thetaComponentsAt 3 a)
    (hXeq : X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X) : False := by
  have hS := hOne.std
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hB := hOne.hyp
  have hc := hOne.config
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  set T := inSubgroup (aschbacherSolvableCore 3) X with hT
  set LB := lB A B with hLB
  have hLBX : LB ≤ X := hXeq ▸ le_sup_left
  have hTX : T ≤ X := hXeq ▸ le_sup_right
  have hXN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    hOne.le_normalizer hXa hLBX
  have hXT : X ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta X
  have hT3 : ¬ 3 ∣ Nat.card T := (Sec6.theta_solvable_and_not_dvd X).2
  have hdLb : d ∈ Lb := by obtain ⟨-, -, -, -, hd, -⟩ := hc; exact hd
  have hdLB : d ∈ LB := by
    rw [hLB, Item148HJ.lB_eq_residual hS hB hc]
    exact Item148HJ.inf_le_residual hS hB hc ⟨hdA, hdLb⟩
  set N := Y ⊓ X with hNdef
  have hdN : d ∈ N := ⟨hdY, hLBX hdLB⟩
  have hNM : N ≤ Y ⊔ A := inf_le_left.trans le_sup_left
  have hNY : img148 A Y N ≤ img148 A Y Y := img148_mono inf_le_left
  have hYNn : img148 A Y Y ≤ Subgroup.normalizer (img148 A Y N : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Late.le_normalizer_inf Subgroup.le_normalizer (hYa.trans hXN))
  have hYs : IsSimpleGroup ↥(img148 A Y Y) := by
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact MulEquiv.isSimpleGroup φ
  have hdα1 : alpha148 A Y d hdA ≠ 1 := by
    intro h
    exact hd1 (alpha148_injective (Y := Y) hA3 hdA (Subgroup.one_mem A) (by rw [h]; rfl))
  have hdαN : alpha148 A Y d hdA ∈ img148 A Y N :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdN, rfl⟩
  have hNeq : img148 A Y N = img148 A Y Y := by
    have hn : ((img148 A Y N).subgroupOf (img148 A Y Y)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYNn
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      have : (⟨alpha148 A Y d hdA, hNY hdαN⟩ : ↥(img148 A Y Y)) ∈
          (img148 A Y N).subgroupOf (img148 A Y Y) := Subgroup.mem_subgroupOf.mpr hdαN
      rw [h, Subgroup.mem_bot] at this
      exact hdα1 (congrArg Subtype.val this)
    · exact le_antisymm hNY (Subgroup.subgroupOf_eq_top.mp h)
  have hNcard : Nat.card (img148 A Y N) = 604800 := by
    rw [hNeq, Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
  have hNTα : img148 A Y (N ⊓ T) = ⊥ := by
    have hle : img148 A Y (N ⊓ T) ≤ img148 A Y N := img148_mono inf_le_left
    have hNN : N ≤ Subgroup.normalizer ((N ⊓ T : Subgroup G) : Set G) :=
      Late.le_normalizer_inf Subgroup.le_normalizer (inf_le_right.trans hXT)
    have hn : ((img148 A Y (N ⊓ T)).subgroupOf (img148 A Y N)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (img148_le_normalizer hNN)
    have hNs : IsSimpleGroup ↥(img148 A Y N) := hNeq ▸ hYs
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hle
    · exfalso
      have hle' : img148 A Y N ≤ img148 A Y (N ⊓ T) := Subgroup.subgroupOf_eq_top.mp h
      have h1 : Nat.card (img148 A Y N) ∣ Nat.card T :=
        ((Subgroup.card_dvd_of_le hle').trans (card_img148_dvd (inf_le_left.trans hNM))).trans
          (Subgroup.card_dvd_of_le inf_le_right)
      rw [hNcard] at h1
      exact hT3 ((by norm_num : 3 ∣ 604800).trans h1)
  have hNTO : N ⊓ T ≤ pPrimeCoreOf 3 Y := by
    intro x hx
    have hxα : QuotientGroup.mk' (ker148 A Y) (⟨x, hNM hx.1⟩ : ↥(Y ⊔ A)) ∈ img148 A Y (N ⊓ T) :=
      mem_img148_iff.mpr ⟨x, hNM hx.1, hx, rfl⟩
    rw [hNTα, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxα
    exact hxα
  have hdvd := card_img148_mul_dvd hNM hNTO
  have hLBT : LB ≤ Subgroup.normalizer (T : Set G) := hLBX.trans hXT
  have hNsup : N ⊔ T ≤ LB ⊔ T := by
    rw [← hXeq]
    exact sup_le inf_le_right hTX
  have hLB7 : Nat.card (img148 A Y N) ∣ Nat.card LB :=
    dvd_card_of_le_sup148 (inf_le_right.trans hXT) hLBT hNsup hdvd Nat.card_pos Nat.card_pos
  rw [hNcard] at hLB7
  apply not_seven_dvd_card_inf_centralizer hA hB hc
  have hLBle : LB ≤ Lb ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hLB, Item148HJ.lB_eq_residual hS hB hc]
    exact Subgroup.map_subtype_le _
  exact ((by norm_num : 7 ∣ 604800).trans hLB7).trans (Subgroup.card_dvd_of_le hLBle)

section Certificates


theorem step148HJCentPoint2_holds
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) :
    Step148HJCentPoint2 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2 hΩ hJYeq hex hJX
  let := ker148_normal hY.2
  obtain ⟨a, haA, ha1, hac, hYa⟩ := hex
  by_contra hbJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨hYB6, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hdYd : d ∈ Yd := hYBYd hdYB
  obtain ⟨φ⟩ := hJ2
  obtain ⟨n, hn⟩ := exists_sectionCentralizer_of_j2 hS.mem_partTwoF hY.2 hJ hAJ hdA hYd hYdJ
    hdYd hA6 hθ hdc hbc φ
  set a' := b * (d ^ n)⁻¹ with ha'
  have ha'B : a' ∈ B := B.mul_mem hbB (B.inv_mem (B.pow_mem hdB n))
  have ha'A : a' ∈ A := hB.1 ha'B
  have hbd : b ∉ Subgroup.zpowers d := by
    intro hbd
    have hBle : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      rintro z (rfl | hz)
      · exact hbd
      · rw [Set.mem_singleton_iff.mp hz]
        exact Subgroup.mem_zpowers d
    have hz3 : Nat.card (Subgroup.zpowers d) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 d hdA))
    have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, hA.2]
    have := Subgroup.card_le_of_le hBle
    omega
  have ha'1 : a' ≠ 1 := by
    intro h
    apply hbd
    have : b = d ^ n := by
      calc b = (b * (d ^ n)⁻¹) * d ^ n := by group
        _ = d ^ n := by rw [← ha', h, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n
  obtain ⟨hC3, -⟩ := Ronan148J.card_inf_centralizer_eq_three_of_j2 hS hY hJ hAJ hYd hYdJ hA6 hθ
    hdA hdYd hdc ⟨φ⟩
  have hmemC : ∀ (x : G) (hx : x ∈ A), x ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
      alpha148 A Y x hx ∈ img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx hxc
    refine ⟨alpha148_mem_img148 hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (HJRes2.le_centralizer_of_mem_sectionCentralizer hx hxc hy))
  have ha'α1 : alpha148 A Y a' ha'A ≠ 1 := by
    intro h
    exact ha'1 (alpha148_injective (Y := Y) hA3 ha'A (Subgroup.one_mem A) (by rw [h]; rfl))
  have hCeq : Subgroup.zpowers (alpha148 A Y a' ha'A) = img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hmemC a' ha'A hn)) ?_
    rw [hC3, Nat.card_zpowers]
    have h3' : alpha148 A Y a' ha'A ^ 3 = 1 := by
      rw [alpha148_eq_mk', ← map_pow]
      have : (⟨a', Subgroup.mem_sup_right ha'A⟩ : ↥(Y ⊔ A)) ^ 3 = 1 :=
        Subtype.ext (hA3 a' ha'A)
      rw [this, map_one]
    rw [orderOf_eq_prime h3' ha'α1]
  have haa' : a ∈ Subgroup.zpowers a' := by
    have hα : alpha148 A Y a haA ∈ Subgroup.zpowers (alpha148 A Y a' ha'A) := by
      rw [hCeq]; exact hmemC a haA hac
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hα
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    refine alpha148_injective (Y := Y) hA3 (A.zpow_mem ha'A k) haA ?_
    rw [← hk, alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
    rfl
  have haB : a ∈ B := (Subgroup.zpowers_le.mpr ha'B) haa'
  have hza : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr haB
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha1
  have hab : Subgroup.zpowers a ≠ Subgroup.zpowers b := fun h =>
    hbJ (mem_sectionCentralizer_of_zpowers_eq hJM haA hbA h hac)
  have had : Subgroup.zpowers a ≠ Subgroup.zpowers d := fun h =>
    hdc (mem_sectionCentralizer_of_zpowers_eq hJM haA hdA h hac)
  have haΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [hΩ]
    exact fun h => hab (Set.mem_singleton_iff.mp h)
  have hOne : Desc143X.One A c L a b d B Lb := ⟨hS, haA, ha1, haΩ, hB, haB, hc, had⟩
  obtain ⟨-, -, -, -, -, hYd1080, hYdX, -⟩ :=
    hj_frame148 h142 h134 h48 Ronan148V.khjPerfectOver_holds hS hY ih hB hYB hc hJ hAJ hYd
      hYBYd hYdJ hA6 hθ hdc hYB6 hdYB hdA ⟨φ⟩
  have h3X : 3 ∣ Nat.card (img148 A Y (deltaZero A (lB A) Y)) := by
    have := Subgroup.card_dvd_of_le hYdX
    rw [hYd1080] at this
    exact (by norm_num : 3 ∣ 1080).trans this
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 G A c L hS a haA ha1 haΩ Qs hQs
  have hΔY : deltaZero A (lB A) Y ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) :=
    sSup_le fun _ hQ => le_delta hQ.1.1 (hQ.2.trans hYa)
  have hXM : deltaZero A (lB A) Y ≤ Y ⊔ A := (deltaZero_le Y).trans le_sup_left
  rcases halt with hcase1 | ⟨b', d', Lb', hb'Ω, hLb', -, hd'A, hd'1, h3c', -, X, -, -, hX⟩
  ·
    have hCa : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))).trans
          (le_normalizer_pPrimeCoreOf 3 _)
    have hcop : Nat.Coprime 3
        (Nat.card (delta A (lB A) (Subgroup.centralizer ({a} : Set G)))) := by
      rw [hcase1]
      exact Nat.Coprime.coprime_dvd_right (card_sup_dvd_of_le_normalizer148 _ _ hCa)
        (Nat.Coprime.mul_right (coprime_card_pPrimeCoreOf 3 _) (coprime_card_pPrimeCoreOf 3 _))
    have hcopX : Nat.Coprime 3 (Nat.card (img148 A Y (deltaZero A (lB A) Y))) :=
      Nat.Coprime.coprime_dvd_right
        ((card_img148_dvd hXM).trans (Subgroup.card_dvd_of_le hΔY)) hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopX h3X
  have hb'b : Subgroup.zpowers b' = Subgroup.zpowers b := by
    rw [hΩ] at hb'Ω
    exact Set.mem_singleton_iff.mp hb'Ω
  have hb'B : b' ∈ B :=
    (Subgroup.zpowers_le.mpr hbB) (hb'b ▸ Subgroup.mem_zpowers b' : b' ∈ Subgroup.zpowers b)
  have hCb : Subgroup.centralizer ({b'} : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rw [← centralizer_zpowers148, hb'b, centralizer_zpowers148]
  have hlA : lA A b' = lA A b := by
    have hθb : thetaComponentsAt 3 b' = thetaComponentsAt 3 b := by
      unfold thetaComponentsAt
      rw [hCb]
    unfold lA
    rw [hθb, hb'b]
  have hLb'eq : Lb' = Lb := by
    have h := hlA ▸ hLb'
    rw [hc.2.2.1] at h
    exact Set.mem_singleton_iff.mp h
  rcases hX with ⟨hXa, hXeq, -⟩ | ⟨had', -⟩
  swap
  ·
    obtain ⟨hd'L, -⟩ := h3c'
    have hd'B : d' ∈ B := hza (had' ▸ Subgroup.mem_zpowers d')
    have hd'd : d' ∈ Subgroup.zpowers d := by
      rw [← hOne.inf_lb_eq]
      exact ⟨hd'B, hLb'eq ▸ hd'L⟩
    have hod' : orderOf d' = 3 := orderOf_eq_prime (hA3 d' hd'A) hd'1
    have hod : orderOf d = 3 := orderOf_eq_prime (hA3 d hdA) hd1
    exact had (had'.trans (Desc143X.zpowers_eq_of_mem hod' hod hd'd))
  have hb'a : b' ∉ Subgroup.zpowers a := by
    intro h
    have hob' : orderOf b' = 3 := by
      have hb'1 : b' ≠ 1 := by
        rintro rfl
        rw [Subgroup.zpowers_one_eq_bot] at hb'b
        have := hb'b ▸ Subgroup.mem_zpowers b
        exact hbd ((Subgroup.mem_bot.mp this) ▸ Subgroup.one_mem _)
      exact orderOf_eq_prime (hA3 b' (hB.1 hb'B)) hb'1
    exact hab ((Desc143X.zpowers_eq_of_mem hob' hoa h).symm.trans hb'b)
  rw [Desc143X.closure_pair_eq_of_not_mem hA hB haB hb'B ha1 hb'a] at hXeq
  exact false_of_member_of_j2 hOne hYa (hYBJ.trans hJY hdYB)
    ((MulEquiv.subgroupCongr (by rw [hJYeq])).trans φ) hXa hXeq

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
