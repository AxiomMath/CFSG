module

public import CFSG.RankThree.PartTwo.Sec21.FF84S22
public import CFSG.RankThree.PartTwo.Sec21.FF84S33
public import CFSG.RankThree.PartTwo.Sec21.Commute33Tools
public import CFSG.GroupTheory.SteinbergCBFTHall
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

@[expose] def O3 (X : Subgroup G) : Subgroup G := Subgroup.closure {x : G | x ∈ X ∧ ¬ 3 ∣ orderOf x}

theorem mem_of_zpow_mem_of_orderOf_three {S : Subgroup G} {x : G} (hx : orderOf x = 3) {k : ℤ}
    (hk : ¬ (3 : ℤ) ∣ k) (hmem : x ^ k ∈ S) : x ∈ S := by
  have h3 : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hx, pow_orderOf_eq_one]
  have hkk : x ^ (k * k) = x := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, k * k = 1 + 3 * t := by
      obtain ⟨q, hq | hq⟩ : ∃ q : ℤ, k = 3 * q + 1 ∨ k = 3 * q + 2 := ⟨k / 3, by omega⟩
      · exact ⟨3 * q ^ 2 + 2 * q, by rw [hq]; ring⟩
      · exact ⟨3 * q ^ 2 + 4 * q + 1, by rw [hq]; ring⟩
    rw [ht, zpow_add, zpow_one, zpow_mul, h3, one_zpow, mul_one]
  have hx' : x = (x ^ k) ^ k := by rw [← zpow_mul, hkk]
  rw [hx']
  exact S.zpow_mem hmem k

theorem three_dvd_of_zpow_eq_one {x : G} (hx : orderOf x = 3) {m : ℤ} (h1 : x ^ m = 1) :
    (3 : ℤ) ∣ m := by
  have := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hx] at this
  exact_mod_cast this

private theorem mem_zpowers_of_cyclic_sylow_S3 {H : Type} [Group H] [Finite H]
    (hS : ∀ P : Sylow 3 H, IsCyclic ↥(P : Subgroup H)) {u v : H} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (huv : Commute u v) :
    u ∈ Subgroup.zpowers v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hov : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hzu : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  have hzv : IsPGroup 3 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hov, pow_one])
  have hle : Subgroup.zpowers u ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup H) : Set H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact huv.symm.zpow_left k
  obtain ⟨P, hP⟩ := (IsPGroup.to_sup_of_normal_right' hzu hzv hle).exists_le_sylow
  haveI := hS P
  have hmu : u ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hmv : v ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hu' : orderOf (⟨u, hmu⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hou]
  have hv' : orderOf (⟨v, hmv⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hov]
  have heq : Subgroup.zpowers (⟨u, hmu⟩ : (P : Subgroup H)) =
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hu', hv'])
  have hmem : (⟨u, hmu⟩ : (P : Subgroup H)) ∈
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_zpowers_of_cyc {L : Subgroup G} (hcyc : FFCentCyclicSylow L) {u v : G}
    (hu : u ∈ Subgroup.centralizer (L : Set G)) (hv : v ∈ Subgroup.centralizer (L : Set G))
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (huv : Commute u v) :
    u ∈ Subgroup.zpowers v := by
  have h := mem_zpowers_of_cyclic_sylow_S3 (H := ↥(Subgroup.centralizer (L : Set G))) hcyc
    (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) (Subtype.ext hu3) (fun h => hu1 (congrArg Subtype.val h))
    (Subtype.ext hv3) (fun h => hv1 (congrArg Subtype.val h)) (Subtype.ext huv.eq)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩

section Standing
variable {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem P_cardB (h : FF84Sec3 b L B b₁ b₂) : Nat.card B = 27 := by
  rw [h.mono.1.2]; norm_num

theorem P_card_E (h : FF84Sec3 b L B b₁ b₂) : Nat.card ↥(B ⊓ L) = 9 := by
  have hB27 : Nat.card ↥B = 27 := P_cardB h
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, -⟩ :=
    mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have hdvd : Nat.card ↥(B ⊓ L) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
  rw [hB27, show (27 : ℕ) = 3 ^ 3 by norm_num] at hdvd
  have hle9 : Nat.card ↥(B ⊓ L) ≤ 9 := by
    rw [h.gen]
    exact CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.card_closure_pair_le_nine hcomm h13 h23
  have hgt3 : 3 < Nat.card ↥(B ⊓ L) := by
    have hle : Subgroup.zpowers b₁ ≤ B ⊓ L := Subgroup.zpowers_le.2 h.hb₁
    have hcard3 : Nat.card ↥(Subgroup.zpowers b₁) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime h13 hne1]
    by_contra hcon
    push_neg at hcon
    have heq : Subgroup.zpowers b₁ = B ⊓ L :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard3]; exact hcon)
    have hb2mem : b₂ ∈ Subgroup.zpowers b₁ := by rw [heq]; exact h.hb₂
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hb2mem
    exact hind m hm.symm
  generalize hc : Nat.card ↥(B ⊓ L) = c at hdvd hle9 hgt3 ⊢
  interval_cases c <;> first | rfl | (norm_num at hdvd)

theorem P_b_notin_L (h : FF84Sec3 b L B b₁ b₂) : b ∉ L := by
  intro hbL
  have hBL : B ≤ L := by
    calc B = Subgroup.closure {b, b₁, b₂} := h.mono.2.1
      _ ≤ L := by
        refine (Subgroup.closure_le _).2 ?_
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hbL
        · exact (Subgroup.mem_inf.1 h.hb₁).2
        · exact (Subgroup.mem_inf.1 h.hb₂).2
  have hE : B ⊓ L = B := inf_eq_left.2 hBL
  have h1 := P_card_E h
  have h2 := P_cardB h
  rw [hE] at h1
  omega

theorem P_zpowers_inf_E (h : FF84Sec3 b L B b₁ b₂) :
    Subgroup.zpowers b ⊓ (B ⊓ L) = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  obtain ⟨hxb, hxE⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
  by_cases hk : (3 : ℤ) ∣ k
  · have hbk : b ^ k = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.1
      rw [h.hyp.ord]
      exact_mod_cast hk
    rw [hbk]
    exact Subgroup.one_mem _
  · exact absurd (mem_of_zpow_mem_of_orderOf_three h.hyp.ord hk (Subgroup.mem_inf.1 hxE).2)
      (P_b_notin_L h)

theorem P_b_mem_CenS (h : FF84Sec3 b L B b₁ b₂) : b ∈ CenS L :=
  Subgroup.mem_centralizer_iff.2 fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hl)

theorem P_E (h : FF84Sec3 b L B b₁ b₂) :
    IsElemAb 3 2 (B ⊓ L) ∧ Subgroup.zpowers b ⊓ (B ⊓ L) = ⊥ ∧ Subgroup.zpowers b ⊔ (B ⊓ L) = B ∧
      B ⊓ CenS L = Subgroup.zpowers b := by
  refine ⟨?_, P_zpowers_inf_E h, ?_, ?_⟩
  · unfold IsElemAb
    exact ⟨CFSG.IsElementaryAbelian.of_le h.mono.1.1 inf_le_left, (P_card_E h).trans (by norm_num)⟩
  · apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.2 (mem_B_b h)) inf_le_left
    · calc B = Subgroup.closure {b, b₁, b₂} := h.mono.2.1
        _ ≤ Subgroup.zpowers b ⊔ (B ⊓ L) := by
          refine (Subgroup.closure_le _).2 ?_
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
          · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mem_B_b₁ h, (Subgroup.mem_inf.1 h.hb₁).2⟩)
          · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mem_B_b₂ h, (Subgroup.mem_inf.1 h.hb₂).2⟩)
  · apply le_antisymm
    · intro x hx
      obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.1 hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · have hb3 : b ^ 3 = 1 := by rw [← h.hyp.ord]; exact pow_orderOf_eq_one b
        have hb1 : b ≠ 1 := by
          intro e
          have := h.hyp.ord
          rw [e, orderOf_one] at this
          norm_num at this
        exact mem_zpowers_of_cyc h.hyp.cyc hxC (P_b_mem_CenS h) (pow3_of_mem_B h hxB) hx1 hb3 hb1
          (comm_of_mem_B h hxB (mem_B_b h))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨mem_B_b h, P_b_mem_CenS h⟩

theorem P_basis (h : FF84Sec3 b L B b₁ b₂) (i j k : ℤ) (e : b ^ i * b₁ ^ j * b₂ ^ k = 1) :
    (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
  obtain ⟨-, hEb, -, -⟩ := P_E h
  obtain ⟨h13, h23, -, hne1, hne2, hind, -⟩ :=
    mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have hb₁ord : orderOf b₁ = 3 := orderOf_eq_prime h13 hne1
  have hb₂ord : orderOf b₂ = 3 := orderOf_eq_prime h23 hne2
  have hy : b₁ ^ j * b₂ ^ k ∈ B ⊓ L :=
    mul_mem (zpow_mem h.hb₁ j) (zpow_mem h.hb₂ k)
  have e' : b ^ i * (b₁ ^ j * b₂ ^ k) = 1 := by rw [← mul_assoc]; exact e
  have hbi : b ^ i = (b₁ ^ j * b₂ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left e'
  have hbi1 : b ^ i = 1 := by
    have hmem : b ^ i ∈ Subgroup.zpowers b ⊓ (B ⊓ L) := by
      refine Subgroup.mem_inf.2 ⟨zpow_mem (Subgroup.mem_zpowers b) i, ?_⟩
      rw [hbi]
      exact inv_mem hy
    rw [hEb] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hi : (3 : ℤ) ∣ i := three_dvd_of_zpow_eq_one h.hyp.ord hbi1
  rw [hbi1, one_mul] at e'
  have hk2 : b₂ ^ k = (b₁ ^ j)⁻¹ := eq_inv_of_mul_eq_one_right e'
  have hk : (3 : ℤ) ∣ k := by
    by_contra hk
    have hmem : b₂ ^ k ∈ Subgroup.zpowers b₁ := by
      rw [hk2]; exact inv_mem (zpow_mem (Subgroup.mem_zpowers b₁) j)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1
      (mem_of_zpow_mem_of_orderOf_three hb₂ord hk hmem)
    exact hind m hm.symm
  have hk1 : b₂ ^ k = 1 :=
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hb₂ord]; exact_mod_cast hk)
  have hj1 : b₁ ^ j = 1 := by
    rw [hk1, mul_one] at e'
    exact e'
  exact ⟨hi, three_dvd_of_zpow_eq_one hb₁ord hj1, hk⟩

theorem P_center_dvd_two
    (h : FF84Sec3 b L B b₁ b₂) : Nat.card (Subgroup.center L) ∣ 2 := by
  obtain ⟨e⟩ : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, h.hyp.model⟩)
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_two_of_eight h.hyp.quasi e

private theorem quasi_normal_le_center_or_eq_top {K : Type*} [Group K] (hq : CFSG.IsQuasisimple K)
    (M : Subgroup K) [M.Normal] : M ≤ Subgroup.center K ∨ M = ⊤ := by
  obtain ⟨hperf, hs, -⟩ := hq
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center K) m ∈
        M.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ hm
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff m).mp h1
  · right
    have hsup : M ⊔ Subgroup.center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.isPerfect_def.mp hperf] at hle
    exact top_le_iff.mp hle

theorem quasi_commute_of_normal_proper {G : Type*} [Group G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple L) {I : Subgroup G} (hIL : I ≤ L)
    (hI : ∀ x ∈ L, ∀ y ∈ I, x * y * x⁻¹ ∈ I) (hne : ¬ L ≤ I) :
    ∀ y ∈ I, ∀ x ∈ L, x * y = y * x := by
  haveI : (I.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hI (g : G) g.2 (n : G) hn
    simpa using this⟩
  rcases quasi_normal_le_center_or_eq_top hq (I.subgroupOf L) with h | h
  · intro y hy x hx
    have hyL : (⟨y, hIL hy⟩ : ↥L) ∈ I.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 (h hyL) ⟨x, hx⟩)
  · exfalso
    apply hne
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ I.subgroupOf L := by
      rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem quasi_commute_of_normalized {G : Type} [Group G] {M L J : Subgroup G}
    (hq : CFSG.IsQuasisimple L) (hLM : L ≤ M) (hJM : J ≤ M)
    (hLn : ∀ g ∈ M, ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hJn : ∀ g ∈ M, ∀ x ∈ J, g * x * g⁻¹ ∈ J)
    (hJL : ¬ L ≤ J) : ∀ x ∈ L, ∀ y ∈ J, x * y = y * x := by
  have hcomm : ⁅L, J⁆ ≤ L ⊓ J := by
    refine Subgroup.commutator_le.2 ?_
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ L := hLn g₂ (hJM hg₂) g₁⁻¹ (L.inv_mem hg₁)
      have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
      rw [e]
      exact L.mul_mem hg₁ h1
    · have h2 : g₁ * g₂ * g₁⁻¹ ∈ J := hJn g₁ (hLM hg₁) g₂ hg₂
      exact J.mul_mem h2 (J.inv_mem hg₂)
  have hcen : ∀ y ∈ L ⊓ J, ∀ x ∈ L, x * y = y * x :=
    quasi_commute_of_normal_proper hq inf_le_left
      (fun x hx y hy => Subgroup.mem_inf.2
        ⟨hLn x (hLM hx) y (Subgroup.mem_inf.1 hy).1, hJn x (hLM hx) y (Subgroup.mem_inf.1 hy).2⟩)
      (fun h => hJL (fun x hx => (Subgroup.mem_inf.1 (h hx)).2))
  have hthree : ⁅⁅L, J⁆, L⁆ ≤ ⊥ := by
    refine Subgroup.commutator_le.2 ?_
    intro c hc z hz
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hcen c (hcomm hc) z hz).symm
  have hK : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  have hbot : ∀ x : G, x ∈ (Subgroup.normalizer ((⊥ : Subgroup G) : Set G)) :=
    fun x => Subgroup.mem_normalizer_iff.2 (fun h => by simp [Subgroup.mem_bot])
  have hR : ⁅L, J⁆ ≤ (⊥ : Subgroup G) :=
    Commute33Steps.commutator_le_of_perfect hK (fun x _ => hbot x) (fun x _ => hbot x) hthree
  intro x hx y hy
  have := hR (Subgroup.commutator_mem_commutator hx hy)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem P_Nb_normalizes_L (h : FF84Sec3 b L B b₁ b₂) : Nor (Subgroup.zpowers b) ≤ Nor L := by
  intro n hn
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, -⟩ :=
    mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have hb₂ord : orderOf b₂ = 3 := orderOf_eq_prime h23 hne2
  have hLb : ∀ x ∈ L, Commute x b := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hx)
  have hnb : n * b * n⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.1 hn b).1 (Subgroup.mem_zpowers b)
  have hnb' : n⁻¹ * b * n ∈ Subgroup.zpowers b := by
    refine (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * b * n)).2 ?_
    have e : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
    rw [e]
    exact Subgroup.mem_zpowers b
  have hc1 : ∀ x ∈ L, Commute (n * x * n⁻¹) b := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hnb'
    have hxc : Commute x (n⁻¹ * b * n) := by
      rw [← hk]
      exact (hLb x hx).zpow_right k
    show n * x * n⁻¹ * b = b * (n * x * n⁻¹)
    calc n * x * n⁻¹ * b = n * (x * (n⁻¹ * b * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * b * n) * x) * n⁻¹ := by rw [hxc.eq]
      _ = b * (n * x * n⁻¹) := by group
  have hc2 : ∀ g ∈ Cen b, n⁻¹ * g * n ∈ Cen b := by
    intro g hg
    have hgb : Commute g b := Subgroup.mem_centralizer_singleton_iff.1 hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hnb
    have hgc : Commute g (n * b * n⁻¹) := by
      rw [← hk]
      exact hgb.zpow_right k
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc (n⁻¹ * g * n) * b = n⁻¹ * (g * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * b * n⁻¹) * g) * n := by rw [hgc.eq]
      _ = b * (n⁻¹ * g * n) := by group
  obtain ⟨J, hJdef⟩ : ∃ J : Subgroup G, J = L.map (MulAut.conj n).toMonoidHom := ⟨_, rfl⟩
  have hmemJ : ∀ x, x ∈ J ↔ ∃ y ∈ L, n * y * n⁻¹ = x := by
    intro x
    rw [hJdef, Subgroup.mem_map]
    rfl
  have hcardJ : Nat.card J = Nat.card L := by
    rw [hJdef]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hJM : J ≤ Cen b := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemJ _).1 hx
    exact Subgroup.mem_centralizer_singleton_iff.2 (hc1 y hy).eq
  have hLn : ∀ g ∈ Cen b, ∀ x ∈ L, g * x * g⁻¹ ∈ L := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (h.hyp.hLN hg) x).1 hx
  have hJn : ∀ g ∈ Cen b, ∀ x ∈ J, g * x * g⁻¹ ∈ J := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := (hmemJ _).1 hx
    rw [hmemJ]
    refine ⟨(n⁻¹ * g * n) * y * (n⁻¹ * g * n)⁻¹, hLn _ (hc2 g hg) y hy, ?_⟩
    group
  have hLJ : L ≤ J := by
    by_contra hcon
    have hcen := quasi_commute_of_normalized (M := Cen b) h.hyp.quasi h.hyp.hLC hJM hLn hJn hcon
    have hu : n * b₁ * n⁻¹ ∈ J := (hmemJ _).2 ⟨b₁, (Subgroup.mem_inf.1 h.hb₁).2, rfl⟩
    have hv : n * b₂ * n⁻¹ ∈ J := (hmemJ _).2 ⟨b₂, (Subgroup.mem_inf.1 h.hb₂).2, rfl⟩
    have hucen : n * b₁ * n⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun l hl => hcen l hl _ hu)
    have hvcen : n * b₂ * n⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun l hl => hcen l hl _ hv)
    have hu3 : (n * b₁ * n⁻¹) ^ 3 = 1 := by
      rw [conj_pow, h13]
      group
    have hv3 : (n * b₂ * n⁻¹) ^ 3 = 1 := by
      rw [conj_pow, h23]
      group
    have hu1 : n * b₁ * n⁻¹ ≠ 1 := by
      intro e
      apply hne1
      have e2 : b₁ = n⁻¹ * (n * b₁ * n⁻¹) * n := by group
      rw [e2, e]
      group
    have hv1 : n * b₂ * n⁻¹ ≠ 1 := by
      intro e
      apply hne2
      have e2 : b₂ = n⁻¹ * (n * b₂ * n⁻¹) * n := by group
      rw [e2, e]
      group
    have hcomm' : Commute (n * b₁ * n⁻¹) (n * b₂ * n⁻¹) :=
      (show Commute b₁ b₂ from hcomm).map (MulAut.conj n)
    have hzp := mem_zpowers_of_cyc h.hyp.cyc hucen hvcen hu3 hu1 hv3 hv1 hcomm'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzp
    rw [conj_zpow] at hk
    have hbk : b₂ ^ k = b₁ := mul_left_cancel (mul_right_cancel hk)
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      intro hdiv
      apply hne1
      rw [← hbk]
      exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hb₂ord]; exact_mod_cast hdiv)
    have hmem : b₂ ^ k ∈ Subgroup.zpowers b₁ := by
      rw [hbk]
      exact Subgroup.mem_zpowers b₁
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.1 (mem_of_zpow_mem_of_orderOf_three hb₂ord hk3 hmem)
    exact hind m hm.symm
  have hLeq : L = J := Subgroup.eq_of_le_of_card_ge hLJ hcardJ.le
  refine Subgroup.mem_normalizer_iff.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · rw [hLeq]
    exact (hmemJ _).2 ⟨x, hx, rfl⟩
  · rw [hLeq] at hx
    obtain ⟨y, hy, hyx⟩ := (hmemJ _).1 hx
    have hyx' : y = x := mul_left_cancel (mul_right_cancel hyx)
    rw [← hyx']
    exact hy

theorem opp3_not_dvd {H : Subgroup G} {x : G} (hx : x ∈ inSubgroup (pPrimeCore 3) H) :
    ¬ 3 ∣ orderOf x := by
  unfold inSubgroup at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  intro h3
  have h1 : 3 ∣ Nat.card ↥(pPrimeCore 3 H) := by
    refine dvd_trans ?_ (orderOf_dvd_natCard (⟨y, hy⟩ : ↥(pPrimeCore 3 H)))
    have e1 : orderOf (⟨y, hy⟩ : ↥(pPrimeCore 3 H)) = orderOf y :=
      (Subgroup.orderOf_coe (⟨y, hy⟩ : ↥(pPrimeCore 3 H))).symm
    have e2 : orderOf y = orderOf (H.subtype y) := (Subgroup.orderOf_coe y).symm
    rw [e1, e2]
    exact h3
  have := Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card h1
  exact absurd this (by norm_num)

theorem opp3_conj {H : Subgroup G} {g x : G} (hg : g ∈ H) (hx : x ∈ inSubgroup (pPrimeCore 3) H) :
    g * x * g⁻¹ ∈ inSubgroup (pPrimeCore 3) H := by
  unfold inSubgroup at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹, ?_, ?_⟩
  · exact (pPrimeCore_normal (p := 3) (G := H)).conj_mem y hy _
  · simp

theorem opp3_of_normal_coprime {H : Subgroup G} {N : Subgroup H} (hN : N.Normal)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N.map H.subtype ≤ inSubgroup (pPrimeCore 3) H := by
  have hmem : N ≤ pPrimeCore 3 H := by
    unfold pPrimeCore
    exact le_sSup ⟨hN, hcop⟩
  unfold inSubgroup
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  exact Subgroup.mem_map.2 ⟨y, hmem hy, rfl⟩

theorem opp3_le_cenS {b : G} {L B : Subgroup G} {b₁ b₂ : G} (h : FF84Sec3 b L B b₁ b₂) :
    inSubgroup (pPrimeCore 3) (Cen b) ≤ CenS L := by
  obtain ⟨h13, -, -, hne1, -, -, -⟩ := mono_facts h.hyp.ord (mem_B_b₁ h) (mem_B_b₂ h) h.mono
  have hb₁ord : orderOf b₁ = 3 := orderOf_eq_prime h13 hne1
  have hXM : inSubgroup (pPrimeCore 3) (Cen b) ≤ Cen b := by
    unfold inSubgroup
    exact Subgroup.map_subtype_le _
  have hLn : ∀ g ∈ Cen b, ∀ x ∈ L, g * x * g⁻¹ ∈ L := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (h.hyp.hLN hg) x).1 hx
  have hnot : ¬ L ≤ inSubgroup (pPrimeCore 3) (Cen b) := by
    intro hLX
    have hb1X : b₁ ∈ inSubgroup (pPrimeCore 3) (Cen b) := hLX (Subgroup.mem_inf.1 h.hb₁).2
    exact opp3_not_dvd hb1X (by rw [hb₁ord])
  have hcen := quasi_commute_of_normalized (M := Cen b) h.hyp.quasi h.hyp.hLC hXM hLn
    (fun g hg x hx => opp3_conj hg hx) hnot
  intro x hx
  exact Subgroup.mem_centralizer_iff.2 (fun l hl => hcen l hl x hx)

theorem zpowers_inf_opp {b : G} {L B : Subgroup G} {b₁ b₂ : G} (h : FF84Sec3 b L B b₁ b₂) :
    Subgroup.zpowers b ⊓ inSubgroup (pPrimeCore 3) (Cen b) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxb, hxX⟩ := Subgroup.mem_inf.1 hx
  have hdvd : orderOf x ∣ 3 := by
    have := orderOf_dvd_of_mem_zpowers hxb
    rwa [h.hyp.ord] at this
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 h1
  · exact absurd (dvd_of_eq h1.symm) (opp3_not_dvd hxX)

theorem P_C_structure (h : FF84Sec3 b L B b₁ b₂) :
    Opp 3 (Cen b) ≤ CenS L ∧ Subgroup.zpowers b ⊔ Opp 3 (Cen b) = CenS L ⊓ Cen b ∧
      Subgroup.zpowers b ⊓ Opp 3 (Cen b) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Cb, hCb⟩ : ∃ C : Subgroup G, C = CenS L ⊓ Cen b := ⟨_, rfl⟩
  have hmemCb : ∀ x, x ∈ Cb ↔ x ∈ CenS L ∧ x ∈ Cen b := fun x => by
    rw [hCb, Subgroup.mem_inf]
  rw [← hCb]
  have hbCen : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hbCb : b ∈ Cb := (hmemCb b).2 ⟨P_b_mem_CenS h, hbCen⟩
  have hBCen : B ≤ Cen b := h.sylB.1
  have hCbLe : Cb ≤ Cen b := fun x hx => ((hmemCb x).1 hx).2
  have hXCen : inSubgroup (pPrimeCore 3) (Cen b) ≤ Cen b := by
    unfold inSubgroup
    exact Subgroup.map_subtype_le _
  have hXCb : inSubgroup (pPrimeCore 3) (Cen b) ≤ Cb := fun x hx =>
    (hmemCb x).2 ⟨opp3_le_cenS h hx, hXCen hx⟩
  have hCbCen : ∀ g ∈ Cen b, ∀ c ∈ Cb, g * c * g⁻¹ ∈ Cb := by
    intro g hg c hc
    obtain ⟨hcL, hcC⟩ := (hmemCb c).1 hc
    refine (hmemCb _).2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' := (Subgroup.mem_normalizer_iff.1 (h.hyp.hLN (inv_mem hg)) l).1 hl
      rw [inv_inv] at hl'
      have hcl := Subgroup.mem_centralizer_iff.1 hcL (g⁻¹ * l * g) hl'
      calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [hcl]
        _ = g * c * g⁻¹ * l := by group
    · have hgb : Commute g b := Subgroup.mem_centralizer_singleton_iff.1 hg
      have hcb : Commute c b := Subgroup.mem_centralizer_singleton_iff.1 hcC
      have hconj : Commute (g * c * g⁻¹) b :=
        Commute.mul_left (Commute.mul_left hgb hcb) hgb.inv_left
      exact Subgroup.mem_centralizer_singleton_iff.2 hconj.eq
  have hBN : B ≤ Subgroup.normalizer (Cb : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 (fun c => ⟨fun hc => hCbCen x (hBCen hx) c hc, fun hc => ?_⟩)
    have hback := hCbCen x⁻¹ (inv_mem (hBCen hx)) _ hc
    have e : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
    rw [e] at hback
    exact hback
  have hBC : B ⊓ Cb = Subgroup.zpowers b := by
    rw [← (P_E h).2.2.2]
    apply le_antisymm
    · exact inf_le_inf_left B (fun x hx => ((hmemCb x).1 hx).1)
    · intro x hx
      obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxB, (hmemCb x).2 ⟨hxC, hBCen hxB⟩⟩
  have hdvd : B.relIndex (B ⊔ Cb) ∣ B.relIndex (Cen b) := by
    rw [← Subgroup.relIndex_mul_relIndex B (B ⊔ Cb) (Cen b) le_sup_left (sup_le hBCen hCbLe)]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime 3 ((Subgroup.zpowers b).relIndex Cb) := by
    rw [← hBC, Subgroup.inf_relIndex_right,
      CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hBN]
    exact Nat.Coprime.coprime_dvd_right hdvd h.sylB.2.2
  set S : Subgroup ↥Cb := Subgroup.zpowers (⟨b, hbCb⟩ : ↥Cb) with hSdef
  have hSeq : (Subgroup.zpowers b).subgroupOf Cb = S := by
    rw [hSdef]
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
  have hSp : IsPGroup 3 S :=
    IsPGroup.of_card (n := 1) (by rw [hSdef, Nat.card_zpowers, Subgroup.orderOf_mk, h.hyp.ord, pow_one])
  have hSi : ¬ 3 ∣ S.index := by
    rw [← hSeq]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  obtain ⟨N, hNn, hNcop, hNq⟩ := CFSG.theorem_1_18 3
    (CFSG.Quasithin.SBc17.sylowOfIndex S hSp hSi) (by
    intro x hx
    have hx' : x ∈ S := hx
    refine ⟨Subgroup.le_normalizer hx, Subgroup.mem_centralizer_iff.mpr (fun n hn => ?_)⟩
    have h1 : (n : G) * b = b * n := Subgroup.mem_centralizer_singleton_iff.1
      ((hmemCb (n : G)).1 n.2).2
    have hbn : Commute (⟨b, hbCb⟩ : ↥Cb) n :=
      show (⟨b, hbCb⟩ : ↥Cb) * n = n * ⟨b, hbCb⟩ from Subtype.ext h1.symm
    rw [hSdef] at hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
    exact ((hbn.zpow_left k).eq).symm)
  have hA : S ⊔ N = ⊤ := by
    have h1 : (S ⊔ N).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (S ⊔ N).index ∣ N.index := Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := hNq.exists_card_eq
    have hc1 : Nat.Coprime (S ⊔ N).index 3 :=
      Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hSi).symm
    have hc2 : Nat.Coprime (S ⊔ N).index (3 ^ k) := Nat.Coprime.pow_right k hc1
    have h3 : (S ⊔ N).index ∣ 3 ^ k := by rw [← hk]; exact h2
    exact Subgroup.index_eq_one.1 (Nat.Coprime.eq_one_of_dvd hc2 h3)
  have hgood : ∀ c : G, c ∈ Cb → ¬ 3 ∣ orderOf c → ∃ y ∈ N, (y : G) = c := by
    intro c hc h3c
    obtain ⟨j, hj⟩ := hNq (QuotientGroup.mk (⟨c, hc⟩ : ↥Cb) : ↥Cb ⧸ N)
    have hd1 : orderOf (QuotientGroup.mk (⟨c, hc⟩ : ↥Cb) : ↥Cb ⧸ N) ∣ 3 ^ j :=
      orderOf_dvd_of_pow_eq_one hj
    have hd2 : orderOf (QuotientGroup.mk (⟨c, hc⟩ : ↥Cb) : ↥Cb ⧸ N) ∣ orderOf (⟨c, hc⟩ : ↥Cb) :=
      orderOf_map_dvd (QuotientGroup.mk' N) _
    have hyord : orderOf (⟨c, hc⟩ : ↥Cb) = orderOf c := (Subgroup.orderOf_coe (⟨c, hc⟩ : ↥Cb)).symm
    have hcop1 : Nat.Coprime (orderOf (⟨c, hc⟩ : ↥Cb)) 3 := by
      rw [hyord]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3c).symm
    have hcop2 : Nat.Coprime (orderOf (QuotientGroup.mk (⟨c, hc⟩ : ↥Cb) : ↥Cb ⧸ N)) 3 :=
      Nat.Coprime.coprime_dvd_left hd2 hcop1
    have hcop3 := Nat.Coprime.pow_right j hcop2
    have hone : orderOf (QuotientGroup.mk (⟨c, hc⟩ : ↥Cb) : ↥Cb ⧸ N) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop3 hd1
    exact ⟨⟨c, hc⟩, (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 hone), rfl⟩
  have hpr : ∀ y ∈ N, ¬ 3 ∣ orderOf (y : G) := by
    intro y hy hd
    have hd' : 3 ∣ orderOf y := by rwa [Subgroup.orderOf_coe] at hd
    have e1 : orderOf (⟨y, hy⟩ : ↥N) = orderOf y := (Subgroup.orderOf_coe (⟨y, hy⟩ : ↥N)).symm
    have h1 : 3 ∣ Nat.card ↥N :=
      dvd_trans (by rw [e1]; exact hd') (orderOf_dvd_natCard (⟨y, hy⟩ : ↥N))
    exact absurd (Nat.Coprime.eq_one_of_dvd hNcop h1) (by norm_num)
  have hconjN : ∀ g ∈ Cen b, ∀ y ∈ N, ∃ y' ∈ N, (y' : G) = g * (y : G) * g⁻¹ := by
    intro g hg y hy
    have hord : orderOf (g * (y : G) * g⁻¹) = orderOf (y : G) :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
    obtain ⟨y', hy', hy'eq⟩ :=
      hgood (g * (y : G) * g⁻¹) (hCbCen g hg y y.2) (by rw [hord]; exact hpr y hy)
    exact ⟨y', hy', hy'eq⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : Subgroup ↥(Cen b), N2 = N.map (Subgroup.inclusion hCbLe) :=
    ⟨_, rfl⟩
  have hN2mem : ∀ y ∈ N, Subgroup.inclusion hCbLe y ∈ N2 := fun y hy => by
    rw [hN2]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hN2n : N2.Normal := ⟨fun n hn g => by
    rw [hN2] at hn
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨y', hy', hy'eq⟩ := hconjN g.1 g.2 y hy
    rw [hN2]
    exact Subgroup.mem_map.2 ⟨y', hy', Subtype.ext (by simp [hy'eq])⟩⟩
  have hN2cop : Nat.Coprime 3 (Nat.card N2) := by
    rw [hN2, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hCbLe)]
    exact hNcop
  have hXN : ∀ y ∈ N, (y : G) ∈ inSubgroup (pPrimeCore 3) (Cen b) := fun y hy =>
    opp3_of_normal_coprime (H := Cen b) hN2n hN2cop
      (Subgroup.mem_map.2 ⟨Subgroup.inclusion hCbLe y, hN2mem y hy, rfl⟩)
  have hT2 : Cb ≤ Subgroup.zpowers b ⊔ inSubgroup (pPrimeCore 3) (Cen b) := by
    intro c hc
    have hle : S ⊔ N ≤ Subgroup.comap Cb.subtype
        (Subgroup.zpowers b ⊔ inSubgroup (pPrimeCore 3) (Cen b)) := by
      refine sup_le ?_ ?_
      · rw [hSdef, Subgroup.zpowers_le]
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
      · intro y hy
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right (hXN y hy))
    have hmem : (⟨c, hc⟩ : ↥Cb) ∈ S ⊔ N := by
      rw [hA]
      exact Subgroup.mem_top _
    exact Subgroup.mem_comap.1 (hle hmem)
  exact ⟨opp3_le_cenS h, le_antisymm (sup_le (Subgroup.zpowers_le.2 hbCb) hXCb) hT2,
    zpowers_inf_opp h⟩

section Monomial

def RealSP (b b₁ b₂ : G) (B : Subgroup G) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤˣ) : Prop :=
  ∃ n ∈ Nor B, ∀ i : Fin 3,
    n * (![b, b₁, b₂] i) * n⁻¹ = (![b, b₁, b₂] (π i)) ^ ((ε i : ℤˣ) : ℤ)

theorem realSP_mul {b b₁ b₂ : G} {B : Subgroup G} {π π' π'' : Equiv.Perm (Fin 3)}
    {ε ε' ε'' : Fin 3 → ℤˣ}
    (h : RealSP b b₁ b₂ B π ε) (h' : RealSP b b₁ b₂ B π' ε') (hπ : π'' = π * π')
    (hε : ∀ i, ε'' i = ε (π' i) * ε' i) : RealSP b b₁ b₂ B π'' ε'' := by
  obtain ⟨n, hn, hnv⟩ := h
  obtain ⟨n', hn', hnv'⟩ := h'
  subst hπ
  refine ⟨n * n', mul_mem hn hn', fun i => ?_⟩
  have e1 : n * n' * (![b, b₁, b₂] i) * (n * n')⁻¹
      = n * (n' * (![b, b₁, b₂] i) * n'⁻¹) * n⁻¹ := by group
  rw [e1, hnv' i, ← conj_zpow, hnv (π' i), ← zpow_mul, Equiv.Perm.mul_apply, hε i,
    Units.val_mul]

theorem realSP_congr_perm {b b₁ b₂ : G} {B : Subgroup G} {π π' : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → ℤˣ} (h : RealSP b b₁ b₂ B π ε) (hπ : π = π') : RealSP b b₁ b₂ B π' ε := by
  subst hπ; exact h

theorem realSP_congr_sign {b b₁ b₂ : G} {B : Subgroup G} {π : Equiv.Perm (Fin 3)}
    {ε ε' : Fin 3 → ℤˣ} (h : RealSP b b₁ b₂ B π ε) (hε : ε = ε') :
    RealSP b b₁ b₂ B π ε' := by
  subst hε; exact h

theorem realSP_one {b b₁ b₂ : G} {B : Subgroup G} : RealSP b b₁ b₂ B 1 1 :=
  ⟨1, one_mem _, fun i => by simp⟩

theorem realSP_all {b b₁ b₂ : G} {B : Subgroup G}
    (hflip : ∃ n ∈ Nor B, n * b * n⁻¹ = b⁻¹ ∧ n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂)
    (hswap : ∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b ∧ n * b₂ * n⁻¹ = b₂)
    (hcyc : ∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b) :
    ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤˣ), RealSP b b₁ b₂ B π ε := by
  have hflipR : RealSP b b₁ b₂ B 1 (fun j => if j = 0 then (-1 : ℤˣ) else 1) := by
    obtain ⟨n, hn, h0, h1, h2⟩ := hflip
    refine ⟨n, hn, fun i => ?_⟩
    fin_cases i <;> simp [h0, h1, h2]
  have hS01 : RealSP b b₁ b₂ B (Equiv.swap 0 1) 1 := by
    obtain ⟨n, hn, h0, h1, h2⟩ := hswap
    refine ⟨n, hn, fun i => ?_⟩
    fin_cases i <;> simp [Equiv.swap_apply_def, h0, h1, h2]
  have hf : RealSP b b₁ b₂ B (finRotate 3) 1 := by
    obtain ⟨n, hn, h0, h1, h2⟩ := hcyc
    refine ⟨n, hn, fun i => ?_⟩
    fin_cases i <;> simp [h0, h1, h2]
  have hff : RealSP b b₁ b₂ B (finRotate 3 * finRotate 3) 1 :=
    realSP_mul hf hf rfl (fun i => by simp)
  have hffS : RealSP b b₁ b₂ B ((finRotate 3 * finRotate 3) * Equiv.swap 0 1) 1 :=
    realSP_mul hff hS01 rfl (fun i => by simp)
  have hffSf : RealSP b b₁ b₂ B ((finRotate 3 * finRotate 3) * Equiv.swap 0 1 * finRotate 3) 1 :=
    realSP_mul hffS hf rfl (fun i => by simp)
  have hS02 : RealSP b b₁ b₂ B (Equiv.swap 0 2) 1 :=
    realSP_congr_perm hffSf (by decide)
  have hfS : RealSP b b₁ b₂ B (finRotate 3 * Equiv.swap 0 1) 1 :=
    realSP_mul hf hS01 rfl (fun i => by simp)
  have hfSff : RealSP b b₁ b₂ B (finRotate 3 * Equiv.swap 0 1 * (finRotate 3 * finRotate 3)) 1 :=
    realSP_mul hfS hff rfl (fun i => by simp)
  have hS12 : RealSP b b₁ b₂ B (Equiv.swap 1 2) 1 :=
    realSP_congr_perm hfSff (by decide)
  have hswap_real : ∀ x y : Fin 3, x ≠ y → RealSP b b₁ b₂ B (Equiv.swap x y) 1 := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    all_goals first
      | exact absurd rfl hxy
      | exact hS01
      | (rw [Equiv.swap_comm]; exact hS01)
      | exact hS02
      | (rw [Equiv.swap_comm]; exact hS02)
      | exact hS12
      | (rw [Equiv.swap_comm]; exact hS12)
  have hconj : ∀ (σ : Equiv.Perm (Fin 3)) (f : Fin 3 → ℤˣ), σ * σ = 1 →
      RealSP b b₁ b₂ B σ 1 → RealSP b b₁ b₂ B 1 f →
      RealSP b b₁ b₂ B 1 (fun i => f (σ i)) := by
    intro σ f hσ hr hf'
    have h1 : RealSP b b₁ b₂ B (σ * 1) f := realSP_mul hr hf' rfl (fun i => by simp)
    exact realSP_mul h1 hr (by rw [mul_one]; exact hσ.symm) (fun i => by simp)
  have hflipAt : ∀ i : Fin 3, RealSP b b₁ b₂ B 1 (fun j => if j = i then (-1 : ℤˣ) else 1) := by
    intro i
    fin_cases i
    · exact hflipR
    · refine realSP_congr_sign (hconj (Equiv.swap 0 1) _ (Equiv.swap_mul_self 0 1) hS01 hflipR) ?_
      funext j; fin_cases j <;> simp [Equiv.swap_apply_def]
    · refine realSP_congr_sign (hconj (Equiv.swap 0 2) _ (Equiv.swap_mul_self 0 2) hS02 hflipR) ?_
      funext j; fin_cases j <;> simp [Equiv.swap_apply_def]
  have hsingle : ∀ (i : Fin 3) (x : ℤˣ), RealSP b b₁ b₂ B 1 (fun j => if j = i then x else 1) := by
    intro i x
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact realSP_congr_sign realSP_one (by funext j; simp)
    · exact hflipAt i
  have hprod : ∀ g h : Fin 3 → ℤˣ, RealSP b b₁ b₂ B 1 g → RealSP b b₁ b₂ B 1 h →
      RealSP b b₁ b₂ B 1 (g * h) :=
    fun g h hg hh => realSP_mul hg hh (by simp) (fun i => by simp)
  have hε1 : ∀ ε : Fin 3 → ℤˣ, RealSP b b₁ b₂ B 1 ε := by
    intro ε
    have hdecomp : ε = (fun j => if j = 0 then ε 0 else 1) * (fun j => if j = 1 then ε 1 else 1) *
        (fun j => if j = 2 then ε 2 else 1) := by
      funext j; fin_cases j <;> simp
    rw [hdecomp]
    exact hprod _ _ (hprod _ _ (hsingle 0 _) (hsingle 1 _)) (hsingle 2 _)
  have hπ1 : ∀ π : Equiv.Perm (Fin 3), RealSP b b₁ b₂ B π 1 := by
    intro π
    refine Equiv.Perm.swap_induction_on π realSP_one ?_
    intro f x y hxy ih
    exact realSP_mul (hswap_real x y hxy) ih rfl (fun i => by simp)
  intro π ε
  exact realSP_mul (hπ1 π) (hε1 ε) (by simp) (fun i => by simp)

end Monomial

theorem P_monomial (h : FF84Sec3 b L B b₁ b₂) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℤˣ) :
    ∃ n ∈ Nor B, ∀ i : Fin 3,
      n * (![b, b₁, b₂] i) * n⁻¹ = (![b, b₁, b₂] (π i)) ^ ((ε i : ℤˣ) : ℤ) := by
  obtain ⟨-, -, -, hflip, hswap, hcyc⟩ := h.mono
  exact realSP_all hflip hswap hcyc π ε

theorem P_inv₂ (h : FF84Sec3 b L B b₁ b₂) : FF84Sec3 b L B b₁ b₂⁻¹ := by
  have P1 := P_monomial h 1 (fun j => if j = 0 then (-1 : ℤˣ) else 1)
  have P2 := P_monomial h (Equiv.swap 0 1) 1
  have P3 := P_monomial h (finRotate 3) (fun j => if j = 0 then (1 : ℤˣ) else -1)
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  have hc : Subgroup.closure ({b₁, b₂⁻¹} : Set G) = B ⊓ L := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact Subgroup.mem_inf.2 ⟨mem_B_b₁ h, (Subgroup.mem_inf.1 h.hb₁).2⟩
      · exact Subgroup.mem_inf.2 ⟨inv_mem (mem_B_b₂ h), inv_mem (Subgroup.mem_inf.1 h.hb₂).2⟩
    · rw [h.gen]
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact Subgroup.subset_closure (by simp)
      · simpa using Subgroup.inv_mem _ (Subgroup.subset_closure
          (show b₂⁻¹ ∈ ({b₁, b₂⁻¹} : Set G) by simp))
  have hcl : B = Subgroup.closure ({b, b₁, b₂⁻¹} : Set G) := by
    apply le_antisymm
    · calc B = Subgroup.closure ({b, b₁, b₂} : Set G) := h.mono.2.1
        _ ≤ Subgroup.closure ({b, b₁, b₂⁻¹} : Set G) := by
          refine (Subgroup.closure_le _).2 ?_
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with hy | hy | hy <;> rw [hy]
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
          · simpa using Subgroup.inv_mem _ (Subgroup.subset_closure
              (show b₂⁻¹ ∈ ({b, b₁, b₂⁻¹} : Set G) by simp))
    · refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact mem_B_b h
      · exact mem_B_b₁ h
      · exact inv_mem (mem_B_b₂ h)
  have hnor : ∀ n ∈ Nor B, ∀ x ∈ ({b, b₁, b₂⁻¹} : Set G),
      n * x * n⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂⁻¹, b₂⁻¹⁻¹} : Set G) := by
    intro n hn x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx | hx <;> rw [hx]
    · have := h.mono.2.2.1 n hn b (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1]
    · have := h.mono.2.2.1 n hn b₁ (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1]
    · rw [show n * b₂⁻¹ * n⁻¹ = (n * b₂ * n⁻¹)⁻¹ by group]
      have := h.mono.2.2.1 n hn b₂ (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> simp
  have flip : ∃ n ∈ Nor B, n * b * n⁻¹ = b⁻¹ ∧ n * b₁ * n⁻¹ = b₁ ∧ n * b₂⁻¹ * n⁻¹ = b₂⁻¹ := by
    obtain ⟨n, hn, hv⟩ := P1
    have e0 : n * b * n⁻¹ = b⁻¹ := by simpa using hv 0
    have e1 : n * b₁ * n⁻¹ = b₁ := by simpa using hv 1
    have e2 : n * b₂ * n⁻¹ = b₂ := by simpa using hv 2
    exact ⟨n, hn, e0, e1, by rw [show n * b₂⁻¹ * n⁻¹ = (n * b₂ * n⁻¹)⁻¹ by group, e2]⟩
  have swap : ∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b ∧ n * b₂⁻¹ * n⁻¹ = b₂⁻¹ := by
    obtain ⟨n, hn, hv⟩ := P2
    have e0 : n * b * n⁻¹ = b₁ := by simpa [Equiv.swap_apply_def] using hv 0
    have e1 : n * b₁ * n⁻¹ = b := by simpa [Equiv.swap_apply_def] using hv 1
    have e2 : n * b₂ * n⁻¹ = b₂ := by simpa [Equiv.swap_apply_def] using hv 2
    exact ⟨n, hn, e0, e1, by rw [show n * b₂⁻¹ * n⁻¹ = (n * b₂ * n⁻¹)⁻¹ by group, e2]⟩
  have cyc : ∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₂⁻¹ ∧ n * b₂⁻¹ * n⁻¹ = b := by
    obtain ⟨n, hn, hv⟩ := P3
    have e0 : n * b * n⁻¹ = b₁ := by simpa [r0] using hv 0
    have e1 : n * b₁ * n⁻¹ = b₂⁻¹ := by simpa [r1] using hv 1
    have e2 : n * b₂ * n⁻¹ = b⁻¹ := by simpa [r2] using hv 2
    exact ⟨n, hn, e0, e1, by rw [show n * b₂⁻¹ * n⁻¹ = (n * b₂ * n⁻¹)⁻¹ by group, e2, inv_inv]⟩
  have mono : IsFullMonomial B b b₁ b₂⁻¹ := by
    unfold IsFullMonomial
    exact ⟨h.mono.1, hcl, hnor, flip, swap, cyc⟩
  exact
    { hyp := h.hyp
      sylB := h.sylB
      hb₁ := h.hb₁
      hb₂ := inv_mem h.hb₂
      gen := hc.symm
      mono := mono
      fus := h.fus
      caseA := h.caseA }

theorem P_caseA₂ (h : FF84Sec3 b L B b₁ b₂) :
    Nat.card ↥(L ⊓ Cen b₂) = 18 * Nat.card (Subgroup.center L) := by
  obtain ⟨n, hnB, hv⟩ := P_monomial h (Equiv.swap 1 2) 1
  have e0 : n * b * n⁻¹ = b := by simpa [Equiv.swap_apply_def] using hv 0
  have e1 : n * b₁ * n⁻¹ = b₂ := by simpa [Equiv.swap_apply_def] using hv 1
  have hcen : n ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hnb_comm : n * b = b * n := by
      have h1 : n * b * n⁻¹ * n = b * n := by rw [e0]
      simpa using h1
    have hbn : Commute b n := hnb_comm.symm
    exact (hbn.zpow_left k).eq
  have hnN : n ∈ Nor (Subgroup.zpowers b) := Subgroup.centralizer_le_normalizer _ hcen
  have hnL : n ∈ Nor L := P_Nb_normalizes_L h hnN
  have hc := card_inf_cen_eq_of_conj hnL e1
  rw [← hc]
  exact h.caseA

end Standing

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
