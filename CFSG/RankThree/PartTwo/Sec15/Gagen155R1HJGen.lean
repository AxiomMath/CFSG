module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Cube
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartOne.KF.SU5Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_card_sup_zpowers_of_centralizer {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} {y : G} (hE : CFSG.Open.IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hyE : y ∈ Subgroup.centralizer (E : Set G))
    (hyord : orderOf y = p) (hynot : y ∉ E) :
    CFSG.Open.IsElemAbelian p (E ⊔ Subgroup.zpowers y) ∧
      Nat.card (E ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 3 := by
  have hyp : y ^ p = 1 := by
    rw [← hyord]
    exact pow_orderOf_eq_one y
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hay : Commute a y := Subgroup.mem_centralizer_iff.mp hyE a ha
    rw [← hn]
    exact hay.zpow_right n
  have hea : CFSG.Open.IsElemAbelian p (E ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE
      (CFSG.Open.isElemAbelian_zpowers hyp) hcomm
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (E : Set G) hyE)
  have hdisj : Disjoint E (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    by_contra hne
    have hKne : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) ≠ 1 := by
      intro hc
      exact hne (Subgroup.eq_bot_of_card_eq (E ⊓ Subgroup.zpowers y) hc)
    have hdvd : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) ∣ p := by
      simpa [Nat.card_zpowers, hyord] using
        (Subgroup.card_dvd_of_le
          (inf_le_right : E ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y))
    have hKcard : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) = p := by
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
      · exact absurd h1 hKne
      · exact hp'
    have heq : E ⊓ Subgroup.zpowers y = Subgroup.zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [hKcard, Nat.card_zpowers, hyord]
    have hyK : y ∈ E ⊓ Subgroup.zpowers y := by
      rw [heq]
      exact Subgroup.mem_zpowers y
    exact hynot (Subgroup.mem_inf.mp hyK).1
  refine ⟨hea, ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
    (Subgroup.zpowers y) hnorm hdisj, hEcard, Nat.card_zpowers, hyord]
  ring

theorem exists_sylow_two_image_of_two_element {H U : Subgroup G} (hUH : U ≤ H) {x : G}
    (hxU : x ∈ U) (hx1 : x ≠ 1) (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) :
    ∃ P : Sylow 2 (U.subgroupOf H), ∃ S : Subgroup G,
      S = (((P : Subgroup (U.subgroupOf H)).map (U.subgroupOf H).subtype).map H.subtype) ∧
      S ≤ U ∧ x ∈ S ∧ S ≠ ⊥ ∧ IsPGroup 2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥H := U.subgroupOf H
  let xH : ↥H := ⟨x, hUH hxU⟩
  have hxN : xH ∈ N := by
    rw [Subgroup.mem_subgroupOf]
    exact hxU
  let xN : ↥N := ⟨xH, hxN⟩
  obtain ⟨k, hk⟩ := hx2
  have hxN_order : orderOf xN = 2 ^ k := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hk]
  have hxN2 : IsPGroup 2 (Subgroup.zpowers xN) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hxN_order])
  obtain ⟨P, hPle⟩ := hxN2.exists_le_sylow
  let SH : Subgroup ↥H := (P : Subgroup N).map N.subtype
  let S : Subgroup G := SH.map H.subtype
  have hSU : S ≤ U := by
    intro s hs
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hh
    have hpU : ((p : ↥H) : G) ∈ U := Subgroup.mem_subgroupOf.mp p.2
    rw [← hp_eq]
    simpa using hpU
  have hxS : x ∈ S := by
    have hxH : xH ∈ SH := by
      refine Subgroup.mem_map.mpr ⟨xN, ?_, rfl⟩
      exact hPle (Subgroup.mem_zpowers xN)
    exact Subgroup.mem_map.mpr ⟨xH, hxH, rfl⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxS
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  have hS2 : IsPGroup 2 S := (P.isPGroup'.map N.subtype).map H.subtype
  exact ⟨P, S, rfl, hSU, hxS, hSne, hS2⟩

theorem prime_dvd_card_quotient_of_orderOf_eq_pow_of_not_mem {p : ℕ} (hp : p.Prime)
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal] {f : H} {k : ℕ}
    (hf : orderOf f = p ^ k) (hfN : f ∉ N) : p ∣ Nat.card (H ⧸ N) := by
  let q : H ⧸ N := QuotientGroup.mk' N f
  have hqne : q ≠ 1 := by
    change ((f : H) : H ⧸ N) ≠ 1
    intro h
    exact hfN ((QuotientGroup.eq_one_iff f).mp h)
  have hq_dvd : orderOf q ∣ p ^ k := by
    simpa [q, hf] using orderOf_map_dvd (QuotientGroup.mk' N) f
  obtain ⟨j, -, hj_eq⟩ := (Nat.dvd_prime_pow hp).mp hq_dvd
  have hjpos : 0 < j := by
    by_contra hj0
    have hjz : j = 0 := Nat.eq_zero_of_not_pos hj0
    exact hqne (by rw [← orderOf_eq_one_iff, hj_eq, hjz, pow_zero])
  have hpdvd : p ∣ orderOf q := by
    rw [hj_eq]
    exact dvd_pow_self p hjpos.ne'
  have hcard : orderOf q ∣ Nat.card (H ⧸ N) := by
    have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (H ⧸ N)) (Subgroup.mem_top q)
    rwa [Subgroup.card_top] at h
  exact hpdvd.trans hcard

theorem false_of_e125 (hlr : CFSG.Assembly.RankThreeEven.localRank 5 G < 3)
    {E S : Subgroup G} {y : G} (hE : CFSG.Open.IsElemAbelian 5 E) (hE25 : Nat.card E = 25)
    (hyE : y ∈ Subgroup.centralizer (E : Set G)) (hy5 : orderOf y = 5) (hynot : y ∉ E)
    (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hyS : y ∈ Subgroup.normalizer (S : Set G)) : False := by
  obtain ⟨hF, hFcard⟩ :=
    isElemAbelian_card_sup_zpowers_of_centralizer Nat.prime_five hE hE25 hyE hy5 hynot
  have hFS : E ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (S : Set G) :=
    sup_le hES (Subgroup.zpowers_le.mpr hyS)
  exact CFSG.RankThree.PartTwo.Sec13.F135Last.false_of_elemAbelian_cube
    Nat.prime_five hlr hF hFcard hS hS2 hFS

theorem exists_five_mem_normalizer_two {U : Subgroup G} {f : G}
    (hfU : f ∈ Subgroup.normalizer (U : Set G)) (hf5 : ∃ k : ℕ, orderOf f = 5 ^ k)
    (hfnot : f ∉ U) {x : G} (hxU : x ∈ U) (hx1 : x ≠ 1) (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) :
    ∃ S : Subgroup G, S ≤ U ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∃ y : G, orderOf y = 5 ∧
      y ∈ U ⊔ Subgroup.zpowers f ∧ y ∈ Subgroup.normalizer (S : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set H : Subgroup G := U ⊔ Subgroup.zpowers f with hHdef
  have hfH : f ∈ H := by rw [hHdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hUH : U ≤ H := by rw [hHdef]; exact le_sup_left
  have hHnorm : H ≤ Subgroup.normalizer (U : Set G) := by
    rw [hHdef]
    exact sup_le (fun u hu => Subgroup.le_normalizer hu) (Subgroup.zpowers_le.mpr hfU)
  let N : Subgroup ↥H := U.subgroupOf H
  haveI hNnormal : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  obtain ⟨P, S, hSdef, hSU, hxS, hSne, hS2⟩ :=
    exists_sylow_two_image_of_two_element hUH hxU hx1 hx2
  obtain ⟨k, hk⟩ := hf5
  have hfH_notN : (⟨f, hfH⟩ : ↥H) ∉ N := by
    rw [Subgroup.mem_subgroupOf]
    exact hfnot
  have h5card : 5 ∣ Nat.card (↥H ⧸ N) :=
    prime_dvd_card_quotient_of_orderOf_eq_pow_of_not_mem Nat.prime_five
      (by rw [Subgroup.orderOf_mk, hk]) hfH_notN
  obtain ⟨yH, hyHord, hyHnorm⟩ :=
    CFSG.RankThree.PartOne.KFSU5.exists_orderOf_eq_normalizer_sylow N P h5card
  refine ⟨S, hSU, hSne, hS2, (yH : G), ?_, ?_, ?_⟩
  · simpa using hyHord
  · simpa [hHdef] using yH.2
  · simpa [hSdef] using
      (CFSG.RankThree.PartTwo.Sec13.F135Last.r5b_map_normalizer_mem H.subtype_injective hyHnorm)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
