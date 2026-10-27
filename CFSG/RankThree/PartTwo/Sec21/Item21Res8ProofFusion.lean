module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofAL
public import CFSG.RankThree.PartTwo.Sec21.Item21Res8ProofM24
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res8Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint Subgroup

theorem exists_conj_of_mem_zpowers_sup {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {u v : Y} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (hv : v ∈ zpowers u ⊔ N) :
    ∃ t : Y, (zpowers v).map (MulAut.conj t).toMonoidHom = zpowers u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := zpowers u ⊔ N with hD
  have hcu : Nat.card (zpowers u) = 3 := Sec13.card_zpowers_of_pow_three hu3 hu1
  have hinf : N ⊓ zpowers u = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hcu]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN).symm
  have hDcard : Nat.card D = 3 ^ 1 * Nat.card N := by
    have h1 : N.relIndex D = 3 := by
      rw [hD, sup_comm, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf,
        Subgroup.relIndex_bot_left, hcu]
    have h2 := (N.subgroupOf D).card_mul_index
    rw [show (N.subgroupOf D).index = N.relIndex D from rfl, h1,
      Nat.card_congr (subgroupOfEquivOfLe (show N ≤ D from le_sup_right)).toEquiv] at h2
    rw [← h2]
    ring
  have hDf : (Nat.card D).factorization 3 = 1 := by
    rw [hDcard, Sec4.Item434AltPerm.factorization_three_pow_mul 1 hN]
  have huD : zpowers u ≤ D := le_sup_left
  have hvD : zpowers v ≤ D := zpowers_le.mpr hv
  have hU : Nat.card ((zpowers u).subgroupOf D) = 3 ^ (Nat.card D).factorization 3 := by
    rw [hDf, pow_one, ← hcu]
    exact Nat.card_congr (subgroupOfEquivOfLe huD).toEquiv
  have hV : IsPGroup 3 ((zpowers v).subgroupOf D) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, ← Sec13.card_zpowers_of_pow_three hv3 hv1]
    exact Nat.card_congr (subgroupOfEquivOfLe hvD).toEquiv
  obtain ⟨t, ht⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hU hV
  have hvV : (⟨v, hvD (mem_zpowers v)⟩ : D) ∈ (zpowers v).subgroupOf D :=
    mem_subgroupOf.mpr (mem_zpowers v)
  obtain ⟨y, hyU, hyv⟩ := mem_map.mp (ht hvV)
  have hyu : (y : Y) ∈ zpowers u := mem_subgroupOf.mp hyU
  have hyv' : (t : Y) * y * (t : Y)⁻¹ = v := congrArg Subtype.val hyv
  have hy1 : (y : Y) ≠ 1 := by
    intro h1
    apply hv1
    rw [← hyv', h1]
    group
  have hy3 : (y : Y) ^ 3 = 1 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hyu
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  have hyz : zpowers (y : Y) = zpowers u := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr hyu) ?_
    rw [hcu, Sec13.card_zpowers_of_pow_three hy3 hy1]
  refine ⟨(t : Y)⁻¹, ?_⟩
  rw [MonoidHom.map_zpowers, ← hyz]
  refine congrArg zpowers ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [← hyv']
  group

variable {G : Type} [Group G] [Finite G]

theorem exists_fusion_of_m24 {L : Subgroup G} {d : G}
    (hM24 : Nonempty (lBar L ≃* NativeSporadic.M24)) (hdcen : IsCentral218 L d)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hI : 3 ^ 3 ∣ Nat.card (iOf218 L d)) :
    ∃ a ∈ iOf218 L d, a ^ 3 = 1 ∧ a ∉ zpowers d ∧ ∃ g ∈ L,
      (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  obtain ⟨S, ⟨Q₀, hQ₀S⟩, hdS⟩ := hdcen
  obtain ⟨e⟩ := hM24
  set N := aschbacherSolvableCore 3 ↥L with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  set f : ↥L →* NativeSporadic.M24 := e.toMonoidHom.comp (QuotientGroup.mk' N) with hfdef
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hfker : ∀ l : ↥L, f l = 1 → l ∈ N := by
    intro l hl
    have h1 : QuotientGroup.mk' N l = 1 := e.injective (by rw [map_one]; exact hl)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hSL : S ≤ L := hQ₀S ▸ map_subtype_le _
  have hdSc : ∀ s ∈ S, s * d = d * s := by
    intro s hs
    obtain ⟨z, hz, hzd⟩ := mem_map.mp hdS
    have h1 := mem_center_iff.mp hz ⟨s, hs⟩
    have h2 := congrArg Subtype.val h1
    rw [← hzd]
    exact h2
  have hSp : IsPGroup 3 S := by
    rw [← hQ₀S]
    exact Q₀.isPGroup'.map L.subtype
  have hSC : S ≤ L ⊓ centralizer ({d} : Set G) := fun s hs =>
    ⟨hSL hs, mem_centralizer_singleton_iff.mpr (hdSc s hs)⟩
  have hIL : iOf218 L d ≤ L := (map_subtype_le _).trans inf_le_left
  have hL81 : ¬ 3 ^ (3 + 1) ∣ Nat.card L := Item2110Res3Proof.not_dvd_card_of_lBar (by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    norm_num)
  have hSI : S ≤ iOf218 L d := Item2110Res3Proof.le_of_dvd_card hSL hIL
    (hSC.trans (Item2110Res3Proof.le_normalizer_iOf218 L d)) hSp hI hL81
  have hL24 : (Nat.card NativeSporadic.M24).factorization 3 = 3 := by
    rw [CFSG.Sporadic.Mathieu.card_M24, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  have hQcard : Nat.card ((Q₀ : Subgroup ↥L).map f) = 27 := by
    have h1 := Sylow.card_eq_multiplicity (Q₀.mapSurjective hf)
    rw [Sylow.coe_mapSurjective, hL24] at h1
    rw [h1]
    norm_num
  set d₀ : ↥L := ⟨d, hdL⟩ with hd₀
  have hmemS : ∀ q : ↥L, q ∈ (Q₀ : Subgroup ↥L) → (q : G) ∈ S := fun q hq => by
    rw [← hQ₀S]
    exact mem_map_of_mem _ hq
  have hd₀Q : d₀ ∈ (Q₀ : Subgroup ↥L) := by
    have hdS' : d ∈ S := (map_subtype_le _) hdS
    rw [← hQ₀S] at hdS'
    obtain ⟨q, hq, hqd⟩ := mem_map.mp hdS'
    have hq' : q = d₀ := Subtype.ext hqd
    rwa [← hq']
  have hd₀3 : d₀ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hd₀1 : d₀ ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hxQ : f d₀ ∈ (Q₀ : Subgroup ↥L).map f := mem_map_of_mem f hd₀Q
  have hx1 : f d₀ ≠ 1 := by
    intro h1
    have h2 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 (hfker d₀ h1) (k := 1)
      (by rw [pow_one]; exact hd₀3)
    exact hd₀1 h2
  have hxc : ∀ q ∈ (Q₀ : Subgroup ↥L).map f, q * f d₀ = f d₀ * q := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := mem_map.mp hq
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hdSc _ (hmemS q₀ hq₀)))
  obtain ⟨w, hwQ, hw3, hwx, k, hk⟩ := m24_exists_fusion hQcard hxQ hx1 hxc
  obtain ⟨s₀, hs₀Q, hs₀w⟩ := mem_map.mp hwQ
  have hs₀3 : s₀ ^ 3 = 1 := by
    have hmem : s₀ ^ 3 ∈ N := hfker _ (by rw [map_pow, hs₀w, hw3])
    obtain ⟨m, hm⟩ := Q₀.isPGroup' ⟨s₀, hs₀Q⟩
    have hm' : s₀ ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 hmem (k := m) ?_
    rw [← pow_mul, mul_comm, pow_mul, hm', one_pow]
  have had : (s₀ : G) ∉ zpowers d := by
    intro h
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
    have hs₀d : s₀ = d₀ ^ n := Subtype.ext (by simpa using hn.symm)
    apply hwx
    rw [← hs₀w, hs₀d, map_zpow]
    exact zpow_mem (mem_zpowers _) n
  obtain ⟨g₁, hg₁⟩ := hf k
  have hfv : f (g₁ * s₀ * g₁⁻¹) ∈ zpowers (f d₀) := by
    rw [← hk]
    refine ⟨w, mem_zpowers w, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hg₁, hs₀w]
  have hvD : g₁ * s₀ * g₁⁻¹ ∈ zpowers d₀ ⊔ N := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hfv
    have h1 : (d₀ ^ n)⁻¹ * (g₁ * s₀ * g₁⁻¹) ∈ N :=
      hfker _ (by rw [map_mul, map_inv, map_zpow, hn, inv_mul_cancel])
    have h2 : g₁ * s₀ * g₁⁻¹ = d₀ ^ n * ((d₀ ^ n)⁻¹ * (g₁ * s₀ * g₁⁻¹)) := by group
    rw [h2]
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) n)) (mem_sup_right h1)
  have hv3 : (g₁ * s₀ * g₁⁻¹) ^ 3 = 1 := by rw [conj_pow, hs₀3, mul_one, mul_inv_cancel]
  have hv1 : g₁ * s₀ * g₁⁻¹ ≠ 1 := by
    intro h1
    have hs₀1 : s₀ = 1 := by
      calc s₀ = g₁⁻¹ * (g₁ * s₀ * g₁⁻¹) * g₁ := by group
        _ = 1 := by rw [h1]; group
    apply had
    rw [hs₀1]
    exact one_mem _
  obtain ⟨t, ht⟩ := exists_conj_of_mem_zpowers_sup hN3 hd₀3 hd₀1 hv3 hv1 hvD
  have h1 : zpowers (t * g₁ * s₀ * (t * g₁)⁻¹) = zpowers d₀ := by
    rw [← ht, MonoidHom.map_zpowers]
    refine congrArg zpowers ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h2 : zpowers ((t : G) * g₁ * s₀ * ((t : G) * g₁)⁻¹) = zpowers d := by
    have h3 := congrArg (Subgroup.map L.subtype) h1
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h3
    simpa using h3
  refine ⟨(s₀ : G), hSI (hmemS s₀ hs₀Q), by simpa using congrArg Subtype.val hs₀3, had,
    ((t * g₁ : ↥L) : G), (t * g₁).2, ?_⟩
  rw [MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul]
  exact h2

end CFSG.RankThree.PartTwo.Sec21.Item21Res8Proof
