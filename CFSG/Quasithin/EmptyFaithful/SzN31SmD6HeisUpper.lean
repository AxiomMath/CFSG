module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpB
public import CFSG.Quasithin.EmptyFaithful.SzN31Basic
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinB
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Quasithin.G11 CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem eq_one_of_two_power_centralizes [Nontrivial V] {Pb : Subgroup (GLV V)}
    (hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤) {q : GLV V} {k : ℕ}
    (hq : q ^ 2 ^ k = 1) (hc : ∀ p ∈ Pb, q * p = p * q) : q = 1 := by
  have hN : IsPGroup 2 (Subgroup.zpowers q) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  obtain ⟨v, hv0, hvfix⟩ := exists_ne_zero_fixed_of_isPGroup hN
  have hvq : q v = v := hvfix q (Subgroup.mem_zpowers q)
  have hinv : Invariant Pb (fixSp V q ⊤) := fun g hg u hu =>
    fixSp_invariant (hc g hg).symm (fun _ _ => Submodule.mem_top) u hu
  rcases hirr _ hinv with h0 | h1
  · exfalso
    have : v ∈ fixSp V q ⊤ := mem_fixSp.2 ⟨Submodule.mem_top, hvq⟩
    rw [h0] at this
    exact hv0 ((Submodule.mem_bot (ZMod 2)).1 this)
  · ext u
    have : u ∈ fixSp V q ⊤ := by rw [h1]; exact Submodule.mem_top
    exact (mem_fixSp.1 this).2

theorem card_dvd_sixteen_of_normalizing_two_group [Nontrivial V] {Pb : Subgroup (GLV V)}
    (hP27 : Nat.card Pb = 27) (hnc : ∃ u ∈ Pb, ∃ v ∈ Pb, u * v ≠ v * u)
    (hexp : ∀ g ∈ Pb, g ^ 3 = 1)
    (hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤)
    {T : Subgroup (GLV V)} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (Pb : Set (GLV V))) : Nat.card T ∣ 16 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 Pb := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  have hdisj : Disjoint T Pb := IsPGroup.disjoint_of_ne 2 3 (by norm_num) T Pb hT2 hP3
  set H : Subgroup (GLV V) := T ⊔ Pb
  have hPH : Pb ≤ H := le_sup_right
  haveI hn1 : (Pb.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTN
  haveI hn2 : (Pb.subgroupOf H).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T Pb hTN
  have hbot : Pb.subgroupOf T = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have h1 : (t : GLV V) = 1 := Subgroup.disjoint_def.1 hdisj t.2 ht
    exact Subtype.ext h1
  have hindex : (Pb.subgroupOf H).index = Nat.card T := by
    rw [Subgroup.index_eq_card, ← Nat.card_congr e.toEquiv]
    have hs : Nat.card (Pb.subgroupOf T) = 1 := by rw [hbot]; exact Subgroup.card_bot
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Pb.subgroupOf T)
    rw [hs, mul_one] at this
    exact this.symm
  have hQ2 : IsPGroup 2 (↥H ⧸ Pb.subgroupOf H) := by
    have : IsPGroup 2 (↥T ⧸ Pb.subgroupOf T) := hT2.to_quotient _
    exact this.of_equiv e
  have hC : ∀ g : ↥H, (∀ w ∈ Pb.subgroupOf H, g * w = w * g) → g ∈ Pb.subgroupOf H := by
    intro g hg
    have hcomm : ∀ p ∈ Pb, (g : GLV V) * p = p * g := fun p hp =>
      congrArg Subtype.val (hg ⟨p, hPH hp⟩ hp)
    obtain ⟨j, hj⟩ := hQ2 (g : ↥H ⧸ Pb.subgroupOf H)
    have hgj : g ^ 2 ^ j ∈ Pb.subgroupOf H := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hj
    have hgj' : (g : GLV V) ^ 2 ^ j ∈ Pb := hgj
    have hg3 : (g : GLV V) ^ 3 = 1 := by
      refine eq_one_of_two_power_centralizes hirr (k := j) ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul]
        exact hexp _ hgj'
      · intro p hp
        exact (Commute.pow_left (show Commute (g : GLV V) p from hcomm p hp) 3).eq
    have h4 : (g : GLV V) = ((g : GLV V) ^ 2 ^ j) ^ 2 ^ j := by
      have hmod : (2 ^ j * 2 ^ j) % 3 = 1 := by
        rw [← mul_pow]
        norm_num [Nat.pow_mod]
      rw [← pow_mul, pow_eq_pow_mod _ hg3, hmod, pow_one]
    exact (Subgroup.mem_subgroupOf).2 (by rw [h4]; exact Pb.pow_mem hgj' _)
  have hP'card : Nat.card (Pb.subgroupOf H) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP27]
  have hnc' : ∃ u ∈ Pb.subgroupOf H, ∃ v ∈ Pb.subgroupOf H, u * v ≠ v * u := by
    obtain ⟨u, hu, v, hv, huv⟩ := hnc
    exact ⟨⟨u, hPH hu⟩, hu, ⟨v, hPH hv⟩, hv, fun h => huv (congrArg Subtype.val h)⟩
  have hdvd48 : (Pb.subgroupOf H).index ∣ 48 := index_dvd_forty_eight _ hP'card hnc' hC
  rw [hindex] at hdvd48
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hT2)
  rw [hk] at hdvd48 ⊢
  have h16 : 2 ^ k ∣ 16 * 3 := by simpa using hdvd48
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h16

end SmD6Heis

end CFSG.Quasithin.SzN31
