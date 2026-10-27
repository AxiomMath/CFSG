module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThree
public import CFSG.Quasithin.Background.A318POutMore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

theorem exists_commute_notMem_zpowers_of_card_27 {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 27) {u : G} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) :
    ∃ t : G, t * u = u * t ∧ t ∉ Subgroup.zpowers u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hcardU : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hord]
  have hout : ∃ t : G, t ∉ Subgroup.zpowers u := by
    by_contra hcon
    push_neg at hcon
    have htop : Subgroup.zpowers u = ⊤ := by
      ext x
      simp [hcon x]
    have hc : Nat.card (Subgroup.zpowers u) = Nat.card G := by
      rw [htop, Subgroup.card_top]
    rw [hcardU, hG] at hc
    norm_num at hc
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by rw [hG]; norm_num)
  have hp : IsPGroup 3 G := IsPGroup.iff_card.2 ⟨3, by rw [hG]; norm_num⟩
  obtain ⟨z0, hz0c, hz01⟩ : ∃ z0 ∈ Subgroup.center G, z0 ≠ 1 := by
    haveI := IsPGroup.center_nontrivial hp
    obtain ⟨⟨z, hz⟩, hne⟩ := exists_ne (1 : Subgroup.center G)
    exact ⟨z, hz, fun h => hne (Subtype.ext h)⟩
  by_cases hcase : ∃ z ∈ Subgroup.center G, z ∉ Subgroup.zpowers u
  · obtain ⟨z, hzc, hzn⟩ := hcase
    exact ⟨z, (Subgroup.mem_center_iff.mp hzc u).symm, hzn⟩
  · push_neg at hcase
    have hz0u : z0 ∈ Subgroup.zpowers u := hcase z0 hz0c
    have hz0ord : orderOf z0 = 3 := by
      have hd : orderOf z0 ∣ 3 := by
        have := orderOf_dvd_of_mem_zpowers hz0u
        rwa [hord] at this
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hz01
      · exact h1
    have heq : Subgroup.zpowers z0 = Subgroup.zpowers u := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz0u) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hz0ord, hord]
    have huc : u ∈ Subgroup.center G := by
      have hu' : u ∈ Subgroup.zpowers z0 := by
        rw [heq]
        exact Subgroup.mem_zpowers u
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu'
      rw [← hk]
      exact (Subgroup.center G).zpow_mem hz0c k
    obtain ⟨t, ht⟩ := hout
    exact ⟨t, Subgroup.mem_center_iff.mp huc t, ht⟩

theorem ruK432_sylow_conj
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruSylowSub) (hx1 : x ≠ 1) :
    ∃ g ∈ ruP, g * x * g⁻¹ = ruXperm := by
  obtain ⟨he, -, -, hall⟩ := ruSylow_parts
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps he
  obtain ⟨i, hi, hxi⟩ := (hmem x).1 hx
  have hrep : Rep 4060 (ruSylCert ()).pts[i]! (permOfArr 4060 (ruSylCert ()).pts[i]!) :=
    rep_of_validA (hval i hi)
  rcases hall i hi with hid | ⟨g, hg, hgv, hgs, hgc⟩
  · exfalso
    apply hx1
    rw [← hxi]
    exact (eqA_iff hrep rep_idA).1 hid
  · refine ⟨permOfArr 4060 g, mem_ruP_of_sift (rep_of_validA hgv) hgs, ?_⟩
    rw [← hxi]
    exact eq_of_eqA (rep_conjA hgv hrep) rep_ruX hgc

theorem ruK432_ruXp_pow_three :
    ruXp ^ 3 = 1 :=
  Subtype.ext ruXperm_pow_three

theorem ruK432_ruXp_ne_one :
    ruXp ≠ 1 :=
  fun h => ruXperm_ne_one (congrArg Subtype.val h)

theorem ruK432_witness :
    ∃ w : ↥ruP, (w * ruXp * w⁻¹) * ruXp = ruXp * (w * ruXp * w⁻¹) ∧
      w * ruXp * w⁻¹ ≠ ruXp ∧ w * ruXp * w⁻¹ ≠ ruXp⁻¹ ∧ w * ruXp * w⁻¹ ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card (ruSylowSub.subgroupOf ruP) = 27 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruSylowSub_le).toEquiv
    rw [e, card_ruSylowSub]
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf_prime_sylow 3 3 (ruSylowSub.subgroupOf ruP)
    (by rw [hQ]; norm_num) (by rw [card_ruP]; norm_num)
    (orderOf_eq_prime ruK432_ruXp_pow_three ruK432_ruXp_ne_one)
  obtain ⟨u, hu⟩ : ∃ u : ↥ruP, u = h⁻¹ * ruXp * h := ⟨_, rfl⟩
  have huS : u ∈ ruSylowSub.subgroupOf ruP := by
    rw [hu]
    exact hh
  have hu3 : u ^ 3 = 1 := by
    rw [hu, show h⁻¹ * ruXp * h = h⁻¹ * ruXp * h⁻¹⁻¹ by simp, conj_pow,
      ruK432_ruXp_pow_three]
    simp
  have hu1 : u ≠ 1 := by
    intro h1
    apply ruK432_ruXp_ne_one
    rw [hu] at h1
    calc ruXp = h * (h⁻¹ * ruXp * h) * h⁻¹ := by group
      _ = 1 := by simp [h1]
  have hu3S : (⟨u, huS⟩ : ↥(ruSylowSub.subgroupOf ruP)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hu3)
  have hu1S : (⟨u, huS⟩ : ↥(ruSylowSub.subgroupOf ruP)) ≠ 1 :=
    fun h1 => hu1 (congrArg Subtype.val h1)
  obtain ⟨t, htc, htn⟩ := exists_commute_notMem_zpowers_of_card_27 hQ hu3S hu1S
  have ht1 : (t : ↥ruP) ≠ 1 := by
    intro h0
    apply htn
    have : t = 1 := Subtype.ext h0
    rw [this]
    exact Subgroup.one_mem _
  have htu : (t : ↥ruP) ≠ u := by
    intro h0
    apply htn
    have : t = ⟨u, huS⟩ := Subtype.ext h0
    rw [this]
    exact Subgroup.mem_zpowers _
  have htu' : (t : ↥ruP) ≠ u⁻¹ := by
    intro h0
    apply htn
    have : t = ⟨u, huS⟩⁻¹ := Subtype.ext (by simpa using h0)
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have htcomm : (t : ↥ruP) * u = u * (t : ↥ruP) := by
    have := congrArg Subtype.val htc
    simpa using this
  obtain ⟨g, hg, hgt⟩ := ruK432_sylow_conj (x := ((t : ↥ruP) : Equiv.Perm (Fin 4060)))
    (Subgroup.mem_subgroupOf.1 t.2) (fun h0 => ht1 (Subtype.ext h0))
  obtain ⟨G', hG'⟩ : ∃ G' : ↥ruP, G' * (t : ↥ruP) * G'⁻¹ = ruXp :=
    ⟨⟨g, hg⟩, Subtype.ext hgt⟩
  refine ⟨h * G'⁻¹, ?_⟩
  have hT : h * G'⁻¹ * ruXp * (h * G'⁻¹)⁻¹ = h * (t : ↥ruP) * h⁻¹ := by
    rw [← hG']
    group
  rw [hT]
  have hru : ruXp = h * u * h⁻¹ := by
    rw [hu]
    group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hru]
    calc h * (t : ↥ruP) * h⁻¹ * (h * u * h⁻¹) = h * ((t : ↥ruP) * u) * h⁻¹ := by group
      _ = h * (u * (t : ↥ruP)) * h⁻¹ := by rw [htcomm]
      _ = h * u * h⁻¹ * (h * (t : ↥ruP) * h⁻¹) := by group
  · intro h0
    apply htu
    rw [hu]
    calc (t : ↥ruP) = h⁻¹ * (h * (t : ↥ruP) * h⁻¹) * h := by group
      _ = h⁻¹ * ruXp * h := by rw [h0]
  · intro h0
    apply htu'
    rw [hu]
    calc (t : ↥ruP) = h⁻¹ * (h * (t : ↥ruP) * h⁻¹) * h := by group
      _ = h⁻¹ * ruXp⁻¹ * h := by rw [h0]
      _ = (h⁻¹ * ruXp * h)⁻¹ := by group
  · intro h0
    apply ht1
    calc (t : ↥ruP) = h⁻¹ * (h * (t : ↥ruP) * h⁻¹) * h := by group
      _ = 1 := by rw [h0]; group

theorem ruK432_listRow_ruP :
    ListRow ↥ruP := by
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := ruK432_witness
  refine listRow_of_class_witness (fun _ : Unit => ruXp) (fun _ : Unit => w) ?_ ?_ ?_
  · intro z hz
    have hz3 : z ^ 3 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    obtain ⟨g, hg⟩ := exists_conj_ruXp z hz3 hz1
    refine ⟨(), g⁻¹, ?_⟩
    show z = g⁻¹ * ruXp * g⁻¹⁻¹
    rw [← hg]
    group
  · intro _
    exact ruK432_ruXp_pow_three
  · intro _ _
    exact ⟨hw1, hw2, hw3, hw4⟩

theorem row_carrier_ru :
    RowOf (NativeSporadic.Carrier .Ru) := by
  haveI : Finite (NativeSporadic.Carrier .Ru) := Finite.of_equiv _ ruEquivP.symm.toEquiv
  intro S _ _ _ _ ⟨e⟩
  refine GoodRow.of_mulEquiv e.symm ⟨?_, ?_⟩
  · exact ListRow.of_mulEquiv ruEquivP.symm ruK432_listRow_ruP
  · exact outerRow_of_not_three_dvd_outer
      (CFSG.Quasithin.A318P.not_dvd_outer_Ru (MulEquiv.refl _) Nat.prime_three (by norm_num))

end CFSG.RankThree.PartTwo.Sec4.RonanK432
