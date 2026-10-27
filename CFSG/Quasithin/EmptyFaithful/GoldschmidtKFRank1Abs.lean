module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

section Cyclic

variable {Y : Type} [Group Y] [Finite Y]

theorem isCyclic_of_isPGroup_of_pRank_eq_one {L : Subgroup Y} (h1 : CFSG.Open.pRank 3 L = 1)
    {T : Subgroup ↥L} (hT : IsPGroup 3 ↥T) : IsCyclic ↥T := by
  have hrank : CFSG.pRank 3 ↥L ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype (p := 3) L]
    exact h1.le
  have hcyc' : IsCyclic ↥(T.map L.subtype) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      (show T.map L.subtype ≤ L from Subgroup.map_subtype_le _) (hT.map L.subtype) hrank
  let e : ↥T ≃* ↥(T.map L.subtype) :=
    Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem eq_one_of_mem_center_of_cube {L : Subgroup Y} (hperf : Group.IsPerfect ↥L)
    (h1 : CFSG.Open.pRank 3 L = 1) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hz3 : z ^ 3 = 1) :
    z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_cube hz3).exists_le_sylow
  have hcycP : IsCyclic ↥(P : Subgroup ↥L) :=
    isCyclic_of_isPGroup_of_pRank_eq_one h1 P.isPGroup'
  have : IsMulCommutative (P : Subgroup ↥L) :=
    ⟨⟨fun a b => (IsCyclic.commGroup (α := ↥(P : Subgroup ↥L))).mul_comm a b⟩⟩
  exact eq_one_of_mem_center_of_perfect (p := 3) hperf P.isPGroup' P.not_dvd_index hz
    (hP (Subgroup.mem_zpowers z))

end Cyclic

section Sylow

variable {Y : Type} [Group Y] [Finite Y] {L G : Subgroup Y}

omit [Finite Y] in
theorem normal_subgroupOf_of_le_normalizer (hGN : G ≤ Subgroup.normalizer (L : Set Y)) :
    (L.subgroupOf G).Normal := by
  constructor
  intro n hn g
  have h := (Subgroup.mem_normalizer_iff.mp (hGN g.2) (n : Y)).mp (Subgroup.mem_subgroupOf.mp hn)
  exact Subgroup.mem_subgroupOf.mpr h

theorem inf_sylow_ne_bot (hLG : L ≤ G) (hGN : G ≤ Subgroup.normalizer (L : Set Y))
    (hL3 : 3 ∣ Nat.card ↥L) (R : Sylow 3 ↥G) :
    ((R : Subgroup ↥G).map G.subtype) ⊓ L ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hN := normal_subgroupOf_of_le_normalizer hGN
  set N : Subgroup ↥G := L.subgroupOf G with hNdef
  have hRN : (R : Subgroup ↥G) ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have h1 : (r : Y) ∈ ((R : Subgroup ↥G).map G.subtype) ⊓ L :=
      ⟨⟨r, hr.1, rfl⟩, Subgroup.mem_subgroupOf.mp hr.2⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hrel : N.relIndex (R : Subgroup ↥G) = Nat.card ↥(R : Subgroup ↥G) := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hRN, Subgroup.relIndex_bot_left]
  have hdvd : Nat.card ↥(R : Subgroup ↥G) ∣ N.index := by
    rw [← hrel]
    exact Subgroup.relIndex_dvd_index_of_normal N _
  have hmul : Nat.card ↥N * N.index = Nat.card ↥G := Subgroup.card_mul_index N
  have hN3 : 3 ∣ Nat.card ↥N := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv]
    exact hL3
  have hcardN : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hidx : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hR : Nat.card ↥(R : Subgroup ↥G) = 3 ^ (Nat.card ↥G).factorization 3 :=
    Sylow.card_eq_multiplicity R
  rw [hR] at hdvd
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hidx).mp hdvd
  have h2 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hcardN).mp hN3
  have h3 : (Nat.card ↥G).factorization 3 =
      (Nat.card ↥N).factorization 3 + N.index.factorization 3 := by
    rw [← hmul, Nat.factorization_mul hcardN hidx, Finsupp.add_apply]
  omega

end Sylow

section TwentySeven

variable {Y : Type} [Group Y] [Finite Y] {L B : Subgroup Y}

theorem exists_elemAbelian_twentySeven_of_inf_eq_bot
    (hcyc : ∀ T : Subgroup Y, T ≤ L → IsPGroup 3 ↥T → IsCyclic ↥T) (hL3 : 3 ∣ Nat.card ↥L)
    (hBN : B ≤ Subgroup.normalizer (L : Set Y)) (hBc : Nat.card ↥B = 27)
    (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hBL : B ⊓ L = ⊥) :
    ∃ E : Subgroup Y, E ≤ L ⊔ B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card ↥E = 27 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G : Subgroup Y := L ⊔ B with hG
  have hLG : L ≤ G := le_sup_left
  have hBG : B ≤ G := le_sup_right
  have hBpG : IsPGroup 3 ↥(B.subgroupOf G) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv, hBc]
    norm_num
  obtain ⟨R, hBR⟩ := hBpG.exists_le_sylow
  set R' : Subgroup Y := (R : Subgroup ↥G).map G.subtype with hR'
  have hR'G : R' ≤ G := Subgroup.map_subtype_le _
  have hR'3 : IsPGroup 3 ↥R' := R.isPGroup'.map G.subtype
  have hBR' : B ≤ R' := fun b hb => ⟨⟨b, hBG hb⟩, hBR (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  set P : Subgroup Y := R' ⊓ L with hP
  have hPne : P ≠ ⊥ := inf_sylow_ne_bot hLG (sup_le Subgroup.le_normalizer hBN) hL3 R
  have hPL : P ≤ L := inf_le_right
  have hPp : IsPGroup 3 ↥P := hR'3.to_le inf_le_left
  have hPcyc : IsCyclic ↥P := hcyc P hPL hPp
  have hBP : B ≤ Subgroup.normalizer (P : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hR'conj : h ∈ R' ↔ b * h * b⁻¹ ∈ R' := by
      constructor
      · intro hh
        exact R'.mul_mem (R'.mul_mem (hBR' hb) hh) (R'.inv_mem (hBR' hb))
      · intro hh
        have := R'.mul_mem (R'.mul_mem (R'.inv_mem (hBR' hb)) hh) (hBR' hb)
        simpa [mul_assoc] using this
    have hLconj := Subgroup.mem_normalizer_iff.mp (hBN hb) h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hR'conj.mp h1, hLconj.mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hR'conj.mpr h1, hLconj.mpr h2⟩
  obtain ⟨x, hx3⟩ : ∃ x : ↥P, orderOf x = 3 := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    have hn1 : n ≠ 0 := by
      rintro rfl
      apply hPne
      rw [pow_zero] at hn
      exact (Subgroup.card_eq_one.mp hn)
    exact exists_prime_orderOf_dvd_card' 3 (by
      rw [hn]
      exact dvd_pow_self 3 hn1)
  have : B.Normalizes P := ⟨hBP⟩
  obtain ⟨ker, hkidx, hker⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_action_on_odd_cyclic_pGroup_has_prime_index_kernel
      (acting := ↥B) (source := ↥P) 3 (by norm_num) hPp
      (fun b => Subtype.ext (by simpa using hB3 b b.2))
  have hkcard : 3 ^ 2 ∣ Nat.card ↥ker := by
    have h := Subgroup.card_mul_index ker
    rw [hBc] at h
    rcases hkidx with h1 | h1
    · rw [h1, mul_one] at h
      rw [h]
      norm_num
    · rw [h1] at h
      have : Nat.card ↥ker = 9 := by omega
      rw [this]
      norm_num
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime 3 hkcard
  set B₂ : Subgroup Y := (K₂.map ker.subtype).map B.subtype with hB₂
  have hB₂B : B₂ ≤ B := Subgroup.map_subtype_le _
  have hB₂card : Nat.card ↥B₂ = 3 ^ 2 := by
    rw [hB₂, Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective ker.subtype_injective, hK₂]
  have hB₂comm : IsMulCommutative ↥B₂ :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hB₂card
  have hB₂el : CFSG.Assembly.IsElemAbelian 3 B₂ := ⟨hB₂comm, fun y hy => hB3 y (hB₂B hy)⟩
  have hcent : ∀ y ∈ B₂, ∀ m : ↥P, y * (m : Y) = (m : Y) * y := by
    rintro y ⟨u, ⟨v, hv, rfl⟩, rfl⟩ m
    have h := hker (v : ↥B) v.2 m
    have h2 := Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B P (a := (v : ↥B)) (k := m)
    rw [h] at h2
    calc ((v : ↥B) : Y) * (m : Y) = (((v : ↥B) : Y) * (m : Y) * ((v : ↥B) : Y)⁻¹) *
          ((v : ↥B) : Y) := by group
      _ = (m : Y) * ((v : ↥B) : Y) := by rw [← h2]
  have hxP : (x : Y) ∈ P := x.2
  have hxn : (x : Y) ∉ B₂ := by
    intro hxB
    have hx1 : (x : Y) ∈ B ⊓ L := ⟨hB₂B hxB, hPL hxP⟩
    rw [hBL, Subgroup.mem_bot] at hx1
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx3
    omega
  have hxcube : (x : Y) ^ 3 = 1 := by
    have : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  obtain ⟨hE, hEcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hB₂el hxn hxcube
    (fun a ha => hcent a ha x)
  refine ⟨B₂ ⊔ Subgroup.zpowers (x : Y), sup_le (hB₂B.trans hBG)
    (Subgroup.zpowers_le.mpr (hLG (hPL hxP))), hE, ?_⟩
  rw [hEcard, hB₂card]
  norm_num

end TwentySeven

end CFSG.Quasithin.SBd19F
