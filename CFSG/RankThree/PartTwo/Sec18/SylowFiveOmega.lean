module

public import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.KFacts.K72Omega
import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIb
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace SylowFive

variable {G : Type} [Group G]

theorem zpowers_inf_eq_bot {H : Subgroup G} {u : G} (hu3 : u ^ 3 = 1) (huH : u ∉ H) :
    Subgroup.zpowers u ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxH⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : u ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hu3]
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_ediv_mul k 3, zpow_add, mul_comm (k / 3) 3, zpow_mul, h3,
      one_zpow, mul_one]
  rw [hk] at hxH ⊢
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hxH
    exact absurd hxH huH
  · exfalso
    rw [h, zpow_two] at hxH
    apply huH
    have hu : u = (u * u) * (u * u) := by
      calc u = u ^ 3 * u := by rw [hu3, one_mul]
        _ = (u * u) * (u * u) := by rw [pow_three]; simp only [mul_assoc]
    rw [hu]
    exact H.mul_mem hxH hxH

theorem not_mem_frattini_of_card {H K : Subgroup G} (hHK : H ≤ K)
    (hcard : Nat.card K = 3 * Nat.card H) (hH0 : Nat.card H ≠ 0) {x : G} (hxH : x ∉ H) :
    x ∉ (frattini K).map K.subtype := by
  rintro ⟨y, hy, rfl⟩
  have hidx : (H.subgroupOf K).index = 3 := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hcard, mul_comm 3] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH0) h1
  have hco : IsCoatom (H.subgroupOf K) :=
    Subgroup.isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_three)
  exact hxH (Subgroup.mem_subgroupOf.mp (frattini_le_coatom hco hy))

theorem pow_three_eq_one_of_mul {P Y : Subgroup G} (hYP : Y ≤ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hY3 : IsPGroup 3 Y) (hYc : IsCyclic Y)
    {v y : G} (hv : v ∈ P) (hv3 : v ^ 3 = 1) (hy : y ∈ Y) (h : (v * y) ^ 3 = 1) :
    y ^ 3 = 1 := by
  haveI : (Y.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).mpr hPY
  have e : Y.subgroupOf P ≃* Y := Subgroup.subgroupOfEquivOfLe hYP
  haveI := hYc
  haveI : IsCyclic (Y.subgroupOf P) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hY3' : IsPGroup 3 (Y.subgroupOf P) := hY3.of_equiv e.symm
  have key := KFacts.pow_three_mul_eq_one_iff (P := P) (X₀ := Y.subgroupOf P) hY3'
    (σ := ⟨v, hv⟩) (Subtype.ext (by simpa using hv3)) (y := ⟨y, hYP hy⟩)
    (Subgroup.mem_subgroupOf.mpr hy)
  have h' : ((⟨v, hv⟩ : P) * ⟨y, hYP hy⟩) ^ 3 = 1 := Subtype.ext (by simpa using h)
  simpa using congrArg Subtype.val (key.mp h')

variable [Finite G]

theorem sup_zpowers_facts {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {u : G} (hu3 : u ^ 3 = 1)
    (huB : u ∈ Subgroup.normalizer (B : Set G)) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hub₀ : u * b₀ ≠ b₀ * u) :
    Nat.card (B ⊔ Subgroup.zpowers u : Subgroup G) = 27 ∧
      (∀ x ∈ B ⊔ Subgroup.zpowers u, x ^ 3 = 1) ∧
      Sec4.IsHeisThree (B ⊔ Subgroup.zpowers u : Subgroup G) := by
  set V := B ⊔ Subgroup.zpowers u with hV
  have huB' : u ∉ B := fun h => hub₀ (congrArg Subtype.val (hB.1.is_comm.comm ⟨u, h⟩ ⟨b₀, hb₀⟩))
  have hu1 : u ≠ 1 := fun h => huB' (h ▸ B.one_mem)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hzle : Subgroup.zpowers u ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.mpr huB
  have hcard : Nat.card V = 27 := by
    have h1 := Sec6.card_sup_mul_card_inf hzle
    rw [zpowers_inf_eq_bot hu3 huB', Subgroup.card_bot, mul_one, Nat.card_zpowers, hord, hB9,
      sup_comm] at h1
    rw [h1]
  have hna : ∃ a b : V, a * b ≠ b * a :=
    ⟨⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩, ⟨b₀, Subgroup.mem_sup_left hb₀⟩,
      fun h => hub₀ (congrArg Subtype.val h)⟩
  have hmul := Sec4.RonanK432.mul_pow_three_of_card_27 hcard hna
  have h3 : ∀ x ∈ V, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ (B : Set G) * (Subgroup.zpowers u : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers u) hzle]
      exact hx
    obtain ⟨b, hb, z, hz, rfl⟩ := hx'
    have hbz := congrArg Subtype.val
      (hmul ⟨b, Subgroup.mem_sup_left hb⟩ ⟨z, Subgroup.mem_sup_right hz⟩)
    simp only [Subgroup.coe_pow, Subgroup.coe_mul] at hbz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hz3 : (u ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
    rw [hbz, hB.2 b hb, hz3, mul_one]
  refine ⟨hcard, h3, Sec4.isHeisThree_of V hcard (fun x => Subtype.ext (by simpa using h3 x x.2))
    fun hc => ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  exact hab (hc.is_comm.comm a b)

theorem omegaOne_structure {P B Y : Subgroup G} {c : G}
    (hP3 : IsPGroup 3 P) (hc3 : orderOf c = 3) (hPc : P ≤ Subgroup.centralizer ({c} : Set G))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9) (hBP : B ≤ P)
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hYP : Y ≤ P) (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    (hYB : Y ≤ Subgroup.centralizer (B : Set G)) (hYB1 : Y ⊓ B = ⊥) (hcY : c ∈ Y)
    (hY3 : ∀ y ∈ Y, y ^ 3 = 1 → y ∈ Subgroup.zpowers c)
    (hcard : Nat.card P ∣ 27 * Nat.card Y)
    (hrank : ∀ E : Subgroup G, E ≤ P → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27) :
    (IsE27 (omegaOneThree P) ∨ IsZ3TimesHeis (omegaOneThree P)) ∧
      c ∉ (frattini (omegaOneThree P)).map (omegaOneThree P).subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcP : c ∈ P := hYP hcY
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc3
    norm_num at hc3
  have hcc3 : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hcB : c ∉ B := fun h => hc1 (by
    have hmem : c ∈ Y ⊓ B := ⟨hcY, h⟩
    rwa [hYB1, Subgroup.mem_bot] at hmem)
  have hPc' : ∀ x ∈ P, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPc hx)
  have hYBc : ∀ y ∈ Y, ∀ b ∈ B, y * b = b * y := fun y hy b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hYB hy)) b hb).symm
  have hY3' : IsPGroup 3 Y := hP3.to_le hYP
  have hYcyc : IsCyclic Y := by
    refine isCyclic_of_forall_elemAbelian_card_le_three hY3' fun F hFY hF => ?_
    have hFc : F ≤ Subgroup.zpowers c := fun x hx => hY3 x (hFY hx) (hF.2 x hx)
    calc Nat.card F ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hFc
      _ = 3 := by rw [Nat.card_zpowers, hc3]
  set A : Subgroup G := Subgroup.zpowers c ⊔ B with hA
  have hcBn : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.mpr (hPB hcP)
  have hAP : A ≤ P := sup_le (Subgroup.zpowers_le.mpr hcP) hBP
  have hAel : CFSG.Assembly.IsElemAbelian 3 A :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hcc3) hB
      fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact (Commute.zpow_left (hPc' b (hBP hb)).symm k).eq
  have hA27 : Nat.card A = 27 := by
    have h1 := Sec6.card_sup_mul_card_inf hcBn
    rw [zpowers_inf_eq_bot hcc3 hcB, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3,
      hB9] at h1
    rw [hA, h1]
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := hBP.trans hPY
  set YB : Subgroup G := Y ⊔ B with hYBdef
  have hYBset : (YB : Set G) = (Y : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y B hBY
  have hAYB : A ≤ YB :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcY)) le_sup_right
  by_cases hcase : ∀ x ∈ P, x ^ 3 = 1 → x ∈ YB
  ·
    have hΩA : omegaOneThree P = A := by
      apply le_antisymm
      · rw [omegaOneThree, Subgroup.closure_le]
        rintro x ⟨hxP, hx3⟩
        have hx : x ∈ (Y : Set G) * (B : Set G) := hYBset ▸ hcase x hxP hx3
        obtain ⟨y, hy, b, hb, rfl⟩ := hx
        have hy3 : y ^ 3 = 1 := by
          have h1 : (y * b) ^ 3 = y ^ 3 * b ^ 3 := (Commute.mul_pow (hYBc y hy b hb) 3)
          rwa [h1, hB.2 b hb, mul_one] at hx3
        exact A.mul_mem (Subgroup.mem_sup_left (hY3 y hy hy3)) (Subgroup.mem_sup_right hb)
      · refine sup_le ?_ fun b hb => Subgroup.subset_closure ⟨hBP hb, hB.2 b hb⟩
        rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure ⟨hcP, hcc3⟩
    refine ⟨Or.inl (hΩA ▸ ⟨hAel, hA27⟩), ?_⟩
    rw [hΩA]
    exact not_mem_frattini_of_card le_sup_right (by rw [hA27, hB9]) (by rw [hB9]; norm_num) hcB
  · push Not at hcase
    obtain ⟨u, huP, hu3, huYB⟩ := hcase
    have huA : u ∉ A := fun h => huYB (hAYB h)
    have hu1 : u ≠ 1 := fun h => huYB (h ▸ YB.one_mem)
    obtain ⟨b₀, hb₀, hub₀⟩ : ∃ b₀ ∈ B, u * b₀ ≠ b₀ * u := by
      by_contra hall
      push Not at hall
      have huA' : A ≤ Subgroup.centralizer ({u} : Set G) := by
        refine sup_le ?_ fun b hb => ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (hPc' u huP).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hall b hb).symm
      have hE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers u ⊔ A) :=
        CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hu3) hAel
          fun z hz a ha => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            have hau : a * u = u * a := Subgroup.mem_centralizer_singleton_iff.mp (huA' ha)
            exact (Commute.zpow_left hau.symm k).eq
      have huAn : Subgroup.zpowers u ≤ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.zpowers_le]
        refine Subgroup.centralizer_le_normalizer (A : Set G)
          (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
        exact Subgroup.mem_centralizer_singleton_iff.mp (huA' ha)
      have h81 : Nat.card (Subgroup.zpowers u ⊔ A : Subgroup G) = 81 := by
        have h1 := Sec6.card_sup_mul_card_inf huAn
        rw [zpowers_inf_eq_bot hu3 huA, Subgroup.card_bot, mul_one, Nat.card_zpowers,
          orderOf_eq_prime hu3 hu1, hA27] at h1
        rw [h1]
      have := hrank _ (sup_le (Subgroup.zpowers_le.mpr huP) hAP) hE
      omega
    obtain ⟨hV27, hV3, hVheis⟩ := sup_zpowers_facts hB hB9 hu3 (hPB huP) hb₀ hub₀
    set V : Subgroup G := B ⊔ Subgroup.zpowers u with hV
    have hVP : V ≤ P := sup_le hBP (Subgroup.zpowers_le.mpr huP)
    have hVYB : V ⊓ YB = B := by
      have hle : B ≤ V ⊓ YB := le_inf le_sup_left le_sup_right
      have hdvd : Nat.card (V ⊓ YB : Subgroup G) ∣ 27 := hV27 ▸ Subgroup.card_dvd_of_le inf_le_left
      have hne : Nat.card (V ⊓ YB : Subgroup G) ≠ 27 := by
        intro h27
        have heq : V ⊓ YB = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hV27])
        exact huYB ((heq ▸ inf_le_right : V ≤ YB)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
      obtain ⟨k, hk⟩ : 9 ∣ Nat.card (V ⊓ YB : Subgroup G) := hB9 ▸ Subgroup.card_dvd_of_le hle
      have h9 : Nat.card (V ⊓ YB : Subgroup G) = 9 := by
        rw [hk] at hdvd hne ⊢
        have hk3 : k ≤ 3 := by
          have := Nat.le_of_dvd (by norm_num) hdvd
          omega
        interval_cases k <;> simp_all
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hB9])).symm
    have hVY : V ⊓ Y = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxB : x ∈ B := hVYB ▸ (⟨hx.1, Subgroup.mem_sup_left hx.2⟩ : x ∈ V ⊓ YB)
      have hmem : x ∈ Y ⊓ B := ⟨hx.2, hxB⟩
      rwa [hYB1] at hmem
    have hVYn : V ≤ Subgroup.normalizer (Y : Set G) := hVP.trans hPY
    have hPVY : V ⊔ Y = P := by
      have h1 := Sec6.card_sup_mul_card_inf hVYn
      rw [hVY, Subgroup.card_bot, mul_one, hV27] at h1
      refine Subgroup.eq_of_le_of_card_ge (sup_le hVP hYP) ?_
      rw [h1]
      exact Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) hcard
    have hVYset : ((V ⊔ Y : Subgroup G) : Set G) = (V : Set G) * (Y : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right V Y hVYn
    have hΩV : omegaOneThree P = Subgroup.zpowers c ⊔ V := by
      apply le_antisymm
      · rw [omegaOneThree, Subgroup.closure_le]
        rintro x ⟨hxP, hx3⟩
        have hx : x ∈ (V : Set G) * (Y : Set G) := by
          rw [← hVYset, hPVY]
          exact hxP
        obtain ⟨v, hv, y, hy, rfl⟩ := hx
        have hy3 : y ^ 3 = 1 :=
          pow_three_eq_one_of_mul hYP hPY hY3' hYcyc (hVP hv) (hV3 v hv) hy hx3
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left (hY3 y hy hy3))
      · refine sup_le ?_ fun v hv => Subgroup.subset_closure ⟨hVP hv, hV3 v hv⟩
        rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure ⟨hcP, hcc3⟩
    have hcV : c ∉ V := fun h => hc1 (by
      have hmem : c ∈ V ⊓ Y := ⟨h, hcY⟩
      rwa [hVY, Subgroup.mem_bot] at hmem)
    have hcCV : c ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => hPc' v (hVP hv)
    have hcVn : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) hcCV)
    have hcVinf : Subgroup.zpowers c ⊓ V = ⊥ := zpowers_inf_eq_bot hcc3 hcV
    have hΩ81 : Nat.card (Subgroup.zpowers c ⊔ V : Subgroup G) = 81 := by
      have h1 := Sec6.card_sup_mul_card_inf hcVn
      rw [hcVinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3, hV27] at h1
      rw [h1]
    refine ⟨Or.inr ⟨Subgroup.zpowers c, V, hΩV.symm, hcVinf, by rw [Nat.card_zpowers, hc3],
      hVheis, Subgroup.zpowers_le.mpr hcCV⟩, ?_⟩
    rw [hΩV]
    exact not_mem_frattini_of_card le_sup_right (by rw [hΩ81, hV27]) (by rw [hV27]; norm_num) hcV

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
