module

import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCen

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS CFSG.ABGLocalTools
open scoped Pointwise

namespace Res8Inner

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_of_two_pow_mod_nine {n : ℕ} (h : 2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) : 3 ∣ n := by
  have h6 : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [h6] at h
  have h03 : n % 6 = 0 ∨ n % 6 = 3 := by
    interval_cases hn : n % 6 <;> simp_all
  omega

theorem mem_of_mem_normalizer_conj {A : Subgroup G}
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A) (g : G) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :
      Set G))
    (hx3 : x ^ 3 = 1) : x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hmem : ∀ y, y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ A := fun y => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  rw [hmem]
  refine h1617 _ ?_ (by rw [conj_pow, hx3]; group)
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have ha' : g⁻¹ * a * g ∈ A.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hmem]
    simpa [mul_assoc] using ha
  have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp ha'
  rw [hmem] at h1
  have heq : g * (x * (g⁻¹ * a * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ := by
    group
  rwa [heq] at h1

theorem pow_three_eq_one_of_mem {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) (h138 : Item138N)
    {n : ℕ} (hz : IsZ3LThreeTwo A c L n) {l : G} (hl : l ∈ L) (hl3 : ∃ k : ℕ, l ^ 3 ^ k = 1) :
    l ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 := Proof1617.not_three_dvd_of_isZ3 h h138 hz
  obtain ⟨hn, hiso, -⟩ := hz
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have : θ.Normal := by
    have := Sec4.aschbacherSolvableCore_characteristic ↥L
    infer_instance
  set lL : ↥L := ⟨l, hl⟩ with hlL
  set lb : ↥L ⧸ θ := (lL : ↥L ⧸ θ) with hlb
  have h91 : 2 ^ n % 9 ≠ 1 := fun h1 => hn3 (three_dvd_of_two_pow_mod_nine (Or.inl h1))
  have h98 : 2 ^ n % 9 ≠ 8 := fun h8 => hn3 (three_dvd_of_two_pow_mod_nine (Or.inr h8))
  have hlb3 : IsPGroup 3 (Subgroup.zpowers lb) := by
    obtain ⟨k, hk⟩ := hl3
    rintro ⟨_, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (lb ^ m) ^ 3 ^ k = 1
    have hlbk : lb ^ 3 ^ k = 1 := by
      rw [hlb, ← QuotientGroup.mk_pow]
      have : lL ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, QuotientGroup.mk_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hlbk,
      _root_.one_zpow]
  obtain ⟨S, hlS⟩ := hlb3.exists_le_sylow
  have hlb1 : lb ^ 3 = 1 :=
    (Sec19.Step1915WProof.ks1917Lie3Sylow (↥L ⧸ θ) 2 n hn hiso h91 h98 S).2 lb
      (hlS (Subgroup.mem_zpowers lb))
  have hθ3 := Proof1617.not_three_dvd_card_thetaG L
  have hlθ : lL ^ 3 ∈ θ :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hlb1)
  have hmem : l ^ 3 ∈ θ.map L.subtype := ⟨lL ^ 3, hlθ, by simp [hlL]⟩
  have hP : IsPGroup 3 (Subgroup.zpowers l) := by
    obtain ⟨k, hk⟩ := hl3
    rintro ⟨_, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (l ^ m) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  exact Proof1617.eq_one_of_isPGroup_of_not_dvd hP hθ3
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers l) 3) hmem

end Res8Inner

open Res8Inner

theorem ks1618Inner_of (h1616 : Step1616) (h138 : Item138N) : KS1618Inner := by
  intro G _ _ A c L h h1617 g _ hgc a ha
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hz⟩ := h1616 G A c L h
  obtain ⟨hcL, h9, -⟩ := Proof1617.facts_of_isZ3 h hz
  have hCN := Proof1617.centralizer_le_normalizer_L h hz
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.le_centralizer
  set θG := (aschbacherSolvableCore 3 ↥L).map L.subtype with hθG
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hmemA' : ∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A := fun x => by
    rw [hA', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hcA' : c ∈ A' := (hmemA' c).mpr hgc
  have hA'ab : CFSG.Assembly.IsElemAbelian 3 A' :=
    Proof1617.isElemAbelian_map' _ h.isElemAbelian
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h.card_eq]
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA'ab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA'C : A' ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hA'comm x hx c hcA')
  have hA'N : A' ≤ Subgroup.normalizer (L : Set G) := hA'C.trans hCN
  have hA'3 : IsPGroup 3 A' := IsPGroup.of_card (n := 3) (by rw [hA'27]; norm_num)
  have key : Nat.card (A' ⊓ L : Subgroup G) = 9 := by
    by_contra hne
    have hdvd27 : Nat.card (A' ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA'27]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne27 : Nat.card (A' ⊓ L : Subgroup G) ≠ 27 := by
      intro h27
      have heq : A' ⊓ L = A' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA'27])
      have hcAL : c ∈ A' ⊓ L := by rw [heq]; exact hcA'
      exact hcL hcAL.2
    have hdvd3 : Nat.card (A' ⊓ L : Subgroup G) ∣ 3 := by
      obtain ⟨i, hi, hiA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd27
      interval_cases i
      · rw [hiA]; norm_num
      · rw [hiA]; norm_num
      · exact absurd (hiA.trans (by norm_num)) hne
      · exact absurd (hiA.trans (by norm_num)) hne27
    set M := A' ⊔ L with hM
    have hprod := Proof1617.card_sup_mul_card_inf_of_le_normalizer hA'N
    rw [inf_comm] at hprod
    have h9L : 9 ∣ Nat.card L := h9 ▸ Subgroup.card_dvd_of_le inf_le_right
    have h81 : 3 ^ 4 ∣ Nat.card M := by
      have h1 : 3 ^ 5 ∣ Nat.card M * Nat.card (A' ⊓ L : Subgroup G) := by
        rw [hM, hprod, hA'27]
        obtain ⟨k, hk⟩ := h9L
        rw [hk]
        exact ⟨k, by ring⟩
      have h2 : Nat.card M * Nat.card (A' ⊓ L : Subgroup G) ∣ Nat.card M * 3 :=
        Nat.mul_dvd_mul_left _ hdvd3
      have h3 : 3 ^ 5 ∣ Nat.card M * 3 := h1.trans h2
      rw [show (3 : ℕ) ^ 5 = 3 ^ 4 * 3 by norm_num] at h3
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    obtain ⟨T, hTsyl, hA'T⟩ := Proof1617.exists_isSylowOf_le hA'3 (le_sup_left : A' ≤ M)
    have hTcard := hTsyl.card_eq
    have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have h4 : 4 ≤ (Nat.card M).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hM0).mp h81
    have hA'lt : A' ≠ T := by
      intro hAT
      have h27 : (27 : ℕ) = 3 ^ (Nat.card M).factorization 3 := by
        rw [← hA'27, hAT, hTcard]
      have h81le : 3 ^ 4 ≤ 3 ^ (Nat.card M).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) h4
      rw [← h27] at h81le
      norm_num at h81le
    set IP : Subgroup ↥T := A'.subgroupOf T with hIP
    have hIPlt : IP < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hA'lt (le_antisymm hA'T fun x hxT => ?_)
      have hxIP : (⟨x, hxT⟩ : ↥T) ∈ IP := by
        rw [htop]
        trivial
      exact Subgroup.mem_subgroupOf.mp hxIP
    have : Group.IsNilpotent ↥T := hTsyl.isPGroup.isNilpotent
    have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent (G := ↥T)
    obtain ⟨x, hxN, hxIP⟩ := IsConcreteLE.exists_of_lt (hnc IP hIPlt)
    have hxNorm : (x : G) ∈ Subgroup.normalizer (A' : Set G) := by
      have hxsub : x ∈ (Subgroup.normalizer (A' : Set G)).subgroupOf T := by
        rw [Subgroup.subgroupOf_normalizer_eq hA'T]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hxsub
    have hxA' : (x : G) ∉ A' := fun hx => hxIP (Subgroup.mem_subgroupOf.mpr hx)
    have hxM : (x : G) ∈ (L : Set G) * (A' : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L A' hA'N, sup_comm]
      exact hTsyl.le x.2
    obtain ⟨l, hl, a', ha', hla⟩ := hxM
    have hlx : l = (x : G) * a'⁻¹ := by rw [← hla]; group
    have hlN : l ∈ Subgroup.normalizer (A' : Set G) := by
      rw [hlx]
      exact Subgroup.mul_mem _ hxNorm
        (Subgroup.inv_mem _ (Subgroup.le_normalizer ha'))
    have hlA' : l ∉ A' := fun hlA => hxA' (by rw [← hla]; exact A'.mul_mem hlA ha')
    have hlT : l ∈ T := by
      rw [hlx]
      exact T.mul_mem x.2 (T.inv_mem (hA'T ha'))
    have hl3 : ∃ k : ℕ, l ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hTsyl.isPGroup ⟨l, hlT⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hl1 := pow_three_eq_one_of_mem h h138 hz hl hl3
    exact hlA' (mem_of_mem_normalizer_conj h1617 g hlN hl1)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  obtain ⟨-, h27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc3
    (fun hc => hcL (Subgroup.mem_inf.mp hc).2) le_rfl key
    (fun s hs => hA'ab.2 s hs.1) (fun s hs => hA'comm c hcA' s hs.1)
  have hAeq : A' = Subgroup.zpowers c ⊔ (A' ⊓ L) :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA') inf_le_left)
      (by rw [h27, hA'27])).symm
  have haA' : g⁻¹ * a * g ∈ A' := by
    rw [hmemA']
    simpa [mul_assoc] using ha
  have hcCen : c ∈ Subgroup.centralizer ((A' ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => hA'comm y hy.1 c hcA'
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A' ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hcCen)
  have hmem : g⁻¹ * a * g ∈
      (Subgroup.zpowers c : Set G) * ((A' ⊓ L : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN, ← hAeq]
    exact haA'
  obtain ⟨_, hw, l, hl, hwl⟩ := hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨l, hl.2, fun y hy => ?_⟩
  rw [← hwl]
  have hz : l * y * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl.2 hy) (L.inv_mem hl.2)
  have hcz : Commute (c ^ k) (l * y * l⁻¹) :=
    Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLc hz)).symm k
  have heq : c ^ k * l * y * (c ^ k * l)⁻¹ * (l * y * l⁻¹)⁻¹ = 1 := by
    calc c ^ k * l * y * (c ^ k * l)⁻¹ * (l * y * l⁻¹)⁻¹
        = (c ^ k * (l * y * l⁻¹)) * (c ^ k)⁻¹ * (l * y * l⁻¹)⁻¹ := by group
      _ = ((l * y * l⁻¹) * c ^ k) * (c ^ k)⁻¹ * (l * y * l⁻¹)⁻¹ := by rw [hcz.eq]
      _ = 1 := by group
  rw [heq]
  exact one_mem _

theorem ks1618Card_of_res8 (h1616 : Step1616) (h138 : Item138N) : KS1618Card :=
  ks1618Card_of h1616 (ks1618Inner_of h1616 h138)

end CFSG.RankThree.PartTwo.Sec16
