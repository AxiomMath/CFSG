module

public import CFSG.LocalAnalysis.StandardType.GGSporKFGen
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
import CFSG.GroupTheory.ABGLocalTools.Basic
import TauCeti.GroupTheory.Commutator

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Monster.B.Pinned
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commData_pow_p {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) :
    ∀ g ∈ Subgroup.closure (Set.range q), g ^ p = 1 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hD.pow_q i
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hb : ⁅y, x⁆ ∈ Subgroup.zpowers z := by
      rw [commutatorElement_eq_bcomm]
      exact hD.bcomm_mem (Subgroup.inv_mem _ hy) (Subgroup.inv_mem _ hx)
    have hcx : Commute x ⁅y, x⁆ := hD.commute_of_mem hx hb
    have hcy : Commute y ⁅y, x⁆ := hD.commute_of_mem hy hb
    have h1 := Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two hcx hcy p
    have hdvd : p ∣ p.choose 2 :=
      (Fact.out : p.Prime).dvd_choose_self (by norm_num) (by
        have := (Fact.out : p.Prime).two_le
        omega)
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hpz : (⁅y, x⁆) ^ p = 1 := by
      rw [← he, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← hD.orderOf_z, pow_orderOf_eq_one, one_zpow]
    rw [h1, ihx, ihy, hc, pow_mul, hpz, one_pow]
    simp
  | inv x hx ihx =>
    rw [inv_pow, ihx, inv_one]

theorem commData_commutator {p n : ℕ} {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) {i₀ j₀ : Fin n}
    (hz : bcomm (q i₀) (q j₀) = z) :
    ⁅Subgroup.closure (Set.range q), Subgroup.closure (Set.range q)⁆ = Subgroup.zpowers z := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_eq_bcomm]
    exact hD.bcomm_mem (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ hb)
  · rw [Subgroup.zpowers_le]
    have hqi : (q i₀)⁻¹ ∈ Subgroup.closure (Set.range q) :=
      Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i₀, rfl⟩)
    have hqj : (q j₀)⁻¹ ∈ Subgroup.closure (Set.range q) :=
      Subgroup.inv_mem _ (Subgroup.subset_closure ⟨j₀, rfl⟩)
    have e : ⁅(q i₀)⁻¹, (q j₀)⁻¹⁆ = z := by
      rw [commutatorElement_eq_bcomm, inv_inv, inv_inv, hz]
    rw [← e]
    exact Subgroup.commutator_mem_commutator hqi hqj

theorem commData_inf_centralizer {p n : ℕ} [Fact p.Prime] [Finite G] {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) :
    Subgroup.closure (Set.range q) ⊓
      Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro g ⟨hgQ, hgC⟩
    have hc : (⟨g, hgQ⟩ : Subgroup.closure (Set.range q)) ∈
        Subgroup.center (Subgroup.closure (Set.range q)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgC (b : G) b.2)
    rw [hD.center_eq] at hc
    exact Subgroup.mem_subgroupOf.1 hc
  · rw [Subgroup.zpowers_le]
    refine ⟨hD.mem_z, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact hD.commute_of_mem hh (Subgroup.mem_zpowers z)

private theorem gkd_conj_pow_z {z l : G} {c : ℕ} (h : l * z * l⁻¹ = z ^ c) (j : ℕ) :
    l ^ j * z * (l ^ j)⁻¹ = z ^ (c ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc l ^ (j + 1) * z * (l ^ (j + 1))⁻¹ = l * (l ^ j * z * (l ^ j)⁻¹) * l⁻¹ := by
          simp only [pow_succ', mul_inv_rev, mul_assoc]
      _ = l * z ^ (c ^ j) * l⁻¹ := by rw [ih]
      _ = (l * z * l⁻¹) ^ (c ^ j) := conj_pow.symm
      _ = (z ^ c) ^ (c ^ j) := by rw [h]
      _ = z ^ (c ^ (j + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

private theorem gkd_exists_exp {p : ℕ} (hp : 0 < p) {z l : G} (hz : orderOf z = p)
    (h : l * z * l⁻¹ ∈ Subgroup.zpowers z) : ∃ c : ℕ, l * z * l⁻¹ = z ^ c := by
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 h
  have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  refine ⟨(e % (p : ℤ)).toNat, ?_⟩
  rw [← he, zpow_eq_zpow_emod' e hzp, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))]

private theorem gkd_pgroup_centralizes {p : ℕ} [hp : Fact p.Prime] {z s : G} (hz : orderOf z = p)
    (hs : s * z * s⁻¹ ∈ Subgroup.zpowers z) {k : ℕ} (hsk : s ^ (p ^ k) = 1) :
    s * z = z * s := by
  obtain ⟨c, hc⟩ := gkd_exists_exp hp.out.pos hz hs
  have h1 := gkd_conj_pow_z hc (p ^ k)
  rw [hsk, one_mul, inv_one, mul_one] at h1
  have h2 : (c ^ (p ^ k)) ≡ 1 [MOD p] := by
    have : z ^ (c ^ (p ^ k)) = z ^ 1 := by rw [pow_one]; exact h1.symm
    rw [pow_eq_pow_iff_modEq, hz] at this
    exact this
  have h3 : ((c : ℕ) : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
    push_cast at this
    rwa [ZMod.pow_card_pow] at this
  have h4 : c ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using h3)
  have h5 : z ^ c = z := by
    have : z ^ c = z ^ 1 := by rw [pow_eq_pow_iff_modEq, hz]; exact h4
    rwa [pow_one] at this
  rw [h5] at hc
  exact mul_inv_eq_iff_eq_mul.1 hc

private theorem gkd_pow_m_commute {p : ℕ} [hp : Fact p.Prime] {z l : G} (hz : orderOf z = p)
    (hl : l * z * l⁻¹ ∈ Subgroup.zpowers z) {m : ℕ} (hm : (p - 1) ∣ m) :
    l ^ m * z = z * l ^ m := by
  obtain ⟨c, hc⟩ := gkd_exists_exp hp.out.pos hz hl
  have hc0 : ¬ p ∣ c := by
    intro hdvd
    obtain ⟨t, rfl⟩ := hdvd
    have h1 : z ^ (p * t) = 1 := by rw [pow_mul, ← hz, pow_orderOf_eq_one, one_pow]
    rw [h1] at hc
    have : z = 1 := by
      have h2 : z = l⁻¹ * (l * z * l⁻¹) * l := by group
      rw [h2, hc]
      group
    have h3 : orderOf z = 1 := by rw [this]; exact orderOf_one
    rw [hz] at h3
    exact hp.out.one_lt.ne' h3
  have hcm : c ^ m ≡ 1 [MOD p] := by
    have hne : ((c : ℕ) : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hf : ((c : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
    obtain ⟨t, rfl⟩ := hm
    refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
    push_cast
    rw [pow_mul, hf, one_pow]
  have h1 := gkd_conj_pow_z hc m
  have h2 : z ^ (c ^ m) = z := by
    have : z ^ (c ^ m) = z ^ 1 := by rw [pow_eq_pow_iff_modEq, hz]; exact hcm
    rwa [pow_one] at this
  rw [h2] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem bmPCentralF1At_F4At_of_commData {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ} {q : Fin n → G} {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)}
    (hD : CommData p q z M) {i₀ j₀ : Fin n} (hz : bcomm (q i₀) (q j₀) = z) (L : Subgroup G)
    (hQL : Subgroup.closure (Set.range q) ≤ L)
    (hLN : L ≤ Subgroup.normalizer (Subgroup.closure (Set.range q) : Set G))
    (hLz : ∀ l ∈ L, l * z * l⁻¹ ∈ Subgroup.zpowers z)
    (hL : (Nat.card G).factorization p ≤ (Nat.card L).factorization p)
    (hCQ : ∀ P : Subgroup G,
      P ≤ Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) → IsPGroup p P →
        Nat.card P ≤ p)
    {m : ℕ} (hm : (p - 1) ∣ m)
    (hdich : ∀ N : Subgroup G, N ≤ Subgroup.closure (Set.range q) →
      (∀ a ∈ L, a ^ m ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers z ∨ N = Subgroup.closure (Set.range q))
    (hg1 : LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hno : ∀ C : Subgroup G, ¬ LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) C) :
    BMPCentralF1At p z ∧ BMPCentralF4At p z := by
  haveI hpf : Fact p.Prime := ⟨hp⟩
  have hzo : orderOf z = p := hD.orderOf_z
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p L
  have hSL : S ≤ L := hS.le
  have hSp : IsPGroup p S := hS.isPGroup
  have hQp : IsPGroup p (Subgroup.closure (Set.range q)) :=
    IsPGroup.of_card (n := n + 1) hD.card_eq
  have hQS : Subgroup.closure (Set.range q) ≤ S := by
    obtain ⟨P, rfl⟩ := hS
    haveI : ((Subgroup.closure (Set.range q)).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr hLN
    have hp' : IsPGroup p ((Subgroup.closure (Set.range q)).subgroupOf L) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
    have hle : (Subgroup.closure (Set.range q)).subgroupOf L ≤ (P : Subgroup L) :=
      IsPGroup.le_sylow_of_normal hp' P
    intro g hg
    exact Subgroup.mem_map.mpr ⟨⟨g, hQL hg⟩, hle (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  have hScard : Nat.card S = p ^ (Nat.card G).factorization p := by
    rw [hS.card_eq]
    have hdvd : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
    have hle : (Nat.card L).factorization p ≤ (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
    rw [le_antisymm hle hL]
  have hSc : S ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs
    obtain ⟨k, hk⟩ := hSp ⟨s, hs⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (gkd_pgroup_centralizes hzo (hLz s (hSL hs)) (k := k)
        (by simpa using congrArg Subtype.val hk))
  have hzS : Subgroup.zpowers z ≤ S := (Subgroup.zpowers_le.2 hD.mem_z).trans hQS
  have hQexp := commData_pow_p hp2 hD
  have hQcomm := commData_commutator hD hz
  have hQcent := commData_inf_centralizer hD
  have hzC : Subgroup.zpowers z ≤
      Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) :=
    hQcent.symm.le.trans inf_le_right
  have hCS : S ⊓ Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) =
      Subgroup.zpowers z := by
    have hz' : Subgroup.zpowers z ≤
        S ⊓ Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) := le_inf hzS hzC
    have hP3 : IsPGroup p ↥(S ⊓ Subgroup.centralizer
        (Subgroup.closure (Set.range q) : Set G)) :=
      hSp.to_le (inf_le_left : S ⊓ Subgroup.centralizer
        (Subgroup.closure (Set.range q) : Set G) ≤ S)
    have hc := hCQ (S ⊓ Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G))
      (inf_le_right : S ⊓ Subgroup.centralizer
        (Subgroup.closure (Set.range q) : Set G) ≤ _) hP3
    have hcard : Nat.card ↥(S ⊓ Subgroup.centralizer
        (Subgroup.closure (Set.range q) : Set G)) ≤ Nat.card ↥(Subgroup.zpowers z) := by
      rw [Nat.card_zpowers, hzo]
      exact hc
    exact (Subgroup.eq_of_le_of_card_ge hz' hcard).symm
  have hirr : ∀ R : Subgroup G, Subgroup.zpowers z ≤ R → R ≤ Subgroup.closure (Set.range q) →
      (∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.normalizer (Subgroup.closure (Set.range q) : Set G),
          ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = Subgroup.zpowers z ∨ R = Subgroup.closure (Set.range q) := by
    intro R hzR hRQ hinv
    have hnm : ∀ a ∈ L, a ^ m ∈ Subgroup.normalizer (R : Set G) := by
      intro a ha
      have hc : a ^ m ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (gkd_pow_m_commute hzo (hLz a ha) hm)
      have hq : a ^ m ∈ Subgroup.normalizer (Subgroup.closure (Set.range q) : Set G) :=
        Subgroup.pow_mem _ (hLN ha) m
      exact Subgroup.mem_normalizer_fintype fun r hr => hinv (a ^ m) ⟨hc, hq⟩ r hr
    rcases hdich R hRQ hnm with h1 | h1
    · exact Or.inl (le_antisymm h1 hzR)
    · exact Or.inr h1
  exact bmPCentralF1At_F4At_of_pLocal hp hzo hSp hScard hSc hQS (hSL.trans hLN) hQexp hQcomm
    hQcent hCS hirr hg1 hno

end CFSG.StandardType.SporadicShape
