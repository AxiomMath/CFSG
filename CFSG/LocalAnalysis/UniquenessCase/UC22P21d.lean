module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p21d_pCoreOf_le (L : Subgroup G) : pCoreOf 2 L ≤ L :=
  Subgroup.map_subtype_le _

theorem uc22p21d_conj_mem_pCoreOf {x : G} {L : Subgroup G} (hx : CentralizesBar x L) {q : G}
    (hq : q ∈ pCoreOf 2 L) : x * q * x⁻¹ ∈ pCoreOf 2 L := by
  have h := hx.2 q (uc22p21d_pCoreOf_le L hq)
  have e : x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
  rw [e]
  exact (pCoreOf 2 L).mul_mem h hq

theorem uc22p21d_centralizesBar_mul {x y : G} {L : Subgroup G} (hx : CentralizesBar x L)
    (hy : CentralizesBar y L) : CentralizesBar (x * y) L := by
  refine ⟨(normalizer (L : Set G)).mul_mem hx.1 hy.1, fun l hl => ?_⟩
  have e : x * y * l * (x * y)⁻¹ * l⁻¹ =
      (x * (y * l * y⁻¹ * l⁻¹) * x⁻¹) * (x * l * x⁻¹ * l⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 L).mul_mem (uc22p21d_conj_mem_pCoreOf hx (hy.2 l hl)) (hx.2 l hl)

theorem uc22p21d_centralizesBar_one (L : Subgroup G) : CentralizesBar (1 : G) L :=
  ⟨(normalizer (L : Set G)).one_mem, fun l _ => by simpa using (pCoreOf 2 L).one_mem⟩

theorem uc22p21d_centralizesBar_pow {x : G} {L : Subgroup G} (hx : CentralizesBar x L) (n : ℕ) :
    CentralizesBar (x ^ n) L := by
  induction n with
  | zero => simpa using uc22p21d_centralizesBar_one L
  | succ n ih => rw [pow_succ]; exact uc22p21d_centralizesBar_mul ih hx

theorem uc22p21d_centralizesBar_of_mem_zpowers {x : G} {L : Subgroup G}
    (hx : CentralizesBar x L) {g : G} (hg : g ∈ zpowers x) : CentralizesBar g L := by
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hg
  exact uc22p21d_centralizesBar_pow hx n

theorem uc22p21d_centralizesBar_iff {x : G} {L : Subgroup G} :
    CentralizesBar x L ↔ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hfwd : ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro l hl
    have e : x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l := by group
    rw [e]
    exact L.mul_mem (uc22p21d_pCoreOf_le L (h l hl)) hl
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hfwd y, fun hy => ?_⟩
  let f : ↥L → ↥L := fun l => ⟨x * l * x⁻¹, hfwd l l.2⟩
  have hf : Function.Injective f := by
    intro l₁ l₂ h12
    have h3 : x * (l₁ : G) * x⁻¹ = x * (l₂ : G) * x⁻¹ := congrArg Subtype.val h12
    exact Subtype.ext (by simpa using h3)
  obtain ⟨l, hl⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x * y * x⁻¹, hy⟩
  have h4 : x * (l : G) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hl
  have hly : (l : G) = y := by simpa using h4
  rw [← hly]
  exact l.2

theorem uc22p21d_sup_pCore_eq {L A : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hA : Nat.card A = r) (hAc : ∀ a ∈ A, CentralizesBar a L) :
    (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hAL : A ≤ normalizer (L : Set G) := fun a ha => (hAc a ha).1
  let α : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ (a : ↥A) (l : ↥L), ((α a l : ↥L) : G) = (a : G) * (l : G) * (a : G)⁻¹ :=
    fun a l => rfl
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hNmem : ∀ l : ↥L, l ∈ N ↔ (l : G) ∈ pCoreOf 2 L := by
    intro l
    constructor
    · intro hl
      exact ⟨l, hl, rfl⟩
    · rintro ⟨n, hn, hnl⟩
      have : n = l := Subtype.ext hnl
      rw [← this]
      exact hn
  have hinv : ∀ a : ↥A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    rw [hNmem] at hn ⊢
    rw [hα]
    exact uc22p21d_conj_mem_pCoreOf (hAc a a.2) hn
  have hcard : ¬ r ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hAp : IsPGroup r ↥A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have key := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting r hAp α N hinv hcard
  apply le_antisymm
  · exact sup_le inf_le_left (uc22p21d_pCoreOf_le L)
  · intro x hx
    have hq : ∀ a : ↥A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hinv a
        ((⟨x, hx⟩ : ↥L) : ↥L ⧸ N) = ((⟨x, hx⟩ : ↥L) : ↥L ⧸ N) := by
      intro a
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
        hNmem]
      have h := (hAc a a.2).2 x⁻¹ (L.inv_mem hx)
      have h2 : ((((α a) ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ : ↥L) : G) =
          (a : G) * x⁻¹ * (a : G)⁻¹ * x⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα, mul_inv_rev, inv_inv, mul_assoc]
      rw [h2]
      exact h
    have hmem : ((⟨x, hx⟩ : ↥L) : ↥L ⧸ N) ∈
        {q : ↥L ⧸ N | ∀ a : ↥A,
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hinv a q = q} := hq
    rw [key] at hmem
    obtain ⟨c, hc, hcq⟩ := hmem
    have hcx : c⁻¹ * ⟨x, hx⟩ ∈ N := QuotientGroup.eq.1 hcq
    have hcC : (c : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h' := congrArg (fun y : ↥L => (y : G)) (hc ⟨a, ha⟩)
      simp only [hα] at h'
      exact mul_inv_eq_iff_eq_mul.1 h'
    have hx' : x = (c : G) * ((c : G)⁻¹ * x) := by group
    rw [hx']
    refine ((L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L).mul_mem
      (le_sup_left (a := L ⊓ centralizer (A : Set G)) ⟨c.2, hcC⟩)
      (le_sup_right (a := L ⊓ centralizer (A : Set G)) ?_)
    have := (hNmem _).1 hcx
    simpa using this

theorem uc22p21d_odd_orderOf_of_mem_calB1 {T M L B : Subgroup G} (hB : B ∈ calB1 T M L) {x : G}
    (hx : x ∈ B) : Odd (orderOf x) := by
  obtain ⟨_, hcomm, B', C', hB', _, hCodd, _, hBeq, _⟩ := hB
  have hB'odd : Odd (Nat.card B') := hB'.2.2.2.1
  have hpowB : ∀ {y : G}, y ∈ B' → y ^ Nat.card B' = 1 := by
    intro y hy
    have h : (⟨y, hy⟩ : ↥B') ^ Nat.card ↥B' = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : ↥B' => (z : G)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hpowC : ∀ {y : G}, y ∈ C' → y ^ Nat.card C' = 1 := by
    intro y hy
    have h : (⟨y, hy⟩ : ↥C') ^ Nat.card ↥C' = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : ↥C' => (z : G)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hsup : B = Subgroup.closure ((B' : Set G) ∪ (C' : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    exact hBeq
  have key : ∀ y ∈ B, y ^ (Nat.card B' * Nat.card C') = 1 := by
    intro y hy
    rw [hsup] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · rw [pow_mul, hpowB hy, one_pow]
      · rw [mul_comm, pow_mul, hpowC hy, one_pow]
    | one => exact one_pow _
    | mul y z hy hz ihy ihz =>
      have hyB : y ∈ B := hsup ▸ hy
      have hzB : z ∈ B := hsup ▸ hz
      have hyz : Commute y z := setLike_mul_comm hyB hzB
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have hdvd : orderOf x ∣ Nat.card B' * Nat.card C' := orderOf_dvd_of_pow_eq_one (key x hx)
  exact Odd.of_dvd_nat (hB'odd.mul hCodd) hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22
