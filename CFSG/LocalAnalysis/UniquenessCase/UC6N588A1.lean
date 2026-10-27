module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588A

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

section Conjugation

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjugate_conjugate (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) := by
  ext x
  simp only [mem_conjugate_iff, mul_inv_rev, mul_assoc]

theorem conjugate_one (H : Subgroup G) : CFSG.conjugate H 1 = H := by
  ext x
  simp [mem_conjugate_iff]

theorem map_conj_conjugate (H : Subgroup G) (g : G) :
    (CFSG.conjugate H g).map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using mem_conjugate_iff.mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, mem_conjugate_iff.mpr ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · simp [MulAut.conj_apply, mul_assoc]

end Conjugation

section Sylow

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem exists_sylow_of_isSylowOf_top [Fact p.Prime] {S : Subgroup G} (hS : IsSylowOf p S ⊤) :
    ∃ P : Sylow p G, (P : Subgroup G) = S := by
  rw [isSylowOf_iff, Subgroup.relIndex_top_right] at hS
  exact ⟨hS.2.1.toSylow hS.2.2, rfl⟩

theorem isSylowOf_top_of_sylow [Fact p.Prime] (P : Sylow p G) :
    IsSylowOf p (P : Subgroup G) ⊤ := by
  rw [isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨le_top, P.isPGroup', P.not_dvd_index⟩

theorem exists_le_conjugate [Fact p.Prime] {S Q : Subgroup G} (hS : IsSylowOf p S ⊤)
    (hQ : IsPGroup p Q) : ∃ g : G, Q ≤ CFSG.conjugate S g := by
  obtain ⟨P, rfl⟩ := exists_sylow_of_isSylowOf_top hS
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  refine ⟨g, fun x hx => mem_conjugate_iff.mpr ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  exact ⟨x, hP' hx, by simp [MulAut.conj_apply]⟩

end Sylow

section Rank

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem pRank_conjugate (hp : 1 < p) (H : Subgroup G) (g : G) :
    CFSG.Open.pRank p (CFSG.conjugate H g) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (CFSG.conjugate H g)
    rwa [map_conj_conjugate] at h
  · exact CFSG.SectionRank.pRank_le_map hp _ (MulAut.conj g⁻¹).injective H

theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) :
    IsPGroup p E :=
  fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩

theorem pRank_le_of_isSylowOf (hp : p.Prime) {S : Subgroup G} (hS : IsSylowOf p S ⊤)
    (H : Subgroup G) : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  obtain ⟨g, hg⟩ := exists_le_conjugate hS (isPGroup_of_isElemAbelian hE)
  rw [← pRank_conjugate hp.one_lt S g]
  exact CFSG.SectionRank.le_pRank hp.one_lt hg hE hcard

theorem pRank_le_one_of_isCyclic (hp : 1 < p) {H : Subgroup G} (hH : IsCyclic H) :
    CFSG.Open.pRank p H ≤ 1 := by
  apply CFSG.SectionRank.pRank_le hp
  intro E hEH hE
  have hEc : IsCyclic E := by
    have : IsCyclic (E.subgroupOf H) := inferInstance
    exact (Subgroup.subgroupOfEquivOfLe hEH).isCyclic.mp this
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  rw [← IsCyclic.exponent_eq_card, pow_one]
  exact Nat.le_of_dvd (by omega) hexp

theorem pow_eq_one_of_card {Z : Subgroup G} (hZ : Nat.card Z = p) {z : G} (hz : z ∈ Z) :
    z ^ p = 1 := by
  have h := Subgroup.orderOf_dvd_natCard Z hz
  rw [hZ] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem isElemAbelian_of_card (hp : p.Prime) {Z : Subgroup G} (hZ : Nat.card Z = p) :
    CFSG.Open.IsElemAbelian p Z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨g, hg⟩ := hc.exists_generator
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => pow_eq_one_of_card hZ hx⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← hi, ← hj]
  exact (Commute.zpow_zpow_self g i j).eq

theorem one_le_pRank (hp : p.Prime) {Z H : Subgroup G} (hZH : Z ≤ H) (hZ : Nat.card Z = p) :
    1 ≤ CFSG.Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hZH (isElemAbelian_of_card hp hZ) (by rw [hZ, pow_one])

theorem pRank_eq_one_of_card (hp : p.Prime) {Z : Subgroup G} (hZ : Nat.card Z = p) :
    CFSG.Open.pRank p Z = 1 := by
  refine le_antisymm ?_ (one_le_pRank hp le_rfl hZ)
  apply CFSG.SectionRank.pRank_le hp.one_lt
  intro E hEZ _
  rw [pow_one, ← hZ]
  exact Subgroup.card_le_of_le hEZ

theorem two_le_pRank (hp : p.Prime) {A B H : Subgroup G} (hA : Nat.card A = p)
    (hB : Nat.card B = p) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hAH : A ≤ H) (hBH : B ≤ H) : 2 ≤ CFSG.Open.pRank p H := by
  have hAe := isElemAbelian_of_card hp hA
  have hBe := isElemAbelian_of_card hp hB
  have hAc := hAe.1
  have hBc := hBe.1
  let f : A × B →* G :=
    MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hcomm a a.2 b b.2)
  have hf : ∀ x : A × B, f x = (x.1 : G) * x.2 := fun x => rfl
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := A × B) ?_ ?_ ?_ f ?_ ?_
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact Prod.ext (mul_comm' a₁ a₂) (mul_comm' b₁ b₂)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (by simpa using hAe.2 a a.2))
      (Subtype.ext (by simpa using hBe.2 b b.2))
  · rw [Nat.card_prod, hA, hB, sq]
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hx
    rw [MonoidHom.mem_ker, hf] at hx
    have ha : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hmem : (a : G) ∈ A ⊓ B := ⟨a.2, ha ▸ B.inv_mem b.2⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have hb : (b : G) = 1 := by
      rw [hmem, eq_comm, inv_eq_one] at ha
      exact ha
    exact (Subgroup.mem_bot).mpr (Prod.ext (Subtype.ext hmem) (Subtype.ext hb))
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hf]
    exact H.mul_mem (hAH a.2) (hBH b.2)

end Rank

section WeakClosure

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem conjugate_eq_of_le_isPGroup [Fact p.Prime] {S Z Q : Subgroup G}
    (hS : IsSylowOf p S ⊤) (hwc : IsWeaklyClosedIn Z S) (hQ : IsPGroup p Q) (hZQ : Z ≤ Q)
    {g : G} (hgQ : CFSG.conjugate Z g ≤ Q) : CFSG.conjugate Z g = Z := by
  obtain ⟨h, hh⟩ := exists_le_conjugate hS hQ
  have h1 : CFSG.conjugate Z h⁻¹ = Z := by
    apply hwc
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have := mem_conjugate_iff.mp (hh (hZQ hx))
    simpa [mul_assoc] using this
  have h2 : CFSG.conjugate Z (g * h⁻¹) = Z := by
    apply hwc
    intro x hx
    rw [mem_conjugate_iff] at hx
    have hx' : h⁻¹ * x * h ∈ CFSG.conjugate Z g := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hx
    have := mem_conjugate_iff.mp (hh (hgQ hx'))
    simpa [mul_assoc] using this
  calc CFSG.conjugate Z g = CFSG.conjugate (CFSG.conjugate Z (g * h⁻¹)) h := by
        rw [conjugate_conjugate, inv_mul_cancel_right]
    _ = CFSG.conjugate Z h := by rw [h2]
    _ = CFSG.conjugate (CFSG.conjugate Z h⁻¹) h := by rw [h1]
    _ = Z := by rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]

theorem conjugate_eq_of_le_normalizer [Fact p.Prime] {S Z : Subgroup G} (hS : IsSylowOf p S ⊤)
    (hwc : IsWeaklyClosedIn Z S) (hZ : IsPGroup p Z) {g : G}
    (hg : CFSG.conjugate Z g ≤ Subgroup.normalizer (Z : Set G)) : CFSG.conjugate Z g = Z := by
  have hZg : IsPGroup p (CFSG.conjugate Z g) := hZ.map _
  exact conjugate_eq_of_le_isPGroup hS hwc (IsPGroup.to_sup_of_normal_left' hZ hZg hg)
    le_sup_left le_sup_right

end WeakClosure

structure Hyp (G : Type) [Group G] [Finite G] (p : ℕ) (S Z : Subgroup G) : Prop where
  isKGroup : CFSG.Open.IsKGroup G
  prime : p.Prime
  five_le : 5 ≤ p
  sylow : IsSylowOf p S ⊤
  omega : ∀ x ∈ S, x ^ p = 1 → ∀ y ∈ S, x * y = y * x
  rank : CFSG.Open.pRank p S ≤ 3
  le : Z ≤ S
  card : Nat.card Z = p
  wc : IsWeaklyClosedIn Z S

@[expose] def IHBelow (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (p : ℕ) (S Z : Subgroup G),
    Hyp G p S Z → CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem fact (h : Hyp G p S Z) : Fact p.Prime :=
  ⟨h.prime⟩

theorem pow_eq_one (h : Hyp G p S Z) {z : G} (hz : z ∈ Z) : z ^ p = 1 :=
  pow_eq_one_of_card h.card hz

theorem comm (h : Hyp G p S Z) {z : G} (hz : z ∈ Z) {y : G} (hy : y ∈ S) : z * y = y * z :=
  h.omega z (h.le hz) (h.pow_eq_one hz) y hy

theorem isPGroup (h : Hyp G p S Z) : IsPGroup p Z :=
  IsPGroup.of_card (n := 1) (by rw [pow_one]; exact h.card)

theorem ne_bot (h : Hyp G p S Z) : Z ≠ ⊥ := by
  intro hZ
  have h1 := h.card
  rw [hZ, Subgroup.card_bot] at h1
  exact h.prime.one_lt.ne h1

theorem conjugate_eq_of_le_isPGroup (h : Hyp G p S Z) {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hZQ : Z ≤ Q) {g : G} (hgQ : CFSG.conjugate Z g ≤ Q) : CFSG.conjugate Z g = Z :=
  haveI := h.fact
  N588A.conjugate_eq_of_le_isPGroup h.sylow h.wc hQ hZQ hgQ

theorem conjugate_eq_of_le_normalizer (h : Hyp G p S Z) {g : G}
    (hg : CFSG.conjugate Z g ≤ Subgroup.normalizer (Z : Set G)) : CFSG.conjugate Z g = Z :=
  haveI := h.fact
  N588A.conjugate_eq_of_le_normalizer h.sylow h.wc h.isPGroup hg

theorem one_le_pRank_normalClosure (h : Hyp G p S Z) :
    1 ≤ CFSG.Open.pRank p (normalClosure (Z : Set G)) :=
  one_le_pRank h.prime Subgroup.le_normalClosure h.card

theorem concl_of_le (h : Hyp G p S Z) (hle : CFSG.Open.pRank p (normalClosure (Z : Set G)) ≤ 1) :
    CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 :=
  le_antisymm hle h.one_le_pRank_normalClosure

theorem concl_of_normal (h : Hyp G p S Z) (hN : Z.Normal) :
    CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  rw [Subgroup.normalClosure_eq_self]
  exact pRank_eq_one_of_card h.prime h.card

theorem pRank_le_three (h : Hyp G p S Z) (H : Subgroup G) : CFSG.Open.pRank p H ≤ 3 :=
  (pRank_le_of_isSylowOf h.prime h.sylow H).trans h.rank

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588A
