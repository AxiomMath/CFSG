module

public import CFSG.RankThree.PartOne.SEITZ3.PlaneOver
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open Subgroup CFSG.RankThree.PartOne.K1214

variable {G : Type*} [Group G]

@[expose] def pairHom (A B : Subgroup G) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ↥A × ↥B →* G :=
  MonoidHom.noncommCoprod A.subtype B.subtype fun a b => h a a.2 b b.2

theorem pairHom_apply (A B : Subgroup G) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (a : ↥A) (b : ↥B) :
    pairHom A B h (a, b) = (a : G) * b := rfl

theorem pairHom_range (A B : Subgroup G) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (pairHom A B h).range = A ⊔ B := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
  · refine sup_le ?_ ?_
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by simp [pairHom_apply]⟩
    · intro b hb
      exact ⟨(1, ⟨b, hb⟩), by simp [pairHom_apply]⟩

theorem pairHom_injective {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Function.Injective (pairHom A B h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  have h1 : (a : G) * b = 1 := hab
  have h2 : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : (a : G) ∈ A ⊓ B := ⟨a.2, by rw [h2]; exact B.inv_mem b.2⟩
  rw [hAB] at h3
  have ha : (a : G) = 1 := h3
  have hb : (b : G) = 1 := by
    rw [ha, one_mul] at h1
    exact h1
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem card_sup_pair {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← pairHom_range A B h,
    ← Nat.card_congr (MonoidHom.ofInjective (pairHom_injective hAB h)).toEquiv, Nat.card_prod]

theorem closure_cenGen_eq_top_of_pair_coatoms [Finite G] [IsSimpleGroup G] {p e : ℕ}
    [Fact p.Prime] (A B : Subgroup G) (hAB : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hpA : p ∣ Nat.card A) (hpB : p ∣ Nat.card B)
    (hshape : SylowShape p 2 e G) (hnd : ¬ p ∣ (A ⊔ B).index)
    (hcoatom : ∀ N : Subgroup G, IsCoatom N → A ⊔ B ≤ N → ¬ N.index ≡ 1 [MOD p])
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure (cenGen F) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' p hpA
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' p hpB
  have ha₀p : a₀ ^ p = 1 := by rw [← ha₀]; exact pow_orderOf_eq_one a₀
  have hb₀p : b₀ ^ p = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀
    exact hp.one_lt.ne ha₀
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb₀
    exact hp.one_lt.ne hb₀
  have hzpa : ∀ a ∈ Subgroup.zpowers a₀, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₀p, one_zpow]
  have hzpb : ∀ b ∈ Subgroup.zpowers b₀, b ^ p = 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb₀p, one_zpow]
  let Φ := pairHom A B hcomm
  have hΦ : Function.Injective Φ := pairHom_injective hAB hcomm
  let E'₀ : Subgroup (↥A × ↥B) := (Subgroup.zpowers a₀).prod (Subgroup.zpowers b₀)
  let E' : Subgroup G := E'₀.map Φ
  have hE'M : E' ≤ A ⊔ B := by
    rw [← pairHom_range A B hcomm]
    exact Subgroup.map_le_range _ _
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have hab : (a, b) ^ p = (a ^ p, b ^ p) := rfl
    rw [← map_pow, hab, hzpa a ha, hzpb b hb]
    exact map_one _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hΦ]
    have h1 : Nat.card E'₀ = Nat.card (Subgroup.zpowers a₀) * Nat.card (Subgroup.zpowers b₀) :=
      (Nat.card_congr
        (Subgroup.prodEquiv (Subgroup.zpowers a₀) (Subgroup.zpowers b₀)).toEquiv).trans
        (Nat.card_prod _ _)
    rw [h1, Nat.card_zpowers, Nat.card_zpowers, ha₀, hb₀, sq]
  let M : Subgroup G := A ⊔ B
  have hEmp : IsPGroup p ↥(E'.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv, hE'c]
  obtain ⟨Q, hQ⟩ := hEmp.exists_le_sylow
  let S : Subgroup G := (Q : Subgroup ↥M).map M.subtype
  have hE'S : E' ≤ S := by
    intro x hx
    exact ⟨⟨x, hE'M hx⟩, hQ hx, rfl⟩
  have hSp : IsPGroup p ↥S := Q.isPGroup'.map M.subtype
  have hSidx : ¬ p ∣ S.index := by
    have h1 : S.index = (Q : Subgroup ↥M).index * M.index := Subgroup.index_map_subtype _
    rw [h1]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact Q.not_dvd_index h
    · exact hnd h
  obtain ⟨φ⟩ := hshape S hSp hSidx
  have hgen : M ≤ closure (cenGen E') := by
    refine sup_le ?_ ?_
    · intro a ha
      refine subset_closure ⟨(b₀ : G), ⟨(1, b₀), ⟨one_mem _, Subgroup.mem_zpowers b₀⟩, ?_⟩, ?_, ?_⟩
      · rw [pairHom_apply]; simp
      · intro h
        exact hb₀1 (Subtype.ext h)
      · exact hcomm a ha b₀ b₀.2
    · intro b hb
      refine subset_closure ⟨(a₀ : G), ⟨(a₀, 1), ⟨Subgroup.mem_zpowers a₀, one_mem _⟩, ?_⟩, ?_, ?_⟩
      · rw [pairHom_apply]; simp
      · intro h
        exact ha₀1 (Subtype.ext h)
      · exact (hcomm a₀ a₀.2 b hb).symm
  exact closure_cenGen_eq_top_of_coatoms M S E' φ hSp hSidx hE'S hE'p hE'c hcoatom hgen F hFp hFc

theorem closure_cenGen_eq_top_of_pair [Finite G] [IsSimpleGroup G] {p e : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hpA : p ∣ Nat.card A) (hpB : p ∣ Nat.card B) (hshape : SylowShape p 2 e G)
    (hmax : ∀ N : Subgroup G, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤)
    (hnd : ¬ p ∣ (A ⊔ B).index) (hmod : ¬ (A ⊔ B).index ≡ 1 [MOD p])
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure (cenGen F) = ⊤ := by
  refine closure_cenGen_eq_top_of_pair_coatoms A B hAB hcomm hpA hpB hshape hnd ?_ F hFp hFc
  intro N hN hle
  rw [(hmax N hle).resolve_right hN.1]
  exact hmod

end CFSG.RankThree.PartOne.SEITZ3
