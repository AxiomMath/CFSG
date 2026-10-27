module

public import CFSG.Quasithin.Vol2.Ch10SecKRSk

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open C10P4F

variable {G : Type} [Group G] [Finite G]

@[expose] def pre {J : Subgroup G} (ρ : ↥J →* SL5) (P : Subgroup G) (Y : Subgroup SL5) :
    Subgroup G :=
  P ⊓ (Y.comap ρ).map J.subtype

omit [Finite G] in
theorem mem_pre {J : Subgroup G} {ρ : ↥J →* SL5} {P : Subgroup G} {Y : Subgroup SL5}
    (hPJ : P ≤ J) {x : G} : x ∈ pre ρ P Y ↔ ∃ hx : x ∈ P, ρ ⟨x, hPJ hx⟩ ∈ Y := by
  constructor
  · rintro ⟨hxP, ⟨j, hj, rfl⟩⟩
    exact ⟨hxP, hj⟩
  · rintro ⟨hxP, hY⟩
    exact ⟨hxP, ⟨⟨x, hPJ hxP⟩, hY, rfl⟩⟩

abbrev img {J : Subgroup G} (ρ : ↥J →* SL5) (X : Subgroup G) : Subgroup SL5 :=
  (X.subgroupOf J).map ρ

omit [Finite G] in
theorem card_eq_ker_mul {J : Subgroup G} (ρ : ↥J →* SL5) {X : Subgroup G} (hXJ : X ≤ J) :
    Nat.card X = Nat.card ↥((ρ.comp (Subgroup.inclusion hXJ)).ker) * Nat.card (img ρ X) := by
  set f := ρ.comp (Subgroup.inclusion hXJ)
  have hrange : f.range = img ρ X := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXJ x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, Subgroup.mem_subgroupOf.mp hj⟩, rfl⟩
  have h1 := f.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
  rw [h1, mul_comm]

theorem relIndex_eq_map {J : Subgroup G} (ρ : ↥J →* SL5) {S X P : Subgroup G} (hSX : S ≤ X)
    (hXP : X ≤ P) (hPJ : P ≤ J)
    (hkerS : ∀ x (hx : x ∈ P), ρ ⟨x, hPJ hx⟩ = 1 → x ∈ S) (hSU : img ρ S = uniSL 5) :
    S.relIndex X = (uniSL 5).relIndex (img ρ X) := by
  have hXJ : X ≤ J := hXP.trans hPJ
  have hSJ : S ≤ J := hSX.trans hXJ
  have hX := card_eq_ker_mul ρ hXJ
  have hS := card_eq_ker_mul ρ hSJ
  have hk : Nat.card ↥((ρ.comp (Subgroup.inclusion hXJ)).ker) =
      Nat.card ↥((ρ.comp (Subgroup.inclusion hSJ)).ker) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥((ρ.comp (Subgroup.inclusion hSJ)).ker) =>
        (⟨⟨(x : ↥S), hSX (x : ↥S).2⟩, x.2⟩ : ↥((ρ.comp (Subgroup.inclusion hXJ)).ker)))
      ⟨fun a b h => ?_, fun y => ?_⟩).symm
    · exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥((ρ.comp
        (Subgroup.inclusion hXJ)).ker) => ((z : ↥X) : G)) h))
    · have hyS : ((y : ↥X) : G) ∈ S := hkerS _ (hXP (y : ↥X).2) y.2
      exact ⟨⟨⟨(y : ↥X), hyS⟩, y.2⟩, rfl⟩
  have hSX' : S ⊓ X = S := inf_eq_left.mpr hSX
  have hUX : uniSL 5 ≤ img ρ X := hSU ▸ Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hSX (Subgroup.mem_subgroupOf.mp hx)))
  have h1 := Subgroup.relIndex_mul_card S X
  have h2 := Subgroup.relIndex_mul_card (uniSL 5) (img ρ X)
  rw [hSX'] at h1
  rw [inf_eq_left.mpr hUX] at h2
  rw [hS, hSU] at h1
  rw [hX, ← h2, hk] at h1
  have hpos : 0 < Nat.card ↥((ρ.comp (Subgroup.inclusion hSJ)).ker) * Nat.card (uniSL 5) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have h3 : S.relIndex X * (Nat.card ↥((ρ.comp (Subgroup.inclusion hSJ)).ker) *
      Nat.card (uniSL 5)) = (uniSL 5).relIndex (img ρ X) *
        (Nat.card ↥((ρ.comp (Subgroup.inclusion hSJ)).ker) * Nat.card (uniSL 5)) := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

section Pre

variable {J : Subgroup G} (ρ : ↥J →* SL5) {S P : Subgroup G} (hSP : S ≤ P) (hPJ : P ≤ J)
  (hkerS : ∀ x (hx : x ∈ P), ρ ⟨x, hPJ hx⟩ = 1 → x ∈ S) (hSU : img ρ S = uniSL 5)
include hSP hkerS hSU

omit hSP in
theorem exists_M_of_relIndex (hPQ : img ρ P ≤ Q1) {X : Subgroup G} (hSX : S ≤ X) (hXP : X ≤ P)
    (h3 : S.relIndex X = 3) : ∃ j : ℕ, 2 ≤ j ∧ j ≤ 4 ∧ X = pre ρ P (M j) := by
  have hUX : uniSL 5 ≤ img ρ X := hSU ▸ Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hSX (Subgroup.mem_subgroupOf.mp hx)))
  rw [relIndex_eq_map ρ hSX hXP hPJ hkerS hSU] at h3
  obtain ⟨j, hj1, hj4, hY⟩ := eq_M_of_le hUX h3
  have hYQ : img ρ X ≤ Q1 := (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hXP (Subgroup.mem_subgroupOf.mp hx)))).trans hPQ
  have hj2 : 2 ≤ j := by
    by_contra h
    have hj : j = 1 := by omega
    subst hj
    exact dS_mulVec_ne (mem_Q1_iff_mulVec.mpr (hYQ (hY ▸ dS_mem_M1)))
  refine ⟨j, hj2, hj4, ?_⟩
  ext x
  rw [mem_pre hPJ]
  constructor
  · intro hx
    exact ⟨hXP hx, hY ▸ ⟨⟨x, hPJ (hXP hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩⟩
  · rintro ⟨hxP, hxM⟩
    rw [← hY] at hxM
    obtain ⟨⟨x', hx'J⟩, hx'X, hx'⟩ := hxM
    have hx'X' : x' ∈ X := Subgroup.mem_subgroupOf.mp hx'X
    have hk : ρ ⟨x'⁻¹ * x, hPJ (P.mul_mem (P.inv_mem (hXP hx'X')) hxP)⟩ = 1 := by
      have : (⟨x'⁻¹ * x, hPJ (P.mul_mem (P.inv_mem (hXP hx'X')) hxP)⟩ : ↥J) =
          (⟨x', hx'J⟩ : ↥J)⁻¹ * ⟨x, hPJ hxP⟩ := rfl
      rw [this, map_mul, map_inv, hx', inv_mul_cancel]
    have hS := hkerS (x'⁻¹ * x) (P.mul_mem (P.inv_mem (hXP hx'X')) hxP) hk
    have : x = x' * (x'⁻¹ * x) := by group
    rw [this]
    exact X.mul_mem hx'X' (hSX hS)

theorem relIndex_pre_M (hQP : Q1 ≤ img ρ P) {j : ℕ} (hj2 : 2 ≤ j) (hj4 : j ≤ 4) :
    S.relIndex (pre ρ P (M j)) = 3 := by
  have hSX : S ≤ pre ρ P (M j) := fun s hs => (mem_pre hPJ).mpr ⟨hSP hs, uniSL_le_M j (by
    rw [← hSU]
    exact ⟨⟨s, hPJ (hSP hs)⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩)⟩
  have hXP : pre ρ P (M j) ≤ P := inf_le_left
  have himg : img ρ (pre ρ P (M j)) = M j := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hxJ⟩, hx, rfl⟩
      obtain ⟨_, hM⟩ := (mem_pre hPJ).mp (Subgroup.mem_subgroupOf.mp hx)
      exact hM
    · intro g hg
      obtain ⟨⟨x, hxJ⟩, hxP, rfl⟩ := hQP (M_le_Q1 hj2 hg)
      have hxP' : x ∈ P := Subgroup.mem_subgroupOf.mp hxP
      exact ⟨⟨x, hxJ⟩, Subgroup.mem_subgroupOf.mpr ((mem_pre hPJ).mpr ⟨hxP', hg⟩), rfl⟩
  rw [relIndex_eq_map ρ hSX hXP hPJ hkerS hSU, himg]
  exact relIndex_M (by omega) hj4

end Pre

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
