module

public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.Facts.Section37

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def BabyLineOddOrder : Prop :=
  ∀ r : B, BabyInv 0 r → ∀ M : Subgroup B, M ≤ Subgroup.centralizer ({r} : Set B) →
    Odd (Nat.card M) → Nat.card M ≤ 54463 ∧
      (Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 9477) ∧
      (Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 15309)

namespace BabyReduce

section Image

variable {G : Type} [Group G] {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

noncomputable def coverImg (φ : Subgroup.centralizer ({b} : Set G) →* B) (M : Subgroup G) :
    Subgroup B :=
  (M.subgroupOf (Subgroup.centralizer ({b} : Set G))).map φ

theorem coverImg_le_centralizer {M : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hMx : M ≤ Subgroup.centralizer ({x} : Set G)) :
    coverImg φ M ≤ Subgroup.centralizer ({coverMap φ x} : Set B) := by
  rintro _ ⟨⟨y, hyC⟩, hy, rfl⟩
  have hy' : y ∈ M := Subgroup.mem_subgroupOf.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff, ← coverMap_apply hyC, ← coverMap_mul hx hyC,
    ← coverMap_mul hyC hx, Subgroup.mem_centralizer_singleton_iff.mp (hMx hy')]

theorem card_coverImg (h : IsBabyCover b φ) {M : Subgroup G}
    (hM : M ≤ Subgroup.centralizer ({b} : Set G)) (hodd : Odd (Nat.card M)) :
    Nat.card (coverImg φ M) = Nat.card M := by
  have hinj : Function.Injective
      (φ.domRestrict (M.subgroupOf (Subgroup.centralizer ({b} : Set G)))) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hmφ : coverMap φ (m : Subgroup.centralizer ({b} : Set G)).1 = 1 := by
      rw [coverMap_apply (m : Subgroup.centralizer ({b} : Set G)).2]
      exact hm
    rcases (h.coverMap_eq_one_iff (m : Subgroup.centralizer ({b} : Set G)).2).mp hmφ with e | e
    · exact Subtype.ext (Subtype.ext e)
    · exfalso
      have hbM : b ∈ M := by
        have := Subgroup.mem_subgroupOf.mp m.2
        rwa [e] at this
      have h2 : 2 ∣ Nat.card M := h.orderOf_eq ▸ Subgroup.orderOf_dvd_natCard M hbM
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h1
  rw [coverImg, ← h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv

end Image

section Transfer

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_baby_line
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {y z : G}
    (hy : IsConj a y) (hz : z ∈ twoANbr a y) {M : Subgroup G}
    (hM : M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z})
    (hodd : Odd (Nat.card M)) :
    ∃ r : B, BabyInv 0 r ∧ ∃ T : Subgroup B, T ≤ Subgroup.centralizer ({r} : Set B) ∧
      Nat.card T = Nat.card M := by
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hy).exists_cover
  obtain ⟨hzC, hz0⟩ := (mem_twoANbr_iff I.sls I.tableV I.leech I.tableIII hG hy hφ).mp hz
  exact ⟨coverMap φ z, hz0, coverImg φ M, coverImg_le_centralizer hzC (hM.trans inf_le_right),
    card_coverImg hφ (hM.trans inf_le_left) hodd⟩

end Transfer

end BabyReduce

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem lineOddOrder_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hB : BabyLineOddOrder) : LineOddOrder a := by
  intro y z hy hz M hM hodd
  obtain ⟨r, hr, T, hT, hcard⟩ := BabyReduce.exists_baby_line I hG hy hz hM hodd
  rw [← hcard] at hodd ⊢
  exact hB r hr T hT hodd

end Main

end CFSG.Monster.GMS
